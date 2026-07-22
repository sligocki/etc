use clap::Parser;
use post_tag::enumerate::enumerate_systems;
use post_tag::simulate::{HaltCondition, InfiniteReason};
use post_tag::tag_system::TagSystem;
use std::fs::File;
use std::io::{BufWriter, Write};
use std::time::Instant;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Size to search
    s: usize,

    /// Output file for system execution results
    #[arg(short, long)]
    out: Option<String>,

    /// Deletion number
    #[arg(long = "del", default_value_t = 2)]
    v: usize,

    /// Max steps before classifying as holdout
    #[arg(long, default_value_t = 1_000_000)]
    max_steps: usize,
}

fn main() {
    let args = Args::parse();
    
    let mut out_file = args.out.map(|p| BufWriter::new(File::create(p).unwrap()));

    println!("Computing BB_PT(v={}, S={})", args.v, args.s);

    let mut total = 0;
    let mut max_halt_steps = 0;
    let mut best_step_sys: Vec<TagSystem> = Vec::new();
    let mut max_halt_space = 0;
    let mut best_space_sys: Vec<TagSystem> = Vec::new();
    
    let mut holdouts = 0;
    let mut infinite = 0;
    
    let mut total_steps: u64 = 0;
    
    let start_time = Instant::now();

    enumerate_systems(args.v, args.s, args.max_steps, &mut |sys, condition| {
        total += 1;
        let dense = sys.dense_string();
        match condition {
            HaltCondition::Halted(steps, space) => {
                total_steps += steps as u64;
                if steps > max_halt_steps {
                    max_halt_steps = steps;
                    best_step_sys.clear();
                    best_step_sys.push(sys.clone());
                } else if steps == max_halt_steps {
                    best_step_sys.push(sys.clone());
                }
                
                if space > max_halt_space {
                    max_halt_space = space;
                    best_space_sys.clear();
                    best_space_sys.push(sys.clone());
                } else if space == max_halt_space {
                    best_space_sys.push(sys.clone());
                }
                
                if let Some(ref mut w) = out_file {
                    writeln!(w, "prog={} status=Halt steps={} space={}", dense, steps, space).unwrap();
                }
            }
            HaltCondition::Infinite(reason, steps) => {
                total_steps += steps as u64;
                infinite += 1;
                let reason_str = match reason {
                    InfiniteReason::Cycle(period) => format!("cycle_period_{}", period),
                    InfiniteReason::ImmortalSubstring => "immortal_substring".to_string(),
                    InfiniteReason::NonDecreasingSymbol(c) => format!("non_decreasing_symbol_{}", c),
                };
                if let Some(ref mut w) = out_file {
                    writeln!(w, "prog={} status=Infinite reason={}", dense, reason_str).unwrap();
                }
            }
            HaltCondition::Unknown => {
                total_steps += args.max_steps as u64;
                holdouts += 1;
                if let Some(ref mut w) = out_file {
                    writeln!(w, "prog={} status=Unknown", dense).unwrap();
                }
            }
            HaltCondition::UndefinedRule(_) => {
                // This shouldn't happen, explore_adaptive handles it
            }
        }
    });

    let elapsed = start_time.elapsed();
    let halting = total - holdouts - infinite;

    println!("\n=== S={} ===", args.s);
    println!("Total systems : {}", total);
    
    let pct_halt = if total > 0 { (halting as f64 / total as f64) * 100.0 } else { 0.0 };
    let pct_inf = if total > 0 { (infinite as f64 / total as f64) * 100.0 } else { 0.0 };
    let pct_hold = if total > 0 { (holdouts as f64 / total as f64) * 100.0 } else { 0.0 };
    
    println!("Status Breakdown:");
    println!("  Halting  : {} ({:.2}%)", halting, pct_halt);
    println!("  Infinite : {} ({:.2}%)", infinite, pct_inf);
    println!("  Unknown  : {} ({:.2}%)", holdouts, pct_hold);
    
    println!("\nTotal steps   : {}", total_steps);
    println!("Runtime       : {:.3}s", elapsed.as_secs_f64());
    
    let steps_per_sec = if elapsed.as_secs_f64() > 0.0 {
        total_steps as f64 / elapsed.as_secs_f64()
    } else {
        0.0
    };
    println!("Speed         : {:.2e} steps/sec", steps_per_sec);
    
    if max_halt_steps > 0 {
        println!("\n  BB_PT Time  : {} steps", max_halt_steps);
        println!("  Champions   :");
        for sys in &best_step_sys {
            println!("    {}", sys.dense_string());
        }
    } else {
        println!("\n  BB_PT Time  : 0 (No systems halted!)");
    }
    
    if max_halt_space > 0 {
        println!("\n  BB_PT Space : {} length", max_halt_space);
        println!("  Champions   :");
        for sys in &best_space_sys {
            println!("    {}", sys.dense_string());
        }
    }
}
