pub mod enumerator;
pub mod parser;
pub mod simulator;
pub mod tm;

use clap::{Parser, Subcommand};
use simulator::SimResult;

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Simulate a specific TM
    Simulate {
        /// The TM string in Standard Text Format (e.g. 1RB1GC_1BC0RC)
        tm: String,

        /// The step limit
        #[arg(short, long)]
        steps: u64,
    },
    /// Enumerate all TMs with a given number of states and symbols
    Enumerate {
        /// Number of states
        states: u8,

        /// Number of symbols (default 2)
        #[arg(short, long, default_value_t = 2)]
        symbols: u8,

        /// The step limit
        #[arg(short, long)]
        steps: u64,

        /// Optional file to output all generated TMs to
        #[arg(short, long)]
        output: Option<String>,
    },
}

fn main() {
    let cli = Cli::parse();

    match &cli.command {
        Commands::Simulate { tm, steps } => {
            let turing_machine = match parser::parse_tm(tm) {
                Ok(tm) => tm,
                Err(e) => {
                    eprintln!("Failed to parse TM: {}", e);
                    std::process::exit(1);
                }
            };

            let mut sim = simulator::Simulator::new();
            let result = sim.run(&turing_machine, *steps);

            match result {
                SimResult::Halt(s, score) => {
                    println!("Halt {} {}", s, score);
                }
                SimResult::LimitReached => {
                    println!("Unknown");
                }
                SimResult::UndefinedTrans => {
                    println!("Hit undefined transition");
                }
            }
        }
        Commands::Enumerate {
            states,
            symbols,
            steps,
            output,
        } => {
            let mut num_halt = 0;
            let mut num_unknown = 0;
            let mut num_total = 0;
            let mut max_steps = 0;
            let mut max_steps_tms = Vec::new();
            let mut max_score = 0;
            let mut max_score_tms = Vec::new();
            let mut max_time = std::time::Duration::ZERO;
            
            let start_time = std::time::Instant::now();
            let mut out_file = output.as_ref().map(|p| std::fs::File::create(p).unwrap());
            
            use std::io::Write;

            let (tx, rx) = std::sync::mpsc::channel();
            enumerator::enumerate(*states, *symbols, *steps, tx);

            for (tm, result, duration) in rx {
                num_total += 1;
                if duration > max_time {
                    max_time = duration;
                }

                let tm_str = parser::tm_to_string(&tm);
                let result_str = match result {
                    SimResult::Halt(s, score) => {
                        num_halt += 1;
                        if s > max_steps { 
                            max_steps = s; 
                            max_steps_tms.clear();
                            max_steps_tms.push(tm_str.clone());
                        } else if s == max_steps {
                            max_steps_tms.push(tm_str.clone());
                        }

                        if score > max_score { 
                            max_score = score; 
                            max_score_tms.clear();
                            max_score_tms.push(tm_str.clone());
                        } else if score == max_score {
                            max_score_tms.push(tm_str.clone());
                        }
                        
                        format!("Halt {} {}", s, score)
                    }
                    SimResult::LimitReached => {
                        num_unknown += 1;
                        "Unknown".to_string()
                    }
                    SimResult::UndefinedTrans => unreachable!(),
                };

                if let Some(f) = &mut out_file {
                    writeln!(f, "{} {}", tm_str, result_str).unwrap();
                }

                if num_total % 100_000 == 0 {
                    let pct_halt = if num_total > 0 {
                        (num_halt as f64 / num_total as f64) * 100.0
                    } else {
                        0.0
                    };
                    let now = chrono::Local::now().format("%H:%M:%S").to_string();
                    let step_champ = max_steps_tms.first().map(|s| s.as_str()).unwrap_or("None");
                    let score_champ = max_score_tms.first().map(|s| s.as_str()).unwrap_or("None");
                    
                    println!(
                        "[{}] Total: {} | Halt: {} ({:.2}%) | Max Steps: {} ({}) | Max Score: {} ({})",
                        now, num_total, num_halt, pct_halt, max_steps, step_champ, max_score, score_champ
                    );
                }
            }

            let total_elapsed = start_time.elapsed();
            let avg_time = if num_total > 0 {
                total_elapsed / num_total as u32
            } else {
                std::time::Duration::ZERO
            };

            println!("--- Enumeration Complete ---");
            println!("Total TMs generated : {}", num_total);
            if num_total > 0 {
                println!("Halted              : {} ({:.2}%)", num_halt, (num_halt as f64 / num_total as f64) * 100.0);
                println!("Unknown (Limit)     : {} ({:.2}%)", num_unknown, (num_unknown as f64 / num_total as f64) * 100.0);
            }
            println!("Max Halt Steps      : {}", max_steps);
            if !max_steps_tms.is_empty() {
                println!("Max Steps TMs       :");
                for (i, t) in max_steps_tms.iter().take(5).enumerate() {
                    println!("  {}", t);
                }
                if max_steps_tms.len() > 5 {
                    println!("  ... and {} more", max_steps_tms.len() - 5);
                }
            }

            println!("Max Halt Score      : {}", max_score);
            if !max_score_tms.is_empty() {
                println!("Max Score TMs       :");
                for (i, t) in max_score_tms.iter().take(5).enumerate() {
                    println!("  {}", t);
                }
                if max_score_tms.len() > 5 {
                    println!("  ... and {} more", max_score_tms.len() - 5);
                }
            }

            println!("Total Wallclock Time: {:?}", total_elapsed);
            println!("Avg Time per TM     : {:?}", avg_time);
            println!("Max Time for a TM   : {:?}", max_time);
        }
    }
}
