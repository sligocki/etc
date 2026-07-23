use clap::Parser;
use post_tag::file_io::{read_unknowns, write_result};
use post_tag::simulate::simulate;
use post_tag::tag_system::TagSystem;
use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::PathBuf;
use std::time::Instant;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Input file
    input: PathBuf,

    /// Max steps
    #[arg(long, default_value_t = 10_000_000)]
    max_steps: usize,

    /// Max active tape size before classifying as holdout
    #[arg(long, default_value_t = 1_000_000)]
    max_space: usize,

    /// Output file
    output: PathBuf,

    /// Use deciders (default false, pure simulation)
    #[arg(long, default_value_t = false)]
    deciders: bool,
}

fn main() {
    let args = Args::parse();

    let unknowns = match read_unknowns(&args.input) {
        Ok(u) => u,
        Err(e) => {
            eprintln!("Error reading input file: {}", e);
            std::process::exit(1);
        }
    };

    println!(
        "Found {} Unknown programs in {:?}",
        unknowns.len(),
        args.input
    );

    let mut out_file = BufWriter::new(File::create(&args.output).unwrap());

    let mut halting = 0;
    let mut infinite = 0;
    let mut holdouts = 0;
    let mut max_halt_steps = 0;
    let mut total_steps = 0u64;

    let start_time = Instant::now();
    let total = unknowns.len();

    use rayon::prelude::*;
    use std::sync::atomic::{AtomicUsize, Ordering};

    let completed = AtomicUsize::new(0);

    let results: Vec<_> = unknowns
        .par_iter()
        .map(|prog_str| {
            let sys = TagSystem::parse(2, prog_str);
            let result = simulate(&sys, args.max_steps, args.max_space, false, args.deciders);

            let c = completed.fetch_add(1, Ordering::SeqCst) + 1;
            let pct = c as f64 / total as f64;
            let bar_len = 40;
            let filled = (pct * bar_len as f64) as usize;
            let mut bar = String::new();
            for _ in 0..filled {
                bar.push('=');
            }
            if filled < bar_len {
                bar.push('>');
            }
            for _ in (filled + 1)..bar_len {
                bar.push(' ');
            }

            let mut stdout = std::io::stdout().lock();
            write!(stdout, "\r[{}] {:.1}% ({}/{})", bar, pct * 100.0, c, total).unwrap();
            stdout.flush().unwrap();

            (sys, result)
        })
        .collect();

    for (sys, result) in results {
        write_result(&mut out_file, &sys, &result).unwrap();

        match result {
            post_tag::simulate::HaltCondition::Halted(steps, _) => {
                halting += 1;
                total_steps += steps as u64;
                if steps > max_halt_steps {
                    max_halt_steps = steps;
                }
            }
            post_tag::simulate::HaltCondition::Infinite(_, steps) => {
                infinite += 1;
                total_steps += steps as u64;
            }
            post_tag::simulate::HaltCondition::Unknown(_, steps) => {
                holdouts += 1;
                total_steps += steps as u64;
            }
            post_tag::simulate::HaltCondition::UndefinedRule(_) => {}
        }
    }

    let elapsed = start_time.elapsed();
    println!(
        "\n\nDone. Simulated {} programs in {:.3}s.",
        total,
        elapsed.as_secs_f64()
    );

    let pct_halt = if total > 0 {
        (halting as f64 / total as f64) * 100.0
    } else {
        0.0
    };
    let pct_inf = if total > 0 {
        (infinite as f64 / total as f64) * 100.0
    } else {
        0.0
    };
    let pct_hold = if total > 0 {
        (holdouts as f64 / total as f64) * 100.0
    } else {
        0.0
    };

    println!("Status Breakdown:");
    println!("  Halting  : {} ({:.2}%)", halting, pct_halt);
    println!("  Infinite : {} ({:.2}%)", infinite, pct_inf);
    println!("  Unknown  : {} ({:.2}%)", holdouts, pct_hold);

    println!("\nRuntime       : {:.3}s", elapsed.as_secs_f64());
    println!("Total steps   : {}", total_steps);

    let steps_per_sec = if elapsed.as_secs_f64() > 0.0 {
        total_steps as f64 / elapsed.as_secs_f64()
    } else {
        0.0
    };
    println!("Speed         : {:.2e} steps/sec", steps_per_sec);

    if max_halt_steps > 0 {
        println!("Max Halt Steps: {}", max_halt_steps);
    }

    println!("\nWrote results to {:?}", args.output);
}
