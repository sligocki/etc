use pebble::enumeration::{CartesianEnumerator, EnumEntry, EnumStats, TnfEnumerator};
use pebble::io::{write_records_to_file, ProgramRecord};
use pebble::program::Program;
use std::env;
use std::path::PathBuf;
use std::process;
use std::time::{Duration, Instant};

fn print_usage(bin: &str) {
    eprintln!("Usage: {bin} [OPTIONS] <SIZE> [MAX_STEPS]");
    eprintln!();
    eprintln!("Arguments:");
    eprintln!("  <SIZE>                   Program size / initial pebble count n (e.g. 5)");
    eprintln!("  [MAX_STEPS]              Maximum steps per program (default: 100)");
    eprintln!();
    eprintln!("Options:");
    eprintln!("  -s, --steps <STEPS>      Maximum steps per program (overrides positional)");
    eprintln!("  -p, --progress <COUNT>   Print progress every <COUNT> simulated programs");
    eprintln!("  -o, --output <FILE>      Write program results to <FILE>");
    eprintln!("      --holdouts-only      When using -o, only write non-halting holdout programs");
    eprintln!("      --cartesian          Enumerate all full Cartesian programs instead of TNF");
    eprintln!("  -h, --help               Show this help message");
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let bin = args.first().map(String::as_str).unwrap_or("enum");

    let mut size_arg: Option<usize> = None;
    let mut max_steps: u64 = 100;
    let mut max_steps_set = false;
    let mut progress_interval: Option<u128> = None;
    let mut output_path: Option<PathBuf> = None;
    let mut holdouts_only = false;
    let mut use_cartesian = false;

    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "-h" | "--help" => {
                print_usage(bin);
                return;
            }
            "-s" | "--steps" => {
                i += 1;
                if i >= args.len() {
                    eprintln!("Error: missing value for --steps");
                    process::exit(1);
                }
                max_steps = args[i].parse().unwrap_or_else(|_| {
                    eprintln!("Error: invalid step count '{}'", args[i]);
                    process::exit(1);
                });
                max_steps_set = true;
            }
            "-p" | "--progress" => {
                i += 1;
                if i >= args.len() {
                    eprintln!("Error: missing value for --progress");
                    process::exit(1);
                }
                progress_interval = Some(args[i].parse().unwrap_or_else(|_| {
                    eprintln!("Error: invalid progress interval '{}'", args[i]);
                    process::exit(1);
                }));
            }
            "-o" | "--output" => {
                i += 1;
                if i >= args.len() {
                    eprintln!("Error: missing file path for --output");
                    process::exit(1);
                }
                output_path = Some(PathBuf::from(&args[i]));
            }
            "--holdouts-only" => {
                holdouts_only = true;
            }
            "--cartesian" => {
                use_cartesian = true;
            }
            arg if arg.starts_with('-') => {
                eprintln!("Error: unknown option '{arg}'");
                print_usage(bin);
                process::exit(1);
            }
            arg => {
                if size_arg.is_none() {
                    size_arg = Some(arg.parse().unwrap_or_else(|_| {
                        eprintln!("Error: invalid size '{arg}'");
                        process::exit(1);
                    }));
                } else if !max_steps_set {
                    max_steps = arg.parse().unwrap_or_else(|_| {
                        eprintln!("Error: invalid max_steps '{arg}'");
                        process::exit(1);
                    });
                    max_steps_set = true;
                } else {
                    eprintln!("Error: unexpected argument '{arg}'");
                    print_usage(bin);
                    process::exit(1);
                }
            }
        }
        i += 1;
    }

    let Some(size) = size_arg else {
        print_usage(bin);
        process::exit(1);
    };
    if size == 0 {
        eprintln!("Error: size must be at least 1");
        process::exit(1);
    }

    let total_cartesian = Program::total_cartesian_programs(size);
    let mode_label = if use_cartesian {
        "Cartesian (full)"
    } else {
        "Tree-Normal-Form (TNF)"
    };

    println!("=== Pebble Automaton Enumerator ===");
    println!("Size (n):         {size}");
    println!("Max steps:        {max_steps}");
    println!("Mode:             {mode_label}");
    println!("Total space:      {total_cartesian} Cartesian programs");
    println!();

    let mut stats = EnumStats::new(size, max_steps);
    let mut records_to_write: Vec<ProgramRecord> = Vec::new();
    let start = Instant::now();
    let mut last_report = Instant::now();

    let iter: Box<dyn Iterator<Item = EnumEntry>> = if use_cartesian {
        Box::new(CartesianEnumerator::new(size).with_simulation(max_steps))
    } else {
        Box::new(TnfEnumerator::new(size, max_steps))
    };

    for entry in iter {
        stats.record(&entry);

        if output_path.is_some() && (!holdouts_only || !entry.outcome.is_halted()) {
            records_to_write.push(ProgramRecord::new(entry.program, Some(entry.outcome)));
        }

        let should_report = match progress_interval {
            Some(interval) if interval > 0 => stats.leaves_simulated % interval == 0,
            _ => last_report.elapsed() >= Duration::from_millis(500),
        };

        if should_report {
            let pct_space = if total_cartesian > 0 {
                (stats.total_programs as f64 / total_cartesian as f64) * 100.0
            } else {
                100.0
            };
            let max_steps_str = stats
                .max_halting_steps
                .map(|s| s.to_string())
                .unwrap_or_else(|| "-".to_string());
            println!(
                "[Progress {:>6.2}%] simulated: {} | halted: {} ({:.2}%) | max steps: {} | elapsed: {:.2?}",
                pct_space,
                stats.leaves_simulated,
                stats.halted_programs,
                stats.halted_percentage(),
                max_steps_str,
                start.elapsed()
            );
            last_report = Instant::now();
        }
    }

    let elapsed = start.elapsed();
    let secs = elapsed.as_secs_f64();
    let leaves_per_sec = if secs > 0.0 {
        stats.leaves_simulated as f64 / secs
    } else {
        stats.leaves_simulated as f64
    };
    let cartesian_per_sec = if secs > 0.0 {
        stats.total_programs as f64 / secs
    } else {
        stats.total_programs as f64
    };

    if let Some(ref path) = output_path {
        if let Err(err) = write_records_to_file(path, &records_to_write) {
            eprintln!("Error writing output file '{}': {err}", path.display());
            process::exit(1);
        }
        println!(
            "Wrote {} records to {}",
            records_to_write.len(),
            path.display()
        );
        println!();
    }

    println!("=== Final Statistics (peBBle({size}), max_steps = {max_steps}) ===");
    if !use_cartesian {
        println!(
            "TNF leaves simulated:   {} (halted: {} / {:.2}%, holdouts: {} / {:.2}%)",
            stats.leaves_simulated,
            stats.leaves_halted,
            stats.leaves_halted_percentage(),
            stats.holdout_leaves(),
            100.0 - stats.leaves_halted_percentage()
        );
    }
    println!("Total programs (n={size}):   {}", stats.total_programs);
    println!(
        "Halted programs:        {} ({:.2}%)",
        stats.halted_programs,
        stats.halted_percentage()
    );
    println!(
        "Holdout programs:       {} ({:.2}%)",
        stats.holdout_programs(),
        if stats.total_programs > 0 {
            100.0 - stats.halted_percentage()
        } else {
            0.0
        }
    );
    match (&stats.max_halting_steps, &stats.champion) {
        (Some(max_s), Some(champ)) => {
            println!("Max halting step count: {max_s}");
            println!("Champion program:       {champ}");
        }
        _ => {
            println!("Max halting step count: none");
        }
    }
    println!("Wallclock runtime:      {:.3?}", elapsed);
    println!(
        "Throughput:             {:.0} leaves/s ({:.0} Cartesian programs/s)",
        leaves_per_sec, cartesian_per_sec
    );
}
