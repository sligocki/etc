use pebble::deciders::Decider;
use pebble::enumeration::{EnumStats, TnfEnumerator};
use pebble::io::{write_records_to_file, ProgramRecord};
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
    eprintln!("  -p, --progress <COUNT>   Print progress every <COUNT> enumerated programs");
    eprintln!("  -o, --output <FILE>      Write program results to <FILE>");
    eprintln!("      --holdouts-only      When using -o, only write undecided holdout programs");
    eprintln!("      --no-deciders        Disable non-halting decider pipeline on holdouts");
    eprintln!("  -h, --help               Show this help message");
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let bin = args.first().map(String::as_str).unwrap_or("enum");

    let mut size_arg: Option<usize> = None;
    let mut max_steps: u64 = 100;
    let mut max_steps_set = false;
    let mut progress_interval: Option<u64> = None;
    let mut output_path: Option<PathBuf> = None;
    let mut holdouts_only = false;
    let mut use_deciders = true;

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
            "--no-deciders" => {
                use_deciders = false;
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

    println!("=== Pebble Automaton Enumerator (TNF) ===");
    println!("Size (n):         {size}");
    println!("Max steps:        {max_steps}");
    println!(
        "Deciders:         {}",
        if use_deciders {
            "enabled (EdgeGlider, Cycler, TranslatedCycler, SeparatedComponents)"
        } else {
            "disabled"
        }
    );
    println!();

    let mut stats = EnumStats::new(size, max_steps);
    let mut records_to_write: Vec<ProgramRecord> = Vec::new();
    let start = Instant::now();
    let mut last_report = Instant::now();

    for entry in TnfEnumerator::with_deciders(size, max_steps, use_deciders) {
        stats.record(&entry);

        if output_path.is_some() && (!holdouts_only || entry.outcome.is_holdout()) {
            records_to_write.push(ProgramRecord::new(entry.program, Some(entry.outcome)));
        }

        let should_report = match progress_interval {
            Some(interval) if interval > 0 => stats.total_programs % interval == 0,
            _ => last_report.elapsed() >= Duration::from_millis(500),
        };

        if should_report {
            let max_steps_str = stats
                .max_halting_steps
                .map(|s| s.to_string())
                .unwrap_or_else(|| "-".to_string());
            println!(
                "[Progress] programs: {} | halted: {} ({:.2}%) | decided: {} ({:.2}%) | holdouts: {} ({:.2}%) | max steps: {} | elapsed: {:.2?}",
                stats.total_programs,
                stats.halted_programs,
                stats.halted_percentage(),
                stats.decided_programs,
                stats.decided_percentage(),
                stats.holdout_programs(),
                stats.holdout_percentage(),
                max_steps_str,
                start.elapsed()
            );
            last_report = Instant::now();
        }
    }

    let elapsed = start.elapsed();
    let secs = elapsed.as_secs_f64();
    let programs_per_sec = if secs > 0.0 {
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
    println!("Total programs:         {}", stats.total_programs);
    println!(
        "Halted programs:        {} ({:.2}%)",
        stats.halted_programs,
        stats.halted_percentage()
    );
    if use_deciders {
        println!(
            "Decided non-halting:    {} ({:.2}%)",
            stats.decided_programs,
            stats.decided_percentage()
        );
        for decider in Decider::ALL {
            let count = stats.decided_count(decider);
            let pct = if stats.total_programs > 0 {
                (count as f64 / stats.total_programs as f64) * 100.0
            } else {
                0.0
            };
            println!("  - {:<20} {} ({:.2}%)", format!("{decider}:"), count, pct);
        }
    }
    println!(
        "Holdout programs:       {} ({:.2}%)",
        stats.holdout_programs(),
        stats.holdout_percentage()
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
    println!("Throughput:             {:.0} programs/s", programs_per_sec);
}
