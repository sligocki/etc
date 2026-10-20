use pebble::enumeration::{enumerate_parallel, ProgressSnapshot};
use pebble::io::{write_records_to_file, ProgramRecord};
use std::env;
use std::path::PathBuf;
use std::process;
use std::sync::Mutex;
use std::time::{Duration, Instant};

fn format_duration(d: Duration) -> String {
    let nanos = d.as_nanos();
    if nanos < 1_000 {
        format!("{nanos} ns")
    } else if nanos < 1_000_000 {
        format!("{:.2} µs", nanos as f64 / 1_000.0)
    } else if nanos < 1_000_000_000 {
        format!("{:.2} ms", nanos as f64 / 1_000_000.0)
    } else {
        format!("{:.2} s", nanos as f64 / 1_000_000_000.0)
    }
}

fn print_usage(bin: &str) {
    eprintln!("Usage: {bin} [OPTIONS] <SIZE> [DEEP_STEPS]");
    eprintln!();
    eprintln!("Arguments:");
    eprintln!("  <SIZE>                     Program size / initial pebble count n (e.g. 5)");
    eprintln!("  [DEEP_STEPS]               Maximum deep steps per program (default: 100)");
    eprintln!();
    eprintln!("Options:");
    eprintln!("  -s, --steps <STEPS>        Maximum deep steps per program (overrides positional)");
    eprintln!("  -e, --early-steps <STEPS>  Early simulation / branching steps (default: min(100, deep_steps))");
    eprintln!("  -j, --threads <THREADS>    Number of Rayon worker threads (default: all cores)");
    eprintln!("  -p, --progress <SECS>      Progress update interval in seconds (default: 10s)");
    eprintln!("  -o, --output <FILE>        Write program results to <FILE>");
    eprintln!("      --holdouts-only        When using -o, only write undecided holdout programs");
    eprintln!("      --no-deciders          Disable non-halting decider pipeline on holdouts");
    eprintln!("      --no-symmetry          Disable left-right symmetry reduction (enumerate full space)");
    eprintln!("  -h, --help                 Show this help message");
}

fn parse_duration_arg(raw: &str) -> Result<Duration, String> {
    let s = raw.trim();
    if let Some(ms_str) = s.strip_suffix("ms") {
        let ms: f64 = ms_str
            .trim()
            .parse()
            .map_err(|_| format!("invalid duration '{raw}'"))?;
        if ms < 0.0 || !ms.is_finite() {
            return Err(format!("invalid duration '{raw}'"));
        }
        return Ok(Duration::from_secs_f64(ms / 1000.0));
    }
    let secs_str = s.strip_suffix('s').unwrap_or(s).trim();
    let secs: f64 = secs_str
        .parse()
        .map_err(|_| format!("invalid duration '{raw}'"))?;
    if secs < 0.0 || !secs.is_finite() {
        return Err(format!("invalid duration '{raw}'"));
    }
    Ok(Duration::from_secs_f64(secs))
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let bin = args.first().map(String::as_str).unwrap_or("enum");

    let mut size_arg: Option<usize> = None;
    let mut deep_steps: u64 = 100;
    let mut deep_steps_set = false;
    let mut early_steps_arg: Option<u64> = None;
    let mut num_threads: Option<usize> = None;
    let mut progress_interval = Duration::from_secs(10);
    let mut output_path: Option<PathBuf> = None;
    let mut holdouts_only = false;
    let mut use_deciders = true;
    let mut break_symmetry = true;

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
                deep_steps = args[i].parse().unwrap_or_else(|_| {
                    eprintln!("Error: invalid step count '{}'", args[i]);
                    process::exit(1);
                });
                deep_steps_set = true;
            }
            "-e" | "--early-steps" => {
                i += 1;
                if i >= args.len() {
                    eprintln!("Error: missing value for --early-steps");
                    process::exit(1);
                }
                early_steps_arg = Some(args[i].parse().unwrap_or_else(|_| {
                    eprintln!("Error: invalid early step count '{}'", args[i]);
                    process::exit(1);
                }));
            }
            "-j" | "--threads" => {
                i += 1;
                if i >= args.len() {
                    eprintln!("Error: missing value for --threads");
                    process::exit(1);
                }
                num_threads = Some(args[i].parse().unwrap_or_else(|_| {
                    eprintln!("Error: invalid thread count '{}'", args[i]);
                    process::exit(1);
                }));
            }
            "-p" | "--progress" => {
                i += 1;
                if i >= args.len() {
                    eprintln!("Error: missing value for --progress");
                    process::exit(1);
                }
                progress_interval = parse_duration_arg(&args[i]).unwrap_or_else(|err| {
                    eprintln!("Error: {err}");
                    process::exit(1);
                });
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
            "--no-symmetry" | "--all-symmetries" => {
                break_symmetry = false;
            }
            "--symmetry" => {
                break_symmetry = true;
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
                } else if !deep_steps_set {
                    deep_steps = arg.parse().unwrap_or_else(|_| {
                        eprintln!("Error: invalid deep_steps '{arg}'");
                        process::exit(1);
                    });
                    deep_steps_set = true;
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
    };

    if let Some(threads) = num_threads {
        if let Err(err) = rayon::ThreadPoolBuilder::new()
            .num_threads(threads)
            .build_global()
        {
            eprintln!("Error configuring Rayon thread pool: {err}");
            process::exit(1);
        }
    }

    let early_steps = early_steps_arg
        .unwrap_or_else(|| 100.min(deep_steps))
        .min(deep_steps);

    println!("=== Pebble Automaton Enumerator (TNF) ===");
    println!("Size (n):         {size}");
    println!("Early steps:      {early_steps}");
    println!("Deep steps:       {deep_steps}");
    println!("Threads:          {}", rayon::current_num_threads());
    println!(
        "Deciders:         {}",
        if use_deciders {
            "enabled (EdgeGlider, Cycler, TranslatedCycler, SeparatedComponents, Bouncer, CTL, StaticBacktrack)"
        } else {
            "disabled"
        }
    );
    println!(
        "Symmetry:         {}",
        if break_symmetry {
            "reduced (breaking left-right mirror symmetry)"
        } else {
            "full (enumerating all mirror programs)"
        }
    );
    println!();

    let start = Instant::now();
    let last_report = Mutex::new(Instant::now());

    let should_report = |_snap: &ProgressSnapshot| -> bool {
        if progress_interval.is_zero() {
            return false;
        }
        last_report
            .try_lock()
            .map(|t| t.elapsed() >= progress_interval)
            .unwrap_or(false)
    };

    let on_progress = |snap: &ProgressSnapshot| {
        if let Ok(mut t) = last_report.lock() {
            *t = Instant::now();
        }
        let tot_f = snap.total_programs.max(1) as f64;
        let halt_pct = (snap.halted_programs as f64 / tot_f) * 100.0;
        let dec_pct = (snap.decided_programs as f64 / tot_f) * 100.0;
        let hold_pct = (snap.holdout_programs as f64 / tot_f) * 100.0;
        let max_steps_str = snap
            .max_halting_steps
            .map(|s| s.to_string())
            .unwrap_or_else(|| "-".to_string());
        println!(
            "[Progress] programs: {} | halted: {} ({:.2}%) | decided: {} ({:.2}%) | holdouts: {} ({:.2}%) | max steps: {} | elapsed: {:.2?}",
            snap.total_programs,
            snap.halted_programs,
            halt_pct,
            snap.decided_programs,
            dec_pct,
            snap.holdout_programs,
            hold_pct,
            max_steps_str,
            start.elapsed()
        );
    };

    let (stats, entries) = enumerate_parallel(
        size,
        early_steps,
        deep_steps,
        use_deciders,
        break_symmetry,
        output_path.is_some(),
        holdouts_only,
        on_progress,
        should_report,
    );
    let records_to_write: Vec<ProgramRecord> = entries
        .into_iter()
        .map(|e| ProgramRecord::new(e.program, Some(e.outcome)))
        .collect();

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

    println!("=== Final Statistics (peBBle({size}), early_steps = {early_steps}, deep_steps = {deep_steps}) ===");
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

    if use_deciders {
        println!();
        println!("=== Pipeline & Decider Performance ===");
        println!(
            "{:<42} {:>10} {:>10} {:>10} {:>14} {:>14}",
            "Stage / Decider", "Run On", "Halted", "Infinite", "Total Time", "Avg / Prog"
        );
        println!("{:-<104}", "");
        for stage in &stats.stages {
            let m = &stage.metrics;
            let tot_time_str = format_duration(m.total_time());
            let avg_time_str = m
                .avg_time()
                .map(format_duration)
                .unwrap_or_else(|| "-".to_string());
            println!(
                "{:<42} {:>10} {:>10} {:>10} {:>14} {:>14}",
                stage.name,
                m.invocations,
                m.decided_halting,
                m.decided_infinite,
                tot_time_str,
                avg_time_str,
            );
        }
        println!("{:-<104}", "");

        if stats.ctl_proofs_count > 0 {
            println!();
            println!(
                "=== CTL Proof Statistics ({} proved) ===",
                stats.ctl_proofs_count
            );
            let avg_steps = stats.ctl_total_steps as f64 / stats.ctl_proofs_count as f64;
            println!(
                "Steps:            min = {}, avg = {:.1}, max = {}",
                stats.ctl_min_steps, avg_steps, stats.ctl_max_steps
            );
            let avg_states = stats.ctl_total_states as f64 / stats.ctl_proofs_count as f64;
            println!(
                "States:           min = {}, avg = {:.1}, max = {}",
                stats.ctl_min_states, avg_states, stats.ctl_max_states
            );

            let mod_str = stats
                .ctl_mod_counts
                .iter()
                .map(|(m, c)| format!("mod={m} ({c})"))
                .collect::<Vec<_>>()
                .join(", ");
            println!("Moduli:           {}", mod_str);
        }
    }
}
