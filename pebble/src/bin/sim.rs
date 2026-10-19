use pebble::enumeration::{EnumEntry, EnumStats};
use pebble::io::{read_records_from_file, write_records_to_file, ProgramRecord};
use pebble::program::{Program, Rule};
use pebble::simulation::{format_trace_bounds, simulate_with_trace, SimOutcome, Simulator};
use rayon::prelude::*;
use std::env;
use std::path::{Path, PathBuf};
use std::process;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Mutex;
use std::time::{Duration, Instant};

fn print_usage(bin: &str) {
    eprintln!("Usage:");
    eprintln!("  {bin} [OPTIONS] <PROGRAM>");
    eprintln!("  {bin} [OPTIONS] -i <INFILE> [-o <OUTFILE>]");
    eprintln!("  {bin} [OPTIONS] <INFILE> [OUTFILE]");
    eprintln!();
    eprintln!("Arguments:");
    eprintln!("  <PROGRAM>                Single program in short notation (e.g. 00_11_03_21_04)");
    eprintln!("  <INFILE>                 Path to input file containing programs/records");
    eprintln!("  [OUTFILE]                Optional path to write simulation results");
    eprintln!();
    eprintln!("Options:");
    eprintln!("  -i, --input <FILE>       Read programs to simulate from <FILE> (alias: --infile)");
    eprintln!("  -o, --output <FILE>      Write simulation results to <FILE> (alias: --outfile)");
    eprintln!("      --holdouts-only      When writing output file, only write undecided holdouts");
    eprintln!("  -s, --steps <STEPS>      Maximum number of steps to simulate (default: 1000)");
    eprintln!("  -j, --threads <THREADS>  Number of Rayon worker threads for file mode");
    eprintln!("  -v, --verbose            Print the tape configuration at every step (single program)");
    eprintln!("  -h, --help               Show this help message");
}

fn simulate_tnf_subtree(
    program: Program,
    mut sim: Simulator,
    max_steps: u64,
    out: &mut Vec<EnumEntry>,
) {
    match sim.run(&program, max_steps) {
        SimOutcome::MissingRule { pebbles, .. } => {
            for rule in Rule::all_for_pebbles(pebbles) {
                let mut child_prog = program.clone();
                child_prog
                    .set_rule(pebbles, Some(rule))
                    .expect("valid rule for pebbles");
                let child_sim = sim.clone();
                simulate_tnf_subtree(child_prog, child_sim, max_steps, out);
            }
        }
        outcome => {
            out.push(EnumEntry { program, outcome });
        }
    }
}

fn run_file_mode(infile: &Path, outfile: Option<&Path>, max_steps: u64, holdouts_only: bool) {
    let input_records = read_records_from_file(infile).unwrap_or_else(|err| {
        eprintln!("Error reading input file '{}': {err}", infile.display());
        process::exit(1);
    });

    let total_input = input_records.len();
    let size = input_records.first().map(|r| r.program.size()).unwrap_or(0);

    println!("=== Pebble Automaton Batch Simulator ===");
    println!("Input file:       {} ({total_input} programs)", infile.display());
    if let Some(out) = outfile {
        println!(
            "Output file:      {}{}",
            out.display(),
            if holdouts_only { " (holdouts only)" } else { "" }
        );
    }
    println!("Max steps:        {max_steps}");
    println!("Threads:          {}", rayon::current_num_threads());
    println!();

    let start = Instant::now();
    let last_report = Mutex::new(Instant::now());
    let live_input_done = AtomicU64::new(0);
    let live_total_out = AtomicU64::new(0);
    let live_halted = AtomicU64::new(0);

    let nested_results: Vec<Vec<EnumEntry>> = input_records
        .into_par_iter()
        .map(|rec| {
            let mut local_entries = Vec::with_capacity(1);
            let sim = Simulator::new(rec.program.size());
            simulate_tnf_subtree(rec.program, sim, max_steps, &mut local_entries);

            let local_halt = local_entries
                .iter()
                .filter(|e| matches!(e.outcome, SimOutcome::Halted { .. }))
                .count() as u64;
            let local_out = local_entries.len() as u64;

            let in_done = live_input_done.fetch_add(1, Ordering::Relaxed) + 1;
            let tot_out = live_total_out.fetch_add(local_out, Ordering::Relaxed) + local_out;
            let halt = if local_halt > 0 {
                live_halted.fetch_add(local_halt, Ordering::Relaxed) + local_halt
            } else {
                live_halted.load(Ordering::Relaxed)
            };

            if in_done % 256 == 0 {
                if let Ok(mut last) = last_report.try_lock() {
                    if last.elapsed() >= Duration::from_millis(500) {
                        let hold = tot_out.saturating_sub(halt);
                        let tot_f = tot_out.max(1) as f64;
                        println!(
                            "[Progress] in: {in_done}/{total_input} | out: {tot_out} | halted: {halt} ({:.2}%) | holdouts: {hold} ({:.2}%) | elapsed: {:.2?}",
                            (halt as f64 / tot_f) * 100.0,
                            (hold as f64 / tot_f) * 100.0,
                            start.elapsed()
                        );
                        *last = Instant::now();
                    }
                }
            }

            local_entries
        })
        .collect();

    let elapsed = start.elapsed();
    let mut stats = EnumStats::new(size, max_steps);
    let mut out_records = Vec::new();
    for group in nested_results {
        for entry in group {
            stats.record(&entry);
            if outfile.is_some() && (!holdouts_only || entry.outcome.is_holdout()) {
                out_records.push(ProgramRecord::new(entry.program, Some(entry.outcome)));
            }
        }
    }

    if let Some(out_path) = outfile {
        if let Err(err) = write_records_to_file(out_path, &out_records) {
            eprintln!("Error writing output file '{}': {err}", out_path.display());
            process::exit(1);
        }
        println!(
            "Wrote {} records to {}",
            out_records.len(),
            out_path.display()
        );
        println!();
    }

    let secs = elapsed.as_secs_f64();
    let programs_per_sec = if secs > 0.0 {
        stats.total_programs as f64 / secs
    } else {
        stats.total_programs as f64
    };

    let holdouts = stats.holdout_programs();
    let hold_pct = if stats.total_programs > 0 {
        (holdouts as f64 / stats.total_programs as f64) * 100.0
    } else {
        0.0
    };

    println!("=== Batch Simulation Summary (max_steps = {max_steps}) ===");
    println!("Total input programs:   {total_input}");
    println!("Total output programs:  {}", stats.total_programs);
    println!(
        "Halted programs:        {} ({:.2}%)",
        stats.halted_programs,
        stats.halted_percentage()
    );
    println!("Holdout programs:       {holdouts} ({hold_pct:.2}%)");
    if let (Some(max_s), Some(champ)) = (&stats.max_halting_steps, &stats.champion) {
        println!("Max halting step count: {max_s}");
        println!("Champion program:       {champ}");
    }
    println!("Wallclock runtime:      {:.3?}", elapsed);
    println!("Throughput:             {:.0} programs/s", programs_per_sec);
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let bin = args.first().map(String::as_str).unwrap_or("sim");

    let mut verbose = false;
    let mut holdouts_only = false;
    let mut max_steps: u64 = 1000;
    let mut max_steps_set = false;
    let mut num_threads: Option<usize> = None;
    let mut input_path: Option<PathBuf> = None;
    let mut output_path: Option<PathBuf> = None;
    let mut positionals: Vec<String> = Vec::new();

    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "-h" | "--help" => {
                print_usage(bin);
                return;
            }
            "-v" | "--verbose" => {
                verbose = true;
            }
            "--holdouts-only" => {
                holdouts_only = true;
            }
            "-i" | "--input" | "--infile" => {
                i += 1;
                if i >= args.len() {
                    eprintln!("Error: missing value for --input");
                    process::exit(1);
                }
                input_path = Some(PathBuf::from(&args[i]));
            }
            "-o" | "--output" | "--outfile" => {
                i += 1;
                if i >= args.len() {
                    eprintln!("Error: missing value for --output");
                    process::exit(1);
                }
                output_path = Some(PathBuf::from(&args[i]));
            }
            "-s" | "--steps" => {
                i += 1;
                if i >= args.len() {
                    eprintln!("Error: missing value for --steps");
                    print_usage(bin);
                    process::exit(1);
                }
                max_steps = args[i].parse().unwrap_or_else(|_| {
                    eprintln!("Error: invalid step count '{}'", args[i]);
                    process::exit(1);
                });
                max_steps_set = true;
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
            arg if arg.starts_with('-') => {
                eprintln!("Error: unknown option '{arg}'");
                print_usage(bin);
                process::exit(1);
            }
            arg => {
                positionals.push(arg.to_string());
            }
        }
        i += 1;
    }

    if let Some(threads) = num_threads {
        if let Err(err) = rayon::ThreadPoolBuilder::new()
            .num_threads(threads)
            .build_global()
        {
            eprintln!("Error configuring Rayon thread pool: {err}");
            process::exit(1);
        }
    }

    // Resolve positional arguments into either file mode or single-program mode
    if input_path.is_none() {
        if let Some(first) = positionals.first() {
            if Path::new(first).is_file() {
                input_path = Some(PathBuf::from(first));
                if let Some(second) = positionals.get(1) {
                    if !max_steps_set && second.parse::<u64>().is_ok() && output_path.is_some() {
                        max_steps = second.parse().unwrap();
                    } else if output_path.is_none() {
                        output_path = Some(PathBuf::from(second));
                    } else {
                        eprintln!("Error: unexpected argument '{second}'");
                        print_usage(bin);
                        process::exit(1);
                    }
                }
            }
        }
    } else if let Some(first) = positionals.first() {
        if output_path.is_none() {
            output_path = Some(PathBuf::from(first));
        } else {
            eprintln!("Error: unexpected argument '{first}'");
            print_usage(bin);
            process::exit(1);
        }
    }

    if let Some(ref infile) = input_path {
        run_file_mode(infile, output_path.as_deref(), max_steps, holdouts_only);
        return;
    }

    let Some(prog_str) = positionals.first() else {
        print_usage(bin);
        process::exit(1);
    };
    if let Some(second) = positionals.get(1) {
        if !max_steps_set {
            if let Ok(steps) = second.parse::<u64>() {
                max_steps = steps;
            } else if output_path.is_none() {
                output_path = Some(PathBuf::from(second));
            } else {
                eprintln!("Error: unexpected argument '{second}'");
                print_usage(bin);
                process::exit(1);
            }
        }
    }

    let program: Program = prog_str.parse().unwrap_or_else(|err| {
        eprintln!("Error parsing program '{prog_str}': {err}");
        process::exit(1);
    });

    println!("Program: {}", program);
    println!("Size:    {} pebbles", program.size());
    println!("Rules:");
    for line in program.to_long_string().lines() {
        println!("  {line}");
    }
    println!();

    let start = Instant::now();

    if verbose {
        let (outcome, trace) = simulate_with_trace(&program, max_steps);
        let elapsed = start.elapsed();

        let (min_x, max_x) = format_trace_bounds(&trace);
        let step_width = trace
            .last()
            .map(|s| s.step.to_string().len())
            .unwrap_or(1)
            .max(4);

        println!("Trace (x in {min_x}..={max_x}):");
        for snap in &trace {
            println!(
                "  t={:<width$}  {}",
                snap.step,
                snap.format_range(min_x, max_x),
                width = step_width
            );
        }
        println!();
        print_outcome(&outcome, elapsed);
        if let Some(ref out_path) = output_path {
            let rec = ProgramRecord::new(program, Some(outcome));
            if let Err(err) = write_records_to_file(out_path, &[rec]) {
                eprintln!("Error writing output file '{}': {err}", out_path.display());
                process::exit(1);
            }
        }
    } else {
        let mut out_entries = Vec::with_capacity(1);
        let mut sim = Simulator::new(program.size());
        let outcome = sim.run(&program, max_steps);
        if matches!(outcome, SimOutcome::MissingRule { .. }) {
            simulate_tnf_subtree(program.clone(), sim, max_steps, &mut out_entries);
            let elapsed = start.elapsed();
            let mut stats = EnumStats::new(program.size(), max_steps);
            for entry in &out_entries {
                stats.record(entry);
            }
            println!("Total input programs:   1");
            println!("Total output programs:  {}", stats.total_programs);
            println!("Halted programs:        {}", stats.halted_programs);
            println!("Holdout programs:       {}", stats.holdout_programs());
            if let (Some(max_s), Some(champ)) = (&stats.max_halting_steps, &stats.champion) {
                println!("Max halting step count: {max_s}");
                println!("Champion program:       {champ}");
            }
            println!("Runtime: {:.3?}", elapsed);
            if let Some(ref out_path) = output_path {
                let records: Vec<ProgramRecord> = out_entries
                    .into_iter()
                    .filter(|e| !holdouts_only || e.outcome.is_holdout())
                    .map(|e| ProgramRecord::new(e.program, Some(e.outcome)))
                    .collect();
                if let Err(err) = write_records_to_file(out_path, &records) {
                    eprintln!("Error writing output file '{}': {err}", out_path.display());
                    process::exit(1);
                }
            }
        } else {
            let elapsed = start.elapsed();
            let final_snap = sim.snapshot();
            println!(
                "Final tape (x in {}..={}): {}",
                final_snap.min_x(),
                final_snap.max_x(),
                final_snap.format_range(final_snap.min_x(), final_snap.max_x())
            );
            print_outcome(&outcome, elapsed);
            if let Some(ref out_path) = output_path {
                let rec = ProgramRecord::new(program, Some(outcome));
                if let Err(err) = write_records_to_file(out_path, &[rec]) {
                    eprintln!("Error writing output file '{}': {err}", out_path.display());
                    process::exit(1);
                }
            }
        }
    }
}

fn print_outcome(outcome: &SimOutcome, elapsed: std::time::Duration) {
    match outcome {
        SimOutcome::Halted { steps } => {
            println!("Status:  HALTED (stabilized) after {steps} steps");
        }
        SimOutcome::DecidedNonHalting { decider, steps } => {
            println!("Status:  NON-HALTING decided by {decider} (simulated {steps} steps)");
        }
        SimOutcome::MaxStepsReached { steps } => {
            println!("Status:  MAX_STEPS reached ({steps} steps) without halting (undecided)");
        }
        SimOutcome::MissingRule { pebbles, steps } => {
            println!("Status:  MISSING_RULE for {pebbles} pebbles at step {steps}");
        }
    }
    println!("Runtime: {:.3?}", elapsed);
}
