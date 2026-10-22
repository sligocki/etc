use pebble::enumeration::{EnumEntry, EnumStats};
use pebble::io::{read_records_from_file, write_records_to_file, ProgramRecord};
use pebble::program::{Program, Rule};
use pebble::simulation::{
    format_trace_bounds, simulate_from_sim_with_trace, SimOutcome, Simulator, SparseTape,
};
use clap::Parser;
use rayon::prelude::*;
use std::path::{Path, PathBuf};
use std::process;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Mutex;
use std::time::{Duration, Instant};

#[derive(Parser, Debug)]
#[command(
    name = "sim",
    about = "Simulate pebble automata from initial configurations or input files",
    version
)]
struct Cli {
    /// Single program in short notation or input file path
    #[arg(value_name = "PROGRAM")]
    program_or_file: Option<String>,

    /// Maximum steps (if program) or output file (if input file)
    #[arg(value_name = "STEPS_OR_OUTFILE")]
    steps_or_outfile: Option<String>,

    /// Initial tape configuration (e.g. "0230", ".[2]3.", "-5:2, 5:3")
    #[arg(short = 'c', long = "config", visible_aliases = ["tape", "start-config", "init"])]
    config: Option<String>,

    /// Coordinate offset for initial tape (default: 0)
    #[arg(long = "offset", visible_alias = "origin", default_value_t = 0)]
    offset: isize,

    /// Read programs to simulate from <FILE>
    #[arg(short = 'i', long = "input", visible_alias = "infile")]
    input: Option<PathBuf>,

    /// Write simulation results to <FILE>
    #[arg(short = 'o', long = "output", visible_alias = "outfile")]
    output: Option<PathBuf>,

    /// When writing output file, only write undecided holdouts
    #[arg(long = "holdouts-only")]
    holdouts_only: bool,

    /// Maximum number of steps to simulate
    #[arg(short = 's', long = "steps")]
    steps: Option<u64>,

    /// Number of Rayon worker threads for file mode
    #[arg(short = 'j', long = "threads")]
    threads: Option<usize>,

    /// Progress update interval in seconds (default: 10s)
    #[arg(short = 'p', long = "progress", default_value = "10s", value_parser = parse_duration_arg)]
    progress: Duration,

    /// Print the tape configuration at every step (single program)
    #[arg(short = 'v', long = "verbose")]
    verbose: bool,
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

fn run_file_mode(
    infile: &Path,
    outfile: Option<&Path>,
    max_steps: u64,
    holdouts_only: bool,
    progress_interval: Duration,
    initial_tape: Option<SparseTape>,
) {
    let input_records = read_records_from_file(infile).unwrap_or_else(|err| {
        eprintln!("Error reading input file '{}': {err}", infile.display());
        process::exit(1);
    });

    let total_input = input_records.len();
    let size = input_records.first().map(|r| r.program.size()).unwrap_or(0);
    let stat_size = initial_tape.map(|t| t.total_pebbles()).unwrap_or(size);

    println!("=== Pebble Automaton Batch Simulator ===");
    println!("Input file:       {} ({total_input} programs)", infile.display());
    if let Some(out) = outfile {
        println!(
            "Output file:      {}{}",
            out.display(),
            if holdouts_only { " (holdouts only)" } else { "" }
        );
    }
    if let Some(tape) = initial_tape {
        let (min_x, max_x) = match (tape.min_x(), tape.max_x()) {
            (Some(min), Some(max)) => (min, max),
            _ => (0, 0),
        };
        let (off, cells) = tape.to_dense();
        let snap = pebble::simulation::TapeSnapshot {
            step: 0,
            offset: off,
            cells,
        };
        println!(
            "Initial tape:     {} (x in {min_x}..={max_x}, {} pebbles)",
            snap.format_range(min_x, max_x),
            tape.total_pebbles()
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
            let sim = match initial_tape {
                Some(tape) => Simulator::from_tape(tape),
                None => Simulator::new(rec.program.size()),
            };
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

            if !progress_interval.is_zero() && (in_done % 16 == 0 || local_out > 1) {
                if let Ok(mut last) = last_report.try_lock() {
                    if last.elapsed() >= progress_interval {
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
    let mut stats = EnumStats::new(stat_size, max_steps, max_steps);
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
    let cli = Cli::parse();

    let verbose = cli.verbose;
    let holdouts_only = cli.holdouts_only;
    let mut max_steps: u64 = cli.steps.unwrap_or(1000);
    let max_steps_set = cli.steps.is_some();
    let num_threads = cli.threads;
    let progress_interval = cli.progress;
    let mut input_path: Option<PathBuf> = cli.input;
    let mut output_path: Option<PathBuf> = cli.output;
    let initial_config_arg = cli.config;
    let offset_arg = cli.offset;
    let mut positionals: Vec<String> = Vec::new();
    if let Some(p) = cli.program_or_file {
        positionals.push(p);
    }
    if let Some(s) = cli.steps_or_outfile {
        positionals.push(s);
    }

    let initial_tape = match &initial_config_arg {
        Some(s) => match SparseTape::parse_with_offset(s, offset_arg) {
            Ok(tape) => Some(tape),
            Err(err) => {
                eprintln!("Error parsing start configuration '{s}': {err}");
                process::exit(1);
            }
        },
        None => None,
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
            process::exit(1);
        }
    }

    if let Some(ref infile) = input_path {
        run_file_mode(
            infile,
            output_path.as_deref(),
            max_steps,
            holdouts_only,
            progress_interval,
            initial_tape,
        );
        return;
    }

    let Some(prog_str) = positionals.first() else {
        eprintln!("Error: please provide a program or input file");
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

    let sim_init = match initial_tape {
        Some(tape) => Simulator::from_tape(tape),
        None => Simulator::new(program.size()),
    };

    if initial_tape.is_some() {
        let snap = sim_init.snapshot();
        let min_x = snap.min_x();
        let max_x = snap.max_x();
        println!(
            "Initial tape (x in {min_x}..={max_x}): {}",
            snap.format_range(min_x, max_x)
        );
        println!("Total pebbles: {}", sim_init.total_pebbles());
        println!();
    }

    let start = Instant::now();

    if verbose {
        let (outcome, trace) = simulate_from_sim_with_trace(&program, sim_init, max_steps);
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
        let mut sim = sim_init;
        let outcome = sim.run(&program, max_steps);
        if matches!(outcome, SimOutcome::MissingRule { .. }) {
            simulate_tnf_subtree(program.clone(), sim, max_steps, &mut out_entries);
            let elapsed = start.elapsed();
            let stat_size = initial_tape.map(|t| t.total_pebbles()).unwrap_or(program.size());
            let mut stats = EnumStats::new(stat_size, max_steps, max_steps);
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
        SimOutcome::Inf { decider, steps } => {
            println!("Status:  INF decided by {decider} (simulated {steps} steps)");
        }
        SimOutcome::Unknown { steps } => {
            println!("Status:  UNKNOWN reached ({steps} steps) without halting (undecided)");
        }
        SimOutcome::MissingRule { pebbles, steps } => {
            println!("Status:  MISSING_RULE for {pebbles} pebbles at step {steps}");
        }
    }
    println!("Runtime: {:.3?}", elapsed);
}
