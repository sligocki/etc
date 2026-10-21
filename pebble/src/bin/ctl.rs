use pebble::ctl::{run_ctl_search, CtlConfig, CtlSearchOutcome};
use pebble::io::read_records_from_file;
use pebble::program::Program;
use rayon::prelude::*;
use clap::Parser;
use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::{Path, PathBuf};
use std::process;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Mutex;
use std::time::{Duration, Instant};

#[derive(Parser, Debug)]
#[command(
    name = "ctl",
    about = "Run Closed Tape Language (CTL) decider on pebble programs",
    version
)]
struct Cli {
    /// Pebble program in short notation or input file path
    #[arg(value_name = "PROGRAM")]
    program_or_file: Option<String>,

    /// Path to output file
    #[arg(value_name = "OUTFILE")]
    outfile: Option<PathBuf>,

    /// Read programs to evaluate from <FILE>
    #[arg(short = 'i', long = "input", visible_alias = "infile")]
    input: Option<PathBuf>,

    /// Write results to <FILE>
    #[arg(short = 'o', long = "output", visible_alias = "outfile")]
    output: Option<PathBuf>,

    /// Maximum simulation steps to explore
    #[arg(short = 's', long = "max-steps", visible_alias = "steps", default_value_t = 5000)]
    max_steps: u64,

    /// Maximum states allowed in closed language
    #[arg(short = 'm', long = "max-states", visible_alias = "states", default_value_t = 10000)]
    max_states: usize,

    /// Interval between simulation steps to test CTL closure
    #[arg(long = "step-interval", visible_alias = "interval", default_value_t = 10)]
    step_interval: u64,

    /// Minimum simulation step before attempting CTL closure
    #[arg(long = "min-step", default_value_t = 0)]
    min_step: u64,

    /// Split threshold for separating blocks
    #[arg(long = "split-threshold", visible_alias = "thresh", default_value_t = 2)]
    split_threshold: usize,

    /// Minimum gap floor for widening (default: 2*threshold+2)
    #[arg(short = 'f', long = "floor")]
    floor: Option<usize>,

    /// Number of Rayon worker threads for file mode (default: all cores)
    #[arg(short = 'j', long = "threads")]
    threads: Option<usize>,

    /// Progress update interval in seconds (default: 5s)
    #[arg(short = 'p', long = "progress", default_value = "5s", value_parser = parse_duration_arg)]
    progress: Duration,

    /// When writing output file, only write CTL-proved infinite programs
    #[arg(long = "proved-only")]
    proved_only: bool,

    /// When writing output file, only write undecided holdout programs
    #[arg(long = "holdouts-only", visible_alias = "undecided-only")]
    holdouts_only: bool,

    /// Print verbose step inspection details (single program mode)
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

fn format_record_line(prog: &Program, outcome: &CtlSearchOutcome) -> String {
    match outcome {
        CtlSearchOutcome::Proved(proof) => {
            format!(
                "{prog}\tDECIDED\tCTL\t{} # states={} floor={} mod={}",
                proof.num_steps, proof.num_states, proof.floor, proof.modulus
            )
        }
        CtlSearchOutcome::ConcreteHalt { step } => {
            format!("{prog}\tHALT\t{step}")
        }
        CtlSearchOutcome::ConcreteMissingRule { step, pebbles } => {
            format!("{prog}\tMISSING_RULE\t{pebbles}\t{step}")
        }
        CtlSearchOutcome::ClosureHitUndefinedRule { step, pebbles } => {
            format!("{prog}\tMAX_STEPS\t{step} # closure hit undefined rule for {pebbles} pebbles")
        }
        CtlSearchOutcome::ClosureHitHalt { step } => {
            format!("{prog}\tMAX_STEPS\t{step} # closure hit halting configuration")
        }
        CtlSearchOutcome::LimitReached { max_steps, .. } => {
            format!("{prog}\tMAX_STEPS\t{max_steps}")
        }
    }
}

fn run_file_mode(
    infile: &Path,
    outfile: Option<&Path>,
    config: CtlConfig,
    proved_only: bool,
    holdouts_only: bool,
    progress_interval: Duration,
) {
    let input_records = read_records_from_file(infile).unwrap_or_else(|err| {
        eprintln!("Error reading input file '{}': {err}", infile.display());
        process::exit(1);
    });

    let total_input = input_records.len();
    println!("=== Pebble Automaton Batch CTL Decider ===");
    println!("Input file:       {} ({total_input} programs)", infile.display());
    if let Some(out) = outfile {
        let filter_label = if proved_only {
            " (proved only)"
        } else if holdouts_only {
            " (holdouts only)"
        } else {
            ""
        };
        println!("Output file:      {}{filter_label}", out.display());
    }
    let effective_floor = config.floor.unwrap_or(2 * config.split_threshold + 2);
    println!(
        "Parameters:       max_steps={}, max_states={}, step_interval={}, min_step={}, split_threshold={}, floor={}",
        config.max_steps, config.max_states, config.step_interval, config.min_step, config.split_threshold, effective_floor
    );
    println!("Threads:          {}", rayon::current_num_threads());
    println!();

    let start = Instant::now();
    let last_report = Mutex::new(Instant::now());
    let live_input_done = AtomicU64::new(0);
    let live_proved = AtomicU64::new(0);
    let live_halted = AtomicU64::new(0);
    let live_missing = AtomicU64::new(0);
    let live_undecided = AtomicU64::new(0);

    let results: Vec<(Program, CtlSearchOutcome)> = input_records
        .into_par_iter()
        .map(|rec| {
            let outcome = run_ctl_search(&rec.program, &config);

            match &outcome {
                CtlSearchOutcome::Proved(_) => {
                    live_proved.fetch_add(1, Ordering::Relaxed);
                }
                CtlSearchOutcome::ConcreteHalt { .. } => {
                    live_halted.fetch_add(1, Ordering::Relaxed);
                }
                CtlSearchOutcome::ConcreteMissingRule { .. } => {
                    live_missing.fetch_add(1, Ordering::Relaxed);
                }
                CtlSearchOutcome::ClosureHitUndefinedRule { .. }
                | CtlSearchOutcome::ClosureHitHalt { .. }
                | CtlSearchOutcome::LimitReached { .. } => {
                    live_undecided.fetch_add(1, Ordering::Relaxed);
                }
            }

            let in_done = live_input_done.fetch_add(1, Ordering::Relaxed) + 1;

            if !progress_interval.is_zero() && in_done % 8 == 0 {
                if let Ok(mut last) = last_report.try_lock() {
                    if last.elapsed() >= progress_interval {
                        let el = start.elapsed();
                        let el_s = el.as_secs_f64();
                        let pps = if el_s > 0.0 {
                            in_done as f64 / el_s
                        } else {
                            0.0
                        };
                        let pr = live_proved.load(Ordering::Relaxed);
                        let hl = live_halted.load(Ordering::Relaxed);
                        let ms = live_missing.load(Ordering::Relaxed);
                        let un = live_undecided.load(Ordering::Relaxed);
                        let pct = (in_done as f64 / total_input.max(1) as f64) * 100.0;
                        println!(
                            "[Progress] {in_done}/{total_input} ({pct:.1}%) | proved: {pr} | halted: {hl} | missing: {ms} | undecided: {un} | elapsed: {el:.1?} ({pps:.0} progs/s)"
                        );
                        *last = Instant::now();
                    }
                }
            }

            (rec.program, outcome)
        })
        .collect();

    let elapsed = start.elapsed();

    let mut proved_count = 0;
    let mut halted_count = 0;
    let mut missing_count = 0;
    let mut undecided_count = 0;

    for (_, out) in &results {
        match out {
            CtlSearchOutcome::Proved(_) => proved_count += 1,
            CtlSearchOutcome::ConcreteHalt { .. } => halted_count += 1,
            CtlSearchOutcome::ConcreteMissingRule { .. } => missing_count += 1,
            CtlSearchOutcome::ClosureHitUndefinedRule { .. }
            | CtlSearchOutcome::ClosureHitHalt { .. }
            | CtlSearchOutcome::LimitReached { .. } => undecided_count += 1,
        }
    }

    if let Some(out_path) = outfile {
        let file = File::create(out_path).unwrap_or_else(|err| {
            eprintln!("Error creating output file '{}': {err}", out_path.display());
            process::exit(1);
        });
        let mut writer = BufWriter::new(file);

        writeln!(writer, "# Pebble Automaton CTL Decider Results").ok();
        writeln!(writer, "# Input file: {}", infile.display()).ok();
        let effective_floor = config.floor.unwrap_or(2 * config.split_threshold + 2);
        writeln!(
            writer,
            "# Parameters: max_steps={}, max_states={}, step_interval={}, min_step={}, split_threshold={}, floor={}",
            config.max_steps, config.max_states, config.step_interval, config.min_step, config.split_threshold, effective_floor
        )
        .ok();

        let mut written_count = 0;
        for (prog, outcome) in &results {
            let include = if proved_only {
                matches!(outcome, CtlSearchOutcome::Proved(_))
            } else if holdouts_only {
                matches!(
                    outcome,
                    CtlSearchOutcome::ClosureHitUndefinedRule { .. }
                        | CtlSearchOutcome::ClosureHitHalt { .. }
                        | CtlSearchOutcome::LimitReached { .. }
                )
            } else {
                true
            };

            if include {
                if let Err(err) = writeln!(writer, "{}", format_record_line(prog, outcome)) {
                    eprintln!("Error writing record: {err}");
                    process::exit(1);
                }
                written_count += 1;
            }
        }

        if let Err(err) = writer.flush() {
            eprintln!("Error flushing output file: {err}");
            process::exit(1);
        }

        println!("Wrote {written_count} records to {}", out_path.display());
        println!();
    }

    let secs = elapsed.as_secs_f64();
    let pps = if secs > 0.0 {
        total_input as f64 / secs
    } else {
        total_input as f64
    };
    let tot_f = total_input.max(1) as f64;

    println!("=== Batch CTL Decider Summary ===");
    println!("Total input programs:   {total_input}");
    println!(
        "Proven infinite (CTL):  {} ({:.2}%)",
        proved_count,
        (proved_count as f64 / tot_f) * 100.0
    );
    println!(
        "Halted programs:        {} ({:.2}%)",
        halted_count,
        (halted_count as f64 / tot_f) * 100.0
    );
    println!(
        "Undefined transitions:  {} ({:.2}%)",
        missing_count,
        (missing_count as f64 / tot_f) * 100.0
    );
    println!(
        "Undecided / Holdouts:   {} ({:.2}%)",
        undecided_count,
        (undecided_count as f64 / tot_f) * 100.0
    );
    println!("Wallclock runtime:      {:.3?}", elapsed);
    println!("Throughput:             {:.0} programs/s", pps);
}

fn main() {
    let cli = Cli::parse();

    let mut input_path: Option<PathBuf> = cli.input;
    let mut output_path: Option<PathBuf> = cli.output;
    let mut positionals: Vec<String> = Vec::new();
    if let Some(p) = cli.program_or_file {
        positionals.push(p);
    }
    if let Some(o) = cli.outfile {
        positionals.push(o.to_string_lossy().to_string());
    }

    let max_steps = cli.max_steps;
    let max_states = cli.max_states;
    let step_interval = cli.step_interval;
    let min_step = cli.min_step;
    let split_threshold = cli.split_threshold;
    let floor = cli.floor;
    let num_threads = cli.threads;
    let progress_interval = cli.progress;
    let proved_only = cli.proved_only;
    let holdouts_only = cli.holdouts_only;
    let verbose = cli.verbose;

    if let Some(threads) = num_threads {
        if let Err(err) = rayon::ThreadPoolBuilder::new()
            .num_threads(threads)
            .build_global()
        {
            eprintln!("Error configuring Rayon thread pool: {err}");
            process::exit(1);
        }
    }

    let config = CtlConfig {
        min_step,
        max_steps,
        max_states,
        step_interval,
        split_threshold,
        floor,
        verbose,
    };

    // Disambiguate positional arguments: file mode vs single-program mode
    if input_path.is_none() {
        if let Some(first) = positionals.first() {
            if Path::new(first).is_file() {
                input_path = Some(PathBuf::from(first));
                if let Some(second) = positionals.get(1) {
                    if output_path.is_none() {
                        output_path = Some(PathBuf::from(second));
                    }
                }
            }
        }
    } else if let Some(first) = positionals.first() {
        if output_path.is_none() {
            output_path = Some(PathBuf::from(first));
        }
    }

    if let Some(infile) = input_path {
        run_file_mode(
            &infile,
            output_path.as_deref(),
            config,
            proved_only,
            holdouts_only,
            progress_interval,
        );
        return;
    }

    // Single-program mode
    let program_raw = match positionals.first() {
        Some(s) => s.as_str(),
        None => {
            eprintln!("Error: no program or input file specified.");
            process::exit(1);
        }
    };

    let program: Program = match program_raw.parse() {
        Ok(p) => p,
        Err(e) => {
            eprintln!("Error parsing program '{program_raw}': {e}");
            process::exit(1);
        }
    };

    println!(
        "Running CTL decider on program: {program_raw} (size {})",
        program.size()
    );
    let effective_floor = config.floor.unwrap_or(2 * config.split_threshold + 2);
    println!(
        "Limits: max_steps={max_steps}, max_states={max_states}, step_interval={step_interval}, min_step={min_step}, split_threshold={split_threshold}, floor={effective_floor}"
    );
    println!();

    let start = Instant::now();
    let outcome = run_ctl_search(&program, &config);
    let elapsed = start.elapsed();

    match &outcome {
        CtlSearchOutcome::Proved(proof) => {
            println!("Result: Closed Tape Language (CTL) proof found!");
            println!("Status: DECIDED_INFINITE");
            println!();
            println!("Parameters necessary to catch closure:");
            println!("  num_steps:       {}", proof.num_steps);
            println!("  num_states:      {}", proof.num_states);
            println!("  split_threshold: {}", proof.split_threshold);
            println!("  floor:           {}", proof.floor);
            println!("  modulus:         {}", proof.modulus);
            println!("  time:            {:.2?}", elapsed);
        }
        CtlSearchOutcome::ConcreteHalt { step } => {
            println!("Result: Failed to find closure (program halted)");
            println!("Status: DECIDED_HALTING");
            println!("  halt_step: {}", step);
            println!("  reason:    concrete simulation reached empty tape (0 active pebbles)");
            println!("  time:      {:.2?}", elapsed);
        }
        CtlSearchOutcome::ConcreteMissingRule { step, pebbles } => {
            println!("Result: Failed to find closure (reached undefined transition)");
            println!("Status: UNDEFINED_TRANSITION");
            println!("  step:         {}", step);
            println!("  missing_rule: {} pebbles", pebbles);
            println!("  reason:       concrete simulation reached undefined rule slot in TNF");
            println!("  time:         {:.2?}", elapsed);
        }
        CtlSearchOutcome::ClosureHitUndefinedRule { step, pebbles } => {
            println!(
                "Result: Failed to find closure (reached undefined transition in candidate language)"
            );
            println!("Status: CANDIDATE_CLOSURE_UNDEFINED");
            println!("  sampled_step: {}", step);
            println!("  missing_rule: {} pebbles", pebbles);
            println!(
                "  reason:       symbolic forward reachability generated configuration with undefined rule"
            );
            println!("  time:         {:.2?}", elapsed);
        }
        CtlSearchOutcome::ClosureHitHalt { step } => {
            println!("Result: Failed to find closure (reached halting state in candidate language)");
            println!("Status: CANDIDATE_CLOSURE_HALT");
            println!("  sampled_step: {}", step);
            println!("  reason:       symbolic forward reachability generated empty tape (all zeros)");
            println!("  time:         {:.2?}", elapsed);
        }
        CtlSearchOutcome::LimitReached {
            max_steps,
            max_states,
        } => {
            println!("Result: Undecided (closure not found within limits)");
            println!("Status: UNDECIDED");
            println!("  max_steps:  {}", max_steps);
            println!("  max_states: {}", max_states);
            println!("  time:       {:.2?}", elapsed);
        }
    }

    if let Some(ref out_path) = output_path {
        let file = File::create(out_path).unwrap_or_else(|err| {
            eprintln!("Error creating output file '{}': {err}", out_path.display());
            process::exit(1);
        });
        let mut writer = BufWriter::new(file);
        writeln!(writer, "{}", format_record_line(&program, &outcome)).unwrap_or_else(|err| {
            eprintln!("Error writing output file: {err}");
            process::exit(1);
        });
        println!();
        println!("Result written to {}", out_path.display());
    }
}
