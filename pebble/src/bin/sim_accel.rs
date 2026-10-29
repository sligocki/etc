use clap::Parser;
use pebble::accelerated::{AcceleratedSimulator, FastForwardResult};
use pebble::io::{format_count, read_records_from_file, write_records_to_file, ProgramRecord};
use pebble::program::Program;
use pebble::simulation::{SimOutcome, SparseTape, StepResult};
use rayon::prelude::*;
use std::path::{Path, PathBuf};
use std::process;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Mutex;
use std::time::{Duration, Instant};

#[derive(Parser, Debug)]
#[command(
    name = "sim_accel",
    about = "Accelerated pebble automata simulator (fast-forwards long collision-free glider transits)",
    version
)]
struct Cli {
    /// Single program in short notation or input file path
    #[arg(value_name = "PROGRAM")]
    program_or_file: Option<String>,

    /// Maximum simulation steps (sim_steps = normal steps + fast-forwards) or output file
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

    /// Maximum number of simulation steps (normal steps + fast-forwards, default: 10,000)
    #[arg(short = 's', long = "steps", visible_alias = "sim-steps")]
    sim_steps: Option<u64>,

    /// Maximum base CA generations (optional cap on virtual tape clock)
    #[arg(long = "base-steps")]
    base_steps: Option<u64>,

    /// Number of Rayon worker threads for file mode
    #[arg(short = 'j', long = "threads")]
    threads: Option<usize>,

    /// Progress update interval in seconds (default: 10s)
    #[arg(short = 'p', long = "progress", default_value = "10s", value_parser = parse_duration_arg)]
    progress: Duration,

    /// Print the tape configuration at every step and fast-forward leap
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

fn run_file_mode(
    input_file: &Path,
    output_file: Option<&Path>,
    max_sim_steps: u64,
    holdouts_only: bool,
    progress_interval: Duration,
    initial_tape: Option<SparseTape>,
) {
    let records = match read_records_from_file(input_file) {
        Ok(recs) => recs,
        Err(err) => {
            eprintln!("Error reading input file '{}': {err}", input_file.display());
            process::exit(1);
        }
    };

    let total = records.len() as u64;
    println!("Loaded {total} program records from {}", input_file.display());
    println!("Accelerated limit: {max_sim_steps} simulation steps (normal steps + fast-forwards)");

    let completed = AtomicU64::new(0);
    let halted_count = AtomicU64::new(0);
    let inf_count = AtomicU64::new(0);
    let holdout_count = AtomicU64::new(0);

    let output_records = Mutex::new(Vec::with_capacity(records.len()));
    let start_time = Instant::now();
    let last_progress = Mutex::new(Instant::now());

    records.par_iter().for_each(|record| {
        let prog = &record.program;
        let mut sim = match initial_tape {
            Some(tape) => AcceleratedSimulator::from_tape(tape),
            None => AcceleratedSimulator::new(prog.size()),
        };

        let outcome = sim.run_sim_steps(prog, max_sim_steps);

        if outcome.is_halted() {
            halted_count.fetch_add(1, Ordering::Relaxed);
        } else if outcome.is_inf() {
            inf_count.fetch_add(1, Ordering::Relaxed);
        } else {
            holdout_count.fetch_add(1, Ordering::Relaxed);
        }

        if output_file.is_some() && (!holdouts_only || outcome.is_holdout()) {
            let out_rec = ProgramRecord::new(prog.clone(), Some(outcome));
            output_records.lock().unwrap().push(out_rec);
        }

        let done = completed.fetch_add(1, Ordering::Relaxed) + 1;
        let mut lp = last_progress.lock().unwrap();
        if lp.elapsed() >= progress_interval || done == total {
            *lp = Instant::now();
            let elapsed = start_time.elapsed().as_secs_f64();
            let rate = if elapsed > 0.0 { done as f64 / elapsed } else { 0.0 };
            eprintln!(
                "Progress: {done}/{total} ({:.1}%) | Halted: {} | Inf: {} | Holdout: {} | {:.0} prog/s",
                (done as f64 / total as f64) * 100.0,
                halted_count.load(Ordering::Relaxed),
                inf_count.load(Ordering::Relaxed),
                holdout_count.load(Ordering::Relaxed),
                rate
            );
        }
    });

    let elapsed = start_time.elapsed();
    println!();
    println!("=== Summary ===");
    println!("Total programs:     {}", format_count(total));
    println!("Halted:             {}", format_count(halted_count.load(Ordering::Relaxed)));
    println!("Infinite decided:   {}", format_count(inf_count.load(Ordering::Relaxed)));
    println!("Holdouts (undecided): {}", format_count(holdout_count.load(Ordering::Relaxed)));
    println!("Wallclock runtime:  {:.3?}", elapsed);

    if let Some(out_path) = output_file {
        let recs = output_records.into_inner().unwrap();
        if let Err(err) = write_records_to_file(out_path, &recs) {
            eprintln!("Error writing output file '{}': {err}", out_path.display());
            process::exit(1);
        }
        println!("Saved {} records to {}", recs.len(), out_path.display());
    }
}

fn main() {
    let cli = Cli::parse();

    let verbose = cli.verbose;
    let holdouts_only = cli.holdouts_only;
    let mut max_sim_steps: u64 = cli.sim_steps.unwrap_or(10_000);
    let sim_steps_set = cli.sim_steps.is_some();
    let max_base_steps: Option<u64> = cli.base_steps;
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
                    if !sim_steps_set && second.parse::<u64>().is_ok() && output_path.is_some() {
                        max_sim_steps = second.parse().unwrap();
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
            max_sim_steps,
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
        if !sim_steps_set {
            if let Ok(steps) = second.parse::<u64>() {
                max_sim_steps = steps;
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

    let mut sim = match initial_tape {
        Some(tape) => AcceleratedSimulator::from_tape(tape),
        None => AcceleratedSimulator::new(program.size()),
    };

    if initial_tape.is_some() {
        if sim.tape().is_empty() {
            println!("Initial tape: <empty>");
        } else {
            let (min_x, max_x) = (sim.min_x(), sim.max_x());
            let s_str = format_tape_smart(sim.tape());
            println!("Initial tape (x in {min_x}..={max_x}): {s_str}");
        }
        println!("Total pebbles: {}", sim.tape().total_pebbles());
        println!();
    }

    let start = Instant::now();

    if verbose {
        let mut trace_snaps: Vec<(u64, u64, Vec<(isize, u8)>)> = Vec::new(); // (sim_step, base_step, entries)
        trace_snaps.push((sim.sim_steps(), sim.steps(), sim.tape().entries().to_vec()));

        let mut outcome = SimOutcome::Unknown { steps: sim.steps() };

        while sim.sim_steps() < max_sim_steps && max_base_steps.map_or(true, |b| sim.steps() < b) {
            let max_jump = max_base_steps.map_or(u64::MAX, |b| b.saturating_sub(sim.steps()));
            match sim.try_fast_forward(&program, max_jump) {
                FastForwardResult::Jumped(_) => {
                    trace_snaps.push((sim.sim_steps(), sim.steps(), sim.tape().entries().to_vec()));
                    continue;
                }
                FastForwardResult::Halted => {
                    outcome = SimOutcome::Halted { steps: sim.steps() };
                    break;
                }
                FastForwardResult::Inf(d) => {
                    outcome = SimOutcome::Inf { decider: d, steps: sim.steps() };
                    break;
                }
                FastForwardResult::None => {}
            }

            match sim.step(&program) {
                StepResult::Stepped => {
                    trace_snaps.push((sim.sim_steps(), sim.steps(), sim.tape().entries().to_vec()));
                }
                StepResult::Halted => {
                    outcome = SimOutcome::Halted { steps: sim.steps() };
                    break;
                }
                StepResult::MissingRule(k) => {
                    outcome = SimOutcome::MissingRule { pebbles: k, steps: sim.steps() };
                    break;
                }
            }
        }

        if matches!(outcome, SimOutcome::Unknown { .. }) {
            outcome = SimOutcome::Unknown { steps: sim.steps() };
        }

        let elapsed = start.elapsed();
        let overall_min_x = trace_snaps
            .iter()
            .flat_map(|s| s.2.first().map(|e| e.0))
            .min()
            .unwrap_or(0);
        let overall_max_x = trace_snaps
            .iter()
            .flat_map(|s| s.2.last().map(|e| e.0))
            .max()
            .unwrap_or(0);
        let sim_width = trace_snaps.last().map(|s| s.0.to_string().len()).unwrap_or(1).max(3);
        let base_width = trace_snaps.last().map(|s| s.1.to_string().len()).unwrap_or(1).max(4);

        let span = overall_max_x - overall_min_x + 1;
        println!("Trace (x in {overall_min_x}..={overall_max_x}):");
        if span <= 120 {
            for (sim_s, base_s, entries) in &trace_snaps {
                let mut tape_str = String::new();
                let mut entry_idx = 0;
                for x in overall_min_x..=overall_max_x {
                    if entry_idx < entries.len() && entries[entry_idx].0 == x {
                        let v = entries[entry_idx].1;
                        tape_str.push(pebble::program::encode_pebble_digit(v).unwrap_or('#'));
                        entry_idx += 1;
                    } else {
                        tape_str.push('.');
                    }
                }
                println!(
                    "  step={:<sim_w$} (t={:<base_w$})  {}",
                    sim_s,
                    base_s,
                    tape_str,
                    sim_w = sim_width,
                    base_w = base_width
                );
            }
        } else {
            for (sim_s, base_s, entries) in &trace_snaps {
                let clusters = pebble::accelerated::extract_clusters(entries, 1);
                let tape_str = clusters
                    .iter()
                    .map(|c| {
                        let s: String = c
                            .cells
                            .iter()
                            .map(|&v| if v == 0 { '.' } else { pebble::program::encode_pebble_digit(v).unwrap_or('#') })
                            .collect();
                        format!("{} @ {}", s, c.offset)
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                println!(
                    "  step={:<sim_w$} (t={:<base_w$})  {}",
                    sim_s,
                    base_s,
                    tape_str,
                    sim_w = sim_width,
                    base_w = base_width
                );
            }
        }
        println!();

        print_final_summary(&sim, &outcome, elapsed);
        if let Some(ref out_path) = output_path {
            let rec = ProgramRecord::new(program, Some(outcome));
            if let Err(err) = write_records_to_file(out_path, &[rec]) {
                eprintln!("Error writing output file '{}': {err}", out_path.display());
                process::exit(1);
            }
        }
        return;
    }

    let outcome = if let Some(base_cap) = max_base_steps {
        sim.run(&program, base_cap)
    } else {
        sim.run_sim_steps(&program, max_sim_steps)
    };
    let elapsed = start.elapsed();

    print_final_summary(&sim, &outcome, elapsed);
    if let Some(ref out_path) = output_path {
        let rec = ProgramRecord::new(program, Some(outcome));
        if let Err(err) = write_records_to_file(out_path, &[rec]) {
            eprintln!("Error writing output file '{}': {err}", out_path.display());
            process::exit(1);
        }
    }
}

fn format_tape_smart(tape: &SparseTape) -> String {
    if tape.is_empty() {
        return "<empty>".to_string();
    }
    let min_x = tape.min_x().unwrap();
    let max_x = tape.max_x().unwrap();
    let span = max_x - min_x + 1;
    if span <= 120 {
        let (_, dense_cells) = tape.to_dense();
        dense_cells
            .iter()
            .map(|&c| if c == 0 { '.' } else { pebble::program::encode_pebble_digit(c).unwrap_or('#') })
            .collect()
    } else {
        let clusters = pebble::accelerated::extract_clusters(tape.entries(), 1);
        clusters
            .iter()
            .map(|c| {
                let s: String = c
                    .cells
                    .iter()
                    .map(|&v| if v == 0 { '.' } else { pebble::program::encode_pebble_digit(v).unwrap_or('#') })
                    .collect();
                format!("{} @ {}", s, c.offset)
            })
            .collect::<Vec<_>>()
            .join(", ")
    }
}

fn print_final_summary(
    sim: &AcceleratedSimulator,
    outcome: &SimOutcome,
    elapsed: Duration,
) {
    if sim.tape().is_empty() {
        println!("Final tape: <empty>");
    } else {
        let (min_x, max_x) = (sim.min_x(), sim.max_x());
        let tape_str = format_tape_smart(sim.tape());
        println!("Final tape (x in {min_x}..={max_x}): {tape_str}");
    }

    let stats = sim.stats();
    println!(
        "Sim steps:        {} ({} normal steps, {} fast-forwards skipping {} generations)",
        format_count(stats.sim_steps()),
        format_count(stats.normal_steps),
        format_count(stats.fast_forwards),
        format_count(stats.steps_fast_forwarded)
    );
    println!("Base generations: {}", format_count(sim.steps()));

    match outcome {
        SimOutcome::Halted { steps } => {
            println!("Status:           HALTED (stabilized) after {steps} base generations");
        }
        SimOutcome::Inf { decider, steps } => {
            println!("Status:           INF decided by {decider} (at step {steps})");
        }
        SimOutcome::Unknown { steps } => {
            println!("Status:           UNKNOWN reached ({steps} base generations) without halting (undecided)");
        }
        SimOutcome::MissingRule { pebbles, steps } => {
            println!("Status:           MISSING_RULE for {pebbles} pebbles at base generation {steps}");
        }
    }
    println!("Runtime:          {:.3?}", elapsed);
}
