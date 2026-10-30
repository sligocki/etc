use clap::Parser;
use pebble::enumeration::{run_stage, PipelineStage, PipelineStepOutcome};
use pebble::io::{read_records_from_file, ProgramRecord};
use pebble::program::Program;
use pebble::simulation::{SimOutcome, Simulator};
use rayon::prelude::*;
use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::{Path, PathBuf};
use std::process;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Mutex;
use std::time::{Duration, Instant};

#[derive(Parser, Debug)]
#[command(
    name = "decider",
    about = "Run arbitrary decider stages or custom pipelines on pebble programs or files",
    version
)]
struct Cli {
    /// Single program in short notation or input file path
    #[arg(value_name = "PROGRAM_OR_FILE")]
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

    /// One or more decider stages to run in sequence (e.g. -d multibouncer:150 -d ctl:1000).
    /// Supports: multibouncer, bouncer, cycler, separated_components, static_backtrack, edge_glider, ctl, accel, sim.
    #[arg(
        short = 'd',
        long = "decider",
        visible_alias = "stage",
        value_delimiter = ',',
        num_args = 1..
    )]
    stages: Vec<PipelineStage>,

    /// Default step limit for stages that do not specify their own (default: 100)
    #[arg(short = 's', long = "steps", visible_alias = "max-steps", default_value_t = 100)]
    steps: u64,

    /// Number of Rayon worker threads for file mode (default: all cores)
    #[arg(short = 'j', long = "threads")]
    threads: Option<usize>,

    /// Progress update interval in seconds (default: 5s)
    #[arg(short = 'p', long = "progress", default_value = "5s", value_parser = parse_duration_arg)]
    progress: Duration,

    /// When writing output file, only write proved infinite programs
    #[arg(long = "proved-only")]
    proved_only: bool,

    /// When writing output file, only write undecided holdout programs
    #[arg(long = "holdouts-only", visible_alias = "undecided-only")]
    holdouts_only: bool,

    /// Print verbose trace details (single program mode)
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
        Ok(Duration::from_secs_f64(ms / 1000.0))
    } else if let Some(s_str) = s.strip_suffix('s') {
        let secs: f64 = s_str
            .trim()
            .parse()
            .map_err(|_| format!("invalid duration '{raw}'"))?;
        Ok(Duration::from_secs_f64(secs))
    } else {
        let secs: f64 = s
            .parse()
            .map_err(|_| format!("invalid duration '{raw}'"))?;
        Ok(Duration::from_secs_f64(secs))
    }
}

fn main() {
    let cli = Cli::parse();

    if let Some(num_threads) = cli.threads {
        if num_threads > 0 {
            rayon::ThreadPoolBuilder::new()
                .num_threads(num_threads)
                .build_global()
                .unwrap_or_else(|e| eprintln!("Warning: failed to set thread pool size: {e}"));
        }
    }

    // Resolve stages, applying default step limit if not specified inline
    let mut stages = cli.stages;
    if stages.is_empty() {
        // Default to MultiBouncer with CLI steps
        stages.push(PipelineStage::MultiBouncer { steps: cli.steps });
    } else {
        stages = stages
            .into_iter()
            .map(|st| st.with_default_steps(cli.steps))
            .collect();
    }

    // Determine mode: file mode vs single program mode
    let infile = cli
        .input
        .or_else(|| {
            if let Some(ref arg) = cli.program_or_file {
                let p = Path::new(arg);
                if p.is_file() {
                    return Some(p.to_path_buf());
                }
            }
            None
        });

    let outfile = cli.output.or(cli.outfile);

    if let Some(in_path) = infile {
        run_file_mode(
            &in_path,
            outfile.as_deref(),
            &stages,
            cli.progress,
            cli.proved_only,
            cli.holdouts_only,
        );
    } else if let Some(prog_str) = cli.program_or_file {
        run_single_program_mode(&prog_str, &stages, cli.verbose);
    } else {
        eprintln!("Error: no program or input file specified.\n");
        eprintln!("Usage: decider [PROGRAM_OR_FILE] [OUTFILE] [OPTIONS]");
        eprintln!("For more information, try '--help'.");
        process::exit(1);
    }
}

fn run_single_program_mode(prog_str: &str, stages: &[PipelineStage], verbose: bool) {
    let program: Program = match prog_str.parse() {
        Ok(p) => p,
        Err(err) => {
            eprintln!("Error parsing program '{prog_str}': {err}");
            process::exit(1);
        }
    };

    println!("Program: {program}");
    println!("Size:    {} pebbles", program.size());
    println!("Rules:");
    for (idx, rule) in program.rules().iter().enumerate() {
        let pebbles = idx + 1;
        if let Some(r) = rule {
            println!("  {pebbles} --> {} | {} | {}", r.left, r.stay, r.right);
        } else {
            println!("  {pebbles} --> - | - | -");
        }
    }
    println!();

    println!("Configured Decider Pipeline ({} stage{}):", stages.len(), if stages.len() == 1 { "" } else { "s" });
    for (i, stage) in stages.iter().enumerate() {
        println!("  {}. {stage}", i + 1);
    }
    println!();

    let start = Instant::now();
    let mut sim: Option<Simulator> = None;
    let mut final_outcome = PipelineStepOutcome::Undecided;
    let mut decided_stage: Option<&PipelineStage> = None;

    for stage in stages {
        let outcome = run_stage(stage, &program, &mut sim);
        match outcome {
            PipelineStepOutcome::Inf { .. }
            | PipelineStepOutcome::Halted { .. }
            | PipelineStepOutcome::Split { .. } => {
                final_outcome = outcome;
                decided_stage = Some(stage);
                break;
            }
            PipelineStepOutcome::Undecided => {}
        }
    }
    let elapsed = start.elapsed();

    match final_outcome {
        PipelineStepOutcome::Inf { decider, steps } => {
            println!("Status:  PROVED INFINITE");
            println!("Decider: {decider}");
            println!("Stage:   {}", decided_stage.map(|s| s.name()).unwrap_or_default());
            println!("Steps:   {steps}");
            println!("Runtime: {elapsed:.3?}");
        }
        PipelineStepOutcome::Halted { steps } => {
            println!("Status:  HALTED");
            println!("Steps:   {steps}");
            println!("Runtime: {elapsed:.3?}");
        }
        PipelineStepOutcome::Split { pebbles, steps } => {
            println!("Status:  MISSING RULE ({pebbles} pebbles at step {steps})");
            println!("Runtime: {elapsed:.3?}");
        }
        PipelineStepOutcome::Undecided => {
            let cur_steps = sim.as_ref().map_or(0, |s| s.steps());
            println!("Status:  UNDECIDED after {} stage(s) (sim steps: {cur_steps})", stages.len());
            println!("Runtime: {elapsed:.3?}");
        }
    }

    if verbose {
        if let Some(s) = sim {
            let cells = s.cells();
            println!("\nFinal tape state ({} active cells, span x in {}..={}):", cells.len(), s.min_x(), s.max_x());
            print!("  ");
            for &c in &cells {
                if c == 0 {
                    print!(".");
                } else {
                    let ch = char::from_digit(c as u32, 36).unwrap_or('?');
                    print!("{ch}");
                }
            }
            println!();
        }
    }
}

fn run_file_mode(
    infile: &Path,
    outfile: Option<&Path>,
    stages: &[PipelineStage],
    progress_interval: Duration,
    proved_only: bool,
    holdouts_only: bool,
) {
    let records = match read_records_from_file(infile) {
        Ok(r) => r,
        Err(err) => {
            eprintln!("Error reading input file '{}': {err}", infile.display());
            process::exit(1);
        }
    };

    let total_input = records.len();
    println!("=== Pebble Automaton Pipeline Decider ===");
    println!("Input file:      {}", infile.display());
    println!("Dataset:         {total_input} programs");
    println!("Pipeline stages ({}):", stages.len());
    for (i, st) in stages.iter().enumerate() {
        println!("  {}. {st}", i + 1);
    }
    if let Some(out) = outfile {
        println!("Output file:     {}", out.display());
    }
    println!();

    let live_done = AtomicU64::new(0);
    let live_proved = AtomicU64::new(0);
    let live_halted = AtomicU64::new(0);
    let live_missing = AtomicU64::new(0);
    let live_undecided = AtomicU64::new(0);
    let last_report = Mutex::new(Instant::now());
    let start_time = Instant::now();

    let results: Vec<(Program, SimOutcome)> = records
        .into_par_iter()
        .map(|rec: ProgramRecord| {
            let prog = rec.program;
            let mut sim: Option<Simulator> = None;
            let mut outcome = SimOutcome::unknown_step_limit(0);

            for stage in stages {
                let step_res = run_stage(stage, &prog, &mut sim);
                match step_res {
                    PipelineStepOutcome::Inf { decider, steps } => {
                        outcome = SimOutcome::Inf { decider, steps };
                        break;
                    }
                    PipelineStepOutcome::Halted { steps } => {
                        outcome = SimOutcome::Halted { steps };
                        break;
                    }
                    PipelineStepOutcome::Split { pebbles, steps } => {
                        outcome = SimOutcome::MissingRule { pebbles, steps };
                        break;
                    }
                    PipelineStepOutcome::Undecided => {}
                }
            }

            if outcome.is_unknown() {
                let steps = sim.as_ref().map_or(0, |s| s.steps());
                outcome = SimOutcome::unknown_step_limit(steps);
            }

            match outcome {
                SimOutcome::Inf { .. } => {
                    live_proved.fetch_add(1, Ordering::Relaxed);
                }
                SimOutcome::Halted { .. } => {
                    live_halted.fetch_add(1, Ordering::Relaxed);
                }
                SimOutcome::MissingRule { .. } => {
                    live_missing.fetch_add(1, Ordering::Relaxed);
                }
                SimOutcome::Unknown { .. } => {
                    live_undecided.fetch_add(1, Ordering::Relaxed);
                }
            }

            let done = live_done.fetch_add(1, Ordering::Relaxed) + 1;
            if !progress_interval.is_zero() && done % 32 == 0 {
                if let Ok(mut last) = last_report.try_lock() {
                    if last.elapsed() >= progress_interval {
                        let el = start_time.elapsed();
                        let el_s = el.as_secs_f64();
                        let pps = if el_s > 0.0 { done as f64 / el_s } else { 0.0 };
                        let pr = live_proved.load(Ordering::Relaxed);
                        let hl = live_halted.load(Ordering::Relaxed);
                        let un = live_undecided.load(Ordering::Relaxed);
                        let pct = (done as f64 / total_input.max(1) as f64) * 100.0;
                        println!(
                            "[Progress] {done}/{total_input} ({pct:.1}%) | proved: {pr} | halted: {hl} | undecided: {un} | elapsed: {el:.1?} ({pps:.0} progs/s)"
                        );
                        *last = Instant::now();
                    }
                }
            }

            (prog, outcome)
        })
        .collect();

    let total_elapsed = start_time.elapsed();
    let proved_count = live_proved.load(Ordering::Relaxed);
    let halted_count = live_halted.load(Ordering::Relaxed);
    let missing_count = live_missing.load(Ordering::Relaxed);
    let undecided_count = live_undecided.load(Ordering::Relaxed);

    println!("\n=== Final Pipeline Summary ===");
    println!("Total programs:  {total_input}");
    println!(
        "Proved infinite: {} ({:.1}%)",
        proved_count,
        (proved_count as f64 / total_input.max(1) as f64) * 100.0
    );
    println!(
        "Halted:          {} ({:.1}%)",
        halted_count,
        (halted_count as f64 / total_input.max(1) as f64) * 100.0
    );
    if missing_count > 0 {
        println!("Missing rules:   {missing_count}");
    }
    println!(
        "Undecided:       {} ({:.1}%)",
        undecided_count,
        (undecided_count as f64 / total_input.max(1) as f64) * 100.0
    );
    let secs = total_elapsed.as_secs_f64();
    let throughput = if secs > 0.0 {
        total_input as f64 / secs
    } else {
        0.0
    };
    println!("Total time:      {total_elapsed:.3?} ({throughput:.0} progs/s)");

    if let Some(out_path) = outfile {
        let file = File::create(out_path).unwrap_or_else(|err| {
            eprintln!("Error creating output file '{}': {err}", out_path.display());
            process::exit(1);
        });
        let mut writer = BufWriter::new(file);

        writeln!(writer, "# Pebble Automaton Decider Results").ok();
        writeln!(writer, "# Input file: {}", infile.display()).ok();
        let stages_str: Vec<String> = stages.iter().map(|s| s.name()).collect();
        writeln!(writer, "# Stages: [{}]", stages_str.join(", ")).ok();

        let mut written = 0;
        for (prog, outcome) in &results {
            let include = if proved_only {
                outcome.is_inf()
            } else if holdouts_only {
                outcome.is_unknown()
            } else {
                true
            };

            if include {
                writeln!(writer, "{prog}\t{outcome}").ok();
                written += 1;
            }
        }
        writer.flush().ok();
        println!("Wrote {written} record(s) to {}", out_path.display());
    }
}
