use pebble::enumeration::{
    enumerate_parallel_options, is_interrupted, parse_count_arg, parse_duration_arg,
    print_enum_report, register_signal_handler, EnumerateOptions, ProgressSnapshot,
};
use pebble::io::{format_count, write_records_to_file, ProgramRecord};
use std::path::PathBuf;
use std::process;
use std::sync::Mutex;
use std::time::{Duration, Instant};

use clap::Parser;

#[derive(Parser, Debug)]
#[command(
    name = "enum",
    about = "Enumerate pebble programs in Tree Normal Form (TNF) and run simulation / deciders.",
    version
)]
struct Cli {
    /// Program size / initial pebble count n (e.g. 5)
    #[arg(value_name = "SIZE")]
    size: usize,

    /// Maximum deep steps per program (default: 100)
    #[arg(value_name = "DEEP_STEPS")]
    deep_steps: Option<u64>,

    /// Maximum deep steps per program (overrides positional)
    #[arg(short = 's', long = "steps")]
    steps: Option<u64>,

    /// Early simulation / branching steps (default: min(100, deep_steps))
    #[arg(short = 'e', long = "early-steps")]
    early_steps: Option<u64>,

    /// Number of Rayon worker threads (default: all cores)
    #[arg(short = 'j', long = "threads")]
    threads: Option<usize>,

    /// Progress update interval in seconds (default: 10s)
    #[arg(short = 'p', long = "progress", default_value = "10s", value_parser = parse_duration_arg)]
    progress: Duration,

    /// Stop enumeration after evaluating a sample of at least this many programs (e.g. 50k, 1M, 1B)
    #[arg(long = "sample", visible_alias = "limit", value_parser = parse_count_arg)]
    sample: Option<u64>,

    /// Checkpoint file path to save progress and resume interrupted runs
    #[arg(long = "checkpoint")]
    checkpoint: Option<PathBuf>,

    /// Checkpoint save interval (default: 60s)
    #[arg(long = "checkpoint-interval", default_value = "60s", value_parser = parse_duration_arg)]
    checkpoint_interval: Duration,

    /// Write program results to <FILE>
    #[arg(short = 'o', long = "output")]
    output: Option<PathBuf>,

    /// When using -o, only write undecided holdout programs
    #[arg(long = "holdouts-only")]
    holdouts_only: bool,

    /// Disable non-halting decider pipeline on holdouts
    #[arg(long = "no-deciders")]
    no_deciders: bool,

    /// Disable left-right symmetry reduction (enumerate full space)
    #[arg(long = "no-symmetry", visible_alias = "all-symmetries")]
    no_symmetry: bool,

    /// Enable left-right symmetry reduction (default: true)
    #[arg(long = "symmetry")]
    symmetry: bool,
}

fn main() {
    register_signal_handler();
    let cli = Cli::parse();

    let size = cli.size;
    if size == 0 {
        eprintln!("Error: size must be at least 1");
        process::exit(1);
    }

    let deep_steps = cli.steps.or(cli.deep_steps).unwrap_or(100);
    let early_steps_arg = cli.early_steps;
    let num_threads = cli.threads;
    let progress_interval = cli.progress;
    let output_path = cli.output;
    let holdouts_only = cli.holdouts_only;
    let use_deciders = !cli.no_deciders;
    let break_symmetry = !cli.no_symmetry || cli.symmetry;

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
            "enabled (EdgeGlider, Cycler, SeparatedComponents, Bouncer, CTL, StaticBacktrack)"
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
    if let Some(sample) = cli.sample {
        println!("Sample limit:     {} programs", format_count(sample));
    }
    if let Some(ref ckpt) = cli.checkpoint {
        println!("Checkpoint file:  {}", ckpt.display());
        println!("Save interval:    {:?}", cli.checkpoint_interval);
    }
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
        let inf_pct = (snap.inf_programs as f64 / tot_f) * 100.0;
        let unk_pct = (snap.unknown_programs as f64 / tot_f) * 100.0;
        let max_steps_str = snap
            .max_halting_steps
            .map(format_count)
            .unwrap_or_else(|| "-".to_string());
        println!(
            "[Progress] programs: {} | halted: {} ({:.2}%) | inf: {} ({:.2}%) | unknown: {} ({:.2}%) | max steps: {} | elapsed: {:.2?}",
            format_count(snap.total_programs),
            format_count(snap.halted_programs),
            halt_pct,
            format_count(snap.inf_programs),
            inf_pct,
            format_count(snap.unknown_programs),
            unk_pct,
            max_steps_str,
            start.elapsed()
        );
    };

    let options = EnumerateOptions {
        sample_limit: cli.sample,
        checkpoint_path: cli.checkpoint.clone(),
        checkpoint_interval: cli.checkpoint_interval,
        output_path: output_path.clone(),
    };

    let (stats, entries) = enumerate_parallel_options(
        size,
        early_steps,
        deep_steps,
        use_deciders,
        break_symmetry,
        output_path.is_some(),
        holdouts_only,
        options,
        on_progress,
        should_report,
    );
    let records_to_write: Vec<ProgramRecord> = entries
        .into_iter()
        .map(|e| ProgramRecord::new(e.program, Some(e.outcome)))
        .collect();

    let elapsed = start.elapsed();

    if let Some(ref path) = output_path {
        if let Err(err) = write_records_to_file(path, &records_to_write) {
            eprintln!("Error writing output file '{}': {err}", path.display());
            process::exit(1);
        }
        println!(
            "Wrote {} records to {}",
            format_count(records_to_write.len() as u64),
            path.display()
        );
        println!();
    }

    if is_interrupted() {
        println!();
        println!("Run interrupted early by user. Partial statistics below:");
    } else if let Some(sample) = cli.sample {
        if stats.total_programs >= sample {
            println!();
            println!(
                "Sample limit reached ({} evaluated >= {} requested). Sample statistics below:",
                format_count(stats.total_programs),
                format_count(sample)
            );
        }
    }

    print_enum_report(&stats, elapsed, use_deciders);

    if is_interrupted() {
        process::exit(130);
    }
}
