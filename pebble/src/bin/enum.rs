use pebble::enumeration::{enumerate_parallel, ProgressSnapshot};
use pebble::io::{write_records_to_file, ProgramRecord};
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

use clap::Parser;

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

            let floor_str = stats
                .ctl_floor_counts
                .iter()
                .map(|(f, c)| format!("floor={f} ({c})"))
                .collect::<Vec<_>>()
                .join(", ");
            println!("Floors:           {}", floor_str);

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
