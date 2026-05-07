/// Batch-simulate every GRF in an input file and write results to a .grl output file.
///
/// Reads any .grl or legacy holdout file, simulates each 0-arity GRF up to the
/// given step budget, and writes ALL results (Halt / Diverge / Unknown) to the
/// output file.  Periodic progress lines and a final stats summary are printed.
///
/// Usage:
///   cargo run --bin sim_all -- input.grl 100000000 output.grl
///   cargo run --bin sim_all -- holdout.grl 1000000000 next.grl --progress-interval 10
use chrono::Local;
use clap::Parser;
use gen_rec::grf::Grf;
use gen_rec::io_grl::{self, GrfEntry, Status};
use gen_rec::simulate::simulate;
use std::fs;
use std::io::{BufWriter, Write};
use std::path::PathBuf;
use std::time::Instant;

#[derive(Parser, Debug)]
#[command(about = "Batch-simulate GRFs from a .grl file and write results")]
struct Args {
    /// Input file (.grl or legacy holdout format).
    input: PathBuf,

    /// Step budget per simulation (0 = unlimited).
    steps: u64,

    /// Output file (.grl); receives all GRFs with their simulation results.
    output: PathBuf,

    /// Seconds between progress lines (0 = disable).
    #[arg(long, default_value_t = 30)]
    progress_interval: u64,
}

fn fmt_steps(n: u64) -> String {
    if n < 1_000 {
        format!("{}", n)
    } else if n < 1_000_000 {
        format!("{:.1}K", n as f64 / 1_000.0)
    } else if n < 1_000_000_000 {
        format!("{:.2}M", n as f64 / 1_000_000.0)
    } else if n < 1_000_000_000_000u64 {
        format!("{:.2}B", n as f64 / 1_000_000_000.0)
    } else {
        format!("{:.2}T", n as f64 / 1_000_000_000_000.0)
    }
}

fn fmt_elapsed(secs: u64) -> String {
    if secs < 60 {
        format!("{}s", secs)
    } else if secs < 3600 {
        format!("{}m{}s", secs / 60, secs % 60)
    } else {
        format!("{}h{}m{}s", secs / 3600, (secs % 3600) / 60, secs % 60)
    }
}

fn main() {
    let args = Args::parse();

    let content = fs::read_to_string(&args.input).unwrap_or_else(|e| {
        eprintln!("error reading {}: {}", args.input.display(), e);
        std::process::exit(1);
    });

    let entries = io_grl::parse_grf_entries(&content);
    let n_input = entries.len();

    let out_file = fs::File::create(&args.output).unwrap_or_else(|e| {
        eprintln!("error creating {}: {}", args.output.display(), e);
        std::process::exit(1);
    });
    let mut out = BufWriter::new(out_file);
    io_grl::write_grl_header(
        &mut out,
        &format!(
            "sim_all: input={}, budget={}",
            args.input.display(),
            args.steps
        ),
    ).unwrap();

    let max_steps = if args.steps == 0 { u64::MAX } else { args.steps };

    let start = Instant::now();
    let mut last_progress = start;
    let progress_interval = std::time::Duration::from_secs(args.progress_interval);

    let mut n_total      = 0usize;
    let mut n_halted     = 0usize;
    let mut n_diverged   = 0usize;
    let mut n_holdouts   = 0usize;
    let mut n_skipped    = 0usize;
    let mut max_score    = 0u64;
    let mut max_halt_steps = 0u64;
    let mut total_steps  = 0u64;

    for entry in entries {
        // Skip entries already known to diverge.
        if matches!(entry.status, Some(Status::Diverge)) {
            n_skipped += 1;
            continue;
        }

        let grf: Grf = match entry.expr.parse() {
            Ok(g) => g,
            Err(e) => {
                eprintln!("parse error ({}): {}", e, entry.expr);
                continue;
            }
        };

        if grf.arity() != 0 {
            eprintln!("skipping non-0-arity GRF: {}", entry.expr);
            n_skipped += 1;
            continue;
        }

        let (result, sim_steps) = simulate(&grf, &[], max_steps);
        let steps_taken = sim_steps.sim;
        total_steps += steps_taken;
        n_total += 1;

        let (out_status, out_score, out_base_steps) = match result {
            gen_rec::simulate::SimResult::Value(v) => {
                n_halted += 1;
                if v > max_score { max_score = v; }
                if steps_taken > max_halt_steps { max_halt_steps = steps_taken; }
                (Status::Halt, Some(v), Some(sim_steps.base_approx))
            }
            gen_rec::simulate::SimResult::Diverge => {
                n_diverged += 1;
                (Status::Diverge, None, None)
            }
            gen_rec::simulate::SimResult::OutOfSteps => {
                n_holdouts += 1;
                (Status::Unknown, None, None)
            }
        };

        io_grl::write_grf_entry(&mut out, &GrfEntry {
            expr:       entry.expr,
            status:     Some(out_status),
            steps:      Some(steps_taken),
            base_steps: out_base_steps,
            score:      out_score,
        }).unwrap();

        // Progress report.
        if args.progress_interval > 0 && last_progress.elapsed() >= progress_interval {
            let elapsed_s = start.elapsed().as_secs();
            let pct = if n_input > 0 { 100 * n_total / n_input } else { 0 };
            println!(
                "[{}] elapsed: {} | {}/{} ({}%) | halted: {} | holdouts: {} | diverged: {} | max_score: {}",
                Local::now().format("%H:%M:%S"),
                fmt_elapsed(elapsed_s),
                n_total, n_input, pct,
                n_halted, n_holdouts, n_diverged,
                max_score,
            );
            last_progress = Instant::now();
        }
    }

    out.flush().unwrap();

    let elapsed_s = start.elapsed().as_secs();
    println!();
    println!("=== sim_all complete ===");
    println!("input          : {}", args.input.display());
    println!("output         : {}", args.output.display());
    println!("budget         : {}", args.steps);
    println!("total          : {}", n_total);
    println!("halted         : {}", n_halted);
    println!("diverged       : {}", n_diverged);
    println!("holdouts       : {}", n_holdouts);
    if n_skipped > 0 {
        println!("skipped        : {}", n_skipped);
    }
    if n_halted > 0 {
        println!("max score      : {}", max_score);
        println!("max halt steps : {}", fmt_steps(max_halt_steps));
    }
    println!("total steps    : {}", fmt_steps(total_steps));
    println!("elapsed        : {}", fmt_elapsed(elapsed_s));
}
