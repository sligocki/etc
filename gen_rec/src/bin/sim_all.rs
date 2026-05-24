/// Batch-simulate every GRF in an input file and write results to a .grl output file.
///
/// Reads any .grl or legacy holdout file, simulates each 0-arity GRF up to the
/// given step budget, and writes ALL results (Halt / Diverge / Unknown) to the
/// output file.
///
/// Usage:
///   cargo run --bin sim_all -- input.grl 100000000 output.grl
///   cargo run --bin sim_all -- holdout.grl 1000000000 next.grl --progress-interval 10
use clap::Parser;
use gen_rec::grf::Grf;
use gen_rec::io_grl::{GrfEntry, Status, parse_grf_entries, write_grf_entry, write_grl_header};
use gen_rec::sim_nat::SmallNat;
use gen_rec::simulate::simulate;
use rayon::prelude::*;
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
    steps: SmallNat,

    /// Output file (.grl); receives all GRFs with their simulation results.
    output: PathBuf,

    /// Seconds between progress lines (0 = disable).
    #[arg(long, default_value_t = 30)]
    progress_interval: u64,
}

fn read_grfs(filename: &PathBuf) -> Vec<Grf> {
    let content = fs::read_to_string(filename).unwrap_or_else(|e| {
        eprintln!("error reading {}: {}", filename.display(), e);
        std::process::exit(1);
    });
    let entries = parse_grf_entries(&content);

    entries
        .iter()
        .filter_map(|entry| entry.expr.parse().ok())
        .filter(|grf: &Grf| grf.arity() == 0)
        .collect()
}

fn sim_one(grf: &Grf, max_steps: u64) -> GrfEntry {
    let (result, steps) = simulate(grf, &[], max_steps);
    GrfEntry::from_sim_result(grf, result, steps)
}

fn print_summary(results: &Vec<GrfEntry>) {
    let n_total = results.len();
    let n_halted = results
        .iter()
        .filter(|result| matches!(result.status, Some(Status::Halt)))
        .count();
    let n_diverged = results
        .iter()
        .filter(|result| matches!(result.status, Some(Status::Diverge)))
        .count();
    let n_holdouts = results
        .iter()
        .filter(|result| matches!(result.status, Some(Status::Unknown)))
        .count();
    let max_score = results
        .iter()
        .filter(|result| matches!(result.status, Some(Status::Halt)))
        .filter_map(|result| result.score)
        .max();
    let max_steps = results
        .iter()
        .filter(|result| matches!(result.status, Some(Status::Halt)))
        .filter_map(|result| result.steps)
        .max();
    let total_steps: u64 = results.iter().filter_map(|result| result.steps).sum();

    println!("Summary:");
    println!(
        "  Halted:   {} / {} ({}%)",
        n_halted,
        n_total,
        n_halted as f32 / n_total as f32
    );
    println!(
        "  Diverged: {} / {} ({}%)",
        n_diverged,
        n_total,
        n_diverged as f32 / n_total as f32
    );
    println!(
        "  Holdouts: {} / {} ({}%)",
        n_holdouts,
        n_total,
        n_holdouts as f32 / n_total as f32
    );
    if let Some(n) = max_score {
        println!("Max Score: {}", n);
    }
    if let Some(n) = max_steps {
        println!("Max Steps: {}", n);
    }
    println!("Total Sim Steps: {}", total_steps);
}

fn main() {
    let args = Args::parse();

    let max_steps = if args.steps == 0 {
        u64::MAX
    } else {
        args.steps
    };

    let out_file = fs::File::create(&args.output).unwrap_or_else(|e| {
        eprintln!("error creating {}: {}", args.output.display(), e);
        std::process::exit(1);
    });

    let grfs = read_grfs(&args.input);
    println!("Read {} GRFs", grfs.len());

    let start = Instant::now();
    let results: Vec<GrfEntry> = grfs.par_iter().map(|grf| sim_one(grf, max_steps)).collect();
    println!(
        "Simulated {} GRFs for {} steps each in {:?}",
        grfs.len(),
        max_steps,
        start.elapsed()
    );

    // Write results.
    let mut out = BufWriter::new(out_file);
    write_grl_header(
        &mut out,
        &format!(
            "sim_all: input={}, budget={}",
            args.input.display(),
            args.steps
        ),
    )
    .unwrap();

    for grf_entry in results.iter() {
        write_grf_entry(&mut out, &grf_entry).unwrap();
    }
    out.flush().unwrap();

    print_summary(&results);
}
