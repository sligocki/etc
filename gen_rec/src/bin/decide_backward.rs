use clap::Parser;
use gen_rec::backward_decider::BackwardDecider;
use gen_rec::grf::Grf;
use gen_rec::io_grl::{self, Status};
use std::fs;
use std::io::{BufWriter, Write};
use std::path::PathBuf;

#[derive(Parser, Debug)]
#[command(about = "Backward Backtracking Filter Decider for holdout files")]
struct Args {
    /// Input file containing holdouts (.grl or .mgrf)
    input: PathBuf,

    /// Output file for the annotated results
    output: PathBuf,

    /// Maximum depth for the backward evaluation search
    #[arg(long, default_value_t = 10)]
    depth: usize,

    /// Budget for evaluation steps per GRF to prevent exponential blowup
    #[arg(long, default_value_t = 100_000)]
    budget: usize,
}

fn main() {
    let args = Args::parse();

    let content = fs::read_to_string(&args.input).expect("Failed to read input file");
    let entries = io_grl::parse_grf_entries(&content);

    let out_file = fs::File::create(&args.output).expect("Failed to create output file");
    let mut out_writer = BufWriter::new(out_file);

    let decider = BackwardDecider::new(args.depth, args.budget);

    let mut total = 0;
    let mut decided = 0;
    let mut skipped = 0;

    io_grl::write_grl_header(&mut out_writer, "Processed with decide_backward").unwrap();

    for mut entry in entries {
        total += 1;

        // Skip already decided entries unless they are unknown
        if entry.status == Some(Status::Halt) || entry.status == Some(Status::Diverge) {
            skipped += 1;
            io_grl::write_grf_entry(&mut out_writer, &entry).unwrap();
            continue;
        }

        let grf = match entry.expr.parse::<Grf>() {
            Ok(g) => g,
            Err(e) => {
                eprintln!("Warning: could not parse {}: {}", entry.expr, e);
                skipped += 1;
                io_grl::write_grf_entry(&mut out_writer, &entry).unwrap();
                continue;
            }
        };

        if decider.proves_divergence(&grf) {
            entry.status = Some(Status::Diverge);
            entry.unknown_reason = Some("BackwardDecider".to_string());
            decided += 1;
        }

        io_grl::write_grf_entry(&mut out_writer, &entry).unwrap();
    }

    out_writer.flush().unwrap();

    println!("Processed {} entries.", total);
    println!("  Skipped: {}", skipped);
    println!("  Decided Diverge: {}", decided);
    println!("  Unresolved: {}", total - skipped - decided);
}
