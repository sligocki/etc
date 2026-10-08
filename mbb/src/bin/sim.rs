use clap::Parser;
use mbb::parse::parse_program;
use mbb::simulate::{simulate_direct, simulate_macro};
use std::process;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// The program string to simulate
    program: String,

    /// Optional step limit for simulation
    step_limit: Option<u64>,

    /// Enable verbose output
    #[arg(short, long)]
    verbose: bool,

    /// Detect cycles and translated cyclers
    #[arg(short = 'c', long)]
    detect_cycles: bool,

    /// Compute exact start_by step for cycles and TCs
    #[arg(short = 'e', long)]
    exact_start: bool,

    /// Run macro simulation instead of direct simulation
    #[arg(short = 'm', long = "macro")]
    use_macro: bool,
}

fn main() {
    let args = Args::parse();

    let prog = match parse_program(&args.program) {
        Some(p) => p,
        None => {
            eprintln!("Error: Failed to parse program.");
            process::exit(1);
        }
    };

    println!("Simulating: {}", prog);

    let result = if args.use_macro {
        simulate_macro(
            &prog,
            args.step_limit,
            args.detect_cycles,
            args.exact_start,
            args.verbose,
        )
    } else {
        simulate_direct(
            &prog,
            args.step_limit,
            args.detect_cycles,
            args.exact_start,
            args.verbose,
        )
    };

    match result {
        mbb::deciders::DeciderResult::Halt { steps, .. } => {
            println!("Halted after {} steps.", steps);
        }
        mbb::deciders::DeciderResult::Infinite(mbb::deciders::InfiniteReason::Cycle {
            start_by,
            period,
            is_min_start,
        }) => {
            println!(
                "Cycle detected! Starts at step {} (is_min: {}) with period {}.",
                start_by, is_min_start, period
            );
        }
        mbb::deciders::DeciderResult::Infinite(
            mbb::deciders::InfiniteReason::TranslatedCycler {
                start_by,
                period,
                is_min_start,
            },
        ) => {
            println!(
                "Translated Cycler detected! Starts at step {} (is_min: {}) with period {}.",
                start_by, is_min_start, period
            );
        }
        mbb::deciders::DeciderResult::Error(_) => {
            println!("Halted (out of bounds)");
        }
        mbb::deciders::DeciderResult::Unknown => {
            println!("Reached step limit.");
        }
        _ => {
            println!("Unexpected result.");
        }
    }
}
