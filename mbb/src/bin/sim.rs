use mbb::parse::parse_program;
use mbb::simulate::simulate_direct;
use std::env;
use std::process;

fn main() {
    let mut args: Vec<String> = env::args().collect();
    let verbose = args.iter().any(|a| a == "-v" || a == "--verbose");
    args.retain(|a| a != "-v" && a != "--verbose");

    let detect_cycles = args.iter().any(|a| a == "-c" || a == "--detect-cycles");
    args.retain(|a| a != "-c" && a != "--detect-cycles");

    let exact_start_by = args.iter().any(|a| a == "-e" || a == "--exact-start");
    args.retain(|a| a != "-e" && a != "--exact-start");

    let _use_transfer = !args.iter().any(|a| a == "--no-transfer");
    args.retain(|a| a != "--no-transfer");

    if args.len() < 2 {
        eprintln!("Usage: {} [-v] [-c] [-e] [--no-transfer] <program> [step_limit]", args[0]);
        process::exit(1);
    }

    let program_str = &args[1];
    let limit = args.get(2).and_then(|s| s.parse::<u64>().ok());

    let prog = match parse_program(program_str) {
        Some(p) => p,
        None => {
            eprintln!("Error: Failed to parse program.");
            process::exit(1);
        }
    };

    println!("Simulating: {}", prog);

    match simulate_direct(&prog, limit, detect_cycles, exact_start_by, verbose) {
        mbb::deciders::DeciderResult::Halt { steps, .. } => {
            println!("Halted after {} steps.", steps);
        }
        mbb::deciders::DeciderResult::Infinite(mbb::deciders::InfiniteReason::Cycle { start_by, period, is_min_start }) => {
            println!("Cycle detected! Starts at step {} (is_min: {}) with period {}.", start_by, is_min_start, period);
        }
        mbb::deciders::DeciderResult::Infinite(mbb::deciders::InfiniteReason::TranslatedCycler { start_by, period, is_min_start }) => {
            println!("Translated Cycler detected! Starts at step {} (is_min: {}) with period {}.", start_by, is_min_start, period);
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

