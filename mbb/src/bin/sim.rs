use mbb::parse::parse_program;
use mbb::simulate::{simulate, SimResult};
use std::env;
use std::process;

fn main() {
    let mut args: Vec<String> = env::args().collect();
    let verbose = args.iter().any(|a| a == "-v" || a == "--verbose");
    args.retain(|a| a != "-v" && a != "--verbose");

    let detect_cycles = args.iter().any(|a| a == "-c" || a == "--detect-cycles");
    args.retain(|a| a != "-c" && a != "--detect-cycles");

    if args.len() < 2 {
        eprintln!("Usage: {} [-v] [-c] <program> [step_limit]", args[0]);
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

    match simulate(&prog, limit, detect_cycles, verbose) {
        SimResult::Halted { steps, .. } => {
            println!("Halted after {} steps.", steps);
        }
        SimResult::CycleDetected { start_by, period } => {
            println!("Cycle detected! Starts at step {} with period {}.", start_by, period);
        }
        SimResult::OutOfBounds => {
            println!("Halted (out of bounds)");
        }
        SimResult::LimitReached => {
            println!("Reached step limit.");
        }
        _ => {
            println!("Unexpected result.");
        }
    }
}
