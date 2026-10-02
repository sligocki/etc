use mbb::parse::parse_program;
use mbb::simulate::{simulate, SimResult};
use std::env;
use std::process;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("Usage: {} <program> [step_limit]", args[0]);
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

    match simulate(&prog, limit) {
        SimResult::Halted(steps) => {
            println!("Halted after {} steps.", steps);
        }
        SimResult::OutOfBounds => {
            println!("Halted (out of bounds)");
        }
        SimResult::LimitReached => {
            println!("Reached step limit.");
        }
    }
}
