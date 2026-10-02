use mbb::parse::parse_program;
use mbb::simulate::{simulate, SimResult};
use std::env;
use std::fs::File;
use std::io::{self, BufRead};
use std::process;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("Usage: {} <file> [step_limit]", args[0]);
        process::exit(1);
    }

    let file_path = &args[1];
    let limit = args.get(2).and_then(|s| s.parse::<u64>().ok());

    let file = match File::open(file_path) {
        Ok(f) => f,
        Err(e) => {
            eprintln!("Error opening file {}: {}", file_path, e);
            process::exit(1);
        }
    };

    let reader = io::BufReader::new(file);

    let mut total_programs = 0;
    let mut halted_count = 0;
    let mut max_halt_steps = 0;

    for line_result in reader.lines() {
        let line = line_result.unwrap();
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }

        total_programs += 1;

        if let Some(prog) = parse_program(line) {
            match simulate(&prog, limit) {
                SimResult::Halted(steps) => {
                    halted_count += 1;
                    if steps > max_halt_steps {
                        max_halt_steps = steps;
                    }
                }
                SimResult::OutOfBounds => {
                    eprintln!("Warning: Program halted (out of bounds): {}", line);
                    halted_count += 1; // It halted technically
                }
                SimResult::LimitReached => {}
            }
        } else {
            eprintln!("Warning: Failed to parse program on line: {}", line);
        }
    }

    println!("Total programs: {}", total_programs);
    println!("Halted: {}", halted_count);
    println!("Max halt steps: {}", max_halt_steps);
}
