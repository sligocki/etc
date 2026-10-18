use pebble::program::Program;
use pebble::simulation::{format_trace_bounds, simulate_with_trace, SimOutcome, Simulator};
use std::env;
use std::process;
use std::time::Instant;

fn print_usage(bin: &str) {
    eprintln!("Usage: {bin} [OPTIONS] <PROGRAM>");
    eprintln!();
    eprintln!("Arguments:");
    eprintln!("  <PROGRAM>              Program in short notation (e.g. 00_11_03_21_04)");
    eprintln!();
    eprintln!("Options:");
    eprintln!("  -v, --verbose          Print the tape configuration at every step");
    eprintln!("  -s, --steps <STEPS>    Maximum number of steps to simulate (default: 1000)");
    eprintln!("  -h, --help             Show this help message");
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let bin = args.first().map(String::as_str).unwrap_or("sim");

    let mut verbose = false;
    let mut max_steps: u64 = 1000;
    let mut program_arg: Option<String> = None;

    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "-h" | "--help" => {
                print_usage(bin);
                return;
            }
            "-v" | "--verbose" => {
                verbose = true;
            }
            "-s" | "--steps" => {
                i += 1;
                if i >= args.len() {
                    eprintln!("Error: missing value for --steps");
                    print_usage(bin);
                    process::exit(1);
                }
                max_steps = args[i].parse().unwrap_or_else(|_| {
                    eprintln!("Error: invalid step count '{}'", args[i]);
                    process::exit(1);
                });
            }
            arg if arg.starts_with('-') => {
                eprintln!("Error: unknown option '{arg}'");
                print_usage(bin);
                process::exit(1);
            }
            arg => {
                if program_arg.is_none() {
                    program_arg = Some(arg.to_string());
                } else if args[i].parse::<u64>().is_ok() && max_steps == 1000 {
                    // Also allow positional `<program> <max_steps>`
                    max_steps = args[i].parse().unwrap();
                } else {
                    eprintln!("Error: unexpected argument '{arg}'");
                    print_usage(bin);
                    process::exit(1);
                }
            }
        }
        i += 1;
    }

    let Some(prog_str) = program_arg else {
        print_usage(bin);
        process::exit(1);
    };

    let program: Program = prog_str.parse().unwrap_or_else(|err| {
        eprintln!("Error parsing program '{prog_str}': {err}");
        process::exit(1);
    });

    println!("Program: {}", program);
    println!("Size:    {} pebbles", program.size());
    println!("Rules:");
    for line in program.to_long_string().lines() {
        println!("  {line}");
    }
    println!();

    let start = Instant::now();

    if verbose {
        let (outcome, trace) = simulate_with_trace(&program, max_steps);
        let elapsed = start.elapsed();

        let (min_x, max_x) = format_trace_bounds(&trace);
        let step_width = trace
            .last()
            .map(|s| s.step.to_string().len())
            .unwrap_or(1)
            .max(4);

        println!("Trace (x in {min_x}..={max_x}):");
        for snap in &trace {
            println!(
                "  t={:<width$}  {}",
                snap.step,
                snap.format_range(min_x, max_x),
                width = step_width
            );
        }
        println!();
        print_outcome(&outcome, elapsed);
    } else {
        let mut sim = Simulator::new(program.size());
        let outcome = sim.run(&program, max_steps);
        let elapsed = start.elapsed();
        let final_snap = sim.snapshot();
        println!(
            "Final tape (x in {}..={}): {}",
            final_snap.min_x(),
            final_snap.max_x(),
            final_snap.format_range(final_snap.min_x(), final_snap.max_x())
        );
        print_outcome(&outcome, elapsed);
    }
}

fn print_outcome(outcome: &SimOutcome, elapsed: std::time::Duration) {
    match outcome {
        SimOutcome::Halted { steps } => {
            println!("Status:  HALTED (stabilized) after {steps} steps");
        }
        SimOutcome::MaxStepsReached { steps } => {
            println!("Status:  MAX_STEPS reached ({steps} steps) without halting");
        }
        SimOutcome::MissingRule { pebbles, steps } => {
            println!("Status:  MISSING_RULE for {pebbles} pebbles at step {steps}");
        }
    }
    println!("Runtime: {:.3?}", elapsed);
}
