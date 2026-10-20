use pebble::ctl::{run_ctl_search, CtlConfig, CtlSearchOutcome};
use pebble::program::Program;
use std::env;
use std::process;
use std::time::Instant;

fn print_usage(bin: &str) {
    eprintln!("Usage: {bin} [OPTIONS] <PROGRAM>");
    eprintln!();
    eprintln!("Arguments:");
    eprintln!("  <PROGRAM>                 Pebble program in short notation (e.g. 00_00_30_10_11_06_21_03_07_19)");
    eprintln!();
    eprintln!("Options:");
    eprintln!("  -s, --max-steps <STEPS>   Maximum simulation steps to explore (default: 5000)");
    eprintln!("  -m, --max-states <STATES> Maximum states allowed in closed language (default: 10000)");
    eprintln!("      --step-interval <N>   Interval between simulation steps to test CTL closure (default: 10)");
    eprintln!("      --min-step <N>        Minimum simulation step before attempting CTL closure (default: 0)");
    eprintln!("  -v, --verbose             Print verbose step inspection details");
    eprintln!("  -h, --help                Show this help message");
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let bin_name = args.get(0).map(|s| s.as_str()).unwrap_or("ctl");

    let mut program_str: Option<String> = None;
    let mut max_steps: u64 = 5000;
    let mut max_states: usize = 10000;
    let mut step_interval: u64 = 10;
    let mut min_step: u64 = 0;
    let mut verbose = false;

    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "-h" | "--help" => {
                print_usage(bin_name);
                process::exit(0);
            }
            "-v" | "--verbose" => {
                verbose = true;
                i += 1;
            }
            "-s" | "--max-steps" | "--steps" => {
                i += 1;
                if i >= args.len() {
                    eprintln!("Error: missing value for {}", args[i - 1]);
                    process::exit(1);
                }
                max_steps = args[i].parse().unwrap_or_else(|_| {
                    eprintln!("Error: invalid steps '{}'", args[i]);
                    process::exit(1);
                });
                i += 1;
            }
            "-m" | "--max-states" | "--states" => {
                i += 1;
                if i >= args.len() {
                    eprintln!("Error: missing value for {}", args[i - 1]);
                    process::exit(1);
                }
                max_states = args[i].parse().unwrap_or_else(|_| {
                    eprintln!("Error: invalid max states '{}'", args[i]);
                    process::exit(1);
                });
                i += 1;
            }
            "--step-interval" | "--interval" => {
                i += 1;
                if i >= args.len() {
                    eprintln!("Error: missing value for {}", args[i - 1]);
                    process::exit(1);
                }
                step_interval = args[i].parse().unwrap_or_else(|_| {
                    eprintln!("Error: invalid step interval '{}'", args[i]);
                    process::exit(1);
                });
                i += 1;
            }
            "--min-step" => {
                i += 1;
                if i >= args.len() {
                    eprintln!("Error: missing value for {}", args[i - 1]);
                    process::exit(1);
                }
                min_step = args[i].parse().unwrap_or_else(|_| {
                    eprintln!("Error: invalid min step '{}'", args[i]);
                    process::exit(1);
                });
                i += 1;
            }
            arg if !arg.starts_with('-') => {
                if program_str.is_none() {
                    program_str = Some(arg.to_string());
                } else {
                    eprintln!("Error: unexpected extra argument '{arg}'");
                    print_usage(bin_name);
                    process::exit(1);
                }
                i += 1;
            }
            other => {
                eprintln!("Error: unknown option '{other}'");
                print_usage(bin_name);
                process::exit(1);
            }
        }
    }

    let program_raw = match program_str {
        Some(s) => s,
        None => {
            eprintln!("Error: no program specified.");
            print_usage(bin_name);
            process::exit(1);
        }
    };

    let program: Program = match program_raw.parse() {
        Ok(p) => p,
        Err(e) => {
            eprintln!("Error parsing program '{program_raw}': {e}");
            process::exit(1);
        }
    };

    println!("Running CTL decider on program: {program_raw} (size {})", program.size());
    println!("Limits: max_steps={max_steps}, max_states={max_states}, step_interval={step_interval}, min_step={min_step}");
    println!();

    let config = CtlConfig {
        min_step,
        max_steps,
        max_states,
        step_interval,
        verbose,
    };

    let start = Instant::now();
    let outcome = run_ctl_search(&program, &config);
    let elapsed = start.elapsed();

    match outcome {
        CtlSearchOutcome::Proved(proof) => {
            println!("Result: Closed Tape Language (CTL) proof found!");
            println!("Status: DECIDED_INFINITE");
            println!();
            println!("Parameters necessary to catch closure:");
            println!("  num_steps:       {}", proof.num_steps);
            println!("  num_states:      {}", proof.num_states);
            println!("  split_threshold: {}", proof.split_threshold);
            println!("  floor:           {}", proof.floor);
            println!("  modulus:         {}", proof.modulus);
            println!("  time:            {:.2?}", elapsed);
        }
        CtlSearchOutcome::ConcreteHalt { step } => {
            println!("Result: Failed to find closure (program halted)");
            println!("Status: DECIDED_HALTING");
            println!("  halt_step: {}", step);
            println!("  reason:    concrete simulation reached empty tape (0 active pebbles)");
            println!("  time:      {:.2?}", elapsed);
        }
        CtlSearchOutcome::ConcreteMissingRule { step, pebbles } => {
            println!("Result: Failed to find closure (reached undefined transition)");
            println!("Status: UNDEFINED_TRANSITION");
            println!("  step:         {}", step);
            println!("  missing_rule: {} pebbles", pebbles);
            println!("  reason:       concrete simulation reached undefined rule slot in TNF");
            println!("  time:         {:.2?}", elapsed);
        }
        CtlSearchOutcome::ClosureHitUndefinedRule { step, pebbles } => {
            println!("Result: Failed to find closure (reached undefined transition in candidate language)");
            println!("Status: CANDIDATE_CLOSURE_UNDEFINED");
            println!("  sampled_step: {}", step);
            println!("  missing_rule: {} pebbles", pebbles);
            println!("  reason:       symbolic forward reachability generated configuration with undefined rule");
            println!("  time:         {:.2?}", elapsed);
        }
        CtlSearchOutcome::ClosureHitHalt { step } => {
            println!("Result: Failed to find closure (reached halting state in candidate language)");
            println!("Status: CANDIDATE_CLOSURE_HALT");
            println!("  sampled_step: {}", step);
            println!("  reason:       symbolic forward reachability generated empty tape (all zeros)");
            println!("  time:         {:.2?}", elapsed);
        }
        CtlSearchOutcome::LimitReached {
            max_steps,
            max_states,
        } => {
            println!("Result: Undecided (closure not found within limits)");
            println!("Status: UNDECIDED");
            println!("  max_steps:  {}", max_steps);
            println!("  max_states: {}", max_states);
            println!("  time:       {:.2?}", elapsed);
        }
    }
}
