mod parse;
mod program;

use crate::parse::parse_program;
use crate::program::{Int, SimResult, State};
use indicatif::ParallelProgressIterator;
use rayon::prelude::*;
use std::env;
use std::fs::File;
use std::io::{self, BufRead};
use std::time::{Duration, Instant};

struct TaskResult {
    sim: SimResult,
    duration: Duration,
}

// Helper function to run the simulation and collect results
fn parse_and_sim(program_str: &str, steps_limit: Int) -> TaskResult {
    let start_time = Instant::now();
    let prog = parse_program(program_str);
    let mut state = State::start(&prog);
    let sim_result = prog.run(&mut state, steps_limit);

    if sim_result.halted {
        println!("  Halt: {} steps: {}", sim_result.total_steps, program_str);
    }

    TaskResult {
        sim: sim_result,
        duration: start_time.elapsed(),
    }
}

// --- The Main Runner ---

fn main() -> io::Result<()> {
    // 1. Parse Command Line Arguments
    let args: Vec<String> = env::args().collect();
    if args.len() < 3 {
        eprintln!("Usage: {} <programs_file> <step_limit>", args[0]);
        std::process::exit(1);
    }

    let filename = &args[1];
    let steps_limit: Int = args[2].parse().expect("Invalid step count provided");

    // 2. Read All Programs into a Vector
    let file = File::open(filename)?;
    let reader = io::BufReader::new(file);

    let programs: Vec<String> = reader
        .lines()
        .filter_map(|line| {
            let line = line.ok()?;
            let trimmed = line.trim();
            if !trimmed.is_empty() && !trimmed.starts_with('#') && !trimmed.starts_with("//") {
                Some(trimmed.to_string())
            } else {
                None
            }
        })
        .collect();

    let num_programs = programs.len();
    if num_programs == 0 {
        println!("No valid programs found in file.");
        return Ok(());
    }

    println!(
        "Simulating {} programs for {} steps using {} threads",
        num_programs,
        steps_limit,
        rayon::current_num_threads()
    );
    let wallclock_start_time = Instant::now();

    // 3. Parallel Execution using Rayon
    let results: Vec<TaskResult> = programs
        .par_iter()
        .progress_count(num_programs as u64)
        .filter_map(|program_str| Some(parse_and_sim(program_str, steps_limit)))
        .collect(); // Collect results back into a Vec on the main thread

    let wallclock_time_sec = wallclock_start_time.elapsed().as_secs_f64();

    // 4. Reporting and Summary
    let halted_count = results.iter().filter(|r| r.sim.halted).count();
    let frac_halted = halted_count as f64 / num_programs as f64;
    let total_steps_simulated: Int = results.iter().map(|r| r.sim.total_steps).sum();

    let wallclock_rate = total_steps_simulated as f64 / wallclock_time_sec;

    let runtimes = results.iter().map(|r| r.duration);
    let max_runtime_sec = runtimes.clone().max().unwrap().as_secs_f64();
    let total_thread_runtime_sec = runtimes.sum::<Duration>().as_secs_f64();
    let mean_runtime_sec = total_thread_runtime_sec / num_programs as f64;

    println!("\nResults Summary:");
    println!(
        "  Halted: {} / {}  ({:.2}%)",
        halted_count,
        num_programs,
        frac_halted * 100.0
    );
    println!("  Total steps: {}", total_steps_simulated);
    println!("Wallclock Time:");
    println!("  {:.2} seconds", wallclock_time_sec);
    println!("  {:.2} Million steps/s", wallclock_rate / 1_000_000.0);
    println!("CPU Time:");
    println!("  Total: {:.2} core-sec", total_thread_runtime_sec);
    println!("  Mean:  {:.2} core-sec / program", mean_runtime_sec);
    println!("  Max:   {:.2} core-sec", max_runtime_sec);

    Ok(())
}
