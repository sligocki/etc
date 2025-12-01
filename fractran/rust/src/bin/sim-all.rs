// Simulate all programs in a file for some number of steps and keep track of halting times.

use std::time::{Duration, Instant};

use clap::Parser;
use indicatif::ParallelProgressIterator;
use rayon::prelude::*;

use fractran::parse::{load_lines, parse_program};
use fractran::program::{Int, SimResult, State};

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    filename: String,
    step_limit: Int,
}

struct TaskResult {
    sim: SimResult,
    duration: Duration,
}

// Helper function to run the simulation and collect results
fn parse_and_sim(program_str: &str, step_limit: Int) -> TaskResult {
    let start_time = Instant::now();
    let prog = parse_program(program_str);
    let mut state = State::start(&prog);
    let sim_result = prog.run(&mut state, step_limit);

    if sim_result.halted {
        println!("  Halt: {} steps: {}", sim_result.total_steps, program_str);
    }

    TaskResult {
        sim: sim_result,
        duration: start_time.elapsed(),
    }
}

fn main() {
    let args = Args::parse();

    // 2. Load all program strings
    let programs = load_lines(&args.filename);
    let num_programs = programs.len();

    println!(
        "Simulating {} programs for {} steps using {} threads",
        num_programs,
        args.step_limit,
        rayon::current_num_threads()
    );
    let wallclock_start_time = Instant::now();

    // 3. Parallel Execution using Rayon
    let results: Vec<TaskResult> = programs
        .par_iter()
        .progress_count(num_programs as u64)
        .filter_map(|program_str| Some(parse_and_sim(program_str, args.step_limit)))
        .collect(); // Collect results back into a Vec on the main thread

    let wallclock_time_sec = wallclock_start_time.elapsed().as_secs_f64();

    // 4. Summarize results
    let halted_count = results.iter().filter(|r| r.sim.halted).count();
    let frac_halted = halted_count as f64 / num_programs as f64;
    let max_halt_steps = results
        .iter()
        .map(|r| if r.sim.halted { r.sim.total_steps } else { 0 })
        .max()
        .unwrap();
    let total_steps_simulated: Int = results.iter().map(|r| r.sim.total_steps).sum();

    let wallclock_rate = total_steps_simulated as f64 / wallclock_time_sec;

    let max_runtime_sec = results
        .iter()
        .map(|r| r.duration)
        .max()
        .unwrap()
        .as_secs_f64();
    let total_thread_runtime_sec = results
        .iter()
        .map(|r| r.duration)
        .sum::<Duration>()
        .as_secs_f64();
    let mean_runtime_sec = total_thread_runtime_sec / num_programs as f64;

    println!("\nResults Summary:");
    println!(
        "  Halted: {} / {}  ({:.2}%)",
        halted_count,
        num_programs,
        frac_halted * 100.0
    );
    println!("  Max Halt Steps: {}", max_halt_steps);
    println!("  Total steps: {}", total_steps_simulated);
    println!("Wallclock Time:");
    println!("  {:.2} seconds", wallclock_time_sec);
    println!("  {:.2} Million steps/s", wallclock_rate / 1_000_000.0);
    println!("CPU Time:");
    println!("  Total: {:.2} core-sec", total_thread_runtime_sec);
    println!("  Mean:  {:.2} core-sec / program", mean_runtime_sec);
    println!("  Max:   {:.2} core-sec", max_runtime_sec);
}
