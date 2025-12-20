// Simulate all programs in a file with ShiftSim.

use std::fs;
use std::time::{Duration, Instant};

use clap::Parser;
use indicatif::ParallelProgressIterator;
use itertools::Itertools;
use rayon::prelude::*;
use rug::Float;

use fractran::parse::{load_lines, parse_program};
use fractran::program::{BigInt, State};
use fractran::shift_sim::{ShiftSim, SimStatus, find_shift_rules};

struct TaskResult {
    program_str: String,
    duration: Duration,
    // Results
    config: State,
    sim_status: SimStatus,
    sim_steps: usize,
    base_steps: BigInt,
}

// Helper function to run the simulation and collect results
fn parse_and_sim(program_str: &str, transcript_steps: usize, sim_steps: usize) -> TaskResult {
    let start_time = Instant::now();
    let prog = parse_program(program_str);
    let start_state = State::start(&prog);

    let shift_rules = find_shift_rules(&prog, start_state.clone(), transcript_steps);
    let mut sim = ShiftSim::new(prog, shift_rules);
    let config = sim.run(start_state, sim_steps);

    TaskResult {
        program_str: program_str.to_string(),
        duration: start_time.elapsed(),
        config,
        sim_status: sim.status,
        sim_steps: sim.sim_steps,
        base_steps: sim.base_steps,
    }
}

fn bigint_log10(val: BigInt) -> Float {
    Float::with_val(24, &val).log10()
}

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    infile: String,
    transcript_steps: usize,
    sim_steps: usize,
    outfile: String,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = Args::parse();

    // 2. Load all program strings
    let programs = load_lines(&args.infile);
    let num_programs = programs.len();

    println!(
        "Simulating {} programs for {} steps using {} threads",
        num_programs,
        args.sim_steps,
        rayon::current_num_threads()
    );
    let wallclock_start_time = Instant::now();

    // 3. Parallel Execution using Rayon
    let results: Vec<TaskResult> = programs
        .par_iter()
        .progress_count(num_programs as u64)
        .filter_map(|program_str| {
            Some(parse_and_sim(
                program_str,
                args.transcript_steps,
                args.sim_steps,
            ))
        })
        .collect(); // Collect results back into a Vec on the main thread

    let wallclock_time_sec = wallclock_start_time.elapsed().as_secs_f64();

    // 4. Write halting programs to outfile
    let data = results
        .iter()
        .map(|r| {
            format!(
                "{}\t{:?}\t{}\t{:?}\n",
                r.program_str, r.sim_status, r.base_steps, r.config.data
            )
        })
        .join("");
    fs::write(&args.outfile, data)?;

    // 5. Summarize results
    let halted_count = results
        .iter()
        .filter(|r| r.sim_status == SimStatus::Halted)
        .count();
    let inf_count = results
        .iter()
        .filter(|r| r.sim_status == SimStatus::Infinite)
        .count();
    let frac_halted = halted_count as f64 / num_programs as f64;
    let frac_inf = inf_count as f64 / num_programs as f64;

    let max_halt_steps = results
        .iter()
        .filter(|r| r.sim_status == SimStatus::Halted)
        .map(|r| r.base_steps.clone())
        .max()
        .unwrap_or(0.into());
    let total_sim_steps: usize = results.iter().map(|r| r.sim_steps).sum();

    let total_base_steps: BigInt = results.iter().map(|r| &r.base_steps).sum();
    let min_base_steps: BigInt = results.iter().map(|r| &r.base_steps).min().unwrap().clone();
    let max_base_steps: BigInt = results.iter().map(|r| &r.base_steps).max().unwrap().clone();

    let wallclock_rate = total_sim_steps as f64 / wallclock_time_sec;

    let max_runtime_sec = results
        .iter()
        .map(|r| r.duration)
        .max()
        .unwrap_or(Duration::from_secs(0))
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
    println!(
        "  Inf: {} / {}  ({:.2}%)",
        inf_count,
        num_programs,
        frac_inf * 100.0
    );
    println!("  Max Halt Steps: {}", max_halt_steps);
    println!("  Total sim steps: {}", total_sim_steps);
    println!("Base steps:");
    println!("  Total base steps: 10^{}", bigint_log10(total_base_steps));
    println!("  Min base steps: 10^{}", bigint_log10(min_base_steps));
    println!("  Max base steps: 10^{}", bigint_log10(max_base_steps));
    println!("Wallclock Time:");
    println!("  {:.2} seconds", wallclock_time_sec);
    println!("  {:.2} Million sim steps/s", wallclock_rate / 1_000_000.0);
    println!("CPU Time:");
    println!("  Total: {:.2} core-sec", total_thread_runtime_sec);
    println!("  Mean:  {:.2} core-sec / program", mean_runtime_sec);
    println!("  Max:   {:.2} core-sec", max_runtime_sec);

    Ok(())
}
