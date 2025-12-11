// Heuristic filter which searches for patterns in program transcript.
//
// A transcript is the transition history (list of which rule was used at each step).
//
// We use tandem_repeat library to find repeated sequences in that transctipt. Ex:
//    ECBCC D^2 EA^2 ECB CB^2 C C^3 D^4 EA^4 ECB CB^4 C C^5 D^6 EA^6 ECB CB^6 C C^7 ...
// We then strip repeat counts to get something like:
//    ECBCC D+ EA+ ECB CB+ C C+ D+ EA+ ECB CB+ C C+ D+ EA+ ECB CB+ C C+ ...
// and search for tandem repeats again among treating each block as a single symbol. Ex:
//    (ECBCC) (D+ EA+ ECB CB+ C C+)^407 (D+ EA+)
//
// This can reveal various level of inductive rules.
//  * The first compressed version discovers "shift rules". All repeated sections are
//    shift rules. Translated cyclers will have a single infinite repeat here (once
//    they start cycling).
//  * All bouncers will have an infinitely repeated second level section (like the
//    example). Note: Not totally sure if all second-level repeats are guaranteed
//    to be inductive rules. But it seems to be a decent heuristic.
//
// Thus our goal here will be to identify for each program whether it has a highly
// repeating second level sections or not. Then the ones without such compression are
// more likely to be of interest for investigation by hand.

use std::fs;
use std::time::{Duration, Instant};

use clap::Parser;
use indicatif::ParallelProgressIterator;
use itertools::Itertools;
use rayon::prelude::*;

use fractran::parse::{load_lines, parse_program};
use fractran::program::{Int, State};
use fractran::tandem_repeat::{as_rep_blocks, find_repeat_info, rep_stats, RepBlockStats};
use fractran::transcript::{strip_reps, transcript};

struct TaskResult {
    program_str: String,
    duration: Duration,

    // Result stats
    l0_stats: RepBlockStats,
    l1_stats: RepBlockStats,
}

// Helper function to run the simulation and collect results
fn process_task(program_str: &str, num_steps: Int) -> TaskResult {
    let start_time = Instant::now();
    let prog = parse_program(program_str);
    let state = State::start(&prog);

    // Load sequence of transitions ("transcript")
    let trans_vec = transcript(&prog, state, num_steps);

    // Find base-level (L0) repeats in transcript
    let l0_rep_info = find_repeat_info(&trans_vec);
    let l0_stats = rep_stats(&l0_rep_info, trans_vec.len());
    let l0_rep_blocks = as_rep_blocks(&trans_vec, l0_rep_info);

    // Find next level (L1) repeats in l0_rep_blocks
    let l0_block_pattern = strip_reps(l0_rep_blocks);
    let l1_rep_info = find_repeat_info(&l0_block_pattern);
    let l1_stats = rep_stats(&l1_rep_info, l0_block_pattern.len());

    TaskResult {
        program_str: program_str.to_string(),
        duration: start_time.elapsed(),
        l0_stats,
        l1_stats,
    }
}

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    infile: String,
    num_steps: Int,
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
        args.num_steps,
        rayon::current_num_threads()
    );

    // 3. Parallel Execution using Rayon
    let wallclock_start_time = Instant::now();
    let results: Vec<TaskResult> = programs
        .par_iter()
        .progress_count(num_programs as u64)
        .map(|program_str| process_task(program_str, args.num_steps))
        .collect(); // Collect results back into a Vec on the main thread
    let wallclock_time_sec = wallclock_start_time.elapsed().as_secs_f64();

    fn out_format(result: &TaskResult) -> String {
        format!(
            "{}\tL0:{:?}\tL1:{:?}\n",
            result.program_str, result.l0_stats, result.l1_stats
        )
    }

    // 4. Write results to outfile
    let data = results.iter().map(out_format).join("");
    fs::write(&args.outfile, data)?;

    // // 5. Summarize results
    // let halted_count = results.iter().filter(|r| r.sim.halted).count();
    // let frac_halted = halted_count as f64 / num_programs as f64;
    // let max_halt_steps = results
    //     .iter()
    //     .map(|r| if r.sim.halted { r.sim.total_steps } else { 0 })
    //     .max()
    //     .unwrap();
    // let total_steps_simulated: Int = results.iter().map(|r| r.sim.total_steps).sum();

    // let wallclock_rate = total_steps_simulated as f64 / wallclock_time_sec;

    // let max_runtime_sec = results
    //     .iter()
    //     .map(|r| r.duration)
    //     .max()
    //     .unwrap()
    //     .as_secs_f64();
    // let total_thread_runtime_sec = results
    //     .iter()
    //     .map(|r| r.duration)
    //     .sum::<Duration>()
    //     .as_secs_f64();
    // let mean_runtime_sec = total_thread_runtime_sec / num_programs as f64;

    // println!("\nResults Summary:");
    // println!(
    //     "  Halted: {} / {}  ({:.2}%)",
    //     halted_count,
    //     num_programs,
    //     frac_halted * 100.0
    // );
    // println!("  Max Halt Steps: {}", max_halt_steps);
    // println!("  Total steps: {}", total_steps_simulated);
    // println!("Wallclock Time:");
    // println!("  {:.2} seconds", wallclock_time_sec);
    // println!("  {:.2} Million steps/s", wallclock_rate / 1_000_000.0);
    // println!("CPU Time:");
    // println!("  Total: {:.2} core-sec", total_thread_runtime_sec);
    // println!("  Mean:  {:.2} core-sec / program", mean_runtime_sec);
    // println!("  Max:   {:.2} core-sec", max_runtime_sec);

    Ok(())
}
