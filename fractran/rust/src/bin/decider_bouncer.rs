use std::fs;
use std::time::Instant;
use clap::Parser;
use rayon::prelude::*;
use indicatif::ParallelProgressIterator;

use fractran::parse::{load_lines, parse_program};
use fractran::program::State;
use fractran::transcript::{transcript, strip_reps};
use fractran::tandem_repeat::find_rep_blocks;
use fractran::bouncer::{decide_bouncer, BouncerError};

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// File containing FRACTRAN programs (one per line)
    #[arg(value_name = "FILE")]
    filename: String,

    /// Number of steps to simulate for transcript generation
    #[arg(long, default_value_t = 10_000)]
    sim_steps: usize,
}

#[derive(Debug)]
enum BouncerResult {
    Proven,
    Error(BouncerError),
    NoPattern,
}

fn process_program(line: &str, sim_steps: usize) -> BouncerResult {
    let prog_str = line.split('\t').next().unwrap_or(line);
    let prog = parse_program(prog_str);
    let state = State::start(&prog);
    
    let trans_vec = transcript(&prog, state.clone(), sim_steps);
    let rep_blocks = find_rep_blocks(&trans_vec);
    let block_pattern = strip_reps(rep_blocks.clone());
    let meta_rep_blocks = find_rep_blocks(&block_pattern);
    
    let bouncer_candidate = meta_rep_blocks.iter().rev().find(|r| r.rep > 1);
    
    if let Some(candidate) = bouncer_candidate {
        let mut stripped_blocks_before = 0;
        for meta_block in &meta_rep_blocks {
            if std::ptr::eq(meta_block, candidate) {
                break;
            }
            stripped_blocks_before += meta_block.rep * meta_block.block.len();
        }
        
        let mut basic_transitions_before = 0;
        for rep_block in rep_blocks.iter().take(stripped_blocks_before) {
            basic_transitions_before += rep_block.rep * rep_block.block.len();
        }
        
        let mut sim_state = state.clone();
        for _ in 0..basic_transitions_before {
            prog.step(&mut sim_state);
        }
        
        match decide_bouncer(&prog, sim_state, &candidate.block) {
            Ok(true) => BouncerResult::Proven,
            Ok(false) => BouncerResult::Error(BouncerError::NotInfinite),
            Err(e) => BouncerResult::Error(e),
        }
    } else {
        BouncerResult::NoPattern
    }
}

fn main() {
    let args = Args::parse();
    let programs = load_lines(&args.filename);
    
    println!("Analyzing {} programs for bouncers (sim_steps={})...", programs.len(), args.sim_steps);
    let start = Instant::now();
    
    let results: Vec<(String, BouncerResult)> = programs.par_iter()
        .progress_count(programs.len() as u64)
        .map(|line| {
            let prog_str = line.split('\t').next().unwrap_or(line);
            let res = process_program(line, args.sim_steps);
            (prog_str.to_string(), res)
        })
        .collect();
        
    let mut proven = 0;
    let mut exponential = 0;
    let mut non_unit = 0;
    
    for (prog_str, res) in &results {
        match res {
            BouncerResult::Proven => {
                proven += 1;
                println!("BOUNCER: {}", prog_str);
            },
            BouncerResult::Error(BouncerError::ExponentialGrowth) => {
                exponential += 1;
            },
            BouncerResult::Error(BouncerError::NonUnitDecrement) => {
                non_unit += 1;
            },
            _ => {}
        }
    }
    
    println!("\nAnalysis completed in {:.2}s", start.elapsed().as_secs_f64());
    println!("Proven Bouncers: {}", proven);
    println!("Exponential / Non-Polynomial Candidates: {}", exponential);
    println!("Non-Unit Decrement Candidates: {}", non_unit);
}
