use mbb::parse::parse_program;
use mbb::deciders::{Decider, DeciderResult};
use mbb::deciders::bouncers::BouncersDecider;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::time::Instant;

fn main() {
    let file = File::open("mbb_sz8_holdouts_6.txt").unwrap_or_else(|_| File::open("bench_6.txt").unwrap());
    let reader = BufReader::new(file);
    let mut progs = Vec::new();
    for line in reader.lines() {
        let line = line.unwrap();
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') { continue; }
        let prog_str = line.split_whitespace().next().unwrap_or("");
        if let Some(p) = parse_program(prog_str) {
            progs.push(p);
        }
    }

    let bouncers = BouncersDecider { step_limit: 10000 };

    // Benchmark Bouncers
    let start = Instant::now();
    let mut bouncer_solved = 0;
    for p in &progs {
        if matches!(bouncers.decide(p), DeciderResult::Infinite(_)) {
            bouncer_solved += 1;
        }
    }
    let bouncer_time = start.elapsed();
    println!("Bouncers: {} solved in {:?}", bouncer_solved, bouncer_time);

    // Benchmark Polyhedral Guesser
    let start = Instant::now();
    let mut poly_solved = 0;
    for p in &progs {
        if mbb::deciders::polyhedral_guesser::find_closed_set(p, false).is_some() {
            poly_solved += 1;
        }
    }
    let poly_time = start.elapsed();
    println!("Polyhedral Guesser: {} solved in {:?}", poly_solved, poly_time);
}
