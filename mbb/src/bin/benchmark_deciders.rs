use mbb::deciders::bouncers::BouncersDecider;
use mbb::deciders::{Decider, DeciderResult};
use mbb::parse::parse_program;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::time::Instant;

fn main() {
    for filename in &["bench_6.txt", "bench_7.txt"] {
        println!("\n=== {} ===", filename);
        let file = File::open(filename).unwrap();
        let reader = BufReader::new(file);
        let mut progs = Vec::new();
        for line in reader.lines() {
            let line = line.unwrap();
            let line = line.trim();
            if line.is_empty() || line.starts_with('#') {
                continue;
            }
            let prog_str = line.split_whitespace().next().unwrap_or("");
            if let Some(p) = parse_program(prog_str) {
                progs.push(p);
            }
        }

        let bouncers = BouncersDecider { step_limit: 10000 };

        // Benchmark Backwards
        let backwards = mbb::deciders::backwards::BackwardsDecider;
        let start = Instant::now();
        let mut backwards_solved = 0;
        for p in &progs {
            if matches!(backwards.decide(p), DeciderResult::Infinite(_)) {
                backwards_solved += 1;
            }
        }
        let backwards_time = start.elapsed();
        println!(
            "Backwards: {} solved in {:?}",
            backwards_solved, backwards_time
        );

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
            if mbb::deciders::polyhedral_guesser::find_closed_set(p, false, 100_000).is_some() {
                poly_solved += 1;
            }
        }
        let poly_time = start.elapsed();
        println!(
            "Polyhedral Guesser: {} solved in {:?}",
            poly_solved, poly_time
        );

        // Benchmark Semilinear1D
        let start = Instant::now();
        let mut semi_solved = 0;
        for p in &progs {
            if matches!(
                mbb::deciders::semilinear1d_guesser::decide_semilinear1d(p, 100_000, false),
                DeciderResult::Infinite(_)
            ) {
                semi_solved += 1;
            }
        }
        let semi_time = start.elapsed();
        println!("Semilinear1D: {} solved in {:?}", semi_solved, semi_time);

        // Benchmark Congruence
        let start = Instant::now();
        let mut cong_solved = 0;
        for p in &progs {
            if matches!(
                mbb::deciders::congruence_guesser::decide_congruence(p, 100_000, false),
                DeciderResult::Infinite(_)
            ) {
                cong_solved += 1;
            }
        }
        let cong_time = start.elapsed();
        println!("Congruence: {} solved in {:?}", cong_solved, cong_time);
    }
}
