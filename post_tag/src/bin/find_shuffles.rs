use clap::Parser;
use itertools::Itertools;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::path::PathBuf;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// The target program string (e.g. 0112_2_10)
    target: String,

    /// Input file (output from enum)
    input: PathBuf,
}

use post_tag::tag_system::TagSystem;

fn to_multiset(s: &[u8]) -> Vec<u8> {
    let mut v = s.to_vec();
    v.sort_unstable();
    v
}

fn is_shuffle(a: &[Vec<u8>], b: &[Vec<u8>]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let n = a.len() as u8;

    // Total chars must be same
    let a_len: usize = a.iter().map(|r| r.len()).sum();
    let b_len: usize = b.iter().map(|r| r.len()).sum();
    if a_len != b_len {
        return false;
    }

    let perms = (0..n).permutations(n as usize);
    for pi in perms {
        let mut all_match = true;
        for i in 0..(n as usize) {
            let mut mapped_a = Vec::with_capacity(a[i].len());
            for &c in &a[i] {
                if c >= n {
                    // Invalid char for permutation
                    mapped_a.push(c);
                } else {
                    mapped_a.push(pi[c as usize]);
                }
            }
            let mapped_a_ms = to_multiset(&mapped_a);
            let b_ms = to_multiset(&b[pi[i as usize] as usize]);
            if mapped_a_ms != b_ms {
                all_match = false;
                break;
            }
        }
        if all_match {
            return true;
        }
    }
    false
}

fn main() {
    let args = Args::parse();

    let resolved_target = post_tag::file_io::resolve_program_string(&args.target);
    let target_sys = TagSystem::parse(2, &resolved_target);
    if target_sys.rules.iter().any(|r| r.is_none()) {
        eprintln!("Target program cannot contain '?'");
        return;
    }
    let target_rules: Vec<Vec<u8>> = target_sys.rules.into_iter().map(|r| r.unwrap()).collect();

    println!("Target program: {}", args.target);

    let file = File::open(&args.input).expect("Failed to open input file");
    let reader = BufReader::new(file);

    let mut shuffles = Vec::new();

    for line in reader.lines() {
        let line = line.expect("Failed to read line");
        if let Some(prog_str) = line.split_whitespace().find(|p| p.starts_with("prog=")) {
            let prog = prog_str.strip_prefix("prog=").unwrap();
            let b_sys = TagSystem::parse(2, prog);
            if b_sys.rules.iter().any(|r| r.is_none()) {
                continue; // Skip programs with '?'
            }
            let b_rules: Vec<Vec<u8>> = b_sys.rules.into_iter().map(|r| r.unwrap()).collect();

            if is_shuffle(&target_rules, &b_rules) {
                shuffles.push((prog.to_string(), line.clone()));
            }
        }
    }

    println!("\nFound {} shuffles in {:?}:", shuffles.len(), args.input);
    for (_prog, line) in shuffles {
        println!("{}", line);
    }
}
