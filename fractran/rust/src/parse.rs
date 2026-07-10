use crate::program::{Instr, Program};
use primal::Primes;
use prime_factorization::Factorization;
use std::collections::HashMap;
use std::fs::File;
use std::io::{self, BufRead};

// Parse a Fractran program and convert into vector form.
pub fn parse_program(program_str: &str) -> Program {
    // 1. Clean and split string
    let mut inner = program_str;
    if let Some(start) = inner.find('[') {
        if let Some(end) = inner.rfind(']') {
            inner = &inner[start + 1..end];
        } else {
            panic!("Program string missing closing ']'");
        }
    } else {
        panic!("Program string missing opening '['");
    }

    // 2. Parse fractions and find max prime
    let mut instrs_fractions: Vec<(u128, u128)> = Vec::new();
    let mut max_prime_found: u128 = 2;

    let normalized = inner.replace(',', " ");
    for part in normalized.split_whitespace() {
        if !part.contains('/') {
            panic!("Invalid fraction format (missing '/'): {}", part);
        }

        let frac: Vec<&str> = part.split('/').collect();
        if frac.len() != 2 {
            panic!("Invalid fraction format: {}", part);
        }

        let num: u128 = frac[0].parse().unwrap_or_else(|_| panic!("Invalid numerator in {}", part));
        let den: u128 = frac[1].parse().unwrap_or_else(|_| panic!("Invalid denominator in {}", part));
        instrs_fractions.push((num, den));

        // Check factors to find the largest prime needed for dimensions
        // We iterate the factors to find the max
        let num_factors = Factorization::run(num);
        let den_factors = Factorization::run(den);

        if let Some(&max) = num_factors.factors.iter().max() {
            if max > max_prime_found {
                max_prime_found = max;
            }
        }
        if let Some(&max) = den_factors.factors.iter().max() {
            if max > max_prime_found {
                max_prime_found = max;
            }
        }
    }

    // 3. Generate prime map (Prime -> Index) using `primal` crate
    // We map standard primes 2->0, 3->1, 5->2... up to max_prime_found
    let mut prime_map = HashMap::new();
    let mut dims = 0;

    // Primes::all() returns an iterator of usize. We cast to u128.
    for (i, p) in Primes::all().enumerate() {
        let p_u128 = p as u128;
        prime_map.insert(p_u128, i);
        dims = i + 1;
        if p_u128 >= max_prime_found {
            break;
        }
    }

    // 4. Build Matrix
    let mut instrs: Vec<Instr> = Vec::new();

    for (num, den) in instrs_fractions.iter() {
        let mut instr = vec![0; dims];
        // Handle Numerator (Additions)
        let num_factors = Factorization::run(*num);
        for p in num_factors.factors {
            if let Some(&col) = prime_map.get(&p) {
                instr[col] += 1;
            }
        }

        // Handle Denominator (Subtractions)
        let den_factors = Factorization::run(*den);
        for p in den_factors.factors {
            if let Some(&col) = prime_map.get(&p) {
                instr[col] -= 1;
            }
        }
        instrs.push(Instr::new(instr));
    }

    Program { instrs }
}

// Load all program strings from a file (without parsing).
pub fn load_lines(filename: &str) -> Vec<String> {
    let file = File::open(filename).expect("File not found");
    let reader = io::BufReader::new(file);

    reader
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
        .collect()
}

// Parse a filename with optional trailing :n record number (defaults to 0).
pub fn split_filename_record(filename_record: &str) -> (String, usize) {
    match filename_record.split_once(":") {
        Some((left, right)) => (left.to_string(), right.parse().expect("Invalid record_num")),
        None => (filename_record.to_string(), 0),
    }
}

pub fn load_program(input: &str) -> Option<Program> {
    // First check if it is a literal program
    if input.contains('[') {
        return Some(parse_program(input));
    }

    // Then attemp to load it as a filename/filename:n
    let (filename, record_num) = split_filename_record(input);
    let lines = load_lines(&filename);
    let prog_str = lines.iter().nth(record_num)?;
    Some(parse_program(prog_str))
}
