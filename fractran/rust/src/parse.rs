use crate::pvas::{Int, Program, Rule};
use primal::Primes;
use prime_factorization::Factorization;
use std::collections::HashMap;

// --- Parsing & Conversion Logic ---

pub fn parse_program(program_str: &str) -> Program {
    // 1. Clean and split string
    let clean_str = program_str.replace(['[', ']', ' '], "");
    let parts: Vec<&str> = clean_str.split(',').collect();

    // 2. Parse fractions and find max prime
    let mut rules_fractions: Vec<(u128, u128)> = Vec::new();
    let mut max_prime_found: u128 = 2;

    for part in parts {
        let frac: Vec<&str> = part.split('/').collect();
        let num: u128 = frac[0].parse().expect("Invalid numerator");
        let den: u128 = frac[1].parse().expect("Invalid denominator");
        rules_fractions.push((num, den));

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
    let mut rules: Vec<Rule> = Vec::new();

    for (num, den) in rules_fractions.iter() {
        let mut rule = vec![0 as Int; dims];
        // Handle Numerator (Additions)
        let num_factors = Factorization::run(*num);
        for p in num_factors.factors {
            if let Some(&col) = prime_map.get(&p) {
                rule[col] += 1;
            }
        }

        // Handle Denominator (Subtractions)
        let den_factors = Factorization::run(*den);
        for p in den_factors.factors {
            if let Some(&col) = prime_map.get(&p) {
                rule[col] -= 1;
            }
        }
        rules.push(Rule::new(rule));
    }

    Program { rules }
}
