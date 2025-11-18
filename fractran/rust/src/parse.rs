use crate::pvas::{Int, PVAS};
use primal::Primes;
use prime_factorization::Factorization;
use std::collections::HashMap;

// --- Parsing & Conversion Logic ---

pub fn parse_and_convert(program_str: &str) -> (PVAS, Vec<Int>) {
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
    let num_rules = rules_fractions.len();
    let mut matrix_flat = vec![0 as Int; dims * num_rules];

    for (row, (num, den)) in rules_fractions.iter().enumerate() {
        // Handle Numerator (Additions)
        let num_factors = Factorization::run(*num);
        for p in num_factors.factors {
            if let Some(&col) = prime_map.get(&p) {
                matrix_flat[row * dims + col] += 1;
            }
        }

        // Handle Denominator (Subtractions)
        let den_factors = Factorization::run(*den);
        for p in den_factors.factors {
            if let Some(&col) = prime_map.get(&p) {
                matrix_flat[row * dims + col] -= 1;
            }
        }
    }

    let pvas = PVAS::new(matrix_flat, dims, num_rules);

    // 5. Initial State: N=2 corresponds to 2^1, so index 0 = 1, others = 0.
    let mut state = vec![0 as Int; dims];
    if dims > 0 {
        state[0] = 1;
    }

    (pvas, state)
}
