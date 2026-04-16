/// Shared fingerprinting utilities for GRF equivalence analysis.
use crate::grf::Grf;
use crate::simulate::simulate;

/// A fingerprint: one entry per canonical input. None = diverged, Some(v) = output value.
pub type Fingerprint = Vec<Option<u64>>;

/// Generate the canonical input set for a given arity.
/// For arity k, produce all k-tuples drawn from {0 .. per_dim-1}
/// where per_dim is chosen so the total stays ≤ ~32 test cases.
pub fn canonical_inputs(arity: usize) -> Vec<Vec<u64>> {
    if arity == 0 {
        return vec![vec![]];
    }
    let per_dim: u64 = match arity {
        1 => 8, // 8 inputs
        2 => 4, // 16 inputs
        3 => 3, // 27 inputs
        _ => 2, // 2^arity inputs
    };
    let mut result: Vec<Vec<u64>> = vec![vec![]];
    for _ in 0..arity {
        let mut next = Vec::new();
        for prefix in &result {
            for v in 0..per_dim {
                let mut row = prefix.clone();
                row.push(v);
                next.push(row);
            }
        }
        result = next;
    }
    result
}

/// Compute the fingerprint of a GRF on the given canonical inputs.
pub fn compute_fp(grf: &Grf, inputs: &[Vec<u64>], max_steps: u64) -> Fingerprint {
    inputs
        .iter()
        .map(|inp| {
            let (result, _) = simulate(grf, inp, max_steps);
            result.into_value()
        })
        .collect()
}
