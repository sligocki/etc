/// Adaptive spec-matching search: find the smallest GRF satisfying a spec.
///
/// Uses the canonical-subexpression strategy from `NovelEnumerator` to enumerate
/// GRFs size-by-size, testing each candidate against a user-supplied spec closure.
/// Exits as soon as a match is confirmed, without needing a pre-built NovelDb.
///
/// # Early-exit testing
///
/// For each candidate the spec is tested adaptively:
/// 1. Run the small canonical input set (~8 or ~32 points). Any counterexample
///    rejects the candidate immediately — fast rejection for wrong functions.
/// 2. If all pass, expand to `confidence_inputs` total points. Once the full set
///    passes, the candidate is verified on `verification_inputs` (broader coverage).
/// 3. The first candidate that survives all checks is returned.
///
/// # Spec signature
///
/// `spec(inputs, output) -> bool`
/// - `inputs`: the argument tuple fed to the GRF.
/// - `output`: the value the GRF returned (already simulated).
/// - Return `true` if this (input, output) pair satisfies the spec.
///
/// If the GRF times out on an input (`OutOfSteps`), that candidate is skipped.
///
/// # Example
///
/// ```ignore
/// // Find the smallest GRF computing predecessor (saturating at 0).
/// let mut spec = exact_spec(|args| Some(args[0].saturating_sub(1)));
/// let config = SearchConfig { arity: 1, max_size: 10, ..Default::default() };
/// let result = search_smallest(&config, &mut spec);
/// ```
use crate::fingerprint::{
    canonical_inputs, canonical_inputs_n, verification_inputs,
};
use crate::grf::Grf;
use crate::novel_enum::NovelEnumerator;
use crate::simulate::{simulate, SimResult};

/// Configuration for `search_smallest`.
pub struct SearchConfig {
    /// Arity of the GRF to search for.
    pub arity: usize,
    /// Whether to allow minimization (`Min`) operators.
    pub allow_min: bool,
    /// Stop searching after this GRF size (inclusive). Returns `None` if not found.
    pub max_size: usize,
    /// Step budget per simulation call. `0` = unlimited.
    pub max_steps: u64,
    /// Number of inputs that must all pass before accepting a candidate.
    /// Higher values reduce false positives but slow down acceptance.
    pub confidence_inputs: usize,
    /// Print progress to stderr as each size is completed.
    pub progress: bool,
}

impl Default for SearchConfig {
    fn default() -> Self {
        SearchConfig {
            arity: 1,
            allow_min: false,
            max_size: 12,
            max_steps: 100_000,
            confidence_inputs: 64,
            progress: false,
        }
    }
}

/// The result of a successful search.
pub struct SearchResult {
    /// The smallest GRF found satisfying the spec.
    pub grf: Grf,
    /// Size of the found GRF.
    pub size: usize,
    /// Number of inputs tested on the accepted candidate before accepting.
    pub inputs_tested: usize,
}

/// Find the smallest GRF of `config.arity` that satisfies `spec` on all tested
/// inputs, searching up to `config.max_size`. Returns `None` if not found.
///
/// Enumerate using canonical subexpressions (via `NovelEnumerator`), testing
/// each candidate adaptively. The first candidate surviving all checks is returned.
pub fn search_smallest(
    config: &SearchConfig,
    spec: &mut dyn FnMut(&[u64], u64) -> bool,
) -> Option<SearchResult> {
    let mut enumerator = NovelEnumerator::new(config.confidence_inputs, config.max_steps, config.allow_min);

    // Small canonical set for fast rejection.
    let fast_inputs = canonical_inputs(config.arity);
    // Full confidence set (superset of fast_inputs).
    let conf_inputs = canonical_inputs_n(config.arity, config.confidence_inputs);
    // Verification set for final false-positive guard.
    let verify_inputs = verification_inputs(config.arity);

    for size in 1..=config.max_size {
        enumerator.compute_size(config.arity, size);
        let candidates = enumerator.candidates(config.arity, size);

        for grf in candidates {
            if let Some(inputs_tested) =
                test_candidate(grf, &fast_inputs, &conf_inputs, &verify_inputs, config.max_steps, spec)
            {
                return Some(SearchResult {
                    grf: grf.clone(),
                    size,
                    inputs_tested,
                });
            }
        }

        if config.progress {
            let n = enumerator.candidates(config.arity, size).len();
            eprintln!("size {:>3}: {:>5} canonical candidates tested", size, n);
        }
    }

    None
}

/// Test a single candidate GRF against the spec.
///
/// Returns `Some(n_tested)` if the candidate passed all checks,
/// or `None` if it was rejected (counterexample found, timed out, or failed verification).
fn test_candidate(
    grf: &Grf,
    fast_inputs: &[Vec<u64>],
    conf_inputs: &[Vec<u64>],
    verify_inputs: &[Vec<u64>],
    max_steps: u64,
    spec: &mut dyn FnMut(&[u64], u64) -> bool,
) -> Option<usize> {
    // Phase 1: fast rejection on canonical inputs.
    for inp in fast_inputs {
        match simulate(grf, inp, max_steps).0 {
            SimResult::OutOfSteps => return None,
            SimResult::Value(v) => {
                if !spec(inp, v) {
                    return None;
                }
            }
        }
    }

    // Phase 2: confidence pass on the full input set.
    // Skip inputs already tested in phase 1 (fast_inputs is a prefix-style set only
    // for arity 1; for arity ≥ 2, conf_inputs uses a different grid so we just
    // re-test all conf_inputs — the cost is low).
    let mut tested = 0usize;
    for inp in conf_inputs {
        match simulate(grf, inp, max_steps).0 {
            SimResult::OutOfSteps => return None,
            SimResult::Value(v) => {
                if !spec(inp, v) {
                    return None;
                }
                tested += 1;
            }
        }
    }

    // Phase 3: verification on broader grid to guard against false positives.
    for inp in verify_inputs {
        match simulate(grf, inp, max_steps).0 {
            SimResult::OutOfSteps => return None,
            SimResult::Value(v) => {
                if !spec(inp, v) {
                    return None;
                }
            }
        }
    }

    Some(tested)
}

/// Build an exact-match spec from a reference function.
///
/// `f(inputs)` should return `Some(expected_output)` when the reference function
/// converges, or `None` when it diverges (that input is skipped, not a counterexample).
pub fn exact_spec<F>(mut f: F) -> impl FnMut(&[u64], u64) -> bool
where
    F: FnMut(&[u64]) -> Option<u64>,
{
    move |inputs: &[u64], output: u64| match f(inputs) {
        Some(expected) => expected == output,
        None => true, // reference diverges: skip this input
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::simulate::Num;

    fn cfg(arity: usize, max_size: usize) -> SearchConfig {
        SearchConfig {
            arity,
            max_size,
            max_steps: 100_000,
            confidence_inputs: 32,
            ..Default::default()
        }
    }

    #[test]
    fn test_search_succ() {
        // Successor: S, size 1.
        let mut spec = exact_spec(|args| Some(args[0] + 1));
        let result = search_smallest(&cfg(1, 5), &mut spec).expect("should find succ");
        assert_eq!(result.size, 1);
        assert_eq!(result.grf.arity(), 1);
    }

    #[test]
    fn test_search_pred() {
        // Predecessor (saturating): R(Z0, P(2,1)), size 3.
        let mut spec = exact_spec(|args| Some(args[0].saturating_sub(1)));
        let result = search_smallest(&cfg(1, 6), &mut spec).expect("should find pred");
        assert_eq!(result.size, 3, "pred should have size 3, got {}: {}", result.size, result.grf);
    }

    #[test]
    fn test_search_add() {
        // Addition: R(P(1,1), C(S, P(3,2))), size 5.
        let mut spec = exact_spec(|args| Some(args[0] + args[1]));
        let result = search_smallest(&cfg(2, 8), &mut spec).expect("should find add");
        assert_eq!(result.size, 5, "add should have size 5, got {}: {}", result.size, result.grf);
        assert_eq!(result.grf.arity(), 2);
    }

    #[test]
    #[ignore = "Too slow to run often"]
    fn test_search_property_ends_in_n_ones() {
        let config = SearchConfig {
            arity: 1,
            max_size: 10,
            max_steps: 100_000,
            confidence_inputs: 16,
            ..Default::default()
        };
        // Property spec: foo(n,_) ends in >= n 1s
        fn spec(inputs: &[u64], output: u64) -> bool {
            let n = inputs[0];
            let mask = 2u64.pow(n as u32) - 1;
            (output & mask) == mask
        }
        let result = search_smallest(&config, &mut spec).expect("should find a match");
        // Arity-1: R(Z0, C(R(S, C(S, P(3,2))), P(2,2), P(2,2))) = \x. 2^x - 1
        // Arity-2: R(S, C(R(S, C(S, P(3,2))), P(3,2), P(3,2)))  = \xy. (y+2) 2^x - 1
        assert_eq!(result.size, 10, "should have size 10, got {}: {}", result.size, result.grf);
        assert_eq!(result.grf.arity(), 1);
    }

    #[test]
    fn test_search_no_match() {
        // A spec no size-3 or smaller GRF can satisfy: must return > 100 for every input.
        let mut spec = |_inputs: &[u64], output: u64| output > 100;
        let result = search_smallest(&SearchConfig { arity: 1, max_size: 3, ..Default::default() }, &mut spec);
        assert!(result.is_none(), "should not find a match");
    }

    #[test]
    fn test_exact_spec_skips_none() {
        // exact_spec should skip inputs where reference returns None.
        let mut spec = exact_spec(|args: &[Num]| {
            if args[0] == 0 { None } else { Some(args[0] - 1) }
        });
        // Input 0: reference diverges -> should pass (skip).
        assert!(spec(&[0], 42));
        // Input 5: reference = 4. GRF output matches.
        assert!(spec(&[5], 4));
        // Input 5: reference = 4. GRF output doesn't match.
        assert!(!spec(&[5], 3));
    }
}
