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
    canonical_inputs, canonical_inputs_n, grid_inputs, verification_inputs,
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
    /// Number of inputs used both by the `NovelEnumerator` to fingerprint/deduplicate
    /// candidates and as the confidence threshold for accepting a match.
    ///
    /// **Tuning note**: this controls two things at once:
    /// 1. How many inputs the enumerator uses to distinguish functions — too small and
    ///    the target GRF may be deduplicated away before the search ever sees it.
    /// 2. How many inputs a candidate must pass before the verifier accepts it.
    ///
    /// For arity ≥ 2, values below 32 are usually too small. The default (64) is safe
    /// for most specs; raise it if the search returns suspicious small results.
    pub confidence_inputs: usize,
    /// Print size-by-size progress and the accepted GRF to stderr.
    pub progress: bool,
    /// Print a trace line for every candidate tested and the reason it was
    /// accepted or rejected. Very verbose — intended for debugging failing tests.
    pub trace: bool,
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
            trace: false,
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
                if config.trace || config.progress {
                    eprintln!("[search arity={}] ACCEPTED size={} grf={}", config.arity, size, grf);
                }
                return Some(SearchResult {
                    grf: grf.clone(),
                    size,
                    inputs_tested,
                });
            } else if config.trace {
                eprintln!("[search arity={}] rejected size={} grf={}", config.arity, size, grf);
            }
        }

        if config.progress || config.trace {
            let n = enumerator.candidates(config.arity, size).len();
            eprintln!("[search arity={}] size={:>3}: {:>5} candidates", config.arity, size, n);
        }
    }

    None
}

/// Test a single candidate GRF against the spec.
///
/// Returns `Some(n_tested)` if the candidate passed all checks,
/// or `None` if it was rejected (a counterexample found or failed verification).
///
/// Timeout (`OutOfSteps`) on an input is treated as "unknown" and skipped, not as
/// a rejection. The spec cannot be checked on inputs the GRF doesn't converge on
/// within the step budget; a GRF that times out on some inputs but passes all others
/// is still a valid candidate. Use a higher `max_steps` if false positives are a
/// concern for slow-growing functions.
///
/// Exception: if the candidate times out on *every* input in the fast phase (no
/// convergent inputs at all), it is rejected to avoid accepting trivially-divergent
/// GRFs.
fn test_candidate(
    grf: &Grf,
    fast_inputs: &[Vec<u64>],
    conf_inputs: &[Vec<u64>],
    verify_inputs: &[Vec<u64>],
    max_steps: u64,
    spec: &mut dyn FnMut(&[u64], u64) -> bool,
) -> Option<usize> {
    // Phase 1: fast rejection on canonical inputs.
    // A spec failure is an immediate rejection; a timeout is skipped.
    let mut fast_converged = 0usize;
    for inp in fast_inputs {
        match simulate(grf, inp, max_steps).0 {
            SimResult::OutOfSteps => {} // skip — unknown output, not a counterexample
            SimResult::Value(v) => {
                if !spec(inp, v) {
                    return None;
                }
                fast_converged += 1;
            }
        }
    }
    // Reject if the GRF didn't converge on a single fast input — it's almost certainly
    // a diverging function, not just slow.
    if !fast_inputs.is_empty() && fast_converged == 0 {
        return None;
    }

    // Phase 2: confidence pass on the full input set.
    let mut tested = 0usize;
    for inp in conf_inputs {
        match simulate(grf, inp, max_steps).0 {
            SimResult::OutOfSteps => {} // skip
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
            SimResult::OutOfSteps => {} // skip
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

// ── Diagnostic tools ────────────────────────────────────────────────────────

/// Result of probing a GRF against a spec on a set of inputs.
#[derive(Debug, PartialEq)]
pub enum ProbeResult {
    /// All inputs passed. Contains the number of inputs evaluated.
    AllPassed(usize),
    /// The spec rejected this (input, output) pair.
    SpecFailed {
        /// The input tuple on which the spec returned false.
        inputs: Vec<u64>,
        /// The value the GRF returned.
        output: u64,
    },
    /// The GRF exceeded the step budget on this input.
    TimedOut {
        /// The input tuple that caused the timeout.
        inputs: Vec<u64>,
    },
}

impl std::fmt::Display for ProbeResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProbeResult::AllPassed(n) => write!(f, "AllPassed({n} inputs)"),
            ProbeResult::SpecFailed { inputs, output } => {
                write!(f, "SpecFailed(inputs={inputs:?}, output={output})")
            }
            ProbeResult::TimedOut { inputs } => write!(f, "TimedOut(inputs={inputs:?})"),
        }
    }
}

/// Test `grf` against `spec` on every input in `inputs`.
///
/// Returns on the first failure or timeout. Useful for:
/// - Verifying a known-good GRF actually satisfies the spec on a custom input set.
/// - Diagnosing why `search_smallest` accepted or rejected a particular candidate.
/// - Checking whether a result is a false positive on inputs outside the search's
///   confidence set.
pub fn probe_spec(
    grf: &Grf,
    spec: &mut dyn FnMut(&[u64], u64) -> bool,
    inputs: &[Vec<u64>],
    max_steps: u64,
) -> ProbeResult {
    for inp in inputs {
        match simulate(grf, inp, max_steps).0 {
            SimResult::OutOfSteps => return ProbeResult::TimedOut { inputs: inp.clone() },
            SimResult::Value(v) => {
                if !spec(inp, v) {
                    return ProbeResult::SpecFailed { inputs: inp.clone(), output: v };
                }
            }
        }
    }
    ProbeResult::AllPassed(inputs.len())
}

/// Test `grf` against `spec` on all input tuples with each component in `0..=max_val`.
///
/// This is an exhaustive check within the given range. Use it to:
/// - Find false positives: GRFs that pass the confidence inputs but fail elsewhere.
/// - Diagnose whether `max_steps` is too low (a timeout here means steps are needed).
/// - Verify the spec is correct (a surprising failure might indicate a spec bug).
///
/// **Note on `n = 0` for trailing-bits specs**: `2u64.pow(0) - 1 = 0`, so the mask
/// is 0 and the spec passes vacuously for every function when `n = 0`. If your first
/// argument is the bit-count, start `max_val` at 1 or use a custom input list.
///
/// # Panics
/// Panics if `grf.arity() == 0` (no inputs to enumerate) — call `probe_spec` instead.
pub fn exhaustive_probe(
    grf: &Grf,
    spec: &mut dyn FnMut(&[u64], u64) -> bool,
    max_val: u64,
    max_steps: u64,
) -> ProbeResult {
    let inputs = grid_inputs(grf.arity(), max_val + 1);
    probe_spec(grf, spec, &inputs, max_steps)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::grf;
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

    // Spec shared by trailing-bits tests: f(n, x) must end in at least n ones.
    // Note: n=0 → mask=0 → spec passes vacuously for every output; n=0 inputs
    // carry no discriminating power.  Keep confidence_inputs large enough that the
    // NovelEnumerator sees inputs with n ≥ 1 so it doesn't collapse distinct
    // functions into the same fingerprint.
    fn trailing_bits_spec(inputs: &[u64], output: u64) -> bool {
        let n = inputs[0];
        if n >= 64 { return true; } // 2^n overflows u64; treat as vacuously satisfied // TODO false
        let mask = (1u64 << n) - 1;
        (output & mask) == mask
    }

    #[test]
    fn test_search_trailing_bits_arity1() {
        let config = SearchConfig {
            arity: 1,
            max_size: 10,
            max_steps: 100_000,
            confidence_inputs: 8,
            ..Default::default()
        };
        let result = search_smallest(&config, &mut trailing_bits_spec)
            .expect("should find a match");
        assert_eq!(result.size, 10, "should have size 10, got {}: {}", result.size, result.grf);
        assert_eq!(result.grf.arity(), 1);
        // R(Z0, C(R(S, C(S, P(3,2))), P(2,2), P(2,2))) = \x. 2^x - 1
        assert_eq!(result.grf, grf!("R(Z0, C(R(S, C(S, P(3,2))), P(2,2), P(2,2)))"));
    }

    #[test]
    #[ignore = "Too slow"]
    fn test_search_trailing_bits_arity2() {
        let config = SearchConfig {
            arity: 2,
            max_size: 10,
            max_steps: 100_000,
            confidence_inputs: 64,
            ..Default::default()
        };
        let result = search_smallest(&config, &mut trailing_bits_spec)
            .expect("should find a match");
        assert_eq!(result.grf.arity(), 2);
        assert_eq!(result.size, 10,
            "should have size 10, got {}: {}", result.size, result.grf);

        // Verify the result exhaustively on a broad input grid (n in 1..=8, x in 0..=8).
        // We don't assert a specific GRF because multiple size-10 GRFs satisfy the spec
        // (e.g. R(Z1, ...) = 2^n-1 and R(S, ...) = (x+2)·2^n-1 both work).
        let inputs: Vec<Vec<u64>> = (1u64..=8)
            .flat_map(|n| (0u64..=8).map(move |x| vec![n, x]))
            .collect();
        assert_eq!(
            probe_spec(&result.grf, &mut trailing_bits_spec, &inputs, 0),
            ProbeResult::AllPassed(inputs.len()),
            "result GRF {} failed exhaustive probe", result.grf
        );
    }

    #[test]
    fn test_probe_spec_detects_false_positive() {
        // Diagnose issue (3): low confidence_inputs allows false positives.
        // With only 8 inputs at arity 2, n is only in {0,1} from the grid — n=0
        // always passes vacuously, n=1 only requires odd output.  Many wrong GRFs pass.
        // P(2,1) returns n itself: satisfies n=0 (vacuous) and n=1 (output=1, odd).
        // But P(2,1)(2, x) = 2, and mask=3: 2 & 3 = 2 ≠ 3 — it fails for n=2.
        let grf: crate::grf::Grf = grf!("P(2,1)");
        let large_inputs = crate::fingerprint::canonical_inputs_n(2, 64);

        // On 8 inputs (grid only covers n ∈ {0,1}) P(2,1) may look correct…
        // …but on 64 inputs (grid covers n ∈ {0..4}) it fails.
        let result_large = probe_spec(&grf, &mut trailing_bits_spec, &large_inputs, 100_000);
        assert!(
            matches!(result_large, ProbeResult::SpecFailed { .. }),
            "expected P(2,1) to fail on larger input set, got: {result_large}"
        );
    }

    #[test]
    fn test_exhaustive_probe_expected_grf() {
        // Diagnose issue (1): is the expected GRF correct?
        // Exhaustively verify R(S, C(R(S, C(S,P(3,2))), P(3,2), P(3,2))) on n=1..=6, x=0..=6.
        let expected = grf!("R(S, C(R(S, C(S, P(3,2))), P(3,2), P(3,2)))");
        let result = exhaustive_probe(&expected, &mut trailing_bits_spec, 6, 0);
        assert_eq!(
            result,
            ProbeResult::AllPassed(49), // 7×7 grid
            "expected GRF failed exhaustive probe: {result}"
        );
    }

    #[test]
    fn test_probe_spec_timeout_detection() {
        // Diagnose issue (2): max_steps too low.
        // M(S) diverges. With max_steps=10 it should time out, not pass.
        let grf: crate::grf::Grf = grf!("M(S)");
        let inputs = vec![vec![]]; // arity 0
        let result = probe_spec(&grf, &mut |_, _| true, &inputs, 10);
        assert!(
            matches!(result, ProbeResult::TimedOut { .. }),
            "expected timeout, got: {result}"
        );
    }

    #[test]
    #[ignore]
    fn trace_trailing_bits_arity2() {
        // Diagnostic: probe the expected GRF through all three test phases.
        let expected: Grf = grf!("R(S, C(R(S, C(S, P(3,2))), P(3,2), P(3,2)))");
        let arity = 2;
        let max_steps = 1_000_000u64;
        let confidence_inputs = 64usize;
        let fast_inputs = canonical_inputs(arity);
        let conf_inputs = canonical_inputs_n(arity, confidence_inputs);
        let verify_inputs = verification_inputs(arity);

        eprintln!("fast_inputs ({}):", fast_inputs.len());
        for inp in &fast_inputs {
            let (r, _) = simulate(&expected, inp, max_steps);
            let ok = match r {
                SimResult::Value(v) => {
                    let pass = trailing_bits_spec(inp, v);
                    eprintln!("  {:?} -> {} ({})", inp, v, if pass { "PASS" } else { "FAIL" });
                    pass
                }
                SimResult::OutOfSteps => { eprintln!("  {:?} -> TIMEOUT", inp); false }
            };
            if !ok { eprintln!("  ^^^ REJECT on fast_inputs"); break; }
        }

        eprintln!("conf_inputs ({}) first 10:", conf_inputs.len());
        for inp in conf_inputs.iter().take(10) {
            let (r, _) = simulate(&expected, inp, max_steps);
            match r {
                SimResult::Value(v) => {
                    let pass = trailing_bits_spec(inp, v);
                    eprintln!("  {:?} -> {} ({})", inp, v, if pass { "PASS" } else { "FAIL" });
                }
                SimResult::OutOfSteps => eprintln!("  {:?} -> TIMEOUT", inp),
            }
        }

        eprintln!("verify_inputs ({}) first 10:", verify_inputs.len());
        for inp in verify_inputs.iter().take(10) {
            let (r, _) = simulate(&expected, inp, max_steps);
            match r {
                SimResult::Value(v) => {
                    let pass = trailing_bits_spec(inp, v);
                    eprintln!("  {:?} -> {} ({})", inp, v, if pass { "PASS" } else { "FAIL" });
                }
                SimResult::OutOfSteps => eprintln!("  {:?} -> TIMEOUT", inp),
            }
        }

        let result = test_candidate(&expected, &fast_inputs, &conf_inputs, &verify_inputs,
                                    max_steps, &mut trailing_bits_spec);
        eprintln!("test_candidate result: {:?}", result);
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
