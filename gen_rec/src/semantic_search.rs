/// Spec-matching search: find the smallest GRF satisfying a spec.
///
/// Enumerates every GRF of each size (via `stream_grf`) and tests each against a
/// user-supplied spec closure.
///
/// # Testing phases
///
/// For each candidate the spec is tested adaptively:
/// 1. Run the small canonical input set (~8 or ~32 points). Any counterexample
///    rejects immediately; if zero inputs converge the candidate is rejected.
/// 2. If all pass, expand to `confidence_inputs` total points.
/// 3. If those pass, verify on `verification_inputs` (broader coverage).
///
/// A candidate is **guaranteed** if no timeouts occurred in phases 2–3.
/// A candidate is **partial** if it passed all convergent inputs but some timed out.
/// Guaranteed matches stop the search; partial matches are collected and the search
/// continues until a guaranteed match is found or `max_size` is reached.
///
/// # Spec signature
///
/// `spec(inputs, output) -> bool`
/// - `inputs`: the argument tuple fed to the GRF.
/// - `output`: the value the GRF returned (already simulated).
/// - Return `true` if this (input, output) pair satisfies the spec.
///
/// # Example
///
/// ```ignore
/// let mut spec = exact_spec(|args| Some(args[0].saturating_sub(1)));
/// let config = SearchConfig { arity: 1, max_size: 10, ..Default::default() };
/// let output = search_smallest(&config, &mut spec);
/// if let Some(r) = output.guaranteed.first() { println!("{}", r.grf); }
/// ```
use crate::enumerate::stream_grf;
use crate::fingerprint::{
    canonical_inputs, canonical_inputs_n, grid_inputs, verification_inputs,
};
use crate::grf::Grf;
use crate::pruning::PruningOpts;
use crate::simulate::{simulate, SimResult};
use std::collections::BTreeMap;
use std::time::Instant;

/// Configuration for `search_smallest`.
pub struct SearchConfig {
    /// Arity of the GRF to search for.
    pub arity: usize,
    /// Whether to allow minimization (`Min`) operators.
    pub allow_min: bool,
    /// Stop searching after this GRF size (inclusive).
    pub max_size: usize,
    /// Step budget per simulation call. `0` = unlimited.
    pub max_steps: u64,
    /// Number of inputs used as the confidence threshold for accepting a match.
    ///
    /// A candidate must pass the spec on all `confidence_inputs` inputs (after the
    /// fast phase) before proceeding to final verification. Larger values reduce
    /// false positives at the cost of more simulation per candidate.
    ///
    /// For arity ≥ 2, values below 32 are usually too small. The default (64) is safe
    /// for most specs; raise it if the search returns suspicious small results.
    pub confidence_inputs: usize,
    /// Print size-by-size progress and accepted GRFs to stderr.
    pub progress: bool,
    /// Print a trace line for every candidate tested. Very verbose.
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

/// The result for a single matching GRF.
pub struct SearchResult {
    /// The GRF found.
    pub grf: Grf,
    /// Size of the GRF.
    pub size: usize,
    /// Number of inputs on which the GRF converged and was verified.
    pub inputs_tested: usize,
    /// Number of inputs on which the GRF timed out (could not be verified).
    /// Zero for guaranteed matches; positive for partial matches.
    pub timed_out_inputs: usize,
}

/// Output of a search: guaranteed matches plus partial matches found along the way.
pub struct SearchOutput {
    /// GRFs that converged and matched on every tested input (no timeouts).
    /// For `search_smallest`, has 0 or 1 entries.
    /// For `search_all_at_min`, contains all such GRFs at the minimum matching size.
    pub guaranteed: Vec<SearchResult>,
    /// GRFs that passed all convergent inputs but timed out on at least one.
    /// These may be correct but cannot be fully verified within the step budget.
    /// At most one entry per size — the one that converged on the most inputs.
    /// Ordered by size ascending.
    pub partials: Vec<SearchResult>,
}

/// Find the smallest GRF of `config.arity` that satisfies `spec` on all tested
/// inputs with no timeouts, searching up to `config.max_size`.
///
/// Partial matches (pass convergent inputs, time out on others) are collected in
/// `output.partials` and the search continues until a guaranteed match is found.
pub fn search_smallest(
    config: &SearchConfig,
    spec: &mut dyn FnMut(&[u64], u64) -> bool,
) -> SearchOutput {
    let opts = PruningOpts::default();
    let fast_inputs = canonical_inputs(config.arity);
    let conf_inputs = canonical_inputs_n(config.arity, config.confidence_inputs);
    let verify_inputs = verification_inputs(config.arity);
    // best partial per size: size → SearchResult with most inputs_tested
    let mut best_partial: BTreeMap<usize, SearchResult> = BTreeMap::new();

    for size in 1..=config.max_size {
        let mut guaranteed: Option<SearchResult> = None;
        let mut candidates_at_size: usize = 0;
        let t_size = Instant::now();

        stream_grf(size, config.arity, config.allow_min, opts, &mut |grf: &Grf| {
            if guaranteed.is_some() {
                return;
            }
            candidates_at_size += 1;
            if let Some((converged, timed_out)) =
                test_candidate(grf, &fast_inputs, &conf_inputs, &verify_inputs, config.max_steps, spec)
            {
                let r = SearchResult { grf: grf.clone(), size, inputs_tested: converged, timed_out_inputs: timed_out };
                if timed_out == 0 {
                    if config.trace || config.progress {
                        eprintln!("[search arity={}] GUARANTEED size={} grf={}", config.arity, size, grf);
                    }
                    guaranteed = Some(r);
                } else {
                    let is_new_best = best_partial.get(&size)
                        .map_or(true, |prev| converged > prev.inputs_tested);
                    if is_new_best {
                        if config.trace || config.progress {
                            eprintln!("[search arity={}] partial   size={} grf={}  ({} timeout(s))", config.arity, size, grf, timed_out);
                        }
                        best_partial.insert(size, r);
                    } else if config.trace {
                        eprintln!("[search arity={}] partial   size={} grf={}  ({} timeout(s)) [not best]", config.arity, size, grf, timed_out);
                    }
                }
            } else if config.trace {
                eprintln!("[search arity={}] rejected  size={} grf={}", config.arity, size, grf);
            }
        });

        if let Some(r) = guaranteed {
            // Drop any partials at the same size — the guaranteed match supersedes them.
            let partials = best_partial.into_iter().filter(|(s, _)| *s < size).map(|(_, v)| v).collect();
            return SearchOutput { guaranteed: vec![r], partials };
        }

        if config.progress || config.trace {
            eprintln!("[search arity={}] size={:>3}: {:>5} candidates  ({:.1?})", config.arity, size, candidates_at_size, t_size.elapsed());
        }
    }

    SearchOutput { guaranteed: vec![], partials: best_partial.into_values().collect() }
}

/// Find ALL structurally-distinct guaranteed GRFs at the minimum matching size.
///
/// Returns a `SearchOutput` where `guaranteed` holds every GRF at the minimum size
/// that converges on all tested inputs, and `partials` holds partial matches from
/// smaller sizes plus any at the minimum size.
pub fn search_all_at_min(
    config: &SearchConfig,
    spec: &mut dyn FnMut(&[u64], u64) -> bool,
) -> SearchOutput {
    // First pass: find the min size and collect early partials.
    let first = search_smallest(config, &mut *spec);
    let min_size = match first.guaranteed.first() {
        Some(r) => r.size,
        None => return first,
    };

    // Partials found before reaching min_size (those at min_size will be re-enumerated).
    let early_partials: Vec<SearchResult> = first.partials.into_iter().filter(|r| r.size < min_size).collect();

    let opts = PruningOpts::default();
    let fast_inputs = canonical_inputs(config.arity);
    let conf_inputs = canonical_inputs_n(config.arity, config.confidence_inputs);
    let verify_inputs = verification_inputs(config.arity);

    // Second pass: collect ALL guaranteed matches at min_size; best partial at min_size.
    let mut all_guaranteed: Vec<SearchResult> = Vec::new();
    let mut best_at_min: Option<SearchResult> = None;
    stream_grf(min_size, config.arity, config.allow_min, opts, &mut |grf: &Grf| {
        if let Some((converged, timed_out)) =
            test_candidate(grf, &fast_inputs, &conf_inputs, &verify_inputs, config.max_steps, spec)
        {
            let r = SearchResult { grf: grf.clone(), size: min_size, inputs_tested: converged, timed_out_inputs: timed_out };
            if timed_out == 0 {
                all_guaranteed.push(r);
            } else {
                let is_new_best = best_at_min.as_ref().map_or(true, |prev| converged > prev.inputs_tested);
                if is_new_best { best_at_min = Some(r); }
            }
        }
    });

    // Only include best_at_min if no guaranteed match was found at this size.
    let partials = if all_guaranteed.is_empty() {
        early_partials.into_iter().chain(best_at_min).collect()
    } else {
        early_partials
    };
    SearchOutput { guaranteed: all_guaranteed, partials }
}

/// Test a single candidate GRF against the spec.
///
/// Returns `Some((converged, timed_out))` if the candidate passed all checks:
/// - `converged`: inputs on which the GRF produced a value that satisfied the spec.
/// - `timed_out`: inputs on which the GRF exceeded the step budget.
/// Returns `None` if a counterexample was found or no fast-phase input converged.
///
/// A timeout is not a counterexample — the spec simply cannot be checked on inputs
/// the GRF doesn't converge on within the step budget. Callers interpret
/// `timed_out > 0` as a partial (unverified) result.
fn test_candidate(
    grf: &Grf,
    fast_inputs: &[Vec<u64>],
    conf_inputs: &[Vec<u64>],
    verify_inputs: &[Vec<u64>],
    max_steps: u64,
    spec: &mut dyn FnMut(&[u64], u64) -> bool,
) -> Option<(usize, usize)> {
    // Phase 1: fast rejection on canonical inputs.
    let mut fast_converged = 0usize;
    for inp in fast_inputs {
        match simulate(grf, inp, max_steps).0 {
            SimResult::OutOfSteps => {}
            SimResult::Value(v) => {
                if !spec(inp, v) {
                    return None;
                }
                fast_converged += 1;
            }
        }
    }
    // Hard-reject if nothing converged in the fast phase — no evidence of correctness.
    if !fast_inputs.is_empty() && fast_converged == 0 {
        return None;
    }

    // Phase 2: confidence pass on the full input set.
    let mut converged = 0usize;
    for inp in conf_inputs {
        match simulate(grf, inp, max_steps).0 {
            SimResult::OutOfSteps => {}
            SimResult::Value(v) => {
                if !spec(inp, v) {
                    return None;
                }
                converged += 1;
            }
        }
    }
    // timed_out = confidence inputs that didn't converge (counted once, not once per phase).
    let timed_out = conf_inputs.len() - converged;

    // Phase 3: verification on broader grid to guard against false positives.
    for inp in verify_inputs {
        match simulate(grf, inp, max_steps).0 {
            SimResult::OutOfSteps => {}
            SimResult::Value(v) => {
                if !spec(inp, v) {
                    return None;
                }
            }
        }
    }

    Some((converged, timed_out))
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
        let output = search_smallest(&cfg(1, 5), &mut spec);
        let result = output.guaranteed.into_iter().next().expect("should find succ");
        assert_eq!(result.size, 1);
        assert_eq!(result.grf.arity(), 1);
    }

    #[test]
    fn test_search_pred() {
        // Predecessor (saturating): R(Z0, P(2,1)), size 3.
        let mut spec = exact_spec(|args| Some(args[0].saturating_sub(1)));
        let output = search_smallest(&cfg(1, 6), &mut spec);
        let result = output.guaranteed.into_iter().next().expect("should find pred");
        assert_eq!(result.size, 3, "pred should have size 3, got {}: {}", result.size, result.grf);
    }

    #[test]
    fn test_search_add() {
        // Addition: R(P(1,1), C(S, P(3,2))), size 5.
        let mut spec = exact_spec(|args| Some(args[0] + args[1]));
        let output = search_smallest(&cfg(2, 8), &mut spec);
        let result = output.guaranteed.into_iter().next().expect("should find add");
        assert_eq!(result.size, 5, "add should have size 5, got {}: {}", result.size, result.grf);
        assert_eq!(result.grf.arity(), 2);
    }

    #[test]
    #[ignore = "Too slow"]
    fn test_search_div2() {
        let mut spec = exact_spec(|args| Some(args[0] / 2));
        let output = search_smallest(&cfg(1, 14), &mut spec);
        let result = output.guaranteed.into_iter().next().unwrap();
        assert_eq!(result.size, 14, "Found size {}: {}", result.size, result.grf);
        assert_eq!(result.grf.arity(), 1);
    }

    #[test]
    #[ignore = "Too slow"]
    fn test_search_ceildiv2() {
        let mut spec = exact_spec(|args| Some(args[0].div_ceil(2)));
        let output = search_smallest(&cfg(1, 14), &mut spec);
        let result = output.guaranteed.into_iter().next().unwrap();
        assert_eq!(result.size, 14, "Found size {}: {}", result.size, result.grf);
        assert_eq!(result.grf.arity(), 1);
    }

    #[test]
    #[ignore = "Too slow"]
    fn test_search_pow2() {
        // confidence_inputs must stay ≤ 16 here: 2^x − 1 takes ~3·2^x simulation steps,
        // so x=16 already exceeds the 100k step budget.
        let mut spec = exact_spec(|args| Some(2u64.pow(args[0] as u32)));
        let config = SearchConfig {
            arity: 1,
            max_size: 12,
            max_steps: 100_000,
            confidence_inputs: 12,
            ..Default::default()
        };
        let output = search_smallest(&config, &mut spec);
        let result = output.guaranteed.into_iter().next().expect("should find pow2");
        assert_eq!(result.size, 12, "Found size {}: {}", result.size, result.grf);
        assert_eq!(result.grf.arity(), 1);
    }

    // Spec shared by trailing-bits tests: f(n, x) must end in at least n ones.
    fn trailing_bits_spec(inputs: &[u64], output: u64) -> bool {
        let n = inputs[0];
        if n >= 64 { return true; }
        let mask = (1u64 << n) - 1;
        (output & mask) == mask
    }

    #[test]
    #[ignore = "Too slow"]
    fn test_search_trailing_bits_arity1() {
        let config = SearchConfig {
            arity: 1,
            max_size: 10,
            max_steps: 100_000,
            confidence_inputs: 8,
            ..Default::default()
        };
        let output = search_smallest(&config, &mut trailing_bits_spec);
        let result = output.guaranteed.into_iter().next().expect("should find a match");
        assert_eq!(result.size, 10, "should have size 10, got {}: {}", result.size, result.grf);
        assert_eq!(result.grf.arity(), 1);
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
        let output = search_smallest(&config, &mut trailing_bits_spec);
        let result = output.guaranteed.into_iter().next().expect("should find a match");
        assert_eq!(result.grf.arity(), 2);
        assert_eq!(result.size, 10, "should have size 10, got {}: {}", result.size, result.grf);

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
        let grf: crate::grf::Grf = grf!("P(2,1)");
        let large_inputs = crate::fingerprint::canonical_inputs_n(2, 64);
        let result_large = probe_spec(&grf, &mut trailing_bits_spec, &large_inputs, 100_000);
        assert!(
            matches!(result_large, ProbeResult::SpecFailed { .. }),
            "expected P(2,1) to fail on larger input set, got: {result_large}"
        );
    }

    #[test]
    fn test_exhaustive_probe_expected_grf() {
        let expected = grf!("R(S, C(R(S, C(S, P(3,2))), P(3,2), P(3,2)))");
        let result = exhaustive_probe(&expected, &mut trailing_bits_spec, 6, 0);
        assert_eq!(result, ProbeResult::AllPassed(49), "expected GRF failed exhaustive probe: {result}");
    }

    #[test]
    fn test_probe_spec_timeout_detection() {
        let grf: crate::grf::Grf = grf!("M(S)");
        let inputs = vec![vec![]];
        let result = probe_spec(&grf, &mut |_, _| true, &inputs, 10);
        assert!(matches!(result, ProbeResult::TimedOut { .. }), "expected timeout, got: {result}");
    }

    #[test]
    #[ignore]
    fn trace_trailing_bits_arity2() {
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
    fn test_diverging_grf_not_guaranteed() {
        // M(P(2,2)) converges only on input 0 (returning 0). With the div3 spec,
        // that single convergence matches (div3(0)=0), so it becomes a partial match.
        // It must NOT appear as a guaranteed match.
        let mut spec = exact_spec(|a| Some(a[0] / 3));
        let output = search_smallest(
            &SearchConfig { arity: 1, allow_min: true, max_size: 2, ..Default::default() },
            &mut spec,
        );
        assert!(
            output.guaranteed.is_empty(),
            "M(P(2,2)) should not be a guaranteed match for div3, got: {}",
            output.guaranteed.iter().map(|r| r.grf.to_string()).collect::<Vec<_>>().join(", "),
        );
    }

    #[test]
    fn test_search_no_match() {
        let mut spec = |_inputs: &[u64], output: u64| output > 100;
        let output = search_smallest(&SearchConfig { arity: 1, max_size: 3, ..Default::default() }, &mut spec);
        assert!(output.guaranteed.is_empty(), "should not find a match");
    }

    #[test]
    fn test_exact_spec_skips_none() {
        let mut spec = exact_spec(|args: &[Num]| {
            if args[0] == 0 { None } else { Some(args[0] - 1) }
        });
        assert!(spec(&[0], 42));
        assert!(spec(&[5], 4));
        assert!(!spec(&[5], 3));
    }
}
