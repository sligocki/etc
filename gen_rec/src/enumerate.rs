use crate::grf::Grf;
use crate::pruning::PruningOpts;
use std::cell::RefCell;
use std::collections::HashMap;

// ---------------------------------------------------------------------------
// GRF streaming enumeration
// ---------------------------------------------------------------------------

/// Call `callback` once for each GRF of exactly `size` with exactly `arity` inputs.
///
/// - `allow_min`: include the Minimization combinator (GRF); exclude for PRF-only.
/// - `opts`: structural pruning options (see [`PruningOpts`]).
///
/// No `Vec<Grf>` is ever materialised — memory use is O(size) at any point.
pub fn stream_grf<F: FnMut(&Grf)>(
    size: usize,
    arity: usize,
    allow_min: bool,
    opts: PruningOpts,
    callback: &mut F,
) {
    for_each_grf(size, arity, allow_min, opts, callback);
}

/// Internal recursive generator.  Uses `&mut dyn FnMut` so nested closures can
/// each capture and call through the same `callback` reference without the
/// borrow checker rejecting two simultaneous `&mut F` borrows.
fn for_each_grf(
    size: usize,
    arity: usize,
    allow_min: bool,
    opts: PruningOpts,
    callback: &mut dyn FnMut(&Grf),
) {
    if size == 0 {
        return;
    }
    if size == 1 {
        callback(&Grf::Zero(arity));
        for i in 1..=arity {
            callback(&Grf::Proj(arity, i));
        }
        if arity == 1 {
            callback(&Grf::Succ);
        }
        return;
    }
    let n = size - 1;

    // C(h, g1..gm): stream h's; for each h, stream all argument tuples
    for hsize in 1..=n {
        let gs_total = n - hsize;
        for m in 1..=gs_total {
            for_each_grf(hsize, m, allow_min, opts, &mut |h: &Grf| {
                // skip_trivial: C(Z,...) and C(P,...) are always equivalent to
                // simpler expressions and can never be BBµ champions.
                if opts.skip_trivial && matches!(h, Grf::Zero(_) | Grf::Proj(_, _)) {
                    return;
                }

                // comp_assoc: C(C(f,g), k) = C(f, C(g,k)) — skip the
                // left-associated form; the right-associated form is generated
                // when the outer loop picks f as head.
                if opts.comp_assoc {
                    if let Grf::Comp(_, inner_gs, _) = h {
                        if inner_gs.len() == 1 {
                            return;
                        }
                    }
                }

                let h_box = Box::new(h.clone());
                let mut args = Vec::with_capacity(m);
                for_each_args(
                    gs_total,
                    m,
                    arity,
                    allow_min,
                    opts,
                    &mut args,
                    &mut |gs: &[Grf]| {
                        callback(&Grf::Comp(h_box.clone(), gs.to_vec(), arity));
                    },
                );
            });
        }
    }

    // R(g, h): stream g's; for each g, stream h's
    if arity >= 1 {
        for gsize in 1..n {
            let hsize = n - gsize;
            for_each_grf(gsize, arity - 1, allow_min, opts, &mut |g: &Grf| {
                let g_box = Box::new(g.clone());
                for_each_grf(hsize, arity + 1, allow_min, opts, &mut |h: &Grf| {
                    callback(&Grf::Rec(g_box.clone(), Box::new(h.clone())));
                });
            });
        }
    }

    // M(f): f ∈ GRF_{arity+1}, |f| = n
    if allow_min {
        for_each_grf(n, arity + 1, allow_min, opts, &mut |f: &Grf| {
            callback(&Grf::Min(Box::new(f.clone())));
        });
    }
}

/// Generate all ordered `remaining_count`-tuples of `arity`-GRFs whose sizes
/// sum to `remaining_size`, appending each element to `current` in turn.
fn for_each_args(
    remaining_size: usize,
    remaining_count: usize,
    arity: usize,
    allow_min: bool,
    opts: PruningOpts,
    current: &mut Vec<Grf>,
    callback: &mut dyn FnMut(&[Grf]),
) {
    if remaining_count == 0 {
        if remaining_size == 0 {
            callback(current);
        }
        return;
    }
    let max_first = remaining_size.saturating_sub(remaining_count - 1);
    for x in 1..=max_first {
        for_each_grf(x, arity, allow_min, opts, &mut |g: &Grf| {
            current.push(g.clone());
            for_each_args(
                remaining_size - x,
                remaining_count - 1,
                arity,
                allow_min,
                opts,
                current,
                callback,
            );
            current.pop();
        });
    }
}

// ---------------------------------------------------------------------------
// GRF counting (pure DP, no GRF trees materialised)
// ---------------------------------------------------------------------------

type CountKey = (usize, usize, bool, PruningOpts);

thread_local! {
    static COUNT_CACHE: RefCell<HashMap<CountKey, usize>> = RefCell::new(HashMap::new());
    // count_as_head(size, arity, allow_min, opts):
    //   count of GRFs valid as a Comp head under `opts`.
    //   = count_grf minus single-argument Comps (when comp_assoc) and minus
    //     Zero/Proj atoms (when skip_trivial).
    static AS_HEAD_CACHE: RefCell<HashMap<CountKey, usize>> = RefCell::new(HashMap::new());
}

/// Count GRFs of given `size` and `arity` without building any GRF tree.
/// Results are memoised in a thread-local DP table.
pub fn count_grf(size: usize, arity: usize, allow_min: bool, opts: PruningOpts) -> usize {
    let key = (size, arity, allow_min, opts);
    if let Some(c) = COUNT_CACHE.with(|cache| cache.borrow().get(&key).copied()) {
        return c;
    }
    let result = compute_count(size, arity, allow_min, opts);
    COUNT_CACHE.with(|cache| cache.borrow_mut().insert(key, result));
    result
}

/// Count of GRFs that are valid as a `Comp` head under `opts`.
///
/// Differs from `count_grf` in two ways:
/// - With `skip_trivial`: Zero and Proj atoms are excluded (they would make
///   `C(Z,…)` or `C(P,…)`, always equivalent to simpler expressions).
/// - With `comp_assoc`: single-argument Comps are excluded (we always prefer
///   the right-associated canonical form).
fn count_as_head(size: usize, arity: usize, allow_min: bool, opts: PruningOpts) -> usize {
    let key = (size, arity, allow_min, opts);
    if let Some(c) = AS_HEAD_CACHE.with(|cache| cache.borrow().get(&key).copied()) {
        return c;
    }
    let result = compute_as_head(size, arity, allow_min, opts);
    AS_HEAD_CACHE.with(|cache| cache.borrow_mut().insert(key, result));
    result
}

fn compute_as_head(size: usize, arity: usize, allow_min: bool, opts: PruningOpts) -> usize {
    // Size-1 atoms: with skip_trivial only Succ (arity==1) is a valid head;
    // without skip_trivial all atoms are valid heads.
    if size == 1 {
        return if opts.skip_trivial {
            usize::from(arity == 1)
        } else {
            // Zero(arity):1 + Proj:arity + Succ(if arity==1):1
            1 + arity + usize::from(arity == 1)
        };
    }

    // Start from the full count of all generated GRFs of this size/arity.
    let all = count_grf(size, arity, allow_min, opts);

    // With comp_assoc: subtract single-argument Comps — they are generated as
    // standalone GRFs but must not be used as Comp heads.
    //
    // A single-arg Comp of size `size` and arity `arity` has the form
    //   C(f, [g])  where  f.arity()=1, g.arity()=arity, f.size()+g.size()=size-1
    // and f must itself be a valid Comp head (not a single-arg Comp).
    if !opts.comp_assoc || size < 3 {
        return all;
    }

    let inner_total = size - 1; // f.size() + g.size()
    let mut single_arg_count = 0usize;
    for fsize in 1..inner_total {
        let gsize = inner_total - fsize;
        // f must be a valid comp head of arity 1
        let f_count = count_as_head(fsize, 1, allow_min, opts);
        // g can be any generated GRF of arity `arity`
        let g_count = count_grf(gsize, arity, allow_min, opts);
        single_arg_count = single_arg_count.saturating_add(f_count.saturating_mul(g_count));
    }
    all.saturating_sub(single_arg_count)
}

fn compute_count(size: usize, arity: usize, allow_min: bool, opts: PruningOpts) -> usize {
    if size == 0 {
        return 0;
    }
    if size == 1 {
        // Zero(arity): 1; Succ: 1 if arity==1; Proj(arity,i): arity choices
        return 1 + usize::from(arity == 1) + arity;
    }
    let n = size - 1;
    let mut total = 0usize;

    // C(h, g1..gm): h ∈ GRF_m (valid head), each gi ∈ GRF_arity
    for hsize in 1..=n {
        let gs_total = n - hsize;
        for m in 1..=gs_total {
            // count_as_head handles both skip_trivial and comp_assoc filters.
            let h_count = count_as_head(hsize, m, allow_min, opts);
            if h_count == 0 {
                continue;
            }
            total = total.saturating_add(
                h_count.saturating_mul(count_many_fast(gs_total, m, arity, allow_min, opts)),
            );
        }
    }

    // R(g, h): g ∈ GRF_{arity-1}, h ∈ GRF_{arity+1}
    if arity >= 1 {
        for gsize in 1..n {
            total = total.saturating_add(
                count_grf(gsize, arity - 1, allow_min, opts)
                    .saturating_mul(count_grf(n - gsize, arity + 1, allow_min, opts)),
            );
        }
    }

    // M(f): f ∈ GRF_{arity+1}
    if allow_min {
        total = total.saturating_add(count_grf(n, arity + 1, allow_min, opts));
    }

    total
}

fn count_many_fast(
    total_size: usize,
    num_funcs: usize,
    arity: usize,
    allow_min: bool,
    opts: PruningOpts,
) -> usize {
    if num_funcs > total_size {
        return 0;
    }
    if num_funcs == 0 {
        return usize::from(total_size == 0);
    }
    let max_first = total_size.saturating_sub(num_funcs - 1);
    let mut total = 0usize;
    for x in 1..=max_first {
        total = total.saturating_add(
            count_grf(x, arity, allow_min, opts).saturating_mul(count_many_fast(
                total_size - x,
                num_funcs - 1,
                arity,
                allow_min,
                opts,
            )),
        );
    }
    total
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    /// Collect all GRFs of given size/arity into a Vec via streaming.
    fn collect(size: usize, arity: usize, allow_min: bool, opts: PruningOpts) -> Vec<Grf> {
        let mut grfs = Vec::new();
        stream_grf(size, arity, allow_min, opts, &mut |g| grfs.push(g.clone()));

        // Assert every GRF in the streamed set has the correct size and arity.
        for grf in &grfs {
            assert_eq!(grf.size(), size, "size mismatch for {grf}");
            assert_eq!(grf.arity(), arity, "arity mismatch for {grf}");
            if !allow_min {
                assert!(grf.is_prf(), "non-PRF when allow_min=false: {grf}");
            }
        }

        grfs
    }

    const NO_PRUNE: PruningOpts = PruningOpts {
        skip_trivial: false,
        comp_assoc: false,
    };
    const SKIP_TRIVIAL: PruningOpts = PruningOpts {
        skip_trivial: true,
        comp_assoc: false,
    };
    const COMP_ASSOC: PruningOpts = PruningOpts {
        skip_trivial: false,
        comp_assoc: true,
    };
    const ALL_OPTS: PruningOpts = PruningOpts {
        skip_trivial: true,
        comp_assoc: true,
    };

    // --- atom counts (size=1) ---

    #[test]
    fn test_atoms_arity0() {
        assert_eq!(collect(1, 0, true, NO_PRUNE).len(), 1); // Z0 only
    }

    #[test]
    fn test_atoms_arity1() {
        assert_eq!(collect(1, 1, true, NO_PRUNE).len(), 3); // Z1, S, P(1,1)
    }

    #[test]
    fn test_atoms_arity2() {
        assert_eq!(collect(1, 2, true, NO_PRUNE).len(), 3); // Z2, P(2,1), P(2,2)
    }

    #[test]
    fn test_atoms_arity3() {
        assert_eq!(collect(1, 3, true, NO_PRUNE).len(), 4); // Z3, P(3,1..3)
    }

    // --- size-2 ---

    #[test]
    fn test_size2_arity0_with_min() {
        assert_eq!(collect(2, 0, true, NO_PRUNE).len(), 3); // M(Z1), M(S), M(P(1,1))
    }

    #[test]
    fn test_size2_arity0_prf() {
        assert_eq!(collect(2, 0, false, NO_PRUNE).len(), 0);
    }

    // --- size-3 ---

    #[test]
    fn test_size3_arity0_with_min() {
        assert_eq!(collect(3, 0, true, NO_PRUNE).len(), 6);
    }

    #[test]
    fn test_size3_arity0_prf() {
        let all = collect(3, 0, false, NO_PRUNE);
        assert_eq!(all.len(), 3);
        let champion = Grf::comp(Grf::Succ, vec![Grf::Zero(0)]);
        assert!(
            all.iter().any(|g| *g == champion),
            "C(S,Z0) should be in size-3 PRF_0"
        );
    }

    #[test]
    fn test_size3_arity1_with_min() {
        assert_eq!(collect(3, 1, true, NO_PRUNE).len(), 16);
    }

    // --- size-4 ---

    #[test]
    fn test_size4_arity0_with_min() {
        assert_eq!(collect(4, 0, true, NO_PRUNE).len(), 31);
    }

    // --- larger sizes ---

    #[test]
    fn test_verify_sizes_5_to_7() {
        for size in 5..=7 {
            for arity in 0..=3 {
                collect(size, arity, false, NO_PRUNE);
                collect(size, arity, true, NO_PRUNE);
            }
        }
    }

    // --- skip_trivial ---

    #[test]
    fn test_skip_trivial_removes_zero_proj_comps() {
        let full = collect(3, 0, false, NO_PRUNE);
        let trim = collect(3, 0, false, SKIP_TRIVIAL);
        assert_eq!(full.len(), 3);
        assert_eq!(trim.len(), 1);
        assert_eq!(trim[0], Grf::comp(Grf::Succ, vec![Grf::Zero(0)]));
    }

    #[test]
    fn test_skip_trivial_never_more_than_full() {
        for size in 1..=8 {
            for arity in 0..=2 {
                let full = count_grf(size, arity, false, NO_PRUNE);
                let trim = count_grf(size, arity, false, SKIP_TRIVIAL);
                assert!(
                    trim <= full,
                    "skip_trivial produced more GRFs at size={size} arity={arity}"
                );
            }
        }
    }

    // --- comp_assoc ---

    #[test]
    fn test_comp_assoc_removes_left_associated_comps() {
        // C(C(S, Z1), Z0) should be removed; C(S, C(Z1, Z0)) generated instead.
        let full = collect(5, 0, false, NO_PRUNE);
        let assoc = collect(5, 0, false, COMP_ASSOC);

        let left_assoc = "C(C(S, Z1), Z0)".parse::<Grf>().unwrap();
        let right_assoc = "C(S, C(Z1, Z0))".parse::<Grf>().unwrap();

        assert!(
            full.iter().any(|g| *g == left_assoc),
            "C(C(S,Z1),Z0) must exist in full set"
        );
        assert!(
            full.iter().any(|g| *g == right_assoc),
            "C(S,C(Z1,Z0)) must exist in full set"
        );
        assert!(
            !assoc.iter().any(|g| *g == left_assoc),
            "C(C(S,Z1),Z0) should be pruned with comp_assoc"
        );
        assert!(
            assoc.iter().any(|g| *g == right_assoc),
            "C(S,C(Z1,Z0)) should still be generated with comp_assoc"
        );
    }

    #[test]
    fn test_comp_assoc_never_more_than_full() {
        for size in 1..=8 {
            for arity in 0..=2 {
                let full = count_grf(size, arity, false, NO_PRUNE);
                let assoc = count_grf(size, arity, false, COMP_ASSOC);
                assert!(
                    assoc <= full,
                    "comp_assoc produced more GRFs at size={size} arity={arity}"
                );
            }
        }
    }

    #[test]
    fn test_comp_assoc_all_opts_fewer_than_skip_trivial() {
        for size in 1..=8 {
            for arity in 0..=2 {
                let st = count_grf(size, arity, false, SKIP_TRIVIAL);
                let all = count_grf(size, arity, false, ALL_OPTS);
                assert!(
                    all <= st,
                    "ALL_OPTS produced more GRFs than SKIP_TRIVIAL at size={size} arity={arity}"
                );
            }
        }
    }

    // --- no duplicates ---

    #[test]
    fn test_no_duplicates() {
        use std::collections::HashSet;
        for size in 1..=7 {
            let all = collect(size, 0, false, NO_PRUNE);
            let unique: HashSet<Grf> = all.iter().cloned().collect();
            assert_eq!(all.len(), unique.len(), "duplicates at size={size}");
        }
    }

    #[test]
    fn test_no_duplicates_comp_assoc() {
        use std::collections::HashSet;
        for size in 1..=7 {
            for arity in 0..=2 {
                let all = collect(size, arity, false, COMP_ASSOC);
                let unique: HashSet<Grf> = all.iter().cloned().collect();
                assert_eq!(
                    all.len(),
                    unique.len(),
                    "duplicates with comp_assoc at size={size} arity={arity}"
                );
            }
        }
    }

    // --- count_grf matches actual stream count ---

    #[test]
    fn test_count_matches_stream() {
        for size in 1..=7 {
            for arity in 0..=3 {
                for allow_min in [false, true] {
                    for opts in [NO_PRUNE, SKIP_TRIVIAL, COMP_ASSOC, ALL_OPTS] {
                        let actual = collect(size, arity, allow_min, opts).len();
                        let count = count_grf(size, arity, allow_min, opts);
                        assert_eq!(
                            actual, count,
                            "count_grf mismatch: size={size} arity={arity} \
                             allow_min={allow_min} opts={opts:?}: \
                             actual={actual} count={count}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    #[ignore = "informational count comparison, not a pass/fail test"]
    fn show_comp_assoc_count_reduction() {
        for n in [14, 15, 16, 17, 18, 19, 20] {
            let base = count_grf(n, 0, false, SKIP_TRIVIAL);
            let reduced = count_grf(n, 0, false, ALL_OPTS);
            println!(
                "n={n:2}: skip_trivial={base:>15}  +comp_assoc={reduced:>15}  ({:.1}%)",
                100.0 * reduced as f64 / base.max(1) as f64
            );
        }
    }
}
