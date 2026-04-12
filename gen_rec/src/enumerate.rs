use crate::grf::Grf;
use std::cell::RefCell;
use std::collections::HashMap;

// ---------------------------------------------------------------------------
// GRF streaming enumeration
// ---------------------------------------------------------------------------

/// Call `callback` once for each GRF of exactly `size` with exactly `arity` inputs.
///
/// - `allow_min`: include the Minimization combinator (GRF); exclude for PRF-only.
/// - `skip_trivial`: skip `C(Z_m, ...)` and `C(P^m_i, ...)`, which are always
///   equivalent to simpler expressions and never BBµ champions.
///
/// No `Vec<Grf>` is ever materialised — memory use is O(size) at any point.
pub fn stream_grf<F: FnMut(&Grf)>(
    size: usize,
    arity: usize,
    allow_min: bool,
    skip_trivial: bool,
    callback: &mut F,
) {
    for_each_grf(size, arity, allow_min, skip_trivial, callback);
}

/// Internal recursive generator.  Uses `&mut dyn FnMut` so nested closures can
/// each capture and call through the same `callback` reference without the
/// borrow checker rejecting two simultaneous `&mut F` borrows.
fn for_each_grf(
    size: usize,
    arity: usize,
    allow_min: bool,
    skip_trivial: bool,
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
            for_each_grf(hsize, m, allow_min, skip_trivial, &mut |h: &Grf| {
                if skip_trivial && matches!(h, Grf::Zero(_) | Grf::Proj(_, _)) {
                    return;
                }
                let h_box = Box::new(h.clone());
                let mut args = Vec::with_capacity(m);
                for_each_args(
                    gs_total,
                    m,
                    arity,
                    allow_min,
                    skip_trivial,
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
            for_each_grf(gsize, arity - 1, allow_min, skip_trivial, &mut |g: &Grf| {
                let g_box = Box::new(g.clone());
                for_each_grf(hsize, arity + 1, allow_min, skip_trivial, &mut |h: &Grf| {
                    callback(&Grf::Rec(g_box.clone(), Box::new(h.clone())));
                });
            });
        }
    }

    // M(f): f ∈ GRF_{arity+1}, |f| = n
    if allow_min {
        for_each_grf(n, arity + 1, allow_min, skip_trivial, &mut |f: &Grf| {
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
    skip_trivial: bool,
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
        for_each_grf(x, arity, allow_min, skip_trivial, &mut |g: &Grf| {
            current.push(g.clone());
            for_each_args(
                remaining_size - x,
                remaining_count - 1,
                arity,
                allow_min,
                skip_trivial,
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

type CountKey = (usize, usize, bool, bool);
thread_local! {
    static COUNT_CACHE: RefCell<HashMap<CountKey, usize>> = RefCell::new(HashMap::new());
}

/// Count GRFs of given `size` and `arity` without building any GRF tree.
/// Results are memoised in a thread-local DP table (stores only `usize`).
pub fn count_grf(size: usize, arity: usize, allow_min: bool, skip_trivial: bool) -> usize {
    let key = (size, arity, allow_min, skip_trivial);
    if let Some(c) = COUNT_CACHE.with(|cache| cache.borrow().get(&key).copied()) {
        return c;
    }
    let result = compute_count(size, arity, allow_min, skip_trivial);
    COUNT_CACHE.with(|cache| cache.borrow_mut().insert(key, result));
    result
}

fn compute_count(size: usize, arity: usize, allow_min: bool, skip_trivial: bool) -> usize {
    if size == 0 {
        return 0;
    }
    if size == 1 {
        // Zero(arity): 1; Succ: 1 if arity==1; Proj(arity,i): arity choices
        return 1 + usize::from(arity == 1) + arity;
    }
    let n = size - 1;
    let mut total = 0usize;

    // C(h, g1..gm): h ∈ GRF_m, each gi ∈ GRF_arity
    for hsize in 1..=n {
        let gs_total = n - hsize;
        for m in 1..=gs_total {
            let h_count = if skip_trivial && hsize == 1 {
                // Only Succ is non-trivial at arity 1; Zero and Proj are always skipped
                usize::from(m == 1)
            } else {
                count_grf(hsize, m, allow_min, skip_trivial)
            };
            if h_count == 0 {
                continue;
            }
            total += h_count.saturating_mul(count_many_fast(
                gs_total,
                m,
                arity,
                allow_min,
                skip_trivial,
            ));
        }
    }

    // R(g, h): g ∈ GRF_{arity-1}, h ∈ GRF_{arity+1}
    if arity >= 1 {
        for gsize in 1..n {
            total += count_grf(gsize, arity - 1, allow_min, skip_trivial)
                .saturating_mul(count_grf(n - gsize, arity + 1, allow_min, skip_trivial));
        }
    }

    // M(f): f ∈ GRF_{arity+1}
    if allow_min {
        total += count_grf(n, arity + 1, allow_min, skip_trivial);
    }

    total
}

fn count_many_fast(
    total_size: usize,
    num_funcs: usize,
    arity: usize,
    allow_min: bool,
    skip_trivial: bool,
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
        total += count_grf(x, arity, allow_min, skip_trivial).saturating_mul(count_many_fast(
            total_size - x,
            num_funcs - 1,
            arity,
            allow_min,
            skip_trivial,
        ));
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
    fn collect(size: usize, arity: usize, allow_min: bool, skip_trivial: bool) -> Vec<Grf> {
        let mut grfs = Vec::new();
        stream_grf(size, arity, allow_min, skip_trivial, &mut |g| {
            grfs.push(g.clone())
        });

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

    // --- atom counts (size=1) ---

    #[test]
    fn test_atoms_arity0() {
        assert_eq!(collect(1, 0, true, false).len(), 1); // Z0 only
    }

    #[test]
    fn test_atoms_arity1() {
        assert_eq!(collect(1, 1, true, false).len(), 3); // Z1, S, P(1,1)
    }

    #[test]
    fn test_atoms_arity2() {
        assert_eq!(collect(1, 2, true, false).len(), 3); // Z2, P(2,1), P(2,2)
    }

    #[test]
    fn test_atoms_arity3() {
        assert_eq!(collect(1, 3, true, false).len(), 4); // Z3, P(3,1..3)
    }

    // --- size-2 ---

    #[test]
    fn test_size2_arity0_with_min() {
        assert_eq!(collect(2, 0, true, false).len(), 3); // M(Z1), M(S), M(P(1,1))
    }

    #[test]
    fn test_size2_arity0_prf() {
        assert_eq!(collect(2, 0, false, false).len(), 0);
    }

    // --- size-3 ---

    #[test]
    fn test_size3_arity0_with_min() {
        assert_eq!(collect(3, 0, true, false).len(), 6);
    }

    #[test]
    fn test_size3_arity0_prf() {
        let all = collect(3, 0, false, false);
        assert_eq!(all.len(), 3);
        let champion = Grf::comp(Grf::Succ, vec![Grf::Zero(0)]);
        assert!(
            all.iter().any(|g| *g == champion),
            "C(S,Z0) should be in size-3 PRF_0"
        );
    }

    #[test]
    fn test_size3_arity1_with_min() {
        assert_eq!(collect(3, 1, true, false).len(), 16);
    }

    // --- size-4 ---

    #[test]
    fn test_size4_arity0_with_min() {
        assert_eq!(collect(4, 0, true, false).len(), 31);
    }

    // --- larger sizes ---

    #[test]
    fn test_verify_sizes_5_to_7() {
        for size in 5..=7 {
            for arity in 0..=3 {
                collect(size, arity, false, false);
                collect(size, arity, true, false);
            }
        }
    }

    // --- skip_trivial ---

    #[test]
    fn test_skip_trivial_removes_zero_proj_comps() {
        let full = collect(3, 0, false, false);
        let trim = collect(3, 0, false, true);
        assert_eq!(full.len(), 3);
        assert_eq!(trim.len(), 1);
        assert_eq!(trim[0], Grf::comp(Grf::Succ, vec![Grf::Zero(0)]));
    }

    #[test]
    fn test_skip_trivial_never_more_than_full() {
        for size in 1..=8 {
            for arity in 0..=2 {
                let full = count_grf(size, arity, false, false);
                let trim = count_grf(size, arity, false, true);
                assert!(
                    trim <= full,
                    "skip_trivial produced more GRFs at size={size} arity={arity}"
                );
            }
        }
    }

    // --- no duplicates ---

    #[test]
    fn test_no_duplicates() {
        use std::collections::HashSet;
        for size in 1..=7 {
            let all = collect(size, 0, false, false);
            let unique: HashSet<Grf> = all.iter().cloned().collect();
            assert_eq!(all.len(), unique.len(), "duplicates at size={size}");
        }
    }

    // --- count_grf matches actual stream count ---

    #[test]
    fn test_count_matches_stream() {
        for size in 1..=7 {
            for arity in 0..=3 {
                for allow_min in [false, true] {
                    for skip_trivial in [false, true] {
                        let actual = collect(size, arity, allow_min, skip_trivial).len();
                        let count = count_grf(size, arity, allow_min, skip_trivial);
                        assert_eq!(
                            actual, count,
                            "count_grf mismatch: size={size} arity={arity} \
                             allow_min={allow_min} skip_trivial={skip_trivial}: \
                             actual={actual} count={count}"
                        );
                    }
                }
            }
        }
    }
}
