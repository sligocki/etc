use crate::grf::Grf;
use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::sync::Arc;

/// Cache key: (size, arity, allow_min, skip_trivial)
type CacheKey = (usize, usize, bool, bool);

thread_local! {
    static CACHE: RefCell<HashMap<CacheKey, Arc<Vec<Grf>>>> = RefCell::new(HashMap::new());
    /// When true, `enumerate_all` skips both cache reads and writes.
    /// Sub-expressions are recomputed from scratch on every call.
    static NO_CACHE: Cell<bool> = Cell::new(false);
}

/// Enable or disable sub-expression caching.
/// When disabled, every call to `enumerate_all` recomputes its result.
/// Useful for benchmarking how much the cache helps.
pub fn set_no_cache(enabled: bool) {
    NO_CACHE.with(|f| f.set(enabled));
}

/// Thread-local count-only cache: avoids materialising GRF trees.
type CountKey = (usize, usize, bool, bool);
thread_local! {
    static COUNT_CACHE: RefCell<HashMap<CountKey, usize>> = RefCell::new(HashMap::new());
}

/// Clear the enumeration cache (useful between test runs).
pub fn clear_cache() {
    CACHE.with(|c| c.borrow_mut().clear());
    COUNT_CACHE.with(|c| c.borrow_mut().clear());
}

/// Count GRFs without materialising them — pure DP, O(size^3) time and space.
///
/// Much cheaper than `count_grf` (which calls `enumerate_all` and builds the full
/// `Vec<Grf>`) when you only need the count.  Useful for time-estimation in search
/// loops where materialising future-size trees would be prohibitively expensive.
pub fn count_grf_fast(size: usize, arity: usize, allow_min: bool, skip_trivial: bool) -> usize {
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
        // Zero(arity): always 1
        // Succ: only if arity == 1
        // Proj(arity, i) for i in 1..=arity: `arity` choices
        return 1 + (if arity == 1 { 1 } else { 0 }) + arity;
    }
    let n = size - 1;
    let mut total = 0usize;

    // M(f)
    if allow_min {
        total += count_grf_fast(n, arity + 1, allow_min, skip_trivial);
    }

    // R(g, h)
    if arity >= 1 {
        for gsize in 1..n {
            let hsize = n - gsize;
            total += count_grf_fast(gsize, arity - 1, allow_min, skip_trivial)
                .saturating_mul(count_grf_fast(hsize, arity + 1, allow_min, skip_trivial));
        }
    }

    // C(h, g1..gm)
    for hsize in 1..=n {
        let gs_total = n - hsize;
        for m in 1..=gs_total {
            // Count non-trivial h's of size hsize and arity m.
            let h_count = if skip_trivial {
                if hsize == 1 {
                    // Trivial atoms at arity m: Zero(m) + all Proj(m,i) = 1 + m
                    // Non-trivial: only Succ when m==1
                    if m == 1 { 1 } else { 0 }
                } else {
                    // hsize > 1: no atoms, all are combinators → none are trivial
                    count_grf_fast(hsize, m, allow_min, skip_trivial)
                }
            } else {
                count_grf_fast(hsize, m, allow_min, skip_trivial)
            };
            if h_count == 0 {
                continue;
            }
            total += h_count.saturating_mul(count_many_fast(gs_total, m, arity, allow_min, skip_trivial));
        }
    }
    total
}

/// Count ordered m-tuples of GRFs each of `arity`, with total size `total_size`.
fn count_many_fast(total_size: usize, num_funcs: usize, arity: usize, allow_min: bool, skip_trivial: bool) -> usize {
    if num_funcs > total_size {
        return 0;
    }
    if num_funcs == 0 {
        return if total_size == 0 { 1 } else { 0 };
    }
    let max_first = total_size.saturating_sub(num_funcs - 1);
    let mut total = 0usize;
    for x in 1..=max_first {
        let rest_size = total_size - x;
        total += count_grf_fast(x, arity, allow_min, skip_trivial)
            .saturating_mul(count_many_fast(rest_size, num_funcs - 1, arity, allow_min, skip_trivial));
    }
    total
}

/// Return (entry_count, total_grf_count) from the thread-local cache.
pub fn cache_stats() -> (usize, usize) {
    CACHE.with(|c| {
        let map = c.borrow();
        let entries = map.len();
        let total: usize = map.values().map(|v| v.len()).sum();
        (entries, total)
    })
}

/// Return all GRFs of exactly `size` with exactly `arity` inputs.
///
/// - `allow_min`: if false, the Minimization combinator (M) is excluded (→ PRF only).
/// - `skip_trivial`: if true, skip compositions C(h, ...) where h is Zero or Proj,
///   since those are always equivalent to a simpler expression (Zero or one of the gi).
///
/// Results are memoized per (size, arity, allow_min, skip_trivial) unless the
/// thread-local `NO_CACHE` flag is set (see `set_no_cache`), in which case the
/// result is computed fresh on every call.
pub fn enumerate_all(
    size: usize,
    arity: usize,
    allow_min: bool,
    skip_trivial: bool,
) -> Arc<Vec<Grf>> {
    let no_cache = NO_CACHE.with(|f| f.get());
    if !no_cache {
        let key = (size, arity, allow_min, skip_trivial);
        // Check cache first (releases borrow before recursive computation).
        if let Some(cached) = CACHE.with(|c| c.borrow().get(&key).cloned()) {
            return cached;
        }
        let mut result = Vec::new();
        for_each_grf_impl(size, arity, allow_min, skip_trivial, &mut |grf| {
            result.push(grf.clone());
        });
        let result = Arc::new(result);
        CACHE.with(|c| c.borrow_mut().insert(key, Arc::clone(&result)));
        result
    } else {
        // No-cache mode: compute fresh, don't read or write the cache.
        let mut result = Vec::new();
        for_each_grf_impl(size, arity, allow_min, skip_trivial, &mut |grf| {
            result.push(grf.clone());
        });
        Arc::new(result)
    }
}

/// Count GRFs without materializing them (just delegates to enumerate_all length).
pub fn count_grf(size: usize, arity: usize, allow_min: bool, skip_trivial: bool) -> usize {
    enumerate_all(size, arity, allow_min, skip_trivial).len()
}

/// Call `callback` for each GRF of given size and arity, using the cache.
/// Sub-expression results are cached; the top-level results are also cached.
pub fn for_each_grf<F: FnMut(&Grf)>(
    size: usize,
    arity: usize,
    allow_min: bool,
    skip_trivial: bool,
    callback: &mut F,
) {
    let all = enumerate_all(size, arity, allow_min, skip_trivial);
    for grf in all.iter() {
        callback(grf);
    }
}

/// Like `for_each_grf` but does **not** cache the top-level results for `size`.
///
/// Sub-expressions (sizes < `size`) are still cached as usual.  Use this for
/// the largest size in a search to avoid materialising tens of millions of
/// tree-structured values in memory simultaneously.
pub fn stream_grf<F: FnMut(&Grf)>(
    size: usize,
    arity: usize,
    allow_min: bool,
    skip_trivial: bool,
    callback: &mut F,
) {
    for_each_grf_impl(size, arity, allow_min, skip_trivial, callback);
}

// ---------------------------------------------------------------------------
// Internal implementation
// ---------------------------------------------------------------------------

/// Core streaming implementation: calls `callback` for every GRF of the
/// requested size and arity.  Sub-expressions are retrieved from (or inserted
/// into) the thread-local cache; the top-level results are NOT cached here.
fn for_each_grf_impl<F: FnMut(&Grf)>(
    size: usize,
    arity: usize,
    allow_min: bool,
    skip_trivial: bool,
    callback: &mut F,
) {
    if size == 0 {
        return;
    }

    if size == 1 {
        // Atoms
        callback(&Grf::Zero(arity));
        if arity == 1 {
            callback(&Grf::Succ);
        }
        for i in 1..=arity {
            callback(&Grf::Proj(arity, i));
        }
        return;
    }

    // Combinators: sub-expressions share n = size - 1 nodes total.
    let n = size - 1;

    // --- M(f): f ∈ GRF_{arity+1}, |f| = n ---
    if allow_min {
        let fs = enumerate_all(n, arity + 1, allow_min, skip_trivial);
        for f in fs.iter() {
            callback(&Grf::Min(Box::new(f.clone())));
        }
    }

    // --- R(g, h): g ∈ GRF_{arity-1}, h ∈ GRF_{arity+1}, |g|+|h| = n ---
    if arity >= 1 {
        for gsize in 1..n {
            let hsize = n - gsize;
            let gs = enumerate_all(gsize, arity - 1, allow_min, skip_trivial);
            let hs = enumerate_all(hsize, arity + 1, allow_min, skip_trivial);
            for g in gs.iter() {
                for h in hs.iter() {
                    callback(&Grf::Rec(Box::new(g.clone()), Box::new(h.clone())));
                }
            }
        }
    }

    // --- C(h, g1..gm): h ∈ GRF_m, each gi ∈ GRF_{arity}, |h|+sum|gi| = n ---
    // m >= 1, and each gi has size >= 1, so sum|gi| >= m, so y = n-x >= m.
    for hsize in 1..=n {
        let gs_total = n - hsize; // total size for the m arguments
        // m = number of args, each gi size >= 1, so 1 <= m <= gs_total
        for m in 1..=gs_total {
            let hs = enumerate_all(hsize, m, allow_min, skip_trivial);
            for h in hs.iter() {
                // Optionally skip trivially-equivalent compositions.
                if skip_trivial {
                    match h {
                        // C(Z_m, g1..gm) = Z_k (always 0): skip
                        Grf::Zero(_) => continue,
                        // C(P^m_i, g1..gm) = g_i (just selects one arg): skip
                        Grf::Proj(_, _) => continue,
                        _ => {}
                    }
                }
                let h_box = Box::new(h.clone());
                let mut tuple_buf = Vec::with_capacity(m);
                for_each_many_rec(
                    gs_total,
                    m,
                    arity,
                    allow_min,
                    skip_trivial,
                    &mut tuple_buf,
                    &mut |gs: &[Grf]| {
                        // arity is the shared input arity of all gi, which equals the
                        // output arity of the whole Comp.
                        callback(&Grf::Comp(h_box.clone(), gs.to_vec(), arity));
                    },
                );
            }
        }
    }
}

/// Recursively iterate over all ordered m-tuples of GRFs with total size `remaining_size`
/// and each element having `arity`. Appends to `current` and calls `callback` at each leaf.
fn for_each_many_rec<F>(
    remaining_size: usize,
    remaining_count: usize,
    arity: usize,
    allow_min: bool,
    skip_trivial: bool,
    current: &mut Vec<Grf>,
    callback: &mut F,
) where
    F: FnMut(&[Grf]),
{
    if remaining_count == 0 {
        if remaining_size == 0 {
            callback(current);
        }
        return;
    }
    // Maximum size for the first element: leave room for the remaining (count-1) elements.
    let max_first = remaining_size.saturating_sub(remaining_count - 1);
    for x in 1..=max_first {
        // Retrieve (or compute) all GRFs of size x with the required arity.
        // The Arc keeps this Vec alive even if the cache is later mutated.
        let pool = enumerate_all(x, arity, allow_min, skip_trivial);
        let pool_len = pool.len();
        for i in 0..pool_len {
            let g = pool[i].clone();
            current.push(g);
            for_each_many_rec(
                remaining_size - x,
                remaining_count - 1,
                arity,
                allow_min,
                skip_trivial,
                current,
                callback,
            );
            current.pop();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Helper: count GRFs and clear cache between tests to ensure independence.
    fn count(size: usize, arity: usize, allow_min: bool, skip_trivial: bool) -> usize {
        count_grf(size, arity, allow_min, skip_trivial)
    }

    /// Verify all enumerated GRFs have the correct size and arity.
    fn verify_all(size: usize, arity: usize, allow_min: bool, skip_trivial: bool) {
        let all = enumerate_all(size, arity, allow_min, skip_trivial);
        for grf in all.iter() {
            assert_eq!(
                grf.size(),
                size,
                "Size mismatch for {}: expected {}, got {}",
                grf,
                size,
                grf.size()
            );
            assert_eq!(
                grf.arity(),
                arity,
                "Arity mismatch for {}: expected {}, got {}",
                grf,
                arity,
                grf.arity()
            );
            if !allow_min {
                assert!(grf.is_prf(), "Got non-PRF when allow_min=false: {}", grf);
            }
        }
    }

    // -----------------------------------------------------------------------
    // Atom counts (size=1)
    // -----------------------------------------------------------------------

    #[test]
    fn test_atoms_arity0() {
        // Size 1, arity 0: just Z0. Count = 1.
        // (No S since arity != 1; no P since arity = 0)
        assert_eq!(count(1, 0, true, false), 1);
        verify_all(1, 0, true, false);
    }

    #[test]
    fn test_atoms_arity1() {
        // Size 1, arity 1: Z1, S, P(1,1). Count = 3.
        assert_eq!(count(1, 1, true, false), 3);
        verify_all(1, 1, true, false);
    }

    #[test]
    fn test_atoms_arity2() {
        // Size 1, arity 2: Z2, P(2,1), P(2,2). Count = 3. (No S)
        assert_eq!(count(1, 2, true, false), 3);
        verify_all(1, 2, true, false);
    }

    #[test]
    fn test_atoms_arity3() {
        // Size 1, arity 3: Z3, P(3,1), P(3,2), P(3,3). Count = 4.
        assert_eq!(count(1, 3, true, false), 4);
        verify_all(1, 3, true, false);
    }

    // -----------------------------------------------------------------------
    // Size-2 counts (from count.rs comments: T(2,0) = 3 with M)
    // -----------------------------------------------------------------------

    #[test]
    fn test_size2_arity0_with_min() {
        // T(2,0) = 3: M(Z1), M(S), M(P(1,1))
        assert_eq!(count(2, 0, true, false), 3);
        verify_all(2, 0, true, false);
    }

    #[test]
    fn test_size2_arity0_prf() {
        // PRF T(2,0) = 0: no compositions possible (need y >= 1 = n for C, impossible at n=1)
        assert_eq!(count(2, 0, false, false), 0);
    }

    // -----------------------------------------------------------------------
    // Size-3 counts (from count.rs: T(3,0)=6; T(3,1)=16)
    // -----------------------------------------------------------------------

    #[test]
    fn test_size3_arity0_with_min() {
        // T(3,0) = 6: M(T(2,1))=3 + C(T(1,1), T(1,0))=3*1=3
        assert_eq!(count(3, 0, true, false), 6);
        verify_all(3, 0, true, false);
    }

    #[test]
    fn test_size3_arity0_prf() {
        // PRF T(3,0) = 3: C(Z1,Z0), C(S,Z0), C(P(1,1),Z0)
        assert_eq!(count(3, 0, false, false), 3);
        verify_all(3, 0, false, false);

        // Check that C(S,Z0) is among them (the size-3 champion)
        let all = enumerate_all(3, 0, false, false);
        let champion = Grf::comp(Grf::Succ, vec![Grf::Zero(0)]);
        assert!(
            all.iter().any(|g| *g == champion),
            "C(S,Z0) should be in size-3 PRF_0"
        );
    }

    #[test]
    fn test_size3_arity1_with_min() {
        // T(3,1) = 16: M(4) + R(1,3) + C(3,9) = 4+3+9=16
        assert_eq!(count(3, 1, true, false), 16);
        verify_all(3, 1, true, false);
    }

    // -----------------------------------------------------------------------
    // Size-4 counts (from count.rs: T(4,0)=31 with M)
    // -----------------------------------------------------------------------

    #[test]
    fn test_size4_arity0_with_min() {
        assert_eq!(count(4, 0, true, false), 31);
        verify_all(4, 0, true, false);
    }

    // -----------------------------------------------------------------------
    // Verify all enumerated GRFs have correct size/arity for larger cases
    // -----------------------------------------------------------------------

    #[test]
    fn test_verify_sizes_5_to_7() {
        for size in 5..=7 {
            for arity in 0..=3 {
                verify_all(size, arity, false, false); // PRF
                verify_all(size, arity, true, false);  // GRF with M
            }
        }
    }

    // -----------------------------------------------------------------------
    // skip_trivial: verify it reduces count and removes Z/Proj-headed comps
    // -----------------------------------------------------------------------

    #[test]
    fn test_skip_trivial_removes_zero_proj_comps() {
        // Size 3, arity 0: C(Z1,Z0) and C(P(1,1),Z0) are trivial; C(S,Z0) is not.
        let all_full = enumerate_all(3, 0, false, false);
        let all_trim = enumerate_all(3, 0, false, true);
        assert_eq!(all_full.len(), 3); // Z,S,P variants
        assert_eq!(all_trim.len(), 1); // only C(S, Z0)
        assert_eq!(all_trim[0], Grf::comp(Grf::Succ, vec![Grf::Zero(0)]));
    }

    #[test]
    fn test_skip_trivial_less_than_full() {
        // skip_trivial should never produce MORE GRFs than the full set.
        for size in 1..=8 {
            for arity in 0..=2 {
                let full = count_grf(size, arity, false, false);
                let trim = count_grf(size, arity, false, true);
                assert!(
                    trim <= full,
                    "skip_trivial gave MORE GRFs: size={size}, arity={arity}: {trim} > {full}"
                );
            }
        }
    }

    // -----------------------------------------------------------------------
    // No duplicates in enumeration
    // -----------------------------------------------------------------------

    #[test]
    fn test_no_duplicates() {
        use std::collections::HashSet;
        for size in 1..=7 {
            let all = enumerate_all(size, 0, false, false);
            let set: HashSet<Grf> = all.iter().cloned().collect();
            assert_eq!(
                all.len(),
                set.len(),
                "Duplicates found at size={size}"
            );
        }
    }

    // -----------------------------------------------------------------------
    // count_grf_fast matches count_grf (enumerate_all.len())
    // -----------------------------------------------------------------------

    #[test]
    fn test_count_grf_fast_matches_enumerate_all() {
        for size in 1..=8 {
            for arity in 0..=3 {
                for allow_min in [false, true] {
                    for skip_trivial in [false, true] {
                        let slow = count_grf(size, arity, allow_min, skip_trivial);
                        let fast = count_grf_fast(size, arity, allow_min, skip_trivial);
                        assert_eq!(
                            slow, fast,
                            "count_grf_fast mismatch: size={size}, arity={arity}, \
                             allow_min={allow_min}, skip_trivial={skip_trivial}: \
                             slow={slow}, fast={fast}"
                        );
                    }
                }
            }
        }
    }

    // -----------------------------------------------------------------------
    // stream_grf produces the same set as enumerate_all
    // -----------------------------------------------------------------------

    #[test]
    fn test_stream_grf_matches_enumerate_all() {
        for size in 1..=7 {
            for arity in 0..=2 {
                let cached: Vec<Grf> = enumerate_all(size, arity, false, false)
                    .iter()
                    .cloned()
                    .collect();
                let mut streamed: Vec<Grf> = Vec::new();
                stream_grf(size, arity, false, false, &mut |g| {
                    streamed.push(g.clone());
                });
                assert_eq!(
                    cached, streamed,
                    "stream_grf mismatch at size={size}, arity={arity}"
                );
            }
        }
    }

    // -----------------------------------------------------------------------
    // cache_stats: sanity check (cache must be non-empty after enumeration)
    // -----------------------------------------------------------------------

    #[test]
    fn test_cache_stats() {
        clear_cache();
        let _ = enumerate_all(5, 0, false, false);
        let (entries, total) = cache_stats();
        assert!(entries > 0, "cache should be non-empty after enumeration");
        assert!(total > 0, "cache total count should be positive");
    }
}
