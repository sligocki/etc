/// ClosedForm-based novel-sub-expression enumerator.
///
/// Enumerates GRF, removing duplication for equal ClosedForm results.
use crate::closed_form::ClosedForm;
use crate::enumerate::for_each_grf_core;
use crate::grf::Grf;
use crate::optimize::inline_proj;
use crate::pruning::PruningOpts;
use std::collections::HashMap;

#[derive(Clone, Copy, PartialEq)]
pub enum EnumMode {
    // Only enumerate GRF that have ClosedForm.
    ClosedFormOnly,
    // Also enumerate all GRF with all children in ClosedForm (but they might not be).
    // Useful for seeing edge case for when ClosedForm first fails.
    ClosedFormChildren,
    // Enumerate all GRF. Those in ClosedForm will be de-duplicated, but others will not.
    AllGrf,
}

pub struct ClosedFormEnumerator {
    /// (arity, size) → list of novel GRFs of exactly that (arity, size)
    memo: HashMap<(usize, usize), Vec<Grf>>,
    /// arity → ClosedForm → smallest Grf seen with that form
    seen_closed: HashMap<usize, HashMap<ClosedForm, Grf>>,
    pub mode: EnumMode,
    pub allow_min: bool,
    /// Structural pruning options applied when generating candidates.
    pub opts: PruningOpts,
    /// Only cache (and CF-deduplicate) domains where `arity + size <= cf_limit`.
    /// Larger domains are streamed on demand without caching, bounding memory use.
    /// Default: `usize::MAX` (no limit, original behavior).
    pub cf_limit: usize,
    /// If true, only strictly RNF GRFs are memoized, and non-RNF variants are regenerated dynamically.
    pub dynamic_rnf: bool,
}

impl ClosedFormEnumerator {
    pub fn new(mode: EnumMode, allow_min: bool, opts: PruningOpts) -> Self {
        // TODO: Not yet supported.
        assert!(mode != EnumMode::ClosedFormChildren);
        let cf_limit = if allow_min { 15 } else { 17 };
        ClosedFormEnumerator {
            memo: HashMap::new(),
            seen_closed: HashMap::new(),
            mode,
            allow_min,
            opts,
            cf_limit,
            dynamic_rnf: false,
        }
    }

    /// Convenience constructor with all recommended pruning flags enabled,
    /// including stream-only flags (`comp_rnf`, `inline_proj`, `min_dom`,
    /// `rec_step_p2`).  Use this for BBµ search and algebraic exploration.
    pub fn with_pruning(mode: EnumMode, allow_min: bool) -> Self {
        let opts = PruningOpts::recommended();
        Self::new(mode, allow_min, opts)
    }

    /// Enable dynamic RNF regeneration for reduced memory usage.
    pub fn with_dynamic_rnf(mut self, enabled: bool) -> Self {
        self.dynamic_rnf = enabled;
        self
    }

    /// Set the arity+size threshold above which domains are streamed instead of cached.
    pub fn with_cf_limit(mut self, limit: usize) -> Self {
        self.cf_limit = limit;
        self
    }

    /// Stream GRFs one at a time via callback
    pub fn stream_grfs<F: FnMut(&Grf)>(&mut self, arity: usize, size: usize, callback: &mut F) {
        self.ensure_dependencies(arity, size);
        self.stream_grf_internal(arity, size, callback);
    }

    pub fn count_grfs(&mut self, arity: usize, size: usize) -> usize {
        let mut count = 0usize;
        self.stream_grfs(arity, size, &mut |_| count += 1);
        count
    }

    /// Get full Vec of all GRFs of a domain
    pub fn all_grfs(&mut self, arity: usize, size: usize) -> Vec<Grf> {
        let mut out = Vec::new();
        self.stream_grfs(arity, size, &mut |grf| out.push(grf.clone()));
        out
    }

    /// Return the canonical (first-seen, smallest) Grf for a given ClosedForm and arity.
    pub fn canonical_grf_for(&self, arity: usize, cf: &ClosedForm) -> Option<&Grf> {
        self.seen_closed.get(&arity)?.get(cf)
    }

    pub fn is_in_memo(&self, grf: &Grf) -> bool {
        if let Some(gs) = self.memo.get(&(grf.arity(), grf.size())) {
            gs.iter().any(|g| g == grf)
        } else {
            false
        }
    }

    /// Populate `memo[(arity, size)]` with novel GRFs, recursing into dependencies.
    /// If `arity + size > cf_limit` this is a no-op: the domain is intentionally
    /// left uncached and will be streamed on demand by `all_grfs`.
    pub fn fill_cache(&mut self, arity: usize, size: usize) {
        if self.memo.contains_key(&(arity, size)) {
            return;
        }
        if arity + size > self.cf_limit {
            return;
        }

        self.ensure_dependencies(arity, size);

        let mut novel: Vec<Grf> = Vec::new();
        for grf in self.all_grfs(arity, size) {
            if self.dynamic_rnf && !grf.is_rnf() {
                continue;
            }
            match (grf.closed_form(), self.mode) {
                (Some(cf), _) => {
                    let seen = self.seen_closed.entry(arity).or_default();
                    if !seen.contains_key(&cf) {
                        seen.insert(cf.clone(), grf.clone());
                        novel.push(grf);
                    }
                }
                (None, EnumMode::AllGrf) => {
                    novel.push(grf);
                }
                _ => {}
            }
        }

        self.memo.insert((arity, size), novel);
    }

    /// Return the cached canonical input set for `(arity, size)`, or empty slice.
    fn candidates(&self, arity: usize, size: usize) -> &[Grf] {
        self.memo
            .get(&(arity, size))
            .map(|v| v.as_slice())
            .unwrap_or(&[])
    }

    /// Stream all GRFs of exactly (arity, size) using canonical sub-expressions,
    /// calling `callback` for each without collecting into a Vec.  For BBµ search:
    /// the champion at size n may compute a value already seen at a smaller size,
    /// so it won't appear in `candidates`, but is still a valid size-n GRF.
    ///
    /// Call `prepare(arity, size)` first to ensure in-limit dependency domains are
    /// in the memo.  Above-limit domains are streamed on demand.
    fn stream_grf_internal<F: FnMut(&Grf)>(&self, arity: usize, size: usize, callback: &mut F) {
        let memo = &self.memo;
        let allow_min = self.allow_min;
        let opts = self.opts;
        let dynamic_rnf = self.dynamic_rnf;
        let mut visitor = crate::enumerate::DummyVisitor;
        for_each_grf_core(
            size,
            arity,
            allow_min,
            opts,
            &|s, a, v, cb| {
                if dynamic_rnf && a + s <= self.cf_limit {
                    // Direct rewirings (s_inner == s)
                    for k in 0..=a {
                        if let Some(grfs) = memo.get(&(k, s)) {
                            for rnf_grf in grfs {
                                Self::generate_valid_rewirings(rnf_grf, a, false, v, cb);
                            }
                        }
                    }

                    // Wrapped rewirings (s_inner < s)
                    for s_inner in 1..s {
                        for k in 0..=s_inner {
                            // k is the arity of the inner function
                            if s_inner + 1 + k == s {
                                if let Some(grfs) = memo.get(&(k, s_inner)) {
                                    for rnf_grf in grfs {
                                        Self::generate_valid_rewirings(rnf_grf, a, true, v, cb);
                                    }
                                }
                            }
                        }
                    }
                } else {
                    if let Some(grfs) = memo.get(&(a, s)) {
                        for grf in grfs {
                            cb(v, grf);
                        }
                    } else {
                        crate::enumerate::for_each_grf_pub(s, a, allow_min, opts, v, cb);
                    }
                }
            },
            &mut visitor,
            &mut |_, grf| callback(grf),
        );
    }

    fn generate_valid_rewirings<F: FnMut(&mut dyn crate::enumerate::EnumVisitor, &Grf) + ?Sized>(
        rnf_grf: &Grf,
        target_arity: usize,
        wrapped_only: bool,
        v: &mut dyn crate::enumerate::EnumVisitor,
        cb: &mut F,
    ) {
        let k = rnf_grf.arity();
        if k > target_arity {
            return;
        }
        let mut rewiring = vec![0; k];
        let mut used = vec![false; target_arity + 1];

        fn backtrack<F: FnMut(&mut dyn crate::enumerate::EnumVisitor, &Grf) + ?Sized>(
            rnf_grf: &Grf,
            target_arity: usize,
            rewiring: &mut [usize],
            used: &mut [bool],
            idx: usize,
            wrapped_only: bool,
            v: &mut dyn crate::enumerate::EnumVisitor,
            cb: &mut F,
        ) {
            if idx == rewiring.len() {
                if wrapped_only {
                    if inline_proj(rnf_grf, target_arity, rewiring).is_none() {
                        let projs = rewiring
                            .iter()
                            .map(|&i| Grf::proj_atom(target_arity, i))
                            .collect();
                        cb(v, &Grf::comp(rnf_grf.clone(), projs));
                    }
                } else {
                    if let Some(g) = inline_proj(rnf_grf, target_arity, rewiring) {
                        cb(v, &g);
                    }
                }
                return;
            }
            for i in 1..=target_arity {
                if !used[i] {
                    used[i] = true;
                    rewiring[idx] = i;
                    backtrack(
                        rnf_grf,
                        target_arity,
                        rewiring,
                        used,
                        idx + 1,
                        wrapped_only,
                        v,
                        cb,
                    );
                    used[i] = false;
                }
            }
        }

        backtrack(
            rnf_grf,
            target_arity,
            &mut rewiring,
            &mut used,
            0,
            wrapped_only,
            v,
            cb,
        );
    }

    pub fn ensure_dependencies(&mut self, arity: usize, size: usize) {
        if size == 1 {
            return;
        }
        let n = size - 1;

        // Comp(h, g1..gm): head has arity m, args have `arity`.
        let mut max_head_size_per_m: HashMap<usize, usize> = HashMap::new();
        for hsize in 1..n {
            let gs_total = n - hsize;
            for m in 1..=gs_total {
                let e = max_head_size_per_m.entry(m).or_insert(0);
                *e = (*e).max(hsize);
            }
        }
        for (m, max_hsize) in &max_head_size_per_m {
            self.ensure_up_to(*m, *max_hsize);
        }
        if n >= 2 {
            self.ensure_up_to(arity, n - 1);
        }

        // 0-arg Comp: C_arity(h) where h has arity 0 and hsize = n.
        if !self.opts.comp_null {
            self.ensure_up_to(0, n);
        }

        // Rec(g, h): base has arity-1, step has arity+1.
        if arity >= 1 {
            self.ensure_up_to(arity - 1, n - 1);
            self.ensure_up_to(arity + 1, n - 1);
        }

        // Min(f): f has arity+1, size = n.
        if self.allow_min {
            self.ensure_up_to(arity + 1, n);
        }
    }

    fn ensure_up_to(&mut self, arity: usize, size: usize) {
        for s in 1..=size {
            if arity + s <= self.cf_limit && !self.memo.contains_key(&(arity, s)) {
                self.fill_cache(arity, s);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pruning::PruningOpts;
    use crate::simulate::simulate;

    // Mode A: ClosedFormOnly
    fn mode_a(max_size: usize) -> ClosedFormEnumerator {
        let mut en =
            ClosedFormEnumerator::new(EnumMode::ClosedFormOnly, false, PruningOpts::default());
        for s in 1..=max_size {
            en.fill_cache(0, s);
            en.fill_cache(1, s);
            en.fill_cache(2, s);
        }
        en
    }

    /// Every Mode A candidate must have a ClosedForm.
    #[test]
    fn mode_a_validity() {
        let en = mode_a(8);
        for arity in 0..=2 {
            for size in 1..=8 {
                for grf in en.candidates(arity, size) {
                    assert!(
                        grf.closed_form().is_some(),
                        "Mode A returned non-ClosedForm GRF: {} (arity={}, size={})",
                        grf,
                        arity,
                        size
                    );
                }
            }
        }
    }

    /// No two Mode A candidates at the same arity may share a ClosedForm.
    #[test]
    fn mode_a_no_duplicate_closed_forms() {
        let en = mode_a(8);
        for arity in 0..=2 {
            let mut seen: std::collections::HashMap<ClosedForm, String> =
                std::collections::HashMap::new();
            for size in 1..=8 {
                for grf in en.candidates(arity, size) {
                    let cf = grf.closed_form().unwrap();
                    if let Some(prev) = seen.insert(cf.clone(), grf.to_string()) {
                        panic!(
                            "Duplicate ClosedForm at arity={}: {} and {}",
                            arity, prev, grf
                        );
                    }
                }
            }
        }
    }

    /// `canonical_grf_for` must return a GRF whose ClosedForm matches the query.
    #[test]
    fn canonical_grf_for_round_trip() {
        let en = mode_a(7);
        for arity in 0..=2 {
            for size in 1..=7 {
                for grf in en.candidates(arity, size) {
                    let cf = grf.closed_form().unwrap();
                    let canon = en.canonical_grf_for(arity, &cf).unwrap();
                    let canon_cf = canon.closed_form().unwrap();
                    assert_eq!(
                        cf, canon_cf,
                        "canonical_grf_for round-trip failed for {}",
                        grf
                    );
                }
            }
        }
    }

    /// Mode B must contain every Mode A candidate (by GRF string).
    #[test]
    fn mode_b_superset_of_mode_a() {
        let en_a = mode_a(7);
        let mut en_b = ClosedFormEnumerator::new(EnumMode::AllGrf, false, PruningOpts::default());
        for s in 1..=7 {
            en_b.fill_cache(0, s);
            en_b.fill_cache(1, s);
            en_b.fill_cache(2, s);
        }

        for arity in 0..=2 {
            for size in 1..=7 {
                let b_set: std::collections::HashSet<String> = en_b
                    .candidates(arity, size)
                    .iter()
                    .map(|g| g.to_string())
                    .collect();
                for grf in en_a.candidates(arity, size) {
                    assert!(
                        b_set.contains(&grf.to_string()),
                        "Mode B missing Mode A candidate {} (arity={}, size={})",
                        grf,
                        arity,
                        size
                    );
                }
            }
        }
    }

    /// Mode B `raw_candidates_at_size` must find the known BBµ values for arity-0 PRFs.
    /// BBµ(2k+1) = k (up to 13)
    #[test]
    fn mode_b_bb_correctness_arity0() {
        let known: &[(usize, u64)] = &[(1, 0), (3, 1), (5, 2), (7, 3), (8, 2), (9, 4)];
        let max_size = 9;
        let max_steps = 100_000_000;

        let mut en = ClosedFormEnumerator::new(EnumMode::AllGrf, false, PruningOpts::recommended());
        for size in 1..=max_size {
            en.fill_cache(0, size);
        }

        for &(size, expected) in known {
            let raw = en.all_grfs(0, size);
            let best: u64 = raw
                .iter()
                .filter_map(|grf| {
                    let (result, _) = simulate(grf, &[], max_steps);
                    result.into_value()
                })
                .max()
                .unwrap_or(0);
            assert_eq!(best, expected, "BBµ({size}) = {best}, expected {expected}");
        }
    }
}
