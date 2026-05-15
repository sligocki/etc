/// ClosedForm-based novel-sub-expression enumerator.
///
/// Like `novel_enum::NovelEnumerator` but uses `ClosedForm` structural equality
/// for deduplication instead of simulation-based fingerprinting.  This avoids
/// all simulation cost for GRFs that have a closed form (~99.7% of all GRFs)
/// and also guarantees the GRF are equal (not just similar).
///
/// # Soundness note
///
/// ClosedForm structural equality is *sound* (same form ⟹ same function) but not
/// *complete* (same function may have different forms).  ClosedFormOnly mode
/// therefore retains some redundancy compared to fingerprint-based dedup.

use crate::closed_form::{closed_form_of, ClosedForm};
use crate::enumerate::{for_each_grf_core, stream_grf};
use crate::grf::Grf;
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
}

impl ClosedFormEnumerator {
    pub fn new(mode: EnumMode, allow_min: bool, opts: PruningOpts) -> Self {
        // TODO: Not yet supported.
        assert!(mode != EnumMode::ClosedFormChildren);
        ClosedFormEnumerator {
            memo: HashMap::new(),
            seen_closed: HashMap::new(),
            mode,
            allow_min,
            opts,
            cf_limit: usize::MAX,
        }
    }

    /// Convenience constructor with all recommended pruning flags enabled,
    /// including stream-only flags (`comp_rnf`, `inline_proj`, `min_dom`,
    /// `rec_step_p2`).  Use this for BBµ search and algebraic exploration.
    pub fn with_pruning(mode: EnumMode, allow_min: bool) -> Self {
        let opts = PruningOpts::recommended()
            .with_flags("min_dom,inline_proj,comp_rnf,rec_step_p2");
        Self::new(mode, allow_min, opts)
    }

    /// Set the arity+size threshold above which domains are streamed instead of cached.
    pub fn with_cf_limit(mut self, limit: usize) -> Self {
        self.cf_limit = limit;
        self
    }

    /// Pre-fill the memo for all in-limit dependency domains needed to call
    /// `raw_candidates_at_size(arity, size)`.  Never caches the target domain
    /// itself, so no above-limit entry is ever written to the memo.
    pub fn prepare(&mut self, arity: usize, size: usize) {
        self.ensure_dependencies(arity, size);
    }

    /// Populate `memo[(arity, size)]` with novel GRFs, recursing into dependencies.
    /// If `arity + size > cf_limit` this is a no-op: the domain is intentionally
    /// left uncached and will be streamed on demand by `generate_candidates`.
    pub fn compute_size(&mut self, arity: usize, size: usize) {
        if self.memo.contains_key(&(arity, size)) {
            return;
        }
        if arity + size > self.cf_limit {
            return;
        }

        self.ensure_dependencies(arity, size);

        let candidates = self.generate_candidates(arity, size);
        let mut novel: Vec<Grf> = Vec::new();

        for grf in candidates {
            match (closed_form_of(&grf), self.mode) {
                (Some(cf), _) => {
                    let seen = self.seen_closed.entry(arity).or_default();
                    if !seen.contains_key(&cf) {
                        seen.insert(cf, grf.clone());
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
    pub fn candidates(&self, arity: usize, size: usize) -> &[Grf] {
        self.memo
            .get(&(arity, size))
            .map(|v| v.as_slice())
            .unwrap_or(&[])
    }

    /// Return the canonical (first-seen, smallest) Grf for a given ClosedForm and arity.
    pub fn canonical_grf_for(&self, arity: usize, cf: &ClosedForm) -> Option<&Grf> {
        self.seen_closed.get(&arity)?.get(cf)
    }

    /// Return `(total_closed_seen, total_raw_included)` across all arities and sizes.
    pub fn memo_stats(&self) -> (usize, usize) {
        let closed: usize = self.seen_closed.values().map(|m| m.len()).sum();
        let raw: usize = self
            .memo
            .values()
            .flat_map(|v| v.iter())
            .filter(|g| closed_form_of(g).is_none())
            .count();
        (closed, raw)
    }

    /// Stream all GRFs of exactly (arity, size) using canonical sub-expressions,
    /// calling `callback` for each without collecting into a Vec.  For BBµ search:
    /// the champion at size n may compute a value already seen at a smaller size,
    /// so it won't appear in `candidates`, but is still a valid size-n GRF.
    ///
    /// Call `prepare(arity, size)` first to ensure in-limit dependency domains are
    /// in the memo.  Above-limit domains are streamed on demand.
    pub fn for_each_raw_candidate<F: FnMut(&Grf)>(&self, arity: usize, size: usize, callback: &mut F) {
        let memo = &self.memo;
        let allow_min = self.allow_min;
        let opts = self.opts;
        for_each_grf_core(
            size, arity, allow_min, opts,
            &|s, a, cb| {
                if let Some(grfs) = memo.get(&(a, s)) {
                    for grf in grfs { cb(grf); }
                } else {
                    stream_grf(s, a, allow_min, opts, &mut |grf| cb(grf));
                }
            },
            &mut |grf| callback(grf),
        );
    }

    /// Convenience wrapper around `for_each_raw_candidate` that collects into a Vec.
    pub fn raw_candidates_at_size(&self, arity: usize, size: usize) -> Vec<Grf> {
        let mut out = Vec::new();
        self.for_each_raw_candidate(arity, size, &mut |grf| out.push(grf.clone()));
        out
    }

    fn ensure_dependencies(&mut self, arity: usize, size: usize) {
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
                self.compute_size(arity, s);
            }
        }
    }

    fn generate_candidates(&self, arity: usize, size: usize) -> Vec<Grf> {
        self.raw_candidates_at_size(arity, size)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sim_nat::SmallNat;
    use crate::closed_form::closed_form_of;
    use crate::pruning::PruningOpts;
    use crate::simulate::simulate;

    // Mode A: ClosedFormOnly
    fn mode_a(max_size: usize) -> ClosedFormEnumerator {
        let mut en = ClosedFormEnumerator::new(EnumMode::ClosedFormOnly, false, PruningOpts::default());
        for s in 1..=max_size {
            en.compute_size(0, s);
            en.compute_size(1, s);
            en.compute_size(2, s);
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
                        closed_form_of(grf).is_some(),
                        "Mode A returned non-ClosedForm GRF: {} (arity={}, size={})",
                        grf, arity, size
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
                    let cf = closed_form_of(grf).unwrap();
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
                    let cf = closed_form_of(grf).unwrap();
                    let canon = en.canonical_grf_for(arity, &cf).unwrap();
                    let canon_cf = closed_form_of(canon).unwrap();
                    assert_eq!(cf, canon_cf, "canonical_grf_for round-trip failed for {}", grf);
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
            en_b.compute_size(0, s);
            en_b.compute_size(1, s);
            en_b.compute_size(2, s);
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
                        grf, arity, size
                    );
                }
            }
        }
    }

    /// Mode B `raw_candidates_at_size` must find the known BBµ values for arity-0 PRFs.
    ///
    /// Known BBµ values: n=1→0, n=3→1, n=5→2, n=7→3, n=8→2, n=9→4.
    #[test]
    fn mode_b_bb_correctness_arity0() {
        let known: &[(usize, SmallNat)] = &[(1, 0), (3, 1), (5, 2), (7, 3), (8, 2), (9, 4)];
        let max_size = 9;
        let max_steps = 100_000_000;

        let mut en = ClosedFormEnumerator::new(EnumMode::AllGrf, false, PruningOpts::recommended());
        for size in 1..=max_size {
            en.compute_size(0, size);
        }

        for &(size, expected) in known {
            let raw = en.raw_candidates_at_size(0, size);
            let best: SmallNat = raw
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
