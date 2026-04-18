/// Novel-sub-expression enumerator.
///
/// Instead of enumerating every GRF of a given size and fingerprinting each one,
/// this enumerator uses the key insight that a minimal GRF can only contain minimal
/// sub-expressions: if sub-expression S has a smaller equivalent S', then G[S'/S] is
/// strictly smaller — contradicting minimality. Therefore, to find all distinct minimal
/// GRFs of size N, we only need to consider GRFs whose sub-expressions are themselves
/// canonical (minimal representatives of their function).
///
/// This dramatically reduces the search space, especially for larger sizes, because
/// the number of distinct functions grows much slower than the number of raw GRFs.
///
/// # Termination
///
/// `compute_size(arity, size)` depends on `compute_size(j, s)` for s < size (strictly
/// smaller) and on arities that change predictably:
/// - Comp: sub-expression arity can be any m ≥ 1 for the head, and `arity` for the args.
/// - Rec:  base has arity-1, step has arity+1.
/// - Min:  inner has arity+1.
///
/// The arity can grow (via Rec step / Min inner), but size strictly decreases, so the
/// recursion always bottoms out at size 1. No infinite chains are possible.
///
/// # fp_inputs vs max_steps interaction
///
/// A larger `fp_inputs` requires each sub-expression to converge on more inputs within
/// the `max_steps` budget. GRFs that converge on a smaller input set but loop on larger
/// inputs are excluded from the memo (`fp_is_complete` returns false), which in turn
/// prevents GRFs that use them as sub-expressions from being generated.  This means
/// increasing `fp_inputs` without also increasing `max_steps` can cause some functions
/// to be missed — not because of fingerprint collisions (more inputs only splits
/// equivalence classes, never merges them) but because more slow-converging intermediate
/// GRFs time out and fall out of the search.
///
/// Rule of thumb: if you increase `fp_inputs` and see a drop in the novel count, raise
/// `max_steps` proportionally until the count stabilises.
///
/// # Usage
///
/// ```ignore
/// let mut en = NovelEnumerator::new(32, 100_000, false);
/// let entries = en.run(2, 1, 8, false);
/// // entries: Vec<(Fingerprint, usize, String)> for arity=2, sizes 1..=8
/// ```
use crate::fingerprint::{canonical_inputs_n, compute_fp, fp_is_complete, Fingerprint};
use crate::grf::Grf;
use std::collections::{HashMap, HashSet};

/// A memoized novel-function enumerator.
pub struct NovelEnumerator {
    /// (arity, size) → list of novel GRFs of exactly that (arity, size)
    memo: HashMap<(usize, usize), Vec<Grf>>,
    /// arity → set of fingerprints already seen (for deduplication across sizes)
    seen: HashMap<usize, HashSet<Fingerprint>>,
    /// arity → canonical inputs (cached)
    inputs: HashMap<usize, Vec<Vec<u64>>>,
    fp_inputs: usize,
    max_steps: u64,
    allow_min: bool,
}

impl NovelEnumerator {
    pub fn new(fp_inputs: usize, max_steps: u64, allow_min: bool) -> Self {
        NovelEnumerator {
            memo: HashMap::new(),
            seen: HashMap::new(),
            inputs: HashMap::new(),
            fp_inputs,
            max_steps,
            allow_min,
        }
    }

    /// Return the cached canonical input set for `arity`, computing it if needed.
    fn inputs_for(&mut self, arity: usize) -> &Vec<Vec<u64>> {
        self.inputs
            .entry(arity)
            .or_insert_with(|| canonical_inputs_n(arity, self.fp_inputs))
    }

    /// Compute the fingerprint for a GRF. Borrows `self` mutably for the inputs cache.
    fn fingerprint(&mut self, grf: &Grf) -> Fingerprint {
        let arity = grf.arity();
        // Avoid borrow conflict: clone the inputs out before passing to compute_fp.
        let inputs = self.inputs_for(arity).clone();
        compute_fp(grf, &inputs, self.max_steps)
    }

    /// Ensure `memo[(arity, size)]` is populated, recursing as needed.
    ///
    /// After this call, `memo[(arity, size)]` contains all novel GRFs of exactly
    /// `(arity, size)` that are not redundant given smaller GRFs already in `seen`.
    pub fn compute_size(&mut self, arity: usize, size: usize) {
        if self.memo.contains_key(&(arity, size)) {
            return;
        }

        // Ensure all dependencies are computed before we start generating candidates.
        self.ensure_dependencies(arity, size);

        let candidates = self.generate_candidates(arity, size);
        let mut novel: Vec<Grf> = Vec::new();

        for grf in candidates {
            let fp = self.fingerprint(&grf);
            if !fp_is_complete(&fp) {
                continue;
            }
            let seen_set = self.seen.entry(arity).or_default();
            if !seen_set.contains(&fp) {
                seen_set.insert(fp);
                novel.push(grf);
            }
        }

        self.memo.insert((arity, size), novel);
    }

    /// Ensure all (arity', size') dependencies for generating candidates at
    /// (arity, size) have been computed.
    ///
    /// For correctness, every call `ensure_up_to(arity', s)` must compute sizes
    /// 1..=s in order for `arity'`, so that `seen[arity']` is fully populated up
    /// to size s before `compute_size(arity', s)` runs.  Plain `ensure(arity', s)`
    /// would call `compute_size(arity', s)` without first computing smaller sizes,
    /// potentially causing a non-minimal GRF to claim a fingerprint before the
    /// smaller GRF that should own it.
    fn ensure_dependencies(&mut self, arity: usize, size: usize) {
        if size == 1 {
            return; // Atoms have no sub-expressions.
        }
        let n = size - 1; // Total size budget for sub-expressions.

        // Comp(h, g1..gm): head has arity m (any m ≥ 1), args have `arity`.
        // Max head size: n-1 (when there is one arg of size 1).
        // Max individual arg size: n-1 (when head size=1 and there is one arg).
        //   Derivation: size = 1 + hsize + sum(arg_sizes), so sum = n - hsize.
        //   With hsize=1 and m=1, the single arg has size n-1.
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
        // Max arg size = n-1 (hsize=1, m=1). Only present when size >= 3 (n >= 2).
        if n >= 2 {
            self.ensure_up_to(arity, n - 1);
        }

        // Rec(g, h): base has arity-1 (sizes 1..n-1), step has arity+1 (sizes 1..n-1).
        if arity >= 1 {
            self.ensure_up_to(arity - 1, n - 1);
            self.ensure_up_to(arity + 1, n - 1);
        }

        // Min(f): f has arity+1, size = n.
        if self.allow_min {
            self.ensure_up_to(arity + 1, n);
        }
    }

    /// Ensure `memo[(arity, s)]` is populated for all s in 1..=size, in order.
    ///
    /// Computing sizes in strictly increasing order guarantees `seen[arity]` is
    /// fully populated up to size s-1 before `compute_size(arity, s)` runs, so
    /// the smallest representative always claims each fingerprint first.
    fn ensure_up_to(&mut self, arity: usize, size: usize) {
        for s in 1..=size {
            if !self.memo.contains_key(&(arity, s)) {
                self.compute_size(arity, s);
            }
        }
    }

    /// Generate all candidate GRFs of exactly (arity, size) using only canonical
    /// sub-expressions from the memo.
    fn generate_candidates(&self, arity: usize, size: usize) -> Vec<Grf> {
        let mut out = Vec::new();

        if size == 1 {
            // Atoms
            out.push(Grf::Zero(arity));
            for i in 1..=arity {
                out.push(Grf::Proj(arity, i));
            }
            if arity == 1 {
                out.push(Grf::Succ);
            }
            return out;
        }

        let n = size - 1;

        // Comp(h, g1..gm)
        for hsize in 1..n {
            let gs_total = n - hsize;
            for m in 1..=gs_total {
                let heads = match self.memo.get(&(m, hsize)) {
                    Some(v) => v,
                    None => continue,
                };
                for head in heads {
                    let head_clone = head.clone();
                    let mut arg_combos: Vec<Vec<Grf>> = Vec::new();
                    self.enum_arg_combos(arity, m, gs_total, &mut Vec::new(), &mut arg_combos);
                    for args in arg_combos {
                        out.push(Grf::Comp(Box::new(head_clone.clone()), args, arity));
                    }
                }
            }
        }

        // Rec(g, h): arity ≥ 1
        if arity >= 1 {
            for gsize in 1..n {
                let hsize = n - gsize;
                let bases = match self.memo.get(&(arity - 1, gsize)) {
                    Some(v) => v,
                    None => continue,
                };
                let steps = match self.memo.get(&(arity + 1, hsize)) {
                    Some(v) => v,
                    None => continue,
                };
                for base in bases {
                    for step in steps {
                        out.push(Grf::rec(base.clone(), step.clone()));
                    }
                }
            }
        }

        // Min(f): allow_min only
        if self.allow_min {
            if let Some(inners) = self.memo.get(&(arity + 1, n)) {
                for inner in inners {
                    out.push(Grf::min(inner.clone()));
                }
            }
        }

        out
    }

    /// Enumerate all `count`-tuples of canonical GRFs with arity `arg_arity` and
    /// total size exactly `total_size`. Each individual GRF has size ≥ 1.
    ///
    /// Results are pushed into `out`.
    fn enum_arg_combos(
        &self,
        arg_arity: usize,
        count: usize,
        total_size: usize,
        current: &mut Vec<Grf>,
        out: &mut Vec<Vec<Grf>>,
    ) {
        if count == 0 {
            if total_size == 0 {
                out.push(current.clone());
            }
            return;
        }
        // Each remaining arg needs at least size 1.
        let max_this = total_size - (count - 1);
        for s in 1..=max_this {
            if let Some(candidates) = self.memo.get(&(arg_arity, s)) {
                for grf in candidates {
                    current.push(grf.clone());
                    self.enum_arg_combos(arg_arity, count - 1, total_size - s, current, out);
                    current.pop();
                }
            }
        }
    }

    /// Main entry point.
    ///
    /// Computes all novel GRFs for `target_arity` at sizes `start_size..=max_size`.
    ///
    /// Returns entries as `(fingerprint, size, grf_string)` in the same form as
    /// `NovelMap` values, suitable for merging into a `NovelMap`.
    ///
    /// All required intermediate arities are computed automatically via memoization.
    pub fn run(
        &mut self,
        target_arity: usize,
        start_size: usize,
        max_size: usize,
        progress: bool,
    ) -> Vec<(Fingerprint, usize, String)> {
        let mut results: Vec<(Fingerprint, usize, String)> = Vec::new();

        for size in start_size..=max_size {
            self.compute_size(target_arity, size);

            // Clone out the novel GRFs to avoid holding a borrow on self.memo
            // while we call self.inputs_for().
            let novel: Vec<Grf> = self
                .memo
                .get(&(target_arity, size))
                .map(|v| v.clone())
                .unwrap_or_default();

            // Ensure inputs are cached before the loop.
            let inputs = self.inputs_for(target_arity).clone();

            for grf in &novel {
                let fp = compute_fp(grf, &inputs, self.max_steps);
                results.push((fp, size, grf.to_string()));
            }

            if progress {
                let n_novel = self.memo.get(&(target_arity, size)).map_or(0, |v| v.len());
                let total: usize = (1..=size)
                    .map(|s| self.memo.get(&(target_arity, s)).map_or(0, |v| v.len()))
                    .sum();
                eprintln!(
                    "size {:>3}: {:>5} novel this size  ({} total for arity={})",
                    size, n_novel, total, target_arity
                );
            }
        }

        results
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::novel_db::{extend_novel_map, NovelMap};

    /// The novel-sub-expression enumerator must find at least as many distinct
    /// functions as the exhaustive `extend_novel_map` enumerator for small sizes
    /// where timeouts are not a concern.
    #[test]
    fn novel_enum_agrees_with_exhaustive_arity1() {
        let max_size = 8;
        let fp_inputs = 16;
        let max_steps = 100_000;

        // Exhaustive reference.
        let mut ref_map: NovelMap = NovelMap::new();
        extend_novel_map(&mut ref_map, 1, 1, max_size, false, max_steps, false, false);

        // Novel-sub-expression enumerator.
        let mut en = NovelEnumerator::new(fp_inputs, max_steps, false);
        let entries = en.run(1, 1, max_size, false);
        let novel_count = entries.len();

        // The novel enumerator may find slightly fewer entries if fp_inputs is too
        // small (fingerprint collisions), but with fp_inputs=16 for arity 1 all
        // functions on {0..15} should be distinguishable for these small sizes.
        // At minimum it should find as many as exhaustive enumeration.
        assert_eq!(
            novel_count,
            ref_map.len(),
            "NovelEnumerator found {novel_count} functions but exhaustive found {}",
            ref_map.len(),
        );
    }

    /// Arity 2 matches exhaustive enumeration.
    #[test]
    fn novel_enum_agrees_with_exhaustive_arity2() {
        let max_size = 5;
        let fp_inputs = 32;
        let max_steps = 100_000;

        let mut ref_map: NovelMap = NovelMap::new();
        extend_novel_map(&mut ref_map, 2, 1, max_size, false, max_steps, false, false);

        let mut en = NovelEnumerator::new(fp_inputs, max_steps, false);
        let entries = en.run(2, 1, max_size, false);
        let novel_count = entries.len();

        assert_eq!(
            novel_count,
            ref_map.len(),
            "NovelEnumerator found {novel_count} arity-2 functions but exhaustive found {}",
            ref_map.len(),
        );
    }

    /// Arity 0: constant functions. Z_0=const-0 at size 1, C(S,Z_0)=const-1 at size 3, etc.
    #[test]
    fn novel_enum_arity0() {
        let mut en = NovelEnumerator::new(8, 10_000, false);
        let entries = en.run(0, 1, 4, false);

        // Exhaustive reference using extend_novel_map.
        let mut ref_map: NovelMap = NovelMap::new();
        extend_novel_map(&mut ref_map, 0, 1, 4, false, 10_000, false, false);

        assert_eq!(
            entries.len(),
            ref_map.len(),
            "NovelEnumerator found {} arity-0 functions but exhaustive found {}",
            entries.len(),
            ref_map.len(),
        );
    }
}
