use crate::grf::{Grf, GrfKind};
use crate::optimize::{InlineConstraints, compute_inline_constraints};
use crate::pruning::{Pruner, PruningOpts};
use std::cell::RefCell;
use std::collections::HashMap;

#[derive(
    clap::ValueEnum, Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize,
)]
pub enum EnumScope {
    #[value(name = "prf")]
    Prf,
    #[value(name = "min_prf")]
    MinPrf,
    #[value(name = "grf")]
    Grf,
}

impl EnumScope {
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Prf => "prf",
            Self::MinPrf => "min_prf",
            Self::Grf => "grf",
        }
    }
}

impl EnumScope {
    pub fn allow_min(&self) -> bool {
        match self {
            EnumScope::Grf => true,
            _ => false,
        }
    }

    pub fn min_prf(&self) -> bool {
        match self {
            EnumScope::MinPrf => true,
            _ => false,
        }
    }
}

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

/// Core recursive generator parameterised by a sub-expression enumerator.
///
/// `sub(size, arity, callback)` is called wherever `for_each_grf` would
/// recursively enumerate sub-expressions (heads, args, Rec base/step, Min
/// inner).  This lets callers swap in alternative sub-expression sources —
/// e.g. a memoised table of novel GRFs — while reusing all pruning logic here.
///
/// For standard streaming enumeration use the [`for_each_grf`] wrapper, which
/// wires `sub` back to `for_each_grf` itself.
pub(crate) fn for_each_grf_core(
    size: usize,
    arity: usize,
    allow_min: bool,
    opts: PruningOpts,
    sub: &dyn Fn(usize, usize, &mut dyn FnMut(&Grf)),
    callback: &mut dyn FnMut(&Grf),
) {
    if size == 0 {
        return;
    }
    if size == 1 {
        callback(&Grf::zero_atom(arity));
        for i in 1..=arity {
            callback(&Grf::proj_atom(arity, i));
        }
        if arity == 1 {
            callback(&Grf::succ_atom());
        }
        return;
    }
    let n = size - 1;

    // C(h, g1..gm): stream h's; for each h, stream all argument tuples
    let pruner = Pruner::new(opts);
    for hsize in 1..=n {
        let gs_total = n - hsize;

        // 0-arg Comp: Ck(h)
        if !opts.comp_null && gs_total == 0 {
            // comp_null_null: prunes C0(h)
            if !(opts.comp_null_null && arity == 0) {
                sub(hsize, 0, &mut |h: &Grf| {
                    if opts.comp_zero && matches!(&h.kind, GrfKind::Zero(_)) {
                        return;
                    }
                    callback(&Grf::comp0(h.clone(), arity));
                });
            }
        }

        for m in 1..=gs_total {
            sub(hsize, m, &mut |h: &Grf| {
                if pruner.should_prune_comp_head(h, m) {
                    return;
                }

                // Compute constraints once per head; O(h.size()) upfront instead of
                // O(h.size()) per arg-tuple.
                let inline_c: Option<InlineConstraints> = if opts.inline_proj {
                    Some(compute_inline_constraints(h))
                } else {
                    None
                };

                let forced: Option<&[bool]> = None;
                let mut args = Vec::with_capacity(m);
                for_each_args_core(
                    gs_total,
                    m,
                    arity,
                    allow_min,
                    opts,
                    sub,
                    forced,
                    &mut args,
                    &mut |gs: &[Grf]| {
                        if pruner.should_prune_comp_args(
                            h,
                            gs,
                            arity,
                            inline_c.as_ref(),
                        ) {
                            return;
                        }
                        callback(&Grf::comp_arity(h.clone(), gs.to_vec(), arity));
                    },
                );
            });
        }
    }

    // R(g, h): stream g's; for each g, stream h's
    if arity >= 1 {
        for gsize in 1..n {
            let hsize = n - gsize;
            sub(gsize, arity - 1, &mut |g: &Grf| {
                sub(hsize, arity + 1, &mut |h: &Grf| {
                    if pruner.should_prune_rec(g, h) {
                        return;
                    }
                    callback(&Grf::rec(g.clone(), h.clone()));
                });
            });
        }
    }

    // M(f): f ∈ GRF_{arity+1}, |f| = n
    if allow_min {
        sub(n, arity + 1, &mut |f: &Grf| {
            if pruner.should_prune_min(f) {
                return;
            }
            callback(&Grf::min(f.clone()));
        });
    }
}

/// Standard streaming enumeration: wraps [`for_each_grf_core`] with a
/// sub-enumerator that recursively calls `for_each_grf` itself.
fn for_each_grf(
    size: usize,
    arity: usize,
    allow_min: bool,
    opts: PruningOpts,
    callback: &mut dyn FnMut(&Grf),
) {
    for_each_grf_core(
        size,
        arity,
        allow_min,
        opts,
        &|s, a, cb| for_each_grf(s, a, allow_min, opts, cb),
        callback,
    )
}

/// Generate all ordered `remaining_count`-tuples of `arity`-GRFs whose sizes
/// sum to `remaining_size`, appending each element to `current` in turn.
///
/// `sub` is the sub-expression enumerator (same contract as in [`for_each_grf_core`]).
/// `forced`: if `Some(f)`, positions where `f[current.len()]` is `true` are
/// constrained to `Zero(arity)` (size 1); all other positions are unconstrained.
fn for_each_args_core(
    remaining_size: usize,
    remaining_count: usize,
    arity: usize,
    allow_min: bool,
    opts: PruningOpts,
    sub: &dyn Fn(usize, usize, &mut dyn FnMut(&Grf)),
    forced: Option<&[bool]>,
    current: &mut Vec<Grf>,
    callback: &mut dyn FnMut(&[Grf]),
) {
    if remaining_count == 0 {
        if remaining_size == 0 {
            callback(current);
        }
        return;
    }
    let pos = current.len();
    if forced.map_or(false, |f| f[pos]) {
        // Forced position: only Zero(arity) with size 1.
        if remaining_size >= remaining_count {
            current.push(Grf::zero_atom(arity));
            for_each_args_core(
                remaining_size - 1,
                remaining_count - 1,
                arity,
                allow_min,
                opts,
                sub,
                forced,
                current,
                callback,
            );
            current.pop();
        }
    } else {
        let max_first = remaining_size.saturating_sub(remaining_count - 1);
        for x in 1..=max_first {
            sub(x, arity, &mut |g: &Grf| {
                current.push(g.clone());
                for_each_args_core(
                    remaining_size - x,
                    remaining_count - 1,
                    arity,
                    allow_min,
                    opts,
                    sub,
                    forced,
                    current,
                    callback,
                );
                current.pop();
            });
        }
    }
}

/// Convenience wrapper: `for_each_args_core` with standard sub-enumerator.
#[allow(dead_code)]
fn for_each_args(
    remaining_size: usize,
    remaining_count: usize,
    arity: usize,
    allow_min: bool,
    opts: PruningOpts,
    forced: Option<&[bool]>,
    current: &mut Vec<Grf>,
    callback: &mut dyn FnMut(&[Grf]),
) {
    for_each_args_core(
        remaining_size,
        remaining_count,
        arity,
        allow_min,
        opts,
        &|s, a, cb| for_each_grf(s, a, allow_min, opts, cb),
        forced,
        current,
        callback,
    )
}

/// Emit or skip a single atom, updating the skip/rem counters.
fn emit_atom(skip: &mut usize, rem: &mut usize, grf: &Grf, callback: &mut dyn FnMut(&Grf)) {
    if *skip > 0 {
        *skip -= 1;
        return;
    }
    if *rem > 0 {
        callback(grf);
        *rem -= 1;
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
    //     Zero/Proj atoms (when skip_comp_*).
    static AS_HEAD_CACHE: RefCell<HashMap<CountKey, usize>> = RefCell::new(HashMap::new());
}

/// Count GRFs of given `size` and `arity` without building any GRF tree.
/// Results are memoised in a thread-local DP table.
///
/// Panics if any stream-only flag is set — those flags are not accounted for
/// in the DP and would produce incorrect counts.
pub fn count_grf(size: usize, arity: usize, allow_min: bool, opts: PruningOpts) -> usize {
    opts.assert_count_compat();
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
/// - With `skip_comp_*`: Zero and Proj atoms are excluded (they would make
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
    if size == 1 {
        let mut count = 0;
        if arity == 1 {
            count += 1; // S is always a legal head
        }
        if !opts.comp_zero {
            count += 1; // Z only valid if not skipping C(Z, ...)
        }
        if !opts.comp_proj {
            count += arity; // P_i only valid if not skipping C(P, ...)
        }
        return count;
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

    // When skip_rec_zero_arg is on, C(R(g,h), Z(arity)) single-arg Comps are pruned
    // and already excluded from count_grf, but the loop above still counts them via
    // count_as_head(fsize=inner_total-1, 1) * count_grf(gsize=1, arity) because
    // Rec heads pass count_as_head and Z(arity) is included in count_grf(1, arity).
    // Correct by subtracting the count of these pruned expressions.
    if opts.rec_zero_arg && inner_total >= 2 {
        let pruned_sa = count_rec_only(inner_total - 1, 1, allow_min, opts);
        single_arg_count = single_arg_count.saturating_sub(pruned_sa);
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
            // count_as_head handles skip_comp_* and comp_assoc filters.
            let h_count = count_as_head(hsize, m, allow_min, opts);
            if h_count == 0 {
                continue;
            }
            total = total.saturating_add(
                h_count.saturating_mul(count_many_fast(gs_total, m, arity, allow_min, opts)),
            );
        }
    }

    // C(h) 0-arg Comp: when comp_null is off, count valid 0-arity heads of size n.
    // comp_zero prunes C(Z0): Z0 is the only 0-arity size-1 form, so only adjust at n==1.
    if !opts.comp_null {
        // comp_null_null: prunes C0(h)
        if !(opts.comp_null_null && arity == 0) {
            let h_count = count_grf(n, 0, allow_min, opts);
            let zero_adj = if opts.comp_zero && n == 1 { 1 } else { 0 };
            total = total.saturating_add(h_count.saturating_sub(zero_adj));
        }
    }

    // rec_zero_arg: subtract C(R(g,h), Z(arity), f2,...,fm) for all m,g,h.
    // These are pruned because the first arg is structurally Zero, forcing n=0,
    // so the equivalent C(g, f2,...) (strictly smaller) is generated instead.
    if opts.rec_zero_arg {
        for hsize in 1..=n {
            let gs_total = n - hsize;
            if gs_total == 0 {
                continue; // need at least one arg (the Zero)
            }
            for m in 1..=gs_total {
                let rec_count = count_rec_only(hsize, m, allow_min, opts);
                if rec_count == 0 {
                    continue;
                }
                // First arg is Z(arity): 1 choice, size 1.
                // Remaining m-1 args of arity `arity` summing to gs_total-1.
                let rest = count_many_fast(gs_total - 1, m - 1, arity, allow_min, opts);
                total = total.saturating_sub(rec_count.saturating_mul(rest));
            }
        }
    }

    // R(g, h): g ∈ GRF_{arity-1}, h ∈ GRF_{arity+1}
    if arity >= 1 {
        for gsize in 1..n {
            total = total.saturating_add(
                count_grf(gsize, arity - 1, allow_min, opts).saturating_mul(count_grf(
                    n - gsize,
                    arity + 1,
                    allow_min,
                    opts,
                )),
            );
        }
        // rec_zero_base: at size=3 (n=2), prune R(Z(arity-1), Z(arity+1)) and
        // R(Z(arity-1), P(arity+1,2)) — 2 expressions, both always ≡ Z(arity).
        // rec_proj_base: at size=3 (n=2), prune R(P(arity-1,i), P(arity+1,2)) and
        // R(P(arity-1,i), P(arity+1,i+2)) for each i in 1..=arity-1 — 2*(arity-1) expressions.
        if n == 2 {
            if opts.rec_zero_base {
                total = total.saturating_sub(2);
            }
            if opts.rec_proj_base {
                total = total.saturating_sub(2 * (arity - 1));
            }
        }
    }

    // M(f): f ∈ GRF_{arity+1}
    if allow_min {
        let inner = count_grf(n, arity + 1, allow_min, opts);
        // min_trivial: at n==1, prune Zero(arity+1) and all Proj(arity+1,_).
        // That's 1 + (arity+1) forms. Inner count at n==1 = 1 + (arity+1) + [arity+1==1],
        // so remaining is [arity+1==1] (just Succ when inner arity is 1). No underflow.
        let pruned = if opts.min_trivial && n == 1 {
            1 + (arity + 1)
        } else {
            0
        };
        total = total.saturating_add(inner.saturating_sub(pruned));
    }

    total
}

/// Count only the `R(g, h)` (Rec) expressions of exactly `size` and `arity`.
/// Used to compute the skip_rec_zero_arg subtraction in `compute_count`.
fn count_rec_only(size: usize, arity: usize, allow_min: bool, opts: PruningOpts) -> usize {
    if size < 3 || arity == 0 {
        return 0;
    }
    let n = size - 1;
    let mut total = 0usize;
    for gsize in 1..n {
        total = total.saturating_add(
            count_grf(gsize, arity - 1, allow_min, opts).saturating_mul(count_grf(
                n - gsize,
                arity + 1,
                allow_min,
                opts,
            )),
        );
    }
    if size == 3 {
        if opts.rec_zero_base {
            total = total.saturating_sub(2);
        }
        if opts.rec_proj_base {
            total = total.saturating_sub(2 * (arity - 1));
        }
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
        total = total.saturating_add(count_grf(x, arity, allow_min, opts).saturating_mul(
            count_many_fast(total_size - x, num_funcs - 1, arity, allow_min, opts),
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
    fn collect(size: usize, arity: usize, allow_min: bool, opts: PruningOpts) -> Vec<Grf> {
        let mut grfs = Vec::new();
        stream_grf(size, arity, allow_min, opts, &mut |g| grfs.push(g.clone()));

        // Assert every GRF in the streamed set has the correct size and arity.
        for grf in &grfs {
            assert_eq!(grf.size(), size, "size mismatch for {grf}");
            assert_eq!(grf.arity(), arity, "arity mismatch for {grf}");
            if !allow_min {
                assert!(grf.analysis.is_prf, "non-PRF when allow_min=false: {grf}");
            }
        }

        grfs
    }

    // --- atom counts (size=1) ---

    #[test]
    fn test_atoms_arity0() {
        assert_eq!(collect(1, 0, true, PruningOpts::default()).len(), 1); // Z0 only
    }

    #[test]
    fn test_atoms_arity1() {
        assert_eq!(collect(1, 1, true, PruningOpts::default()).len(), 3); // Z1, S, P(1,1)
    }

    #[test]
    fn test_atoms_arity2() {
        assert_eq!(collect(1, 2, true, PruningOpts::default()).len(), 3); // Z2, P(2,1), P(2,2)
    }

    #[test]
    fn test_atoms_arity3() {
        assert_eq!(collect(1, 3, true, PruningOpts::default()).len(), 4); // Z3, P(3,1..3)
    }

    // --- size-2 ---

    #[test]
    fn test_size2_arity0() {
        // C0(Z0)
        assert_eq!(collect(2, 0, false, PruningOpts::default()).len(), 1);
        // + M(Z1), M(S), M(P(1,1))
        assert_eq!(collect(2, 0, true, PruningOpts::default()).len(), 4);
    }

    // --- size-3 ---

    #[test]
    fn test_size3_arity0() {
        // C(Z1, Z0), C(P1, Z0), C(S, Z0) + C0(C0(Z0))
        assert_eq!(collect(3, 0, false, PruningOpts::default()).len(), 4);
        // + M(M(Z2)), M(M(P(2,1))), M(M(P(2,2))), M(C1(Z0)) + C0(M(Z1)), C0(M(S)), C0(M(P(1,1)))
        assert_eq!(collect(3, 0, true, PruningOpts::default()).len(), 11);
    }

    #[test]
    fn test_size3_arity1() {
        assert_eq!(collect(3, 1, true, PruningOpts::default()).len(), 21);
    }

    // --- larger sizes ---

    #[test]
    fn test_run_to_size_7() {
        for size in 0..=7 {
            for arity in 0..=3 {
                collect(size, arity, false, PruningOpts::default());
                collect(size, arity, true, PruningOpts::default());
            }
        }
    }

    // --- skip_trivial ---

    #[test]
    fn test_skip_trivial_removes_zero_proj_comps() {
        let trim = collect(
            3,
            0,
            false,
            PruningOpts::default().with_flags("comp_zero,comp_proj"),
        );
        assert_eq!(trim.len(), 1);
        assert_eq!(
            trim[0],
            Grf::comp(Grf::succ_atom(), vec![Grf::zero_atom(0)])
        );
    }

    #[test]
    fn test_skip_trivial_never_more_than_full() {
        for size in 1..=8 {
            for arity in 0..=2 {
                let full = count_grf(size, arity, false, PruningOpts::default());
                let trim = count_grf(
                    size,
                    arity,
                    false,
                    PruningOpts::default().with_flags("comp_zero,comp_proj"),
                );
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
        let full = collect(5, 0, false, PruningOpts::default());
        let assoc = collect(5, 0, false, PruningOpts::default().with_flags("comp_assoc"));

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
                let full = count_grf(size, arity, false, PruningOpts::default());
                let assoc = count_grf(
                    size,
                    arity,
                    false,
                    PruningOpts::default().with_flags("comp_assoc"),
                );
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
                let st = count_grf(
                    size,
                    arity,
                    false,
                    PruningOpts::default().with_flags("comp_zero,comp_proj"),
                );
                let all = count_grf(
                    size,
                    arity,
                    false,
                    PruningOpts::recommended().for_counting(),
                );
                assert!(
                    all <= st,
                    "recommended opts produced more GRFs than comp_zero+comp_proj at size={size} arity={arity}"
                );
            }
        }
    }

    // --- no duplicates ---

    #[test]
    fn test_no_duplicates() {
        use std::collections::HashSet;
        for size in 1..=7 {
            let all = collect(size, 0, false, PruningOpts::default());
            let unique: HashSet<Grf> = all.iter().cloned().collect();
            assert_eq!(all.len(), unique.len(), "duplicates at size={size}");
        }
    }

    #[test]
    fn test_no_duplicates_comp_assoc() {
        use std::collections::HashSet;
        for size in 1..=7 {
            for arity in 0..=2 {
                let all = collect(
                    size,
                    arity,
                    false,
                    PruningOpts::default().with_flags("comp_assoc"),
                );
                let unique: HashSet<Grf> = all.iter().cloned().collect();
                assert_eq!(
                    all.len(),
                    unique.len(),
                    "duplicates with comp_assoc at size={size} arity={arity}"
                );
            }
        }
    }

    // --- skip_rec_zero_arg ---

    // --- skip_rec_zero_base ---

    #[test]
    fn test_skip_rec_zero_base_removes_specific_forms() {
        // R(Z0, Z2) and R(Z0, P(2,2)) should be pruned (≡ Z1).
        let pruned = collect(
            3,
            1,
            false,
            PruningOpts::default().with_flags("rec_zero_base"),
        );
        let rz0z2 = "R(Z0, Z2)".parse::<Grf>().unwrap();
        let rz0p22 = "R(Z0, P(2,2))".parse::<Grf>().unwrap();
        assert!(
            !pruned.iter().any(|g| *g == rz0z2),
            "R(Z0,Z2) should be pruned by skip_rec_zero_base"
        );
        assert!(
            !pruned.iter().any(|g| *g == rz0p22),
            "R(Z0,P(2,2)) should be pruned by skip_rec_zero_base"
        );

        // R(Z0, P(2,1)) should NOT be pruned (step=counter, not acc).
        let rz0p21 = "R(Z0, P(2,1))".parse::<Grf>().unwrap();
        assert!(
            pruned.iter().any(|g| *g == rz0p21),
            "R(Z0,P(2,1)) should not be pruned (step returns counter, not zero)"
        );
    }

    #[test]
    fn test_skip_rec_zero_base_never_more_than_full() {
        for size in 1..=8 {
            for arity in 0..=2 {
                let full = count_grf(size, arity, false, PruningOpts::default());
                let pruned = count_grf(
                    size,
                    arity,
                    false,
                    PruningOpts::default().with_flags("rec_zero_base"),
                );
                assert!(
                    pruned <= full,
                    "skip_rec_zero_base produced more GRFs at size={size} arity={arity}"
                );
            }
        }
    }

    #[test]
    fn test_skip_rec_zero_arg_removes_specific_form() {
        // C(R(Z0, Z2), Z0) should be removed (head is Rec, first arg is Zero).
        // It is equivalent to the strictly smaller C(Z0) = Z0 (size 1).
        let pruned = collect(
            5,
            0,
            false,
            PruningOpts::default().with_flags("rec_zero_arg"),
        );
        let target = "C(R(Z0, Z2), Z0)".parse::<Grf>().unwrap();
        assert!(
            !pruned.iter().any(|g| *g == target),
            "C(R(Z0,Z2),Z0) should be pruned by skip_rec_zero_arg"
        );

        // C(R(Z0, Z2), C(S, Z0)) should NOT be removed (first arg C(S,Z0) is not Zero).
        let full = collect(7, 0, false, PruningOpts::default());
        let non_pruned = "C(R(Z0, Z2), C(S, Z0))".parse::<Grf>().unwrap();
        assert!(
            full.iter().any(|g| *g == non_pruned),
            "C(R(Z0,Z2),C(S,Z0)) must exist in full set"
        );
        let with_rule = collect(
            7,
            0,
            false,
            PruningOpts::default().with_flags("rec_zero_arg"),
        );
        assert!(
            with_rule.iter().any(|g| *g == non_pruned),
            "C(R(Z0,Z2),C(S,Z0)) should not be pruned (first arg is not Zero)"
        );
    }

    #[test]
    fn test_skip_rec_zero_arg_never_more_than_full() {
        for size in 1..=8 {
            for arity in 0..=2 {
                let full = count_grf(size, arity, false, PruningOpts::default());
                let pruned = count_grf(
                    size,
                    arity,
                    false,
                    PruningOpts::default().with_flags("rec_zero_arg"),
                );
                assert!(
                    pruned <= full,
                    "skip_rec_zero_arg produced more GRFs at size={size} arity={arity}"
                );
            }
        }
    }

    // --- skip_inline_proj ---

    #[test]
    fn test_skip_inline_proj_removes_specific_forms() {
        // C(R(Z1, P(3,3)), P(4,1), P(4,4)) — all args are Proj, inlineable → R(Z3, P(5,5)).
        let pruned = collect(
            6,
            4,
            false,
            PruningOpts::default().with_flags("inline_proj"),
        );
        let target = "C(R(Z1,P(3,3)),P(4,1),P(4,4))".parse::<Grf>().unwrap();
        assert!(
            !pruned.iter().any(|g| *g == target),
            "C(R(Z1,P(3,3)),P(4,1),P(4,4)) should be pruned"
        );

        // C(S, P(1,1)) — arity-1, single Proj arg, inlines to S.  Should be pruned.
        let pruned3 = collect(
            3,
            1,
            false,
            PruningOpts::default().with_flags("inline_proj"),
        );
        let target3 = "C(S,P(1,1))".parse::<Grf>().unwrap();
        assert!(
            !pruned3.iter().any(|g| *g == target3),
            "C(S,P(1,1)) should be pruned (inlines to S)"
        );

        // C(S, Z1) — inline_proj(S, 1, [0]) fails (S requires rewiring [1]).
        // This computes \x.1, not zero; correctly NOT pruned.
        let target_z = "C(S,Z1)".parse::<Grf>().unwrap();
        assert!(
            pruned3.iter().any(|g| *g == target_z),
            "C(S,Z1) should NOT be pruned (Succ can't be rewired with a zero slot)"
        );

        // C(S, P(2,1)) — arity-2, but S has arity 1 so new_arity would be 2 ≠ 1.
        // inline_proj(S, 2, [1]) returns None → NOT pruned.
        let pruned3_ar2 = collect(
            3,
            2,
            false,
            PruningOpts::default().with_flags("inline_proj"),
        );
        let target_ar2 = "C(S,P(2,1))".parse::<Grf>().unwrap();
        assert!(
            pruned3_ar2.iter().any(|g| *g == target_ar2),
            "C(S,P(2,1)) should NOT be pruned (Succ can't be rewired to arity 2)"
        );

        // C(R(Z1,P(3,3)), C(S,P(4,1)), P(4,4)) — first arg is not P/Z, NOT pruned.
        let full = collect(8, 4, false, PruningOpts::default());
        let not_pruned = "C(R(Z1,P(3,3)),C(S,P(4,1)),P(4,4))".parse::<Grf>().unwrap();
        assert!(
            full.iter().any(|g| *g == not_pruned),
            "C(R(Z1,P(3,3)),C(S,P(4,1)),P(4,4)) must exist without pruning"
        );
        let pruned8 = collect(
            8,
            4,
            false,
            PruningOpts::default().with_flags("inline_proj"),
        );
        assert!(
            pruned8.iter().any(|g| *g == not_pruned),
            "C(R(Z1,P(3,3)),C(S,P(4,1)),P(4,4)) should NOT be pruned (non-P/Z arg)"
        );
    }

    #[test]
    fn test_skip_inline_proj_never_more_than_full() {
        for size in 1..=8 {
            for arity in 0..=2 {
                let full = collect(size, arity, false, PruningOpts::default()).len();
                let pruned = collect(
                    size,
                    arity,
                    false,
                    PruningOpts::default().with_flags("inline_proj"),
                )
                .len();
                assert!(
                    pruned <= full,
                    "skip_inline_proj produced more GRFs at size={size} arity={arity}"
                );
            }
        }
    }

    #[test]
    #[should_panic(expected = "'inline_proj'")]
    fn count_grf_panics_on_skip_inline_proj() {
        count_grf(
            5,
            1,
            false,
            PruningOpts::default().with_flags("inline_proj"),
        );
    }

    // --- min_trivial ---

    #[test]
    fn test_skip_min_trivial_zero_removes_specific_forms() {
        // M(Z1) and M(P(1,1)) — size 2, arity 0 — should be pruned.
        let full = collect(2, 0, true, PruningOpts::default());
        let pruned = collect(2, 0, true, PruningOpts::default().with_flags("min_trivial"));
        let m_zero = "M(Z1)".parse::<Grf>().unwrap();
        let m_proj1 = "M(P(1,1))".parse::<Grf>().unwrap();
        let m_succ = "M(S)".parse::<Grf>().unwrap();
        assert!(
            full.iter().any(|g| *g == m_zero),
            "M(Z1) must appear without pruning"
        );
        assert!(
            full.iter().any(|g| *g == m_proj1),
            "M(P(1,1)) must appear without pruning"
        );
        assert!(
            !pruned.iter().any(|g| *g == m_zero),
            "M(Z1) should be pruned by skip_min_trivial_zero"
        );
        assert!(
            !pruned.iter().any(|g| *g == m_proj1),
            "M(P(1,1)) should be pruned by skip_min_trivial_zero"
        );
        // M(S) = M(Succ) at arity 0: Succ is not Zero or Proj, so it survives.
        assert!(
            pruned.iter().any(|g| *g == m_succ),
            "M(S) should NOT be pruned by skip_min_trivial_zero"
        );
    }

    #[test]
    fn test_skip_min_trivial_zero_arity1() {
        // M(Z2), M(P(2,1)), M(P(2,2)) — size 2, arity 1 — all pruned (Zero and all Proj).
        // No size-2 Min survives at arity 1 since inner arity is 2 and Succ has arity 1 ≠ 2.
        let pruned = collect(2, 1, true, PruningOpts::default().with_flags("min_trivial"));
        let m_zero2 = "M(Z2)".parse::<Grf>().unwrap();
        let m_proj21 = "M(P(2,1))".parse::<Grf>().unwrap();
        let m_proj22 = "M(P(2,2))".parse::<Grf>().unwrap();
        assert!(
            !pruned.iter().any(|g| *g == m_zero2),
            "M(Z2) should be pruned"
        );
        assert!(
            !pruned.iter().any(|g| *g == m_proj21),
            "M(P(2,1)) should be pruned"
        );
        assert!(
            !pruned.iter().any(|g| *g == m_proj22),
            "M(P(2,2)) should be pruned (all Proj pruned)"
        );
        assert!(
            pruned.iter().all(|g| !matches!(&g.kind, GrfKind::Min(_))),
            "no size-2 Min survives at arity 1"
        );
    }

    #[test]
    fn test_skip_min_dominated_removes_all_size2_min() {
        // With both flags, NO M(atom) survives for any arity — smallest novel Min has size ≥ 4.
        for arity in 0..=2 {
            let pruned = collect(
                2,
                arity,
                true,
                PruningOpts::default().with_flags("min_trivial,min_dom"),
            );
            assert!(
                pruned.iter().all(|g| !matches!(&g.kind, GrfKind::Min(_))),
                "all size-2 Min expressions should be pruned at arity={arity}, got: {:?}",
                pruned
                    .iter()
                    .filter(|g| matches!(&g.kind, GrfKind::Min(_)))
                    .collect::<Vec<_>>()
            );
        }
    }

    #[test]
    fn test_skip_min_trivial_count_matches_stream() {
        // count_grf must agree with stream_grf count under skip_min_trivial_zero.
        for size in 1..=8 {
            for arity in 0..=2 {
                let stream_count = collect(
                    size,
                    arity,
                    true,
                    PruningOpts::default().with_flags("min_trivial"),
                )
                .len();
                let count = count_grf(
                    size,
                    arity,
                    true,
                    PruningOpts::default().with_flags("min_trivial"),
                );
                assert_eq!(
                    count, stream_count,
                    "count/stream mismatch at size={size} arity={arity} skip_min_trivial_zero"
                );
            }
        }
    }

    #[test]
    fn test_skip_min_trivial_never_more_than_full() {
        for size in 1..=8 {
            for arity in 0..=2 {
                let full = collect(size, arity, true, PruningOpts::default()).len();
                let pruned = collect(
                    size,
                    arity,
                    true,
                    PruningOpts::default().with_flags("min_trivial"),
                )
                .len();
                assert!(
                    pruned <= full,
                    "skip_min_trivial_zero produced more at size={size} arity={arity}"
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
                    for opts in [
                        PruningOpts::default(),
                        PruningOpts::default().with_flags("comp_zero"),
                        PruningOpts::default().with_flags("comp_proj"),
                        PruningOpts::default().with_flags("comp_zero,comp_proj"),
                        PruningOpts::default().with_flags("comp_assoc"),
                        PruningOpts::default().with_flags("rec_zero_base"),
                        PruningOpts::default().with_flags("rec_zero_arg"),
                        PruningOpts::default(),
                    ] {
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

    // --- rec_step_p2 ---

    #[test]
    fn test_rec_step_p2_removes_specific_form() {
        // C(R(P(1,1),P(3,2)), P(2,1), P(2,1)): head R(P(1,1),P(3,2)) has arity 2 (m=2),
        // step is P(3,2). Equivalent to C(P(1,1), P(2,1)) which is strictly smaller.
        let full = collect(6, 2, false, PruningOpts::default());
        let pruned = collect(
            6,
            2,
            false,
            PruningOpts::default().with_flags("rec_step_p2"),
        );
        let target = "C(R(P(1,1),P(3,2)),P(2,1),P(2,1))".parse::<Grf>().unwrap();
        assert!(full.iter().any(|g| *g == target), "must exist in full set");
        assert!(
            !pruned.iter().any(|g| *g == target),
            "C(R(g,P2),...) with m=2 should be pruned by rec_step_p2"
        );
    }

    #[test]
    fn test_rec_step_p2_removes_m1_form() {
        // C(R(Z0,P(2,2)), P(1,1)): m=1. R(Z0,P(2,2)) ignores its arg and returns 0,
        // so the whole Comp ≡ Z1. Should be pruned.
        let full = collect(5, 1, false, PruningOpts::default());
        let pruned = collect(
            5,
            1,
            false,
            PruningOpts::default().with_flags("rec_step_p2"),
        );
        let target = "C(R(Z0,P(2,2)),P(1,1))".parse::<Grf>().unwrap();
        assert!(full.iter().any(|g| *g == target), "must exist in full set");
        assert!(
            !pruned.iter().any(|g| *g == target),
            "C(R(g,P2), h) with m=1 should also be pruned by rec_step_p2"
        );
    }

    #[test]
    fn test_rec_step_p2_keeps_non_p2_step() {
        // C(R(P(1,1),P(3,1)), P(2,1), P(2,2)): step is P(3,1) (counter), not P2. NOT pruned.
        // R(P(1,1),P(3,1)) has arity 2, so it heads a Comp with m=2. Size = 1+1+1=3.
        // Full Comp size = 1+3+1+1 = 6, arity 2.
        let pruned = collect(
            6,
            2,
            false,
            PruningOpts::default().with_flags("rec_step_p2"),
        );
        let target = "C(R(P(1,1),P(3,1)),P(2,1),P(2,2))".parse::<Grf>().unwrap();
        assert!(
            pruned.iter().any(|g| *g == target),
            "C(R(g,P(k,1)),...) should not be pruned by rec_step_p2 (step is P1, not P2)"
        );
    }

    #[test]
    fn test_rec_step_p2_never_more_than_full() {
        for size in 1..=8 {
            for arity in 0..=3 {
                let full = collect(size, arity, false, PruningOpts::default()).len();
                let pruned = collect(
                    size,
                    arity,
                    false,
                    PruningOpts::default().with_flags("rec_step_p2"),
                )
                .len();
                assert!(
                    pruned <= full,
                    "rec_step_p2 produced more GRFs at size={size} arity={arity}"
                );
            }
        }
    }

    #[test]
    #[should_panic(expected = "'rec_step_p2'")]
    fn count_grf_panics_on_rec_step_p2() {
        count_grf(
            5,
            1,
            false,
            PruningOpts::default().with_flags("rec_step_p2"),
        );
    }

    // --- rec_proj_base ---

    #[test]
    fn test_rec_proj_base_removes_p2_step() {
        // R(P(1,1), P(3,2)): h = P(3,2) echoes acc → result = base = x₁ ≡ P(2,2).
        let full = collect(3, 2, false, PruningOpts::default());
        let pruned = collect(
            3,
            2,
            false,
            PruningOpts::default().with_flags("rec_proj_base"),
        );
        let target = "R(P(1,1),P(3,2))".parse::<Grf>().unwrap();
        assert!(full.iter().any(|g| *g == target), "must exist in full set");
        assert!(
            !pruned.iter().any(|g| *g == target),
            "R(P_i,P2) should be pruned"
        );
    }

    #[test]
    fn test_rec_proj_base_removes_base_echo() {
        // R(P(1,1), P(3,3)): h = P(3,3) returns x₁ = base ≡ P(2,2).
        let full = collect(3, 2, false, PruningOpts::default());
        let pruned = collect(
            3,
            2,
            false,
            PruningOpts::default().with_flags("rec_proj_base"),
        );
        let target = "R(P(1,1),P(3,3))".parse::<Grf>().unwrap();
        assert!(full.iter().any(|g| *g == target), "must exist in full set");
        assert!(
            !pruned.iter().any(|g| *g == target),
            "R(P_i,P_{{i+2}}) should be pruned"
        );
    }

    #[test]
    fn test_rec_proj_base_keeps_non_matching() {
        // R(P(1,1), P(3,1)): h = P(3,1) returns the counter, not acc or base. NOT pruned.
        let pruned = collect(
            3,
            2,
            false,
            PruningOpts::default().with_flags("rec_proj_base"),
        );
        let target = "R(P(1,1),P(3,1))".parse::<Grf>().unwrap();
        assert!(
            pruned.iter().any(|g| *g == target),
            "R(P,P1) should not be pruned"
        );
    }

    #[test]
    fn test_rec_proj_base_never_more_than_full() {
        for size in 1..=8 {
            for arity in 0..=3 {
                let full = collect(size, arity, false, PruningOpts::default()).len();
                let pruned = collect(
                    size,
                    arity,
                    false,
                    PruningOpts::default().with_flags("rec_proj_base"),
                )
                .len();
                assert!(
                    pruned <= full,
                    "rec_proj_base produced more GRFs at size={size} arity={arity}"
                );
            }
        }
    }

    #[test]
    fn test_rec_proj_base_count_matches_stream() {
        let opts = PruningOpts::default().with_flags("rec_proj_base");
        for size in 1..=9 {
            for arity in 0..=3 {
                let streamed = collect(size, arity, false, opts).len();
                let counted = count_grf(size, arity, false, opts);
                assert_eq!(
                    counted, streamed,
                    "count/stream mismatch with rec_proj_base at size={size} arity={arity}"
                );
            }
        }
    }

    // --- skip_comp_not_rnf ---

    #[test]
    fn test_skip_comp_not_rnf_phase1_removes_unused_arg_head() {
        // Phase 1: C(P(2,2), h1, h2) — head P(2,2) uses only arg 2 of 2, so it's pruned.
        // The canonical equivalent P(2,2) = P(1,1) has arity 1, enumerated as C(P(1,1), h2).
        // C(P(2,2), Z2, Z2): size = 1+1+1+1 = 4, arity 2.
        let full = collect(4, 2, false, PruningOpts::default());
        let pruned = collect(4, 2, false, PruningOpts::default().with_flags("comp_rnf"));
        let bad = "C(P(2,2),Z2,Z2)".parse::<Grf>().unwrap();
        assert!(full.iter().any(|g| *g == bad), "must exist without pruning");
        assert!(
            !pruned.iter().any(|g| *g == bad),
            "P(2,2) as head has unused arg 1 → pruned"
        );
    }

    #[test]
    fn test_skip_comp_not_rnf_phase1_keeps_all_args_used() {
        // R(P(1,1), C(S,P(3,2))) = add, arity 2, uses both args 1 and 2. Must survive.
        let pruned = collect(8, 2, false, PruningOpts::default().with_flags("comp_rnf"));
        let add_head = "C(R(P(1,1),C(S,P(3,2))),P(2,1),P(2,2))"
            .parse::<Grf>()
            .unwrap();
        assert!(
            pruned.iter().any(|g| *g == add_head),
            "add as Comp head (uses both args) must not be pruned"
        );
    }

    #[test]
    fn test_skip_comp_not_rnf_phase2_removes_noncanonical_perm() {
        // R(P(2,2), P(4,3)): arity 3, uses all 3 args, but canonical_arg_order = [1,3,2].
        //   Counter (outer 1) first, then base P(2,2) reveals outer 3, then step P(4,3)
        //   reveals outer 2. Non-canonical → should be pruned as Comp head.
        // C(R(P(2,2),P(4,3)), Z3, Z3, Z3): size = 1+3+1+1+1 = 7, arity 3.
        let full = collect(7, 3, false, PruningOpts::default());
        let pruned = collect(7, 3, false, PruningOpts::default().with_flags("comp_rnf"));
        let non_canon = "C(R(P(2,2),P(4,3)),Z3,Z3,Z3)".parse::<Grf>().unwrap();
        assert!(
            full.iter().any(|g| *g == non_canon),
            "must exist without pruning"
        );
        assert!(
            !pruned.iter().any(|g| *g == non_canon),
            "non-canonical Rec head should be pruned by Phase 2"
        );
    }

    #[test]
    fn test_skip_comp_not_rnf_never_more_than_full() {
        for size in 1..=8 {
            for arity in 0..=3 {
                let full = collect(size, arity, false, PruningOpts::default()).len();
                let pruned = collect(
                    size,
                    arity,
                    false,
                    PruningOpts::default().with_flags("comp_rnf"),
                )
                .len();
                assert!(
                    pruned <= full,
                    "skip_comp_not_rnf produced more GRFs at size={size} arity={arity}"
                );
            }
        }
    }

    #[test]
    #[should_panic(expected = "'comp_rnf'")]
    fn count_grf_panics_on_skip_comp_not_rnf() {
        count_grf(5, 1, false, PruningOpts::default().with_flags("comp_rnf"));
    }
}
