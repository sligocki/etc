use crate::fingerprint::FingerprintDb;
use crate::grf::Grf;

// ---------------------------------------------------------------------------
// Inline-proj constraint system
// ---------------------------------------------------------------------------

/// Per-slot constraint derived from a GRF's structure.
///
/// Describes which values the corresponding rewiring slot may take for
/// `inline_proj(f, k, rewiring)` to succeed.  All constraints are on
/// 1-based slot indices (0 = constant-zero slot).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SlotConstraint {
    /// Any value is allowed.
    Free,
    /// Must equal exactly this value.
    Required(usize),
    /// Must not equal any value whose bit is set (bit `i` = value `i` forbidden).
    Forbidden(u64),
    /// No valid value exists (conflicting constraints).
    Infeasible,
}

impl SlotConstraint {
    fn allows(&self, val: usize) -> bool {
        match self {
            Self::Free => true,
            Self::Required(v) => val == *v,
            Self::Forbidden(mask) => val >= 64 || (mask >> val) & 1 == 0,
            Self::Infeasible => false,
        }
    }

    fn merge(self, other: Self) -> Self {
        match (self, other) {
            (Self::Infeasible, _) | (_, Self::Infeasible) => Self::Infeasible,
            (Self::Free, x) | (x, Self::Free) => x,
            (Self::Required(a), Self::Required(b)) => {
                if a == b { Self::Required(a) } else { Self::Infeasible }
            }
            (Self::Required(a), Self::Forbidden(mask)) | (Self::Forbidden(mask), Self::Required(a)) => {
                if a < 64 && (mask >> a) & 1 != 0 { Self::Infeasible } else { Self::Required(a) }
            }
            (Self::Forbidden(a), Self::Forbidden(b)) => Self::Forbidden(a | b),
        }
    }

    /// Lift a constraint on `g`'s inner rewiring to an outer rewiring constraint.
    ///
    /// `g` sees `inner = if outer == 0 { 0 } else { outer - 1 }`.
    /// `outer == 1` is already ruled out by the Rec forbidden-slot constraint,
    /// but we still produce `Infeasible` if Required(v) would need outer=1.
    fn from_g_base(self) -> Self {
        match self {
            Self::Free => Self::Free,
            Self::Required(0) => Self::Required(0),
            Self::Required(v) => Self::Required(v + 1),
            // bit 0 → outer ≠ 0 (bit 0); bit b≥1 → outer ≠ b+1 (bit b+1)
            // new = (mask & 1) | ((mask >> 1) << 2)
            Self::Forbidden(mask) => Self::Forbidden((mask & 1) | ((mask >> 1) << 2)),
            Self::Infeasible => Self::Infeasible,
        }
    }

    /// Lift a constraint on `h_inner`/`Min`'s inner rewiring to an outer rewiring constraint.
    ///
    /// Inner sees `inner = if outer == 0 { 0 } else { outer + 1 }`.
    /// The inner value is never 1, so Required(1) is infeasible.
    fn from_h_step(self) -> Self {
        match self {
            Self::Free => Self::Free,
            Self::Required(0) => Self::Required(0),
            Self::Required(1) => Self::Infeasible, // inner never equals 1
            Self::Required(v) => Self::Required(v - 1),
            // bit 0 → outer ≠ 0 (bit 0); bit 1 → always satisfied (skip); bit b≥2 → outer ≠ b-1 (bit b-1)
            // new = (mask & 1) | ((mask >> 2) << 1)
            Self::Forbidden(mask) => Self::Forbidden((mask & 1) | ((mask >> 2) << 1)),
            Self::Infeasible => Self::Infeasible,
        }
    }
}

/// Precomputed constraints for `inline_proj` rewiring validity, built bottom-up.
///
/// Replaces the O(f.size()) traversal of `inline_proj` with an O(arity) check
/// per candidate rewiring, after an O(f.size()) one-time build cost.
#[derive(Clone, Debug)]
pub struct InlineConstraints {
    /// Per-slot constraint, indexed 0..f.arity().
    pub slots: Vec<SlotConstraint>,
    /// If `Some(k)`, `inline_proj` requires `new_arity == k`.
    pub requires_new_arity: Option<usize>,
}

impl InlineConstraints {
    fn infeasible(arity: usize) -> Self {
        Self {
            slots: vec![SlotConstraint::Infeasible; arity],
            requires_new_arity: None,
        }
    }

    /// O(arity) check replacing `inline_proj(f, new_arity, rewiring).is_some()`.
    pub fn allows(&self, rewiring: &[usize], new_arity: usize) -> bool {
        if self.requires_new_arity.is_some_and(|a| a != new_arity) {
            return false;
        }
        self.slots.iter().zip(rewiring).all(|(c, &v)| c.allows(v))
    }

    fn merge_arity_req(
        a: Option<usize>,
        b: Option<usize>,
        slots: &mut Vec<SlotConstraint>,
    ) -> Option<usize> {
        match (a, b) {
            (None, x) | (x, None) => x,
            (Some(x), Some(y)) if x == y => Some(x),
            _ => {
                // Conflicting arity requirements → mark everything infeasible.
                for s in slots.iter_mut() { *s = SlotConstraint::Infeasible; }
                None
            }
        }
    }
}

/// Build `InlineConstraints` for `f` bottom-up in O(f.size()).
pub fn compute_inline_constraints(f: &Grf) -> InlineConstraints {
    let arity = f.arity();
    match f {
        Grf::Zero(_) | Grf::Proj(_, _) => InlineConstraints {
            slots: vec![SlotConstraint::Free; arity],
            requires_new_arity: None,
        },

        Grf::Succ => InlineConstraints {
            slots: vec![SlotConstraint::Required(1)],
            requires_new_arity: Some(1),
        },

        Grf::Comp(_, gs, k) => {
            let mut slots = vec![SlotConstraint::Free; *k];
            let mut req_arity: Option<usize> = None;
            for g in gs {
                let c = compute_inline_constraints(g);
                req_arity = InlineConstraints::merge_arity_req(req_arity, c.requires_new_arity, &mut slots);
                for (s, gc) in slots.iter_mut().zip(c.slots) {
                    let old = std::mem::replace(s, SlotConstraint::Free);
                    *s = old.merge(gc);
                }
            }
            InlineConstraints { slots, requires_new_arity: req_arity }
        }

        Grf::Rec(g, h_inner) => {
            // f = R(g, h_inner), arity = k where g.arity()=k-1, h_inner.arity()=k+1.
            let k = arity;
            let mut slots = vec![SlotConstraint::Free; k];

            // Counter (slot 0) must stay at 1.
            slots[0] = SlotConstraint::Required(1);
            // Rest slots (1..k) must not be 1.
            for s in slots[1..].iter_mut() {
                *s = SlotConstraint::Forbidden(1u64 << 1);
            }

            let gc = compute_inline_constraints(g);
            let hc = compute_inline_constraints(h_inner);

            // h_inner's synthetic slots 0 and 1 are fixed to 1 and 2.
            // If h_inner's constraints on those are unsatisfiable, the whole thing fails.
            let h0_ok = hc.slots.first().map_or(true, |c| c.allows(1));
            let h1_ok = hc.slots.get(1).map_or(true, |c| c.allows(2));
            if !h0_ok || !h1_ok {
                return InlineConstraints::infeasible(k);
            }

            // Propagate g's per-slot constraints: g slot j → outer slot j+1.
            let mut req_arity = gc.requires_new_arity.map(|a| a + 1);
            for (j, c) in gc.slots.into_iter().enumerate() {
                let outer = j + 1;
                let derived = c.from_g_base();
                let old = std::mem::replace(&mut slots[outer], SlotConstraint::Free);
                slots[outer] = old.merge(derived);
            }

            // Propagate h_inner's per-slot constraints: h_inner slot j+2 → outer slot j+1.
            let h_req_arity = hc.requires_new_arity.map(|a| a.saturating_sub(1));
            req_arity = InlineConstraints::merge_arity_req(req_arity, h_req_arity, &mut slots);
            for (j, c) in hc.slots.into_iter().skip(2).enumerate() {
                let outer = j + 1;
                if outer >= k { break; }
                let derived = c.from_h_step();
                let old = std::mem::replace(&mut slots[outer], SlotConstraint::Free);
                slots[outer] = old.merge(derived);
            }

            InlineConstraints { slots, requires_new_arity: req_arity }
        }

        Grf::Min(inner) => {
            // f = M(inner), arity = k where inner.arity() = k+1.
            // inner's slot 0 is fixed synthetic search var → rewiring_for_inner[0] = 1.
            let ic = compute_inline_constraints(inner);
            let mut slots = vec![SlotConstraint::Free; arity];

            if ic.slots.first().map_or(false, |c| !c.allows(1)) {
                return InlineConstraints::infeasible(arity);
            }

            // inner slot j+1 → outer slot j.
            let req_arity = ic.requires_new_arity.map(|a| a.saturating_sub(1));
            for (j, c) in ic.slots.into_iter().skip(1).enumerate() {
                if j >= arity { break; }
                slots[j] = c.from_h_step();
            }

            InlineConstraints { slots, requires_new_arity: req_arity }
        }
    }
}

/// Rewires `f` to inline `Proj` and `Zero` args specified in `rewiring`.
///
/// `new_arity` is the arity of the resulting function.
/// `rewiring[i-1]` gives the new 1-based index for old parameter `i`, or `0` to
/// indicate that parameter `i` is a constant zero (never drawn from inputs).
/// `rewiring.len()` must equal `f.arity()`.
///
/// Returns `None` if the rewiring is structurally incompatible:
/// - `Succ` when `new_arity != 1` or the single param doesn't map to 1.
/// - `Rec` when the counter (first input) is not kept at position 1, or when
///   a "rest" variable is rewired into the counter slot.
pub fn inline_proj(f: &Grf, new_arity: usize, rewiring: &[usize]) -> Option<Grf> {
    debug_assert_eq!(rewiring.len(), f.arity());
    match f {
        Grf::Zero(_) => Some(Grf::Zero(new_arity)),

        // Succ has a fixed 1-arity signature; the rewiring must be a no-op.
        Grf::Succ => {
            if new_arity == 1 && rewiring == [1] {
                Some(Grf::Succ)
            } else {
                None
            }
        }

        Grf::Proj(_, i) => {
            let j = rewiring[i - 1];
            if j == 0 {
                Some(Grf::Zero(new_arity))
            } else {
                Some(Grf::Proj(new_arity, j))
            }
        }

        // Each argument gi has the same outer arity as f, so apply the same rewiring.
        // The head h is fed by the outputs of gi and never sees the outer params directly.
        Grf::Comp(h, gs, _) => {
            let new_gs = gs
                .iter()
                .map(|g| inline_proj(g, new_arity, rewiring))
                .collect::<Option<Vec<_>>>()?;
            Some(Grf::Comp(h.clone(), new_gs, new_arity))
        }

        Grf::Rec(g, h) => {
            // f = R(g, h) where g has arity k and h has arity k+2, f has arity k+1.
            // The counter (f's param 1) must remain at slot 1; otherwise the recursion
            // structure breaks down and we cannot inline.
            if rewiring[0] != 1 {
                return None;
            }

            let k = g.arity();

            // Rewiring for base case g (arity k → new_arity - 1):
            //   g's param i  =  f's param i+1  →  new index rewiring[i] - 1
            //   "Rest" variables must map to slots >= 2 (slot 1 belongs to the counter),
            //   or to 0 (constant zero — always safe, doesn't touch the counter slot).
            let new_arity_g = new_arity.checked_sub(1)?;
            let rewiring_for_g: Vec<usize> = (1..=k)
                .map(|i| {
                    let j = rewiring[i];
                    if j == 0 {
                        Some(0) // constant zero — never conflicts with counter
                    } else if j >= 2 {
                        Some(j - 1)
                    } else {
                        None // rest var mapped into counter slot — invalid
                    }
                })
                .collect::<Option<Vec<_>>>()?;

            // Rewiring for step function h (arity k+2 → new_arity + 1):
            //   h's param 1  =  n_prev           → stays at slot 1
            //   h's param 2  =  recursive result → stays at slot 2
            //   h's param m (m >= 3)  =  f's param m-1  →  rewiring[m-2] + 1, or 0 if zero
            //   (the +1 shift makes room for the two synthetic leading slots)
            let new_arity_h = new_arity + 1;
            let mut rewiring_for_h = vec![1usize, 2usize];
            for m in 3..=(k + 2) {
                let j = rewiring[m - 2];
                rewiring_for_h.push(if j == 0 { 0 } else { j + 1 });
            }

            let new_g = inline_proj(g, new_arity_g, &rewiring_for_g)?;
            let new_h = inline_proj(h, new_arity_h, &rewiring_for_h)?;
            Some(Grf::Rec(Box::new(new_g), Box::new(new_h)))
        }

        Grf::Min(inner) => {
            // f = M(inner) where inner has arity f.arity() + 1.
            // inner's param 1  =  search variable (synthetic) → stays at slot 1
            // inner's param m (m >= 2)  =  f's param m-1  →  rewiring[m-2] + 1, or 0 if zero
            // (same +1 shift pattern as the "rest" vars in Rec's step function)
            let new_arity_inner = new_arity + 1;
            let mut rewiring_for_inner = vec![1usize];
            for &j in rewiring.iter() {
                rewiring_for_inner.push(if j == 0 { 0 } else { j + 1 });
            }

            let new_inner = inline_proj(inner, new_arity_inner, &rewiring_for_inner)?;
            Some(Grf::Min(Box::new(new_inner)))
        }
    }
}

/// Walks the GRF tree and inlines Proj and Zero arguments wherever possible.
///
/// At each `Comp(h, gs, k)` node where every `gi` is a `Proj` or `Zero`, the composition
/// is replaced by `inline_proj(h, k, rewiring)` (which always produces a smaller
/// result).  The walk continues recursively into the inlined result so that newly
/// exposed opportunities are caught.
///
/// Returns the optimized GRF, or the original unchanged if no opportunity was found.
pub fn opt_inline_proj(f: Grf) -> Grf {
    match f {
        // Atoms have no sub-expressions to descend into.
        Grf::Zero(_) | Grf::Succ | Grf::Proj(_, _) => f,

        Grf::Comp(h, gs, k) => {
            // Collect the rewiring if every argument is a Proj or Zero.
            // Proj(_, i) → slot i (1-based); Zero(_) → 0 (constant zero).
            let rewiring: Option<Vec<usize>> = gs
                .iter()
                .map(|g| match g {
                    Grf::Proj(_, i) => Some(*i),
                    Grf::Zero(_) => Some(0),
                    _ => None,
                })
                .collect();

            // rewiring == Some(rw) means that all gs were projections
            if let Some(rw) = rewiring {
                if let Some(inlined) = inline_proj(&h, k, &rw) {
                    // Inlining always shrinks size; recurse into the result to
                    // catch any newly exposed opportunities.
                    return opt_inline_proj(inlined);
                }
            }

            // Can't inline at this level — recurse into the head and each arg.
            let new_h = opt_inline_proj(*h);
            let new_gs = gs.into_iter().map(opt_inline_proj).collect();
            Grf::Comp(Box::new(new_h), new_gs, k)
        }

        Grf::Rec(g, h) => Grf::Rec(
            Box::new(opt_inline_proj(*g)),
            Box::new(opt_inline_proj(*h)),
        ),

        Grf::Min(inner) => Grf::Min(Box::new(opt_inline_proj(*inner))),
    }
}

/// Optimizes a GRF by replacing subexpressions with smaller equivalents from `db`.
///
/// Traversal is top-down: at each node, check the DB first. If a smaller equivalent
/// is found, return it immediately (the subtree is replaced wholesale — no need to
/// recurse into children that are being thrown away). If no match, recurse into
/// children and reconstruct.
///
/// The DB only contains fully-computed fingerprints, so every match is guaranteed
/// to be a correct functional equivalence.
pub fn opt_fingerprint(f: Grf, db: &FingerprintDb) -> Grf {
    // Top-down: try to replace the whole node before touching children.
    if let Some(smaller) = db.lookup_smaller(&f) {
        return smaller.clone();
    }

    // No match at this level — recurse into children.
    match f {
        Grf::Zero(_) | Grf::Succ | Grf::Proj(_, _) => f,

        Grf::Comp(h, gs, k) => {
            let new_h = opt_fingerprint(*h, db);
            let new_gs = gs.into_iter().map(|g| opt_fingerprint(g, db)).collect();
            Grf::Comp(Box::new(new_h), new_gs, k)
        }

        Grf::Rec(g, h) => Grf::rec(opt_fingerprint(*g, db), opt_fingerprint(*h, db)),

        Grf::Min(inner) => Grf::min(opt_fingerprint(*inner, db)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::grf;

    // ── InlineConstraints agrees with inline_proj ─────────────────────────────

    /// For every GRF h of size ≤ max_size and every arity-m P/Z rewiring into a
    /// new_arity-k context, verify that `compute_inline_constraints(h).allows(r, k)`
    /// matches `inline_proj(h, k, r).is_some()`.
    fn check_constraints_vs_inline_proj(max_size: usize, max_arity: usize) {
        use crate::enumerate::stream_grf;
        use crate::pruning::PruningOpts;

        for h_size in 1..=max_size {
            for m in 0..=max_arity {
                stream_grf(h_size, m, true, PruningOpts::none(), &mut |h| {
                    let ic = compute_inline_constraints(h);
                    for k in 0..=max_arity {
                        // All (k+1)^m rewirings into new_arity k.
                        let n_rewirings = (k + 1).pow(m as u32);
                        for idx in 0..n_rewirings {
                            let rw: Vec<usize> = (0..m)
                                .map(|d| (idx / (k + 1).pow(d as u32)) % (k + 1))
                                .collect();
                            let expected = inline_proj(h, k, &rw).is_some();
                            let got = ic.allows(&rw, k);
                            assert_eq!(
                                got, expected,
                                "constraints vs inline_proj mismatch:\n  h={h}\n  k={k} rw={rw:?}\n  constraints={:?}\n  expected={expected} got={got}",
                                ic.slots
                            );
                        }
                    }
                });
            }
        }
    }

    #[test]
    fn constraints_agree_with_inline_proj_small() {
        check_constraints_vs_inline_proj(5, 3);
    }

    #[test]
    #[ignore]
    fn constraints_agree_with_inline_proj_larger() {
        check_constraints_vs_inline_proj(7, 4);
    }

    // ── atoms ────────────────────────────────────────────────────────────────

    #[test]
    fn zero() {
        assert_eq!(
            inline_proj(&grf!("Z2"), 5, &[1, 3]),
            Some(grf!("Z5"))
        );
        // Z0 has arity 0, empty rewiring, new_arity can be anything.
        assert_eq!(inline_proj(&grf!("Z0"), 0, &[]), Some(grf!("Z0")));
        assert_eq!(inline_proj(&grf!("Z0"), 3, &[]), Some(grf!("Z3")));
    }

    #[test]
    fn succ() {
        assert_eq!(inline_proj(&grf!("S"), 1, &[1]), Some(grf!("S")));
        assert_eq!(inline_proj(&grf!("S"), 2, &[1]), None);
        assert_eq!(inline_proj(&grf!("S"), 1, &[2]), None);
    }

    #[test]
    fn proj_remaps() {
        // P(3,2) with rewiring [4,2,1] → param 2 maps to new index 2 → P(5,2)
        assert_eq!(
            inline_proj(&grf!("P(3,2)"), 5, &[4, 2, 1]),
            Some(grf!("P(5,2)"))
        );
    }

    // ── composition ──────────────────────────────────────────────────────────

    #[test]
    fn comp_rewires_args_not_head() {
        // C(S, P(2,1)) with new_arity=3, rewiring=[1,3]
        // P(2,1) → P(3, rewiring[0]) = P(3,1); head S is untouched.
        assert_eq!(
            inline_proj(&grf!("C(S,P(2,1))"), 3, &[1, 3]),
            Some(grf!("C(S,P(3,1))"))
        );
    }

    #[test]
    fn comp_multi_arg() {
        assert_eq!(
            inline_proj(&grf!("C(P(2,1),P(3,1),P(3,3))"), 4, &[4, 2, 4]),
            Some(grf!("C(P(2,1),P(4,4),P(4,4))"))
        );
    }

    // ── recursion ────────────────────────────────────────────────────────────

    #[test]
    fn rec_projection_inline_example() {
        // The motivating example from the problem description:
        //   f = R(Z1, P(3,3))   — \xy. if x=0 then 0 else y  (arity 2)
        //   g = C(f, P(4,1), P(4,4)) — \xyzw. if x=0 then 0 else w
        // Inlining the projections into f with rewiring [1,4]:
        //   f* = R(Z3, P(5,5))                       (arity 4)
        assert_eq!(
            inline_proj(&grf!("R(Z1,P(3,3))"), 4, &[1, 4]),
            Some(grf!("R(Z3,P(5,5))"))
        );
    }

    #[test]
    fn rec_fails_counter_remapped() {
        // rewiring[0] = 2 ≠ 1 → counter would move, must fail.
        assert_eq!(
            inline_proj(&grf!("R(Z1,P(3,3))"), 4, &[2, 4]),
            None
        );
    }

    #[test]
    fn rec_fails_rest_var_in_counter_slot() {
        // rewiring[1] = 1 → rest variable mapped into counter slot.
        assert_eq!(
            inline_proj(&grf!("R(Z1,P(3,3))"), 3, &[1, 1]),
            None
        );
    }

    #[test]
    fn rec_plus_drops_middle_arg() {
        // plus = R(P(1,1), C(S, P(3,2)))   — arity 2, plus(n, x) = n + x
        // Rewire with [1, 3]: keep n at slot 1, move x to slot 3 (new_arity = 3).
        // Expected: R(P(2,2), C(S, P(4,2)))
        //   base: P(1,1) rewired with [2] → P(2,2)  (new_arity_g=2)
        //   step: C(S,P(3,2)) rewired with [1,2,4]:
        //         P(3,2) → P(4, rewiring_for_h[1]) = P(4,2)  ✓
        let plus = grf!("R(P(1,1),C(S,P(3,2)))");
        assert_eq!(
            inline_proj(&plus, 3, &[1, 3]),
            Some(grf!("R(P(2,2),C(S,P(4,2)))"))
        );
    }

    // ── minimization ─────────────────────────────────────────────────────────

    #[test]
    fn min_updates_inner_arity() {
        // M(Z2) has arity 1. Rewire with new_arity=3, rewiring=[2].
        // rewiring_for_inner = [1, 2+1] = [1, 3]; inner Z2 → Z4.
        assert_eq!(
            inline_proj(&grf!("M(Z2)"), 3, &[2]),
            Some(grf!("M(Z4)"))
        );
    }

    #[test]
    fn min_rewires_proj() {
        // M(P(2,2)) has arity 1. P(2,2) inside refers to inner's param 2 = f's param 1.
        // Rewire with new_arity=2, rewiring=[3]:
        //   rewiring_for_inner = [1, 3+1] = [1, 4]
        //   P(2,2) → P(3, rewiring_for_inner[1]) = P(3,4)? Wait arity of inner is new+1=3.
        // inline_proj(P(2,2), 3, [1,4]):
        //   P(2,2) → Proj(3, rewiring[2-1]) = Proj(3, rewiring[1]) = Proj(3, 4)
        // Result: M(P(3,4))
        assert_eq!(
            inline_proj(&grf!("M(P(2,2))"), 2, &[3]),
            Some(grf!("M(P(3,4))"))
        );
    }

    // ── identity rewiring ─────────────────────────────────────────────────────

    #[test]
    fn identity_rewiring_is_noop() {
        // An identity rewiring (same arity, params stay put) should reproduce the
        // original structure exactly for each variant.
        let cases: &[(&str, &[usize])] = &[
            ("Z3", &[1, 2, 3]),
            ("P(3,2)", &[1, 2, 3]),
            ("C(S,P(2,1))", &[1, 2]),
            ("R(Z1,P(3,3))", &[1, 2]),
            ("R(P(1,1),C(S,P(3,2)))", &[1, 2]),
            ("M(Z2)", &[1]),
        ];
        for &(s, rw) in cases {
            let f: Grf = s.parse().unwrap();
            let new_arity = f.arity();
            assert_eq!(
                inline_proj(&f, new_arity, rw),
                Some(f.clone()),
                "identity rewiring changed {s}"
            );
        }
    }

    // ── opt_inline_proj ───────────────────────────────────────────────────────

    // Runs `f` and `g` on every input tuple with each element in `0..=max_val`
    // and asserts they produce identical results.
    fn check_equiv(f: &Grf, g: &Grf, max_val: u64) {
        use crate::simulate::simulate;
        let arity = f.arity();
        assert_eq!(arity, g.arity(), "arity mismatch between f and g");
        let count = (max_val + 1).pow(arity as u32);
        for i in 0..count {
            let args: Vec<u64> = (0..arity)
                .map(|d| (i / (max_val + 1).pow(d as u32)) % (max_val + 1))
                .collect();
            let (rf, _) = simulate(f, &args, 100_000);
            let (rg, _) = simulate(g, &args, 100_000);
            assert_eq!(
                rf.into_value(),
                rg.into_value(),
                "mismatch at args {:?}",
                args
            );
        }
    }

    #[test]
    fn opt_motivating_example() {
        // C(R(Z1,P(3,3)), P(4,1), P(4,4)):  \nxyz. if n=0 then 0 else z  (size 6)
        // Should optimize to R(Z3,P(5,5))                                 (size 3)
        let before = grf!("C(R(Z1,P(3,3)),P(4,1),P(4,4))");
        let after = opt_inline_proj(before.clone());
        assert_eq!(after.size(), before.size() - 3, "expected size saving of 3");
        check_equiv(&before, &after, 4);
    }

    #[test]
    fn opt_plus_skip_middle_arg() {
        // C(plus, P(3,1), P(3,3)):  \nyx. n + x  (ignores y)
        // plus = R(P(1,1), C(S,P(3,2)))
        let before = grf!("C(R(P(1,1),C(S,P(3,2))),P(3,1),P(3,3))");
        let after = opt_inline_proj(before.clone());
        assert!(after.size() < before.size(), "size should shrink");
        check_equiv(&before, &after, 5);
    }

    #[test]
    fn opt_atoms_unchanged() {
        // Atoms have nothing to optimize.
        for s in ["S", "Z3", "P(4,2)"] {
            let f: Grf = s.parse().unwrap();
            assert_eq!(opt_inline_proj(f.clone()), f, "atom {s} should not change");
        }
    }

    #[test]
    fn zero_rewiring_in_proj() {
        // P(2,1) with rewiring [0, 2]: param 1 is zeroed → Zero(3)
        assert_eq!(
            inline_proj(&grf!("P(2,1)"), 3, &[0, 2]),
            Some(grf!("Z3"))
        );
        // P(2,2) with rewiring [1, 0]: param 2 is zeroed → Zero(2)
        assert_eq!(
            inline_proj(&grf!("P(2,2)"), 2, &[1, 0]),
            Some(grf!("Z2"))
        );
    }

    #[test]
    fn opt_inline_zero_arg() {
        // C(P(2,1), Z2, P(2,2)): head picks param 1 which is always 0 → Z2
        let before = grf!("C(P(2,1),Z2,P(2,2))");
        let after = opt_inline_proj(before.clone());
        assert_eq!(after, grf!("Z2"));
        check_equiv(&before, &after, 5);
    }

    #[test]
    fn opt_inline_zero_into_rec() {
        // R(Z1, P(3,3)) with all-Proj args where one is Zero:
        // C(R(Z1,P(3,3)), Z3, P(3,2)): n=0 always → always returns 0 (base case Z)
        // Rewiring: [0, 2] (counter → 0 = always-zero → Rec counter is 0 which != 1 → inline fails)
        // So this must NOT inline (counter must stay at slot 1).
        let f = grf!("C(R(Z1,P(3,3)),Z3,P(3,2))");
        // rewiring = [0, 2]; counter slot would be 0, which is rejected
        assert_eq!(inline_proj(&grf!("R(Z1,P(3,3))"), 3, &[0, 2]), None);
        // The opt should leave this Comp but still recurse into children
        let after = opt_inline_proj(f.clone());
        check_equiv(&f, &after, 4);
    }

    #[test]
    fn opt_inline_zero_into_base_case() {
        // R(P(1,1), C(S,P(3,2))) with counter at 1, rest-param zeroed:
        // C(R(P(1,1),C(S,P(3,2))), P(3,1), Z3): rewiring=[1,0]
        // new_arity=3, g=P(1,1) rewired with [0]→ Z2, h=C(S,P(3,2)) rewired with [1,2,0+1=1]?
        // Actually rewiring_for_h for m=3: j=rewiring[1]=0 → 0. So rewiring_for_h=[1,2,0].
        // P(3,2) in h → rewiring_for_h[1] = 2 → P(4,2). C(S,P(3,2)) → C(S,P(4,2)).
        // g: P(1,1) rewired with [0] → Z2.
        // Result: R(Z2, C(S,P(4,2))) which has arity 3.
        let before = grf!("C(R(P(1,1),C(S,P(3,2))),P(3,1),Z3)");
        let after = opt_inline_proj(before.clone());
        assert_eq!(after, grf!("R(Z2,C(S,P(4,2)))"));
        check_equiv(&before, &after, 5);
    }

    #[test]
    fn opt_non_proj_arg_blocks_inlining() {
        // C(P(2,1), S, P(2,2)) — second arg is S (not a Proj); inlining blocked.
        // No other Comp-with-all-Proj exists inside, so the whole tree is unchanged.
        let f = grf!("C(P(2,1),S,P(2,2))");
        assert_eq!(opt_inline_proj(f.clone()), f);
    }

    #[test]
    fn opt_nested_in_rec_step() {
        // R(Z1, C(P(3,3), P(3,1), P(3,2), P(3,3))):
        //   the all-Proj Comp in the step function collapses to P(3,3).
        // Expected: R(Z1, P(3,3))
        let before = grf!("R(Z1,C(P(3,3),P(3,1),P(3,2),P(3,3)))");
        let after = opt_inline_proj(before.clone());
        assert_eq!(after, grf!("R(Z1,P(3,3))"));
        check_equiv(&before, &after, 5);
    }

    #[test]
    fn opt_multi_step() {
        // C(R(Z1, C(P(3,3),P(3,1),P(3,2),P(3,3))), P(4,1), P(4,4)):
        //   Step 1 — outer C inlines its Proj args into the Rec, producing
        //             R(Z3, C(P(3,3), P(5,1), P(5,2), P(5,5))).
        //   Step 2 — the Comp in the step fn collapses to P(5,5).
        //   Final: R(Z3, P(5,5))
        let before = grf!("C(R(Z1,C(P(3,3),P(3,1),P(3,2),P(3,3))),P(4,1),P(4,4))");
        let after = opt_inline_proj(before.clone());
        assert_eq!(after, grf!("R(Z3,P(5,5))"));
        check_equiv(&before, &after, 4);
    }

    #[test]
    fn opt_nested_c_in_c() {
        // C(C(R(Z1,P(3,3)), P(2,1), P(2,2)), P(3,1), P(3,3))
        //   computes (n, x, y) -> if n=0 then 0 else y  (size 9)
        //
        // The two Comps are directly nested: the outer C's HEAD is itself a Comp
        // with all-Proj args.  Optimization proceeds in two sequential passes:
        //
        //   Pass 1 (outer C, args=[P(3,1),P(3,3)]):
        //     inline_proj rewires the inner C's Proj args → P(2,1)->P(3,1), P(2,2)->P(3,3)
        //     intermediate: C(R(Z1,P(3,3)), P(3,1), P(3,3))
        //
        //   Pass 2 (that intermediate C, args=[P(3,1),P(3,3)]):
        //     inline_proj(R(Z1,P(3,3)), 3, [1,3]) → R(Z2, P(4,4))
        //     final: R(Z2, P(4,4))  (size 3, saves 6)
        let before = grf!("C(C(R(Z1,P(3,3)),P(2,1),P(2,2)),P(3,1),P(3,3))");
        let after = opt_inline_proj(before.clone());
        assert_eq!(after, grf!("R(Z2,P(4,4))"));
        check_equiv(&before, &after, 5);
    }

    #[test]
    fn fingerprint_monus2() {
        // Build a DB up to size 8 covering arities 0..=3.
        let db = FingerprintDb::build(8, 3, false, 10_000);

        let pred = grf!("R(Z0, P(2,1))");
        // C(Pred, Pred)
        let before = Grf::comp(pred.clone(), vec![pred]);
        let after = opt_fingerprint(before.clone(), &db);

        assert_eq!(after, grf!("R(Z0, R(Z1, P(3,1)))"));
        assert!(after.size() < before.size());
        check_equiv(&before, &after, 16);
    }

    #[test]
    fn fingerprint_monus2_app() {
        // Build a DB up to size 8 covering arities 0..=3.
        let db = FingerprintDb::build(8, 3, false, 10_000);

        let pred = grf!("R(Z0, P(2,1))");
        // C(Pred, C(Pred, P(3,2)))
        let before = Grf::comp(pred.clone(), vec![Grf::comp(pred, vec![Grf::Proj(3,2)])]);
        let after = opt_fingerprint(before.clone(), &db);

        assert_eq!(after, grf!("C(R(Z0, R(Z1, P(3,1))), P(3,2))"));
        assert!(after.size() < before.size());
        check_equiv(&before, &after, 16);
    }

    #[test]
    fn fingerprint_sgn() {
        // Optimal Sgn is size 4, using M().
        let db = FingerprintDb::build(4, 2, true, 1_000);

        let before = grf!("R(Z0, C(S, Z2))");
        let after = opt_fingerprint(before.clone(), &db);

        assert_eq!(after, grf!("M(R(P(1,1), Z3))"));
        assert!(after.size() < before.size());
        check_equiv(&before, &after, 16);
    }

    #[test]
    fn opt_fingerprint_correct_on_small() {
        // C(S, Z1) computes \x. 1. The DB should contain Z1 -> \x. 0 and
        // C(S,Z1) -> \x. 1. A size-5 GRF like C(S,C(S,Z1)) computes \x. 2,
        // which equals C(S,C(S,Z1)) at size 5 — no smaller form exists without Min.
        // But C(S,R(Z0,P(2,1))) (\x. 1+pred(x)) should reduce to C(S,Z1) for x>0
        // ... actually these compute different functions. Just verify no incorrect
        // replacements are made.
        let db = FingerprintDb::build(6, 1, false, 10_000);

        for s in ["S", "Z1", "P(1,1)", "C(S,Z1)", "C(S,S)", "R(Z0,P(2,1))"] {
            let f: Grf = s.parse().unwrap();
            let opt = opt_fingerprint(f.clone(), &db);
            // Optimized form must be no larger and must compute the same function.
            assert!(opt.size() <= f.size(), "{s}: size grew");
            check_equiv(&f, &opt, 8);
        }
    }

    /// Measures how many GRFs (under ALL_OPTS) have all-P/Z args and are inlineable.
    /// Run with: cargo test --lib optimize::tests::inline_proj_savings -- --ignored --nocapture
    #[test]
    #[ignore]
    fn inline_proj_savings() {
        use crate::enumerate::stream_grf;
        use crate::pruning::PruningOpts;

        let opts = PruningOpts::all();
        println!("{:<6} {:<5} {:<10} {:<10} {:<10} {:<8}",
            "size", "arity", "total", "candidate", "prunable", "pct");

        for arity in 0..=2usize {
            for size in 3..=10 {
                let mut total = 0usize;
                let mut candidate = 0usize;
                let mut prunable = 0usize;

                stream_grf(size, arity, false, opts, &mut |grf| {
                    total += 1;
                    if let Grf::Comp(h, gs, k) = grf {
                        let rewiring: Option<Vec<usize>> = gs.iter().map(|g| match g {
                            Grf::Proj(_, i) => Some(*i),
                            Grf::Zero(_) => Some(0),
                            _ => None,
                        }).collect();
                        if let Some(rw) = rewiring {
                            candidate += 1;
                            if inline_proj(h, *k, &rw).is_some() {
                                prunable += 1;
                            }
                        }
                    }
                });

                let pct = if total > 0 { prunable * 100 / total } else { 0 };
                println!("{:<6} {:<5} {:<10} {:<10} {:<10} {:<8}",
                    size, arity, total, candidate, prunable, format!("{}%", pct));
            }
        }
    }

    #[test]
    fn opt_ack_worm() {
        use crate::example_ack::ack_worm;

        let db = FingerprintDb::build(8, 3, false, 10_000);

        let orig = ack_worm();
        let opt_ip = opt_inline_proj(orig.clone());
        let opt_fp = opt_fingerprint(opt_ip.clone(), &db);

        println!("Original: {}", orig.to_string());
        println!("Opt_IP:   {}", opt_ip.to_string());
        println!("Opt_FP:   {}", opt_fp.to_string());
        println!("Size: {} -> {} -> {}", orig.size(), opt_ip.size(), opt_fp.size());

        assert!(opt_ip.size() < orig.size(),
            "opt_inline_proj should not grow the GRF; before={}, after={}",
            orig.size(),
            opt_ip.size()
        );
        check_equiv(&orig, &opt_ip, 16);

        assert!(opt_fp.size() < opt_ip.size(),
            "opt_fingerprint should not grow the GRF; before={}, after={}",
            opt_ip.size(),
            opt_fp.size()
        );
        check_equiv(&opt_ip, &opt_fp, 16);
    }
}
