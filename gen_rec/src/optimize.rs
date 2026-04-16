use crate::grf::Grf;

/// Rewires `f` to a new arity context.
///
/// `new_arity` is the arity of the resulting function.
/// `rewiring[i-1]` gives the new 1-based index for old parameter `i`.
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

        Grf::Proj(_, i) => Some(Grf::Proj(new_arity, rewiring[i - 1])),

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
            //   "Rest" variables must map to slots >= 2 (slot 1 belongs to the counter).
            let new_arity_g = new_arity.checked_sub(1)?;
            let rewiring_for_g: Vec<usize> = (1..=k)
                .map(|i| {
                    let j = rewiring[i];
                    if j >= 2 {
                        Some(j - 1)
                    } else {
                        None // rest var mapped into counter slot — invalid
                    }
                })
                .collect::<Option<Vec<_>>>()?;

            // Rewiring for step function h (arity k+2 → new_arity + 1):
            //   h's param 1  =  n_prev           → stays at slot 1
            //   h's param 2  =  recursive result → stays at slot 2
            //   h's param m (m >= 3)  =  f's param m-1  →  rewiring[m-2] + 1
            //   (the +1 shift makes room for the two synthetic leading slots)
            let new_arity_h = new_arity + 1;
            let mut rewiring_for_h = vec![1usize, 2usize];
            for m in 3..=(k + 2) {
                rewiring_for_h.push(rewiring[m - 2] + 1);
            }

            let new_g = inline_proj(g, new_arity_g, &rewiring_for_g)?;
            let new_h = inline_proj(h, new_arity_h, &rewiring_for_h)?;
            Some(Grf::Rec(Box::new(new_g), Box::new(new_h)))
        }

        Grf::Min(inner) => {
            // f = M(inner) where inner has arity f.arity() + 1.
            // inner's param 1  =  search variable (synthetic) → stays at slot 1
            // inner's param m (m >= 2)  =  f's param m-1  →  rewiring[m-2] + 1
            // (same +1 shift pattern as the "rest" vars in Rec's step function)
            let new_arity_inner = new_arity + 1;
            let mut rewiring_for_inner = vec![1usize];
            for &j in rewiring.iter() {
                rewiring_for_inner.push(j + 1);
            }

            let new_inner = inline_proj(inner, new_arity_inner, &rewiring_for_inner)?;
            Some(Grf::Min(Box::new(new_inner)))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! grf {
        ($s:expr) => {
            $s.parse::<Grf>().unwrap()
        };
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
            let f = grf!(s);
            let new_arity = f.arity();
            assert_eq!(
                inline_proj(&f, new_arity, rw),
                Some(f.clone()),
                "identity rewiring changed {s}"
            );
        }
    }
}
