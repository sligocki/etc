use crate::grf::Grf;
use rug::Integer;

/// Result of simulating a GRF.
#[derive(Clone, Debug)]
pub enum SimResult {
    /// The function terminated with this value.
    Value(Integer),
    /// The function exceeded the step budget (may or may not terminate with more steps).
    OutOfSteps,
}

impl SimResult {
    pub fn is_value(&self) -> bool {
        matches!(self, SimResult::Value(_))
    }

    pub fn value(&self) -> Option<&Integer> {
        match self {
            SimResult::Value(v) => Some(v),
            SimResult::OutOfSteps => None,
        }
    }

    pub fn into_value(self) -> Option<Integer> {
        match self {
            SimResult::Value(v) => Some(v),
            SimResult::OutOfSteps => None,
        }
    }
}

/// Simulate `grf` applied to `args`, spending at most `max_steps` evaluation steps.
///
/// Returns `(result, steps_taken)`.
///
/// Step counting: every call to `eval` costs 1 step. This naturally captures:
/// - Atoms: 1 step each
/// - C(h, g1..gm): 1 + steps(g1) + ... + steps(gm) + steps(h) steps
/// - R(g,h)(n,...): 1 + steps(g) + n * avg_steps(h) steps
/// - M(f)(...): 1 + N * avg_steps(f) steps where N is iterations until success
pub fn simulate(grf: &Grf, args: &[u64], max_steps: u64) -> (SimResult, u64) {
    let int_args: Vec<Integer> = args.iter().map(|&x| Integer::from(x)).collect();
    let mut steps = 0u64;
    let result = eval(grf, &int_args, &mut steps, max_steps);
    (result, steps)
}

fn eval(grf: &Grf, args: &[Integer], steps: &mut u64, max_steps: u64) -> SimResult {
    if *steps >= max_steps {
        return SimResult::OutOfSteps;
    }
    *steps += 1;

    match grf {
        Grf::Zero(_) => SimResult::Value(Integer::ZERO),

        Grf::Succ => SimResult::Value(Integer::from(&args[0]) + 1u32),

        Grf::Proj(_, i) => SimResult::Value(args[i - 1].clone()),

        Grf::Comp(h, gs, _) => {
            // Evaluate each gi(args), collecting results as new arg list for h.
            let mut h_args: Vec<Integer> = Vec::with_capacity(gs.len());
            for g in gs.iter() {
                match eval(g, args, steps, max_steps) {
                    SimResult::Value(v) => h_args.push(v),
                    other => return other,
                }
            }
            eval(h, &h_args, steps, max_steps)
        }

        Grf::Rec(g, h) => {
            // args = [n, x2, ..., x_{k+1}]
            // R(g,h)(0, rest) = g(rest)
            // R(g,h)(n+1, rest) = h(n, R(g,h)(n, rest), rest)
            // Iteratively: acc = g(rest); for i in 0..n: acc = h(i, acc, rest)
            let n = &args[0];
            let rest = &args[1..];

            let mut acc = match eval(g, rest, steps, max_steps) {
                SimResult::Value(v) => v,
                other => return other,
            };

            let mut i = Integer::ZERO;
            while &i < n {
                // Check step budget before starting next iteration (eval(h) will also check,
                // but this avoids the overhead of building h_args when over budget).
                if *steps >= max_steps {
                    return SimResult::OutOfSteps;
                }
                let mut h_args: Vec<Integer> = Vec::with_capacity(rest.len() + 2);
                h_args.push(i.clone());
                h_args.push(acc);
                h_args.extend_from_slice(rest);

                acc = match eval(h, &h_args, steps, max_steps) {
                    SimResult::Value(v) => v,
                    other => return other,
                };
                i += 1u32;
            }

            SimResult::Value(acc)
        }

        Grf::Min(f) => {
            // M(f)(args) = min{i : f(i, args...) = 0}
            let mut i = Integer::ZERO;
            loop {
                if *steps >= max_steps {
                    return SimResult::OutOfSteps;
                }
                let mut f_args: Vec<Integer> = Vec::with_capacity(args.len() + 1);
                f_args.push(i.clone());
                f_args.extend_from_slice(args);

                match eval(f, &f_args, steps, max_steps) {
                    SimResult::Value(ref v) if *v == 0u32 => return SimResult::Value(i),
                    SimResult::Value(_) => i += 1u32,
                    other => return other,
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::grf::Grf;

fn sim(grf: &Grf, args: &[u64]) -> Option<u64> {
        let (result, _steps) = simulate(grf, args, 1_000_000);
        result.into_value().map(|v| u64::try_from(v).unwrap())
    }

    fn sim_with_steps(grf: &Grf, args: &[u64]) -> (Option<u64>, u64) {
        let (result, steps) = simulate(grf, args, 1_000_000);
        (result.into_value().map(|v| u64::try_from(v).unwrap()), steps)
    }

    #[test]
    fn test_zero() {
        assert_eq!(sim(&Grf::Zero(0), &[]), Some(0));
        assert_eq!(sim(&Grf::Zero(2), &[3, 5]), Some(0));
    }

    #[test]
    fn test_succ() {
        assert_eq!(sim(&Grf::Succ, &[0]), Some(1));
        assert_eq!(sim(&Grf::Succ, &[5]), Some(6));
    }

    #[test]
    fn test_proj() {
        assert_eq!(sim(&Grf::Proj(2, 1), &[3, 5]), Some(3));
        assert_eq!(sim(&Grf::Proj(2, 2), &[3, 5]), Some(5));
        assert_eq!(sim(&Grf::Proj(3, 2), &[1, 2, 3]), Some(2));
    }

    #[test]
    fn test_comp_k0_1() {
        // C(S, Z0)() = S(Z0()) = S(0) = 1
        let f = Grf::comp(Grf::Succ, vec![Grf::Zero(0)]);
        assert_eq!(sim(&f, &[]), Some(1));
    }

    #[test]
    fn test_comp_k0_2() {
        // C(S, C(S, Z0))() = 2
        let k01 = Grf::comp(Grf::Succ, vec![Grf::Zero(0)]);
        let k02 = Grf::comp(Grf::Succ, vec![k01]);
        assert_eq!(sim(&k02, &[]), Some(2));
    }

    #[test]
    fn test_comp_projection_selects_arg() {
        // C(P(2,1), S, Z1)([3]) = P(2,1)(S(3), Z1(3)) = P(2,1)(4, 0) = 4
        let f = Grf::comp(Grf::Proj(2, 1), vec![Grf::Succ, Grf::Zero(1)]);
        assert_eq!(sim(&f, &[3]), Some(4));
    }

    #[test]
    fn test_rec_plus() {
        // Plus = R(P(1,1), C(S, P(3,2)))
        // Plus(n, m) = n + m
        // g = P(1,1): Plus(0, m) = m
        // h = C(S, P(3,2)): Plus(n+1, m) = S(Plus(n, m))
        let g = Grf::Proj(1, 1);
        let h = Grf::comp(Grf::Succ, vec![Grf::Proj(3, 2)]);
        let plus = Grf::Rec(Box::new(g), Box::new(h));

        assert_eq!(sim(&plus, &[0, 0]), Some(0));
        assert_eq!(sim(&plus, &[3, 2]), Some(5));
        assert_eq!(sim(&plus, &[0, 7]), Some(7));
        assert_eq!(sim(&plus, &[4, 4]), Some(8));
    }

    #[test]
    fn test_rec_identity() {
        // R(Z0, C(S, P(3,2)))(n) iterates: acc=0, then acc=acc+1 n times = n
        // Actually this is identity: R(Z0, C(S, P(3,2)))(n) ... no
        // g=Z0 (arity 0), h=C(S,P(3,2)) (arity 3 with k=0 so arity = k+2 = 2... wait)
        // For R(g,h) ∈ GRF_1: g ∈ GRF_0, h ∈ GRF_2
        // R(Z0, P(2,2))(n):
        //   Base: acc = Z0() = 0
        //   i=0..n-1: acc = P(2,2)(i, acc) = acc (unchanged!)
        //   Result: 0 for all n
        // Let's test R(Z0, C(S, P(2,2)))(n) instead:
        //   Base: acc = 0
        //   i=0..n-1: acc = C(S, P(2,2))(i, acc) = S(P(2,2)(i,acc)) = S(acc) = acc+1
        //   Result: n
        let g = Grf::Zero(0);
        let h = Grf::comp(Grf::Succ, vec![Grf::Proj(2, 2)]);
        let identity = Grf::Rec(Box::new(g), Box::new(h));
        assert_eq!(identity.arity(), 1);
        assert_eq!(sim(&identity, &[0]), Some(0));
        assert_eq!(sim(&identity, &[5]), Some(5));
    }

    #[test]
    fn test_min_proj() {
        // M(P(1,1))() = min{i : P(1,1)(i) = 0} = min{i : i = 0} = 0
        let f = Grf::Min(Box::new(Grf::Proj(1, 1)));
        assert_eq!(sim(&f, &[]), Some(0));
    }

    #[test]
    fn test_min_zero() {
        // M(Z1)() = min{i : Z1(i) = 0} = min{i : 0 = 0} = 0
        let f = Grf::Min(Box::new(Grf::Zero(1)));
        assert_eq!(sim(&f, &[]), Some(0));
    }

    #[test]
    fn test_min_succ_diverges() {
        // M(S)() = min{i : S(i) = 0} = min{i : i+1 = 0} = diverges
        let f = Grf::Min(Box::new(Grf::Succ));
        let (result, steps) = simulate(&f, &[], 1000);
        assert!(result.value().is_none());
        assert!(steps >= 1000);
    }

    #[test]
    fn test_step_counting() {
        // Z0(): 1 step
        let (_, steps) = sim_with_steps(&Grf::Zero(0), &[]);
        assert_eq!(steps, 1);

        // C(S, Z0)(): eval(C) = 1, eval(Z0) = 1, eval(S) = 1 → 3 steps
        let f = Grf::comp(Grf::Succ, vec![Grf::Zero(0)]);
        let (_, steps) = sim_with_steps(&f, &[]);
        assert_eq!(steps, 3);
    }

    #[test]
    fn test_rec_steps() {
        // R(Z0, P(2,2))(3): eval(R)=1, eval(Z0)=1, then 3 evals of h → 5 steps
        let g = Grf::Zero(0);
        let h = Grf::Proj(2, 2);
        let r = Grf::Rec(Box::new(g), Box::new(h));
        let (val, steps) = sim_with_steps(&r, &[3]);
        assert_eq!(val, Some(0)); // P(2,2)(i, 0) = 0 for all i (acc never changes from 0)
        // steps: 1 (Rec) + 1 (Z0) + 3 (P(2,2) called 3 times) = 5
        assert_eq!(steps, 5);
    }

    #[test]
    fn test_out_of_steps() {
        // R with large n should exhaust step budget
        let g = Grf::Zero(0);
        let h = Grf::comp(Grf::Succ, vec![Grf::Proj(2, 2)]);
        let r = Grf::Rec(Box::new(g), Box::new(h));
        let (result, steps) = simulate(&r, &[1_000_000], 100);
        assert!(matches!(result, SimResult::OutOfSteps));
        assert!(steps >= 100);
    }

    // -------------------------------------------------------------------------
    // Tri and RepDiag[Tri] champion expressions
    // -------------------------------------------------------------------------

    /// Build Tri = R(Z0, R(S, C(S, P(3,2)))) ∈ GRF_1.
    /// Tri(n) = n*(n+1)/2.
    fn make_tri() -> Grf {
        let inner_h = Grf::Rec(
            Box::new(Grf::Succ),
            Box::new(Grf::comp(Grf::Succ, vec![Grf::Proj(3, 2)])),
        );
        Grf::Rec(Box::new(Grf::Zero(0)), Box::new(inner_h))
    }

    /// Build RepDiag[f] = C(R(S, C(f, P(3,2))), S, S) ∈ GRF_1.
    /// RepDiag[f](x) = f^{x+1}(x+2).
    fn make_rep_diag(f: Grf) -> Grf {
        let step = Grf::comp(f, vec![Grf::Proj(3, 2)]);
        let outer = Grf::Rec(Box::new(Grf::Succ), Box::new(step));
        Grf::comp(outer, vec![Grf::Succ, Grf::Succ])
    }

    /// Build K[n] = C(S, C(S, ...(Z0)...)) ∈ GRF_0.  K[n]() = n.
    fn k0(n: usize) -> Grf {
        let mut f: Grf = Grf::Zero(0);
        for _ in 0..n {
            f = Grf::comp(Grf::Succ, vec![f]);
        }
        f
    }

    #[test]
    fn test_tri_values() {
        let tri = make_tri();
        assert_eq!(tri.arity(), 1);
        assert_eq!(tri.size(), 7);
        // Tri(n) = n*(n+1)/2
        for (n, expected) in [(0, 0u64), (1, 1), (2, 3), (3, 6), (4, 10), (5, 15), (10, 55)] {
            assert_eq!(
                sim(&tri, &[n]),
                Some(expected),
                "Tri({n}) should be {expected}"
            );
        }
    }

    #[test]
    fn test_rep_diag_tri_small() {
        let rd_tri = make_rep_diag(make_tri());
        assert_eq!(rd_tri.arity(), 1);
        assert_eq!(rd_tri.size(), 14);
        // RepDiag[Tri](x) = Tri^{x+1}(x+2)
        // RepDiag[Tri](1) = Tri^2(3) = Tri(Tri(3)) = Tri(6) = 21
        assert_eq!(sim(&rd_tri, &[1]), Some(21));
        // RepDiag[Tri](2) = Tri^3(4) = Tri(Tri(10)) = Tri(55) = 1540
        assert_eq!(sim(&rd_tri, &[2]), Some(1540));
    }

    #[test]
    fn test_rep_diag_tri_n3() {
        // RepDiag[Tri](3) = Tri^4(5) = Tri(Tri(Tri(15))) = Tri(Tri(120)) = Tri(7260) = 26,357,430
        let rd_tri = make_rep_diag(make_tri());
        let (result, _steps) = simulate(&rd_tri, &[3], 200_000_000);
        assert_eq!(result.into_value().map(|v| u64::try_from(v).unwrap()), Some(26_357_430));
    }

    #[test]
    fn test_c_rep_diag_tri_k_n() {
        // C(RepDiag[Tri], K[n])() = RepDiag[Tri](n) = Tri^{n+1}(n+2)
        let make_champ = |n: usize| {
            Grf::comp(make_rep_diag(make_tri()), vec![k0(n)])
        };
        // n=1: Tri^2(3) = 21
        assert_eq!(sim(&make_champ(1), &[]), Some(21));
        // n=2: Tri^3(4) = 1540
        assert_eq!(sim(&make_champ(2), &[]), Some(1540));
        // n=3: Tri^4(5) = 26,357,430  (may be slow; allow 200M steps)
        let (r3, _) = simulate(&make_champ(3), &[], 200_000_000);
        assert_eq!(r3.into_value().map(|v| u64::try_from(v).unwrap()), Some(26_357_430));
    }

    #[test]
    fn test_c_rep_diag_tri_k4_times_out() {
        // C(RepDiag[Tri], K[4])() = Tri^5(6) ≈ 10^16; requires ~10^9 steps → times out at 100M
        let champ = Grf::comp(make_rep_diag(make_tri()), vec![k0(4)]);
        let (result, _steps) = simulate(&champ, &[], 100_000_000);
        assert!(
            result.value().is_none(),
            "C(RepDiag[Tri], K[4]) should time out at 100M steps"
        );
    }
}
