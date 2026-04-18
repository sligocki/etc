use crate::grf::Grf;

/// Numeric type used for both GRF values and simulation step counts.
/// Swap this alias to `u128` or a bignum type to widen the range.
pub type Num = u64;

/// Result of simulating a GRF.
#[derive(Clone, Debug)]
pub enum SimResult {
    /// The function terminated with this value.
    Value(Num),
    /// The function exceeded the step budget (may or may not terminate with more steps).
    OutOfSteps,
}

impl SimResult {
    pub fn is_value(&self) -> bool {
        matches!(self, SimResult::Value(_))
    }

    pub fn value(&self) -> Option<&Num> {
        match self {
            SimResult::Value(v) => Some(v),
            SimResult::OutOfSteps => None,
        }
    }

    pub fn into_value(self) -> Option<Num> {
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
/// **`max_steps = 0` means no limit** — the simulation runs until it terminates or
/// loops forever. Use only when the GRF is known to be total (e.g. PRF-only).
///
/// Step counting: every call to `eval` costs 1 step. This naturally captures:
/// - Atoms: 1 step each
/// - C(h, g1..gm): 1 + steps(g1) + ... + steps(gm) + steps(h) steps
/// - R(g,h)(n,...): 1 + steps(g) + n * avg_steps(h) steps
/// - M(f)(...): 1 + N * avg_steps(f) steps where N is iterations until success
pub fn simulate(grf: &Grf, args: &[Num], max_steps: Num) -> (SimResult, Num) {
    let mut steps: Num = 0;
    let result = eval(grf, args, &mut steps, max_steps);
    (result, steps)
}

fn eval(grf: &Grf, args: &[Num], steps: &mut Num, max_steps: Num) -> SimResult {
    if max_steps != 0 && *steps >= max_steps {
        return SimResult::OutOfSteps;
    }
    *steps += 1;

    match grf {
        Grf::Zero(_) => SimResult::Value(0),

        Grf::Succ => SimResult::Value(args[0] + 1),

        Grf::Proj(_, i) => SimResult::Value(args[i - 1]),

        Grf::Comp(h, gs, _) => {
            // Evaluate each gi(args), collecting results as new arg list for h.
            let mut h_args: Vec<Num> = Vec::with_capacity(gs.len());
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
            let n = args[0];
            let rest = &args[1..];

            let mut acc = match eval(g, rest, steps, max_steps) {
                SimResult::Value(v) => v,
                other => return other,
            };

            for i in 0..n {
                let mut h_args: Vec<Num> = Vec::with_capacity(rest.len() + 2);
                h_args.push(i);
                h_args.push(acc);
                h_args.extend_from_slice(rest);

                acc = match eval(h, &h_args, steps, max_steps) {
                    SimResult::Value(v) => v,
                    other => return other,
                };
            }

            SimResult::Value(acc)
        }

        Grf::Min(f) => {
            // M(f)(args) = min{i : f(i, args...) = 0}
            let mut i: Num = 0;
            loop {
                let mut f_args: Vec<Num> = Vec::with_capacity(args.len() + 1);
                f_args.push(i);
                f_args.extend_from_slice(args);

                match eval(f, &f_args, steps, max_steps) {
                    SimResult::Value(0) => return SimResult::Value(i),
                    SimResult::Value(_) => i += 1,
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

    fn eval_helper(grf: &Grf, args: &[Num]) -> Option<Num> {
        let (result, _steps) = simulate(grf, args, 1_000_000);
        result.into_value()
    }

    #[test]
    fn test_zero() {
        assert_eq!(eval_helper(&Grf::Zero(0), &[]), Some(0));
        assert_eq!(eval_helper(&Grf::Zero(2), &[3, 5]), Some(0));
    }

    #[test]
    fn test_succ() {
        assert_eq!(eval_helper(&Grf::Succ, &[0]), Some(1));
        assert_eq!(eval_helper(&Grf::Succ, &[5]), Some(6));
    }

    #[test]
    fn test_proj() {
        assert_eq!(eval_helper(&Grf::Proj(2, 1), &[3, 5]), Some(3));
        assert_eq!(eval_helper(&Grf::Proj(2, 2), &[3, 5]), Some(5));
        assert_eq!(eval_helper(&Grf::Proj(3, 2), &[1, 2, 3]), Some(2));
    }

    #[test]
    fn test_comp_k0_1() {
        // C(S, Z0)() = S(Z0()) = S(0) = 1
        let f = Grf::comp(Grf::Succ, vec![Grf::Zero(0)]);
        assert_eq!(eval_helper(&f, &[]), Some(1));
    }

    #[test]
    fn test_comp_k0_2() {
        // C(S, C(S, Z0))() = 2
        let k01 = Grf::comp(Grf::Succ, vec![Grf::Zero(0)]);
        let k02 = Grf::comp(Grf::Succ, vec![k01]);
        assert_eq!(eval_helper(&k02, &[]), Some(2));
    }

    #[test]
    fn test_comp_projection_selects_arg() {
        // C(P(2,1), S, Z1)([3]) = P(2,1)(S(3), Z1(3)) = P(2,1)(4, 0) = 4
        let f = Grf::comp(Grf::Proj(2, 1), vec![Grf::Succ, Grf::Zero(1)]);
        assert_eq!(eval_helper(&f, &[3]), Some(4));
    }

    #[test]
    fn test_rec_plus() {
        // Plus = R(P(1,1), C(S, P(3,2)))
        // Plus(n, m) = n + m
        let g = Grf::Proj(1, 1);
        let h = Grf::comp(Grf::Succ, vec![Grf::Proj(3, 2)]);
        let plus = Grf::Rec(Box::new(g), Box::new(h));

        assert_eq!(eval_helper(&plus, &[0, 0]), Some(0));
        assert_eq!(eval_helper(&plus, &[3, 2]), Some(5));
        assert_eq!(eval_helper(&plus, &[0, 7]), Some(7));
        assert_eq!(eval_helper(&plus, &[4, 4]), Some(8));
    }

    #[test]
    fn test_rec_identity() {
        let g = Grf::Zero(0);
        let h = Grf::comp(Grf::Succ, vec![Grf::Proj(2, 2)]);
        let identity = Grf::Rec(Box::new(g), Box::new(h));
        assert_eq!(identity.arity(), 1);
        assert_eq!(eval_helper(&identity, &[0]), Some(0));
        assert_eq!(eval_helper(&identity, &[5]), Some(5));
    }

    #[test]
    fn test_min_proj() {
        // M(P(1,1))() = min{i : P(1,1)(i) = 0} = 0
        let f = Grf::Min(Box::new(Grf::Proj(1, 1)));
        assert_eq!(eval_helper(&f, &[]), Some(0));
    }

    #[test]
    fn test_min_zero() {
        // M(Z1)() = min{i : Z1(i) = 0} = 0
        let f = Grf::Min(Box::new(Grf::Zero(1)));
        assert_eq!(eval_helper(&f, &[]), Some(0));
    }

    #[test]
    fn test_min_succ_diverges() {
        // M(S)() = min{i : S(i) = 0} = diverges
        let f = Grf::Min(Box::new(Grf::Succ));
        let (result, steps) = simulate(&f, &[], 1000);
        assert!(result.value().is_none());
        assert!(steps >= 1000);
    }

    #[test]
    fn test_step_counting() {
        // Z0(): 1 step
        let (_, steps) = simulate(&Grf::Zero(0), &[], 1_000_000);
        assert_eq!(steps, 1);

        // C(S, Z0)(): eval(C) = 1, eval(Z0) = 1, eval(S) = 1 → 3 steps
        let f = Grf::comp(Grf::Succ, vec![Grf::Zero(0)]);
        let (_, steps) = simulate(&f, &[], 1_000_000);
        assert_eq!(steps, 3);
    }

    #[test]
    fn test_rec_steps() {
        // R(Z0, P(2,2))(3): eval(R)=1, eval(Z0)=1, then 3 evals of h → 5 steps
        let g = Grf::Zero(0);
        let h = Grf::Proj(2, 2);
        let r = Grf::Rec(Box::new(g), Box::new(h));
        let (val, steps) = simulate(&r, &[3], 1_000_000);
        assert_eq!(val.into_value(), Some(0));
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
}
