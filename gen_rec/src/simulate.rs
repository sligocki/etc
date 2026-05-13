use crate::grf::Grf;

pub use crate::base::Num;

/// Result of simulating a GRF.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SimResult {
    /// The function terminated with this value.
    Value(Num),
    /// The function exceeded the step budget (may or may not terminate with more steps).
    OutOfSteps,
    /// The function will provably never terminate regardless of step budget.
    Diverge,
    /// The function was called with the wrong number of arguments.
    ArityMismatch,
}

impl SimResult {
    pub fn is_value(&self) -> bool {
        matches!(self, SimResult::Value(_))
    }

    pub fn value(&self) -> Option<&Num> {
        match self {
            SimResult::Value(v) => Some(v),
            _ => None,
        }
    }

    pub fn into_value(self) -> Option<Num> {
        match self {
            SimResult::Value(v) => Some(v),
            _ => None,
        }
    }
}

/// Step counts returned by simulation functions.
///
/// `sim` is the number of evaluation steps actually taken (with all enabled optimizations).
/// `base_approx` approximates what `no_ff` (unoptimized) simulation would have counted;
/// it is exact for most code paths and an approximation for the acc-ignored `rec_fast_forward`
/// case (which skips re-evaluating g, so its exact base cost would require re-doing the
/// full loop and defeating the optimization).
///
/// **Invariant:** for any run with `no_ff()`, `sim == base_approx`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SimSteps {
    pub sim: Num,
    pub base_approx: Num,
}

impl SimSteps {
    fn zero() -> Self {
        SimSteps { sim: 0, base_approx: 0 }
    }
    fn one() -> Self {
        SimSteps { sim: 1, base_approx: 1 }
    }
}

impl std::ops::AddAssign<SimSteps> for SimSteps {
    fn add_assign(&mut self, rhs: SimSteps) {
        self.sim += rhs.sim;
        self.base_approx += rhs.base_approx;
    }
}

/// Options controlling simulation behavior.
#[derive(Clone, Copy, Debug)]
pub struct SimOpts {
    /// When true (default), skip the Rec iteration when the step function provably
    /// ignores its accumulator (arg 2), computing `h(n-1, 0, rest)` in O(1) instead
    /// of iterating `n` times. Semantically equivalent; dramatically faster for
    /// patterns like `R(Z0, R(Z1, P(3,1)))` which would otherwise be O(n²).
    pub rec_fast_forward: bool,

    /// When true (default), short-circuit `M(f)` when `f` provably ignores its
    /// search variable (1-indexed arg 1): evaluate `f(0, args)` once and return
    /// `Value(0)` if 0, or `Diverge` if non-zero (no i will ever satisfy f=0).
    pub min_fast_forward: bool,

    /// When true (default), fuse `M(R(g,h))` into a single forward pass:
    /// evaluate `acc=g(args)` once, then repeatedly apply `h(k,acc,args)`
    /// until `acc=0`. Reduces O(n²) Min+Rec to O(n).
    pub min_rec_fuse: bool,
}

impl Default for SimOpts {
    fn default() -> Self {
        SimOpts { rec_fast_forward: true, min_fast_forward: true, min_rec_fuse: true }
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
/// - R(g,h)(n,...): 1 + steps(g) + n * avg_steps(h) steps  [without fast-forward]
/// - M(f)(...): 1 + N * avg_steps(f) steps where N is iterations until success
///
/// Uses `SimOpts::default()` (rec_fast_forward enabled). Use `simulate_opts` to
/// disable the optimization, e.g. for benchmarking or step-count tests.
pub fn simulate(grf: &Grf, args: &[Num], max_steps: Num) -> (SimResult, SimSteps) {
    let step_budget = if max_steps == 0 { None } else { Some(max_steps) };
    simulate_opts(grf, args, step_budget, SimOpts::default())
}

/// Simulate `M(f)(args)`, applying all Min optimizations, calling `on_iter`
/// after each candidate evaluation in the general or fused loop.
///
/// `on_iter(n, result, steps_so_far)` fires after evaluating `f` at search
/// index `n` (or its fused-Rec equivalent). Fast-forward paths that return
/// without iterating do not fire `on_iter`. Suitable for progress-reporting
/// wrappers; pass `&mut |_, _, _| {}` for the no-op case.
///
/// `step_budget` and `opts` follow the same semantics as [`simulate_opts`].
pub fn simulate_min<F>(
    f: &Grf,
    args: &[Num],
    step_budget: Option<Num>,
    opts: SimOpts,
    on_iter: &mut F,
) -> (SimResult, SimSteps)
where
    F: FnMut(Num, &SimResult, SimSteps),
{
    if step_budget == Some(0) {
        return (SimResult::OutOfSteps, SimSteps::zero());
    }
    let mut steps = SimSteps::one(); // cost of the Min node

    if f.is_never_zero() {
        return (SimResult::Diverge, steps);
    }

    // Fast-forward: f ignores its search variable (1-indexed arg 1).
    if opts.min_fast_forward && !f.used_args().contains(&1) {
        let mut f_args: Vec<Num> = Vec::with_capacity(args.len() + 1);
        f_args.push(0);
        f_args.extend_from_slice(args);
        let (result, s) = simulate_opts(f, &f_args, step_budget.map(|b| b - steps.sim), opts);
        steps += s;
        // base_approx: base loop also evaluates f(0, args) first; no extra steps.
        return match result {
            SimResult::Value(0) => (SimResult::Value(0), steps),
            SimResult::Value(_) => (SimResult::Diverge, steps),
            other => (other, steps),
        };
    }

    // Fast-forward: f(i, args) > 0 whenever i > 0, so only i=0 is a candidate.
    if opts.min_fast_forward && f.is_positive_for_pos_arg(1) {
        let mut f_args: Vec<Num> = Vec::with_capacity(args.len() + 1);
        f_args.push(0);
        f_args.extend_from_slice(args);
        let (result, s) = simulate_opts(f, &f_args, step_budget.map(|b| b - steps.sim), opts);
        steps += s;
        // base_approx: base loop also evaluates f(0, args) first; no extra steps.
        return match result {
            SimResult::Value(0) => (SimResult::Value(0), steps),
            SimResult::Value(_) => (SimResult::Diverge, steps),
            other => (other, steps),
        };
    }

    // Fused M(R(g,h)): carry accumulator forward instead of restarting
    // the recursion from scratch for each Min candidate.
    if opts.min_rec_fuse {
        if let Grf::Rec(rec_g, rec_h) = f {
            let (base, s_g) = simulate_opts(rec_g, args, step_budget.map(|b| b - steps.sim), opts);
            let sg = s_g.base_approx;
            steps += s_g;
            let mut acc = match base {
                SimResult::Value(v) => v,
                other => return (other, steps),
            };

            if acc == 0 {
                // Unoptimized would evaluate R(g,h)(0,args) = 1(Rec) + g(args).
                // Fused only evaluated g(args), so base_extra = 1 (skipped Rec node).
                steps.base_approx += 1;
                return (SimResult::Value(0), steps);
            }

            let mut k: Num = 0;
            let mut sum_h: Num = 0;   // Σ sh_k.base_approx
            let mut k_sum_h: Num = 0; // Σ k * sh_k.base_approx

            loop {
                let mut h_args: Vec<Num> = Vec::with_capacity(args.len() + 2);
                h_args.push(k);
                h_args.push(acc);
                h_args.extend_from_slice(args);

                let (result, s_h) = simulate_opts(rec_h, &h_args, step_budget.map(|b| b - steps.sim), opts);
                let sh_base = s_h.base_approx;
                steps += s_h;
                sum_h += sh_base;
                k_sum_h += k * sh_base;

                match result {
                    SimResult::Value(v) => {
                        on_iter(k + 1, &SimResult::Value(v), steps);
                        if v == 0 {
                            let n = k + 1;
                            // Exact base_extra derivation:
                            //   unoptimized M(R(g,h)) at result n = 1 + Σᵢ₌₀ⁿ (1+sg + Σⱼ<ᵢ shⱼ)
                            // formula: (n+1) + n*sg + (n-1)*sum_h - k_sum_h
                            // rewritten to avoid underflow: (n+1) + n*(sg+sum_h) - sum_h - k_sum_h
                            let base_extra = (n + 1) + n * (sg + sum_h) - sum_h - k_sum_h;
                            steps.base_approx += base_extra;
                            return (SimResult::Value(k + 1), steps);
                        }
                        acc = v;
                    }
                    other => return (other, steps),
                }
                k += 1;
            }
        }
    }

    // General loop: M(f)(args) = min{i : f(i, args...) = 0}
    let mut i: Num = 0;
    loop {
        let remaining = step_budget.map(|b| b.saturating_sub(steps.sim));
        if remaining == Some(0) {
            return (SimResult::OutOfSteps, steps);
        }
        let mut f_args: Vec<Num> = Vec::with_capacity(args.len() + 1);
        f_args.push(i);
        f_args.extend_from_slice(args);

        let (result, s) = simulate_opts(f, &f_args, remaining, opts);
        steps += s;
        on_iter(i, &result, steps);
        match result {
            SimResult::Value(0) => return (SimResult::Value(i), steps),
            SimResult::Value(_) => i += 1,
            other => return (other, steps),
        }
    }
}

/// Simulate with explicit options. See `SimOpts` and `simulate`.
///
/// `step_budget` is the total number of steps available for this call and all
/// its sub-calls. `None` means unlimited. The returned step count is how many
/// steps were consumed.
pub fn simulate_opts(grf: &Grf, args: &[Num], step_budget: Option<Num>, opts: SimOpts) -> (SimResult, SimSteps) {
    if step_budget == Some(0) {
        return (SimResult::OutOfSteps, SimSteps::zero());
    }
    if args.len() != grf.arity() {
        return (SimResult::ArityMismatch, SimSteps::zero());
    }
    let mut steps = SimSteps::one(); // cost of this call

    let result = match grf {
        Grf::Zero(_) => SimResult::Value(0),

        Grf::Succ => SimResult::Value(args[0] + 1),

        Grf::Proj(_, i) => SimResult::Value(args[i - 1]),

        Grf::Comp(h, gs, _) => {
            // Evaluate each gi(args), collecting results as new arg list for h.
            let mut h_args: Vec<Num> = Vec::with_capacity(gs.len());
            for g in gs.iter() {
                let (result, s) = simulate_opts(g, args, step_budget.map(|b| b - steps.sim), opts);
                steps += s;
                match result {
                    SimResult::Value(v) => h_args.push(v),
                    other => return (other, steps),
                }
            }
            let (result, s) = simulate_opts(h, &h_args, step_budget.map(|b| b - steps.sim), opts);
            steps += s;
            result
        }

        Grf::Rec(g, h) => {
            // args = [n, x2, ..., x_{k+1}]
            // R(g,h)(0, rest) = g(rest)
            // R(g,h)(n+1, rest) = h(n, R(g,h)(n, rest), rest)
            // Iteratively: acc = g(rest); for i in 0..n: acc = h(i, acc, rest)
            let n = args[0];
            let rest = &args[1..];

            // Base case
            let (base, s) = simulate_opts(g, rest, step_budget.map(|b| b - steps.sim), opts);
            steps += s;
            let mut acc = match base {
                SimResult::Value(v) => v,
                other => return (other, steps),
            };

            // Fast-forward two different (opposite cases):
            //      * h ignores accumulator (arg 2)
            //      * h echos (or adds a constant each iteration to) the accumulator
            if opts.rec_fast_forward {
                // If h ignores its accumulator (arg 2), every iteration
                // h(i, acc, rest) = h(i, _, rest) is independent of acc.  The final
                // result is therefore h(n-1, 0, rest), computable in O(1).
                if n > 0 && !h.used_args().contains(&2) {
                    let mut h_args: Vec<Num> = Vec::with_capacity(rest.len() + 2);
                    h_args.push(n - 1);
                    h_args.push(0); // accumulator: ignored by h, value is arbitrary
                    h_args.extend_from_slice(rest);
                    let (result, s) = simulate_opts(h, &h_args, step_budget.map(|b| b - steps.sim), opts);
                    let sh_base = s.base_approx;
                    steps += s;
                    // Approx: unoptimized does g(rest) + (n-1) more h calls.
                    // This may not be exactly correct since other calls have different i value.
                    steps.base_approx += (n - 1) * sh_base;
                    return (result, steps);
                }

                // If h(i, acc, rest) = acc + k for a constant k, then
                // R(g, h)(n, rest) = g(rest) + n*k — direct multiplication.
                if let Some(k) = h.acc_plus_k() {
                    // Each h = S^k(P2) call costs k Comp nodes + k Succ atoms + 1 Proj = 2k+1 steps.
                    steps.base_approx += n * (2 * k + 1);
                    // Plain arithmetic: matches the unoptimized loop, which uses plain + in Succ.
                    // Wraps in release and panics in debug on overflow, same as the slow path would.
                    return (SimResult::Value(acc + n * k), steps);
                }
            }

            for i in 0..n {
                let mut h_args: Vec<Num> = Vec::with_capacity(rest.len() + 2);
                h_args.push(i);
                h_args.push(acc);
                h_args.extend_from_slice(rest);

                let (result, s) = simulate_opts(h, &h_args, step_budget.map(|b| b - steps.sim), opts);
                steps += s;
                acc = match result {
                    SimResult::Value(v) => v,
                    other => return (other, steps),
                };
            }

            SimResult::Value(acc)
        }

        Grf::Min(f) => {
            return simulate_min(f, args, step_budget, opts, &mut |_, _, _| {});
        }
    };

    (result, steps)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::grf::Grf;
    use crate::grf;

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
    fn test_rec_affine_k1() {
        // R(Z0, C(S, P(2,2)))(n) = n  (acc starts at 0, +1 each step)
        let f = grf!("R(Z0, C(S, P(2,2)))");
        for n in (0 as Num)..=10 {
            assert_eq!(eval_helper(&f, &[n]), Some(n));
        }
    }

    #[test]
    fn test_rec_affine_k2() {
        // R(S, C(S, C(S, P(3,2))))(n, x) = S(x) + 2*n = x + 2n + 1
        let f = grf!("R(S, C(S, C(S, P(3,2))))");
        for n in (0 as Num)..=5 {
            for x in (0 as Num)..=3 {
                assert_eq!(eval_helper(&f, &[n, x]), Some(2*n + x + 1));
            }
        }
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
        // M(S)() = min{i : S(i) = 0} = diverges; caught cheaply by is_never_zero.
        let f = Grf::Min(Box::new(Grf::Succ));
        let (result, steps) = simulate(&f, &[], 1000);
        assert_eq!(result, SimResult::Diverge);
        assert!(steps.sim < 10, "is_never_zero should short-circuit, got {} steps", steps.sim);
    }

    #[test]
    fn test_step_counting() {
        // Z0(): 1 step
        let (_, steps) = simulate(&Grf::Zero(0), &[], 1_000_000);
        assert_eq!(steps.sim, 1);

        // C(S, Z0)(): simulate_opts(C) = 1, simulate_opts(Z0) = 1, simulate_opts(S) = 1 → 3 steps
        let f = Grf::comp(Grf::Succ, vec![Grf::Zero(0)]);
        let (_, steps) = simulate(&f, &[], 1_000_000);
        assert_eq!(steps.sim, 3);
    }

    #[test]
    fn test_rec_steps() {
        // R(Z0, P(2,2))(3): h = P(2,2) is Proj(_, 2), so the identity ff fires:
        // result = g(rest) = Z0() = 0 in steps: 1 (Rec) + 1 (Z0) = 2.
        let g = Grf::Zero(0);
        let h = Grf::Proj(2, 2);
        let r = Grf::Rec(Box::new(g), Box::new(h));
        let (val, steps) = simulate(&r, &[3], 1_000_000);
        assert_eq!(val.into_value(), Some(0));
        assert_eq!(steps.sim, 2);
    }

    #[test]
    fn test_out_of_steps() {
        // R where h = C(Plus, [P(2,1), P(2,2)]) adds the loop counter to the
        // accumulator each step.  acc_plus_k returns None so no ff fires, and
        // each call to Plus itself costs O(i) steps, making the total O(n^2).
        let r = grf!("R(Z0, C(R(P(1,1), C(S, P(3,2))), P(2,1), P(2,2)))");
        let (result, steps) = simulate(&r, &[1_000], 50);
        assert!(matches!(result, SimResult::OutOfSteps));
        assert!(steps.sim >= 50);
    }

    // --- rec_fast_forward tests ---

    fn no_ff() -> SimOpts {
        SimOpts { rec_fast_forward: false, min_fast_forward: false, min_rec_fuse: false }
    }

    fn no_min_ff() -> SimOpts {
        SimOpts { min_fast_forward: false, ..SimOpts::default() }
    }

    #[test]
    fn test_rec_ff_simple() {
        // Pred: R(Z0, P(2,1))
        // Ignores accumulator
        let r = Grf::rec(Grf::Zero(0), Grf::Proj(2, 1));
        for n in (0 as Num)..=10 {
            let expected = n.saturating_sub(1);
            let (v_ff, _) = simulate(&r, &[n], 1_000_000);
            let (v_no, _) = simulate_opts(&r, &[n], Some(1_000_000), no_ff());
            assert_eq!(v_ff.into_value(), Some(expected), "ff wrong at n={n}");
            assert_eq!(v_no.into_value(), Some(expected), "no_ff wrong at n={n}");
        }
    }

    // Monus2: R(Z0, R(Z1, P(3,1)))
    // P(3,1) ignores the accumulator so both Rs fast-forward.
    fn nested_rec() -> Grf {
        // Pred = R(Z1, P(3,1))
        let inner = Grf::rec(Grf::Zero(1), Grf::Proj(3, 1));
        // Monus2 = R(Z0, Pred)
        Grf::rec(Grf::Zero(0), inner)
    }

    #[test]
    fn test_rec_ff_nested_correctness() {
        let f = nested_rec();
        // Both with and without fast-forward must give the same answer.
        for n in (0 as Num)..=20 {
            let (r_ff, _) = simulate(&f, &[n], 1_000_000);
            let (r_no, _) = simulate_opts(&f, &[n], Some(1_000_000), no_ff());
            assert_eq!(
                r_ff.into_value(),
                r_no.into_value(),
                "mismatch at n={n}"
            );
        }
    }

    #[test]
    fn test_rec_ff_fewer_steps() {
        let f = nested_rec();
        let n : Num = 1000;
        let (_, steps_ff) = simulate(&f, &[n], 0);
        let (_, steps_no) = simulate_opts(&f, &[n], None, no_ff());
        // Without fast-forward: O(n^2). With: O(1). Confirm dramatically fewer steps.
        // Difference is really 3 vs 501502 !
        assert!(
            steps_ff.sim < steps_no.sim / n,
            "expected fast-forward to use far fewer steps: ff={}, no_ff={}", steps_ff.sim, steps_no.sim
        );
    }

    #[test]
    fn test_rec_ff_proj_acc_identity() {
        // R(Z0, P(2,2)): h is Proj(_, 2) so the new ff fires: result = g(rest) = Z0() = 0.
        // With ff:    steps = 1(Rec) + 1(Z0) = 2.
        // Without ff: steps = 1(Rec) + 1(Z0) + 3*1(P) = 5.
        let r = Grf::rec(Grf::Zero(0), Grf::Proj(2, 2));
        for n in (0 as Num)..=10 {
            let (v_ff, _) = simulate(&r, &[n], 1_000_000);
            let (v_no, _) = simulate_opts(&r, &[n], Some(1_000_000), no_ff());
            assert_eq!(v_ff.into_value(), Some(0), "ff wrong at n={n}");
            assert_eq!(v_no.into_value(), Some(0), "no_ff wrong at n={n}");
        }
        let (_, steps_ff) = simulate(&r, &[3], 1_000_000);
        let (_, steps_no) = simulate_opts(&r, &[3], Some(1_000_000), no_ff());
        assert_eq!(steps_ff.sim, 2, "ff should skip the loop");
        assert_eq!(steps_no.sim, 5);
        assert_eq!(steps_ff.base_approx, steps_no.base_approx);
    }

    #[test]
    fn test_rec_ff_proj_acc_identity_arity2() {
        // R(P(1,1), P(3,2))(n, m): h = P(3,2) returns acc; result = P(1,1)(m) = m for all n.
        let r = Grf::rec(Grf::Proj(1, 1), Grf::Proj(3, 2));
        for n in (0 as Num)..=5 {
            for m in (0 as Num)..=5 {
                let (v_ff, _) = simulate(&r, &[n, m], 1_000_000);
                let (v_no, _) = simulate_opts(&r, &[n, m], Some(1_000_000), no_ff());
                assert_eq!(v_ff.into_value(), Some(m), "ff wrong at n={n} m={m}");
                assert_eq!(v_no.into_value(), Some(m), "no_ff wrong at n={n} m={m}");
            }
        }
    }

    #[test]
    fn test_rec_non_affine_step_correct() {
        // R(Z0, C(Plus, [P(2,1), P(2,2)]))(n) = n*(n-1)/2 (triangular numbers).
        // h = C(Plus, [i, acc]): acc_plus_k returns None, so outer affine ff doesn't fire.
        // (Inner Plus calls may still be accelerated; we verify only correctness here.)
        let r = grf!("R(Z0, C(R(P(1,1), C(S, P(3,2))), P(2,1), P(2,2)))");
        for n in (0 as Num)..=8 {
            // acc_0 = 0; acc_{i+1} = Plus(i, acc_i). acc_n = sum_{j=0}^{n-1} j = n*(n-1)/2.
            let expected = n * n.saturating_sub(1) / 2;
            let (v_ff, _) = simulate(&r, &[n], 1_000_000);
            let (v_no, _) = simulate_opts(&r, &[n], Some(1_000_000), no_ff());
            assert_eq!(v_ff.into_value(), Some(expected), "ff wrong at n={n}");
            assert_eq!(v_no.into_value(), Some(expected), "no_ff wrong at n={n}");
        }
    }

    // --- min_fast_forward tests ---

    #[test]
    fn test_min_ff_unused_search_var_zero() {
        // M(Z1)(): Z1 ignores arg 1. f(0)=0 → Value(0).
        let f = Grf::Min(Box::new(Grf::Zero(1)));
        let (r, _) = simulate(&f, &[], 1_000_000);
        assert_eq!(r, SimResult::Value(0));
    }

    #[test]
    fn test_min_ff_proj_outer_arg_zero() {
        // M(P(2,2))(0): P(2,2) ignores arg 1 (search var). f(0,0)=0 → Value(0).
        let f = Grf::Min(Box::new(Grf::Proj(2, 2)));
        let (r, _) = simulate(&f, &[0], 1_000_000);
        assert_eq!(r, SimResult::Value(0));
    }

    #[test]
    fn test_min_ff_proj_outer_arg_diverges() {
        // M(P(2,2))(3): f(0,3)=3≠0 → Diverge.
        let f = Grf::Min(Box::new(Grf::Proj(2, 2)));
        let (r, _) = simulate(&f, &[3], 1_000_000);
        assert_eq!(r, SimResult::Diverge);
    }

    #[test]
    fn test_min_ff_diverge_vs_oos() {
        // M(P(2,2))(3): P(2,2) ignores arg 1. f(0,3)=3≠0 → Diverge (with ff).
        // Without ff + small budget → OutOfSteps (budget exhausted, not proven diverge).
        // P(2,2).is_never_zero() is false so the is_never_zero short-circuit doesn't fire.
        let f = Grf::Min(Box::new(Grf::Proj(2, 2)));
        let (r_ff, _) = simulate(&f, &[3], 0);  // unlimited
        assert_eq!(r_ff, SimResult::Diverge);
        let (r_no, _) = simulate_opts(&f, &[3], Some(100), no_min_ff());
        assert_eq!(r_no, SimResult::OutOfSteps);
    }

    #[test]
    fn test_min_ff_not_applied_when_search_var_used() {
        // M(S)(): S uses arg 1 (search var) so the fast-forward (which relies on
        // the search var being ignored) must NOT apply.  However, S.is_never_zero()
        // so the never-zero short-circuit fires first and returns Diverge cheaply.
        let f = Grf::Min(Box::new(Grf::Succ));
        let (r_ff, _) = simulate_opts(&f, &[], Some(1000), SimOpts::default());
        let (r_no, _) = simulate_opts(&f, &[], Some(1000), no_min_ff());
        assert_eq!(r_ff, SimResult::Diverge);
        assert_eq!(r_no, SimResult::Diverge);
    }

    #[test]
    fn test_min_ff_fewer_steps() {
        // M(P(2,2))(3): ff detects divergence in one eval; without ff exhausts budget.
        // P(2,2).is_never_zero() is false so is_never_zero doesn't short-circuit.
        let f = Grf::Min(Box::new(Grf::Proj(2, 2)));
        let (_, steps_ff) = simulate(&f, &[3], 0);
        let (_, steps_no) = simulate_opts(&f, &[3], Some(100), no_min_ff());
        assert!(steps_ff.sim < 10, "ff should use very few steps, got {}", steps_ff.sim);
        assert!(steps_no.sim >= 100, "no_ff should exhaust budget");
    }

    #[test]
    fn test_min_pos_arg1_rec_step_diverges() {
        // M(R(P(1,1), C(S, P(3,2)))): body = add(i, x) = i+x.
        // is_never_zero() = false (base P(1,1) can be 0).
        // is_positive_for_pos_arg1() = true (Rec with never-zero step C(S,...)).
        // f(0, 5) = 5 > 0, and f(i≥1, x) ≥ 1 always, so Min diverges.
        let grf = grf!("M(R(P(1,1), C(S, P(3,2))))");
        assert_eq!(simulate(&grf, &[5], 10_000).0, SimResult::Diverge);
        assert_eq!(simulate(&grf, &[3], 10_000).0, SimResult::Diverge);
    }

    #[test]
    fn test_min_pos_arg1_no_false_positive() {
        // M(P(1,1)): body returns the search counter i, which is 0 at i=0.
        // is_positive_for_pos_arg1() = true (Proj(1,1)) but f(0) = 0, so Min = 0.
        let grf = grf!("M(P(1,1))");
        assert_eq!(simulate(&grf, &[], 100).0, SimResult::Value(0));
        // M(R(P(1,1), C(S, P(3,2))))(0): f(0,0)=0, so Min=0, not Diverge.
        let grf2 = grf!("M(R(P(1,1), C(S, P(3,2))))");
        assert_eq!(simulate(&grf2, &[0], 100).0, SimResult::Value(0));
    }

    #[test]
    fn test_min_pos_arg1_fewer_steps() {
        // Divergent result
        // Without the fast-forward, M(R(P(1,1),C(S,P(3,2))))(5) exhausts step budget.
        // The body is add(i,5)=i+5, so the loop needs many Rec evaluations.
        let grf = grf!("M(R(P(1,1), C(S, P(3,2))))");
        let (_, steps_ff) = simulate(&grf, &[5], 0);
        let (_, steps_no) = simulate_opts(&grf, &[5], Some(100), no_min_ff());
        assert!(steps_ff.sim < 20, "ff should resolve quickly, got {}", steps_ff.sim);
        assert!(steps_no.sim >= 100, "no_ff should exhaust budget");
    }

    // --- min_rec_fuse tests ---

    fn no_rec_fuse() -> SimOpts {
        SimOpts { min_rec_fuse: false, ..SimOpts::default() }
    }

    #[test]
    fn test_min_rec_fuse_base_zero() {
        // M(R(Z0, Z2))(): g=Z0 (arity 0), h=Z2 (arity 2).
        // Base: Z0()=0 → fuse detects immediately, returns Value(0).
        let grf = grf!("M(R(Z0, Z2))");
        assert_eq!(simulate(&grf, &[], 1_000_000).0, SimResult::Value(0));
        assert_eq!(simulate_opts(&grf, &[], Some(1_000_000), no_rec_fuse()).0, SimResult::Value(0));
    }

    #[test]
    fn test_min_rec_fuse_step_zero() {
        // M(R(C(S,Z0), Z2))(): base=1, h=Z2 always returns 0.
        // Fuse: acc=1 ≠ 0, k=0: h(0,1)=0 → return Value(1).
        let grf = grf!("M(R(C(S,Z0), Z2))");
        assert_eq!(simulate(&grf, &[], 1_000_000).0, SimResult::Value(1));
        assert_eq!(simulate_opts(&grf, &[], Some(1_000_000), no_rec_fuse()).0, SimResult::Value(1));
    }

    #[test]
    fn test_min_rec_fuse_correctness() {
        // M(R(P(1,1), C(R(Z0,P(2,1)), P(3,2))))(x) = x.
        // R counts down: base=x, step=pred(acc), reaches 0 at iteration x.
        let grf = grf!("M(R(P(1,1), C(R(Z0,P(2,1)),P(3,2))))");
        for x in (0 as Num)..=10 {
            let (r_fuse, steps_fuse) = simulate(&grf, &[x], 1_000_000);
            let (r_no, steps_no) = simulate_opts(&grf, &[x], Some(1_000_000), no_rec_fuse());
            assert_eq!(r_fuse, SimResult::Value(x), "fuse wrong at x={x}");
            assert_eq!(r_no, SimResult::Value(x), "no_fuse wrong at x={x}");
            assert!(steps_fuse.sim < steps_no.sim);
            assert_eq!(steps_fuse.base_approx, steps_no.base_approx);
        }
    }

    #[test]
    fn test_min_rec_fuse_fewer_steps() {
        // Same GRF as above with x=50: naive is O(x²), fused is O(x).
        let grf = grf!("M(R(P(1,1), C(R(Z0,P(2,1)),P(3,2))))");
        let (r_fuse, steps_fuse) = simulate(&grf, &[50], 0);
        let (r_no, steps_no) = simulate_opts(&grf, &[50], None, no_rec_fuse());
        assert_eq!(r_fuse, SimResult::Value(50));
        assert_eq!(r_no, SimResult::Value(50));
        assert!(
            steps_fuse.sim * 10 < steps_no.sim,
            "fuse should use far fewer steps: fuse={}, no_fuse={}", steps_fuse.sim, steps_no.sim
        );
        assert_eq!(steps_fuse.base_approx, steps_no.base_approx);
    }

    // --- base_approx tests ---

    #[test]
    fn test_base_approx_no_ff_invariant() {
        // With no_ff(), sim == base_approx for any GRF (no optimizations fire).
        let (_, s) = simulate_opts(&grf!("R(Z0,C(S,P(3,2)))"), &[5], None, no_ff());
        assert_eq!(s.sim, s.base_approx, "R: sim={} base={}", s.sim, s.base_approx);
        let (_, s) = simulate_opts(&grf!("M(R(P(1,1),C(R(Z0,P(2,1)),P(3,2))))"), &[5], None, no_ff());
        assert_eq!(s.sim, s.base_approx, "M(R): sim={} base={}", s.sim, s.base_approx);
    }

    #[test]
    fn test_base_approx_proj_identity_rec() {
        // R(Z0, P(2,2))(3): Proj-identity ff fires → sim=2, base_approx=5 (2 + 3 Proj calls).
        let r = Grf::rec(Grf::Zero(0), Grf::Proj(2, 2));
        let (_, s) = simulate(&r, &[3], 0);
        assert_eq!(s.sim, 2, "sim steps");
        assert_eq!(s.base_approx, 5, "base_approx steps");
        let (_, s_noff) = simulate_opts(&r, &[3], None, no_ff());
        assert_eq!(s.base_approx, s_noff.sim, "base_approx should match no_ff sim");
    }

    #[test]
    fn test_base_approx_min_rec_fuse_exact() {
        // M(R(C(S,Z0), Z2))(): g()=1, h(k,acc)=0 (atom, no inner Rec → base_approx exact).
        // Fused: acc=1, k=0: h returns 0 → result=1. One loop iteration.
        let grf_0 = grf!("M(R(C(S,Z0), Z2))");
        let (_, s) = simulate(&grf_0, &[], 0);
        let (_, s_noff) = simulate_opts(&grf_0, &[], None, no_ff());
        assert_eq!(s.base_approx, s_noff.sim, "M(R(C(S,Z0),Z2)): base_approx={} no_ff={}", s.base_approx, s_noff.sim);

        // M(R(Z0, Z2))(): g()=0 → base case, acc=0 immediately, result=0.
        // base_extra = 1 (skipped Rec node for i=0).
        let grf_base = grf!("M(R(Z0, Z2))");
        let (_, s2) = simulate(&grf_base, &[], 0);
        let (_, s2_noff) = simulate_opts(&grf_base, &[], None, no_ff());
        assert_eq!(s2.base_approx, s2_noff.sim, "M(R(Z0,Z2)) base case: base_approx={} no_ff={}", s2.base_approx, s2_noff.sim);

        // For the GRF from the plan M(R(P(1,1),C(R(Z0,P(2,1)),P(3,2)))):
        // x=0 is exact (acc=0 base case, inner h never evaluated).
        // x>0 is a lower bound because h contains acc-ignored rec_ff inside R(Z0,P(2,1)).
        let grf_plan = grf!("M(R(P(1,1),C(R(Z0,P(2,1)),P(3,2))))");
        let (_, s3) = simulate(&grf_plan, &[0], 0);
        let (_, s3_noff) = simulate_opts(&grf_plan, &[0], None, no_ff());
        assert_eq!(s3.base_approx, s3_noff.sim, "x=0 exact: base_approx={} no_ff={}", s3.base_approx, s3_noff.sim);
        for x in (1 as Num)..=10 {
            let (_, sx) = simulate(&grf_plan, &[x], 0);
            let (_, sx_noff) = simulate_opts(&grf_plan, &[x], None, no_ff());
            assert!(sx.base_approx >= sx.sim, "x={x}: base_approx must be >= sim");
            assert!(sx.base_approx <= sx_noff.sim, "x={x}: base_approx={} must be <= no_ff={}", sx.base_approx, sx_noff.sim);
        }
    }
}
