use crate::grf::{Grf, GrfKind};

pub use crate::sim_nat::{SmallNat, BigNat, SimNat};

/// Result of simulating a GRF.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SimResult<N = SmallNat> {
    /// The function terminated with this value.
    Value(N),
    /// The function exceeded the step budget (may or may not terminate with more steps).
    OutOfSteps,
    /// The function will provably never terminate regardless of step budget.
    Diverge,
    /// The function was called with the wrong number of arguments.
    ArityMismatch,
    /// A value computation overflowed the numeric type.
    /// Only reachable when `N = u64` (bounded); `BigNat` never returns this.
    ValueOverflow,
}

impl<N: SimNat> SimResult<N> {
    pub fn is_value(&self) -> bool {
        matches!(self, SimResult::Value(_))
    }

    pub fn value(&self) -> Option<&N> {
        match self {
            SimResult::Value(v) => Some(v),
            _ => None,
        }
    }

    pub fn into_value(self) -> Option<N> {
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
/// it is exact for most code paths and an approximation for the acc-ignored
/// `rec_fast_forward` case.
///
/// **Invariant:** for any run with `no_ff()`, `sim == base_approx`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SimSteps<N = SmallNat> {
    pub sim: u64,
    pub base_approx: N,
}

impl<N: SimNat> SimSteps<N> {
    fn zero() -> Self {
        SimSteps { sim: 0, base_approx: N::zero() }
    }
    fn one() -> Self {
        SimSteps { sim: 1, base_approx: N::one() }
    }
}

impl<N: SimNat> std::ops::AddAssign<SimSteps<N>> for SimSteps<N> {
    fn add_assign(&mut self, rhs: SimSteps<N>) {
        // We are not afraid of sim step overflowing
        self.sim += rhs.sim;
        // base steps can overflow, saturate instead
        self.base_approx.saturating_add_assign(rhs.base_approx);
    }
}

/// Options controlling simulation behavior.
#[derive(Clone, Copy, Debug)]
pub struct SimOpts {
    /// When true (default), evaluate GRFs with a known `ClosedForm` directly via
    /// algebraic evaluation instead of structural simulation. Subsumes `acc_plus_k`
    /// and handles all affine/piecewise patterns in O(GRF_size) time.
    /// Set to `false` to measure raw simulation (e.g. in CF validation tests).
    pub use_closed_form: bool,

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
        SimOpts { use_closed_form: true, rec_fast_forward: true, min_fast_forward: true, min_rec_fuse: true }
    }
}

/// Simulate `grf` applied to `args`, spending at most `max_steps` evaluation steps.
///
/// Returns `(result, steps_taken)`.
///
/// **`max_steps = 0` means no limit** — the simulation runs until it terminates or
/// loops forever. Use only when the GRF is known to be total (e.g. PRF-only).
///
/// Uses `SimOpts::default()` (rec_fast_forward enabled). Use `simulate_opts` to
/// disable the optimization, e.g. for benchmarking or step-count tests.
pub fn simulate(grf: &Grf, args: &[SmallNat], max_steps: SmallNat) -> (SimResult, SimSteps) {
    let step_budget = if max_steps == 0 { None } else { Some(max_steps) };
    simulate_opts(grf, args, step_budget, SimOpts::default())
}

/// Simulate using arbitrary-precision integers (`BigNat`).
/// Values never overflow; returns `OutOfSteps` when the step budget is exhausted.
pub fn simulate_big(grf: &Grf, args: &[BigNat], max_steps: u64) -> (SimResult<BigNat>, SimSteps<BigNat>) {
    let step_budget = if max_steps == 0 { None } else { Some(max_steps) };
    simulate_opts(grf, args, step_budget, SimOpts::default())
}

/// Simulate with native `u64`; on `ValueOverflow` automatically retry with `BigNat`.
/// Callers that want a single result without managing the two-step retry should use this.
pub fn simulate_with_fallback(grf: &Grf, args: &[SmallNat], max_steps: SmallNat) -> (SimResult<BigNat>, SimSteps<BigNat>) {
    let (result, steps) = simulate(grf, args, max_steps);
    let big_steps = SimSteps { sim: steps.sim, base_approx: BigNat::from(steps.base_approx) };
    match result {
        SimResult::ValueOverflow => {
            let big_args: Vec<BigNat> = args.iter().map(|&n| BigNat::from(n)).collect();
            simulate_big(grf, &big_args, max_steps)
        }
        SimResult::Value(v)      => (SimResult::Value(BigNat::from(v)), big_steps),
        SimResult::OutOfSteps    => (SimResult::OutOfSteps,    big_steps),
        SimResult::Diverge       => (SimResult::Diverge,       big_steps),
        SimResult::ArityMismatch => (SimResult::ArityMismatch, big_steps),
    }
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
pub fn simulate_min<N: SimNat, F>(
    f: &Grf,
    args: &[N],
    step_budget: Option<u64>,
    opts: SimOpts,
    on_iter: &mut F,
) -> (SimResult<N>, SimSteps<N>)
where
    F: FnMut(N, &SimResult<N>, SimSteps<N>),
{
    if step_budget == Some(0) {
        return (SimResult::OutOfSteps, SimSteps::zero());
    }
    let mut steps = SimSteps::one(); // cost of the Min node

    if f.is_never_zero() {
        return (SimResult::Diverge, steps);
    }

    // Fast-forward: if f has a ClosedForm, use compute_min for an exact O(1)-or-O(n) answer.
    if opts.min_fast_forward && opts.use_closed_form {
        if let Some(cf) = f.closed_form() {
            return match cf.compute_min(args) {
                Some(v) => (SimResult::Value(v), steps),
                None => (SimResult::Diverge, steps),
            };
        }
    }

    // Fast-forward: f ignores its search variable (1-indexed arg 1).
    if opts.min_fast_forward && !f.used_args().contains(&1) {
        let mut f_args: Vec<N> = Vec::with_capacity(args.len() + 1);
        f_args.push(N::zero());
        f_args.extend(args.iter().cloned());
        let (result, s) = simulate_opts(f, &f_args, step_budget.map(|b| b - steps.sim), opts);
        steps += s;
        // base_approx: base loop also evaluates f(0, args) first; no extra steps.
        return match result {
            SimResult::Value(v) if v.is_zero() => (SimResult::Value(N::zero()), steps),
            SimResult::Value(_) => (SimResult::Diverge, steps),
            other => (other, steps),
        };
    }

    // Fast-forward: f(i, args) > 0 whenever i > 0, so only i=0 is a candidate.
    if opts.min_fast_forward && f.is_positive_for_pos_arg(1) {
        let mut f_args: Vec<N> = Vec::with_capacity(args.len() + 1);
        f_args.push(N::zero());
        f_args.extend(args.iter().cloned());
        let (result, s) = simulate_opts(f, &f_args, step_budget.map(|b| b - steps.sim), opts);
        steps += s;
        // base_approx: base loop also evaluates f(0, args) first; no extra steps.
        return match result {
            SimResult::Value(v) if v.is_zero() => (SimResult::Value(N::zero()), steps),
            SimResult::Value(_) => (SimResult::Diverge, steps),
            other => (other, steps),
        };
    }

    // Fused M(R(g,h)): carry accumulator forward instead of restarting
    // the recursion from scratch for each Min candidate.
    if opts.min_rec_fuse {
        if let GrfKind::Rec(rec_g, rec_h) = &f.kind {
            let (base, s_g) = simulate_opts(rec_g, args, step_budget.map(|b| b - steps.sim), opts);
            let sg = s_g.base_approx.clone();
            steps += s_g;
            let mut acc = match base {
                SimResult::Value(v) => v,
                other => return (other, steps),
            };

            if acc.is_zero() {
                // Unoptimized would evaluate R(g,h)(0,args) = 1(Rec) + g(args).
                // Fused only evaluated g(args), so base_extra = 1 (skipped Rec node).
                steps.base_approx.saturating_add_assign(N::one());
                return (SimResult::Value(N::zero()), steps);
            }

            let mut k: u64 = 0;
            // sum_h:   Σ sh_j.base_approx  (accumulated as N)
            // delta_h: Σ (k-j)*sh_j.base_approx, updated each step as delta_h += old sum_h
            // Avoids subtraction: base_extra = (n+1) + sg*n + delta_h
            let mut sum_h: N = N::zero();
            let mut delta_h: N = N::zero();

            loop {
                let mut h_args: Vec<N> = Vec::with_capacity(args.len() + 2);
                h_args.push(N::from_u64(k));
                h_args.push(acc.clone());
                h_args.extend(args.iter().cloned());

                let (result, s_h) = simulate_opts(rec_h, &h_args, step_budget.map(|b| b - steps.sim), opts);
                let sh_base = s_h.base_approx.clone();
                steps += s_h;
                // Update accumulators before updating sum_h.
                delta_h = delta_h.saturating_add(sum_h.clone());
                sum_h = sum_h.saturating_add(sh_base);

                match result {
                    SimResult::Value(v) => {
                        on_iter(N::from_u64(k + 1), &SimResult::Value(v.clone()), steps.clone());
                        if v.is_zero() {
                            let n = k + 1;
                            // base_extra = (n+1) + sg*n + delta_h
                            let n_times_sg = sg.clone()
                                .checked_mul_u64(n)
                                .unwrap_or_else(|| N::from_u64(u64::MAX));
                            let base_extra = N::from_u64(n + 1)
                                .saturating_add(n_times_sg)
                                .saturating_add(delta_h);
                            steps.base_approx.saturating_add_assign(base_extra);
                            return (SimResult::Value(N::from_u64(n)), steps);
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
    let mut i: N = N::zero();
    loop {
        let remaining = step_budget.map(|b| b.saturating_sub(steps.sim));
        if remaining == Some(0) {
            return (SimResult::OutOfSteps, steps);
        }
        let mut f_args: Vec<N> = Vec::with_capacity(args.len() + 1);
        f_args.push(i.clone());
        f_args.extend(args.iter().cloned());

        let (result, s) = simulate_opts(f, &f_args, remaining, opts);
        steps += s;
        on_iter(i.clone(), &result, steps.clone());
        match result {
            SimResult::Value(v) if v.is_zero() => return (SimResult::Value(i), steps),
            SimResult::Value(_) => {
                i = match i.succ() {
                    Some(v) => v,
                    None => return (SimResult::ValueOverflow, steps),
                };
            }
            other => return (other, steps),
        }
    }
}

/// Simulate with explicit options. See `SimOpts` and `simulate`.
///
/// `step_budget` is the total number of steps available for this call and all
/// its sub-calls. `None` means unlimited. The returned step count is how many
/// steps were consumed.
pub fn simulate_opts<N: SimNat>(grf: &Grf, args: &[N], step_budget: Option<u64>, opts: SimOpts) -> (SimResult<N>, SimSteps<N>) {
    if step_budget == Some(0) {
        return (SimResult::OutOfSteps, SimSteps::zero());
    }
    if args.len() != grf.arity() {
        return (SimResult::ArityMismatch, SimSteps::zero());
    }

    // CF fast-path: evaluate directly via closed form when available.
    // Works for any N: SimNat — no SmallNat conversion needed.
    // TODO: base_approx for CF-evaluated runs
    if opts.use_closed_form {
        if let Some(cf) = grf.closed_form() {
            return match cf.eval(args) {
                Some(v) => (SimResult::Value(v), SimSteps::one()),
                None    => (SimResult::ValueOverflow, SimSteps::one()),
            };
        }
    }

    let mut steps = SimSteps::one(); // cost of this call

    let result = match &grf.kind {
        GrfKind::Zero(_) => SimResult::Value(N::zero()),

        GrfKind::Succ => match args[0].clone().succ() {
            Some(v) => SimResult::Value(v),
            None => SimResult::ValueOverflow,
        },

        GrfKind::Proj(_, i) => SimResult::Value(args[i - 1].clone()),

        GrfKind::Comp(h, gs, _) => {
            // Evaluate each gi(args), collecting results as new arg list for h.
            let mut h_args: Vec<N> = Vec::with_capacity(gs.len());
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

        GrfKind::Rec(g, h) => {
            // args = [n, x2, ..., x_{k+1}]
            // R(g,h)(0, rest) = g(rest)
            // R(g,h)(n+1, rest) = h(n, R(g,h)(n, rest), rest)
            // Iteratively: acc = g(rest); for i in 0..n: acc = h(i, acc, rest)
            let n = args[0].clone();
            let rest = &args[1..];

            // Base case
            let (base, s) = simulate_opts(g, rest, step_budget.map(|b| b - steps.sim), opts);
            steps += s;
            let mut acc = match base {
                SimResult::Value(v) => v,
                other => return (other, steps),
            };

            // Fast-forward two different (opposite) cases:
            //   * h ignores accumulator (arg 2)
            //   * h echos (or adds a constant each iteration to) the accumulator
            if opts.rec_fast_forward {
                // If h ignores its accumulator (arg 2), every iteration
                // h(i, acc, rest) = h(i, _, rest) is independent of acc.  The final
                // result is therefore h(n-1, 0, rest), computable in O(1).
                if !n.is_zero() && !h.used_args().contains(&2) {
                    let n_m1 = n.clone().pred();
                    let mut h_args: Vec<N> = Vec::with_capacity(rest.len() + 2);
                    h_args.push(n_m1.clone());
                    h_args.push(N::zero()); // accumulator: ignored by h, value is arbitrary
                    h_args.extend(rest.iter().cloned());
                    let (result, s) = simulate_opts(h, &h_args, step_budget.map(|b| b - steps.sim), opts);
                    let sh_base = s.base_approx.to_u64_sat(); // exact: bounded by step budget
                    steps += s;
                    // base_approx += (n - 1) * sh_base
                    let approx = n_m1.checked_mul_u64(sh_base)
                        .unwrap_or_else(|| N::from_u64(u64::MAX));
                    steps.base_approx.saturating_add_assign(approx);
                    return (result, steps);
                }

                // If h(i, acc, rest) = acc + k for a constant k, then
                // R(g, h)(n, rest) = g(rest) + n*k — direct multiplication.
                if let Some(k) = h.acc_plus_k() {
                    // base_approx += n * (2k + 1)
                    let factor = 2 * k + 1;
                    let approx = n.clone().checked_mul_u64(factor)
                        .unwrap_or_else(|| N::from_u64(u64::MAX));
                    steps.base_approx.saturating_add_assign(approx);
                    // Value: acc + n * k (checked for overflow)
                    let val = n.checked_mul_u64(k)
                        .and_then(|nk| acc.checked_add(nk));
                    return match val {
                        Some(v) => (SimResult::Value(v), steps),
                        None => (SimResult::ValueOverflow, steps),
                    };
                }
            }

            let mut i = N::zero();
            while i < n {
                let mut h_args: Vec<N> = Vec::with_capacity(rest.len() + 2);
                h_args.push(i.clone());
                h_args.push(acc.clone());
                h_args.extend(rest.iter().cloned());

                let (result, s) = simulate_opts(h, &h_args, step_budget.map(|b| b - steps.sim), opts);
                steps += s;
                acc = match result {
                    SimResult::Value(v) => v,
                    other => return (other, steps),
                };
                i = match i.succ() {
                    Some(v) => v,
                    None => return (SimResult::ValueOverflow, steps),
                };
            }

            SimResult::Value(acc)
        }

        GrfKind::Min(f) => {
            return simulate_min(f, args, step_budget, opts, &mut |_, _, _| {});
        }
    };

    (result, steps)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::grf;

    fn eval_helper(grf: &Grf, args: &[SmallNat]) -> Option<SmallNat> {
        let (result, _steps) = simulate(grf, args, 1_000_000);
        result.into_value()
    }

    #[test]
    fn test_zero() {
        assert_eq!(eval_helper(&Grf::zero_atom(0), &[]), Some(0));
        assert_eq!(eval_helper(&Grf::zero_atom(2), &[3, 5]), Some(0));
    }

    #[test]
    fn test_succ() {
        assert_eq!(eval_helper(&Grf::succ_atom(), &[0]), Some(1));
        assert_eq!(eval_helper(&Grf::succ_atom(), &[5]), Some(6));
    }

    #[test]
    fn test_proj() {
        assert_eq!(eval_helper(&Grf::proj_atom(2, 1), &[3, 5]), Some(3));
        assert_eq!(eval_helper(&Grf::proj_atom(2, 2), &[3, 5]), Some(5));
        assert_eq!(eval_helper(&Grf::proj_atom(3, 2), &[1, 2, 3]), Some(2));
    }

    #[test]
    fn test_comp_k0_1() {
        // C(S, Z0)() = S(Z0()) = S(0) = 1
        let f = Grf::comp(Grf::succ_atom(), vec![Grf::zero_atom(0)]);
        assert_eq!(eval_helper(&f, &[]), Some(1));
    }

    #[test]
    fn test_comp_k0_2() {
        // C(S, C(S, Z0))() = 2
        let k01 = Grf::comp(Grf::succ_atom(), vec![Grf::zero_atom(0)]);
        let k02 = Grf::comp(Grf::succ_atom(), vec![k01]);
        assert_eq!(eval_helper(&k02, &[]), Some(2));
    }

    #[test]
    fn test_comp_projection_selects_arg() {
        // C(P(2,1), S, Z1)([3]) = P(2,1)(S(3), Z1(3)) = P(2,1)(4, 0) = 4
        let f = Grf::comp(Grf::proj_atom(2, 1), vec![Grf::succ_atom(), Grf::zero_atom(1)]);
        assert_eq!(eval_helper(&f, &[3]), Some(4));
    }

    #[test]
    fn test_rec_plus() {
        // Plus = R(P(1,1), C(S, P(3,2)))
        // Plus(n, m) = n + m
        let g = Grf::proj_atom(1, 1);
        let h = Grf::comp(Grf::succ_atom(), vec![Grf::proj_atom(3, 2)]);
        let plus = Grf::rec(g, h);

        assert_eq!(eval_helper(&plus, &[0, 0]), Some(0));
        assert_eq!(eval_helper(&plus, &[3, 2]), Some(5));
        assert_eq!(eval_helper(&plus, &[0, 7]), Some(7));
        assert_eq!(eval_helper(&plus, &[4, 4]), Some(8));
    }

    #[test]
    fn test_rec_identity() {
        let g = Grf::zero_atom(0);
        let h = Grf::comp(Grf::succ_atom(), vec![Grf::proj_atom(2, 2)]);
        let identity = Grf::rec(g, h);
        assert_eq!(identity.arity(), 1);
        assert_eq!(eval_helper(&identity, &[0]), Some(0));
        assert_eq!(eval_helper(&identity, &[5]), Some(5));
    }

    #[test]
    fn test_rec_affine_k1() {
        // R(Z0, C(S, P(2,2)))(n) = n  (acc starts at 0, +1 each step)
        let f = grf!("R(Z0, C(S, P(2,2)))");
        for n in (0 as SmallNat)..=10 {
            assert_eq!(eval_helper(&f, &[n]), Some(n));
        }
    }

    #[test]
    fn test_rec_affine_k2() {
        // R(S, C(S, C(S, P(3,2))))(n, x) = S(x) + 2*n = x + 2n + 1
        let f = grf!("R(S, C(S, C(S, P(3,2))))");
        for n in (0 as SmallNat)..=5 {
            for x in (0 as SmallNat)..=3 {
                assert_eq!(eval_helper(&f, &[n, x]), Some(2*n + x + 1));
            }
        }
    }

    #[test]
    fn test_min_proj() {
        // M(P(1,1))() = min{i : P(1,1)(i) = 0} = 0
        let f = Grf::min(Grf::proj_atom(1, 1));
        assert_eq!(eval_helper(&f, &[]), Some(0));
    }

    #[test]
    fn test_min_zero() {
        // M(Z1)() = min{i : Z1(i) = 0} = 0
        let f = Grf::min(Grf::zero_atom(1));
        assert_eq!(eval_helper(&f, &[]), Some(0));
    }

    #[test]
    fn test_min_succ_diverges() {
        // M(S)() = min{i : S(i) = 0} = diverges; caught cheaply by is_never_zero.
        let f = Grf::min(Grf::succ_atom());
        let (result, steps) = simulate(&f, &[], 1000);
        assert_eq!(result, SimResult::Diverge);
        assert!(steps.sim < 10, "is_never_zero should short-circuit, got {} steps", steps.sim);
    }

    #[test]
    fn test_step_counting() {
        // These tests verify structural step counts; use_closed_form=false so the CF
        // fast-path doesn't collapse multi-step expressions to a single step.
        let no_cf = SimOpts { use_closed_form: false, ..SimOpts::default() };

        // Z0(): 1 step
        let (_, steps) = simulate_opts::<SmallNat>(&Grf::zero_atom(0), &[], Some(1_000_000), no_cf);
        assert_eq!(steps.sim, 1);

        // C(S, Z0)(): simulate_opts(C) = 1, simulate_opts(Z0) = 1, simulate_opts(S) = 1 → 3 steps
        let f = Grf::comp(Grf::succ_atom(), vec![Grf::zero_atom(0)]);
        let (_, steps) = simulate_opts::<SmallNat>(&f, &[], Some(1_000_000), no_cf);
        assert_eq!(steps.sim, 3);
    }

    #[test]
    fn test_rec_steps() {
        // R(Z0, P(2,2))(3): h = P(2,2) is Proj(_, 2), so the identity ff fires:
        // result = g(rest) = Z0() = 0 in steps: 1 (Rec) + 1 (Z0) = 2.
        // use_closed_form=false so the Rec itself is evaluated structurally.
        let no_cf = SimOpts { use_closed_form: false, ..SimOpts::default() };
        let g = Grf::zero_atom(0);
        let h = Grf::proj_atom(2, 2);
        let r = Grf::rec(g, h);
        let (val, steps) = simulate_opts(&r, &[3], Some(1_000_000), no_cf);
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

    #[test]
    fn test_succ_overflow_u64() {
        // S(u64::MAX) should return ValueOverflow, not wrap.
        let (result, _) = simulate(&Grf::succ_atom(), &[u64::MAX], 100);
        assert_eq!(result, SimResult::ValueOverflow);
    }

    #[test]
    fn test_succ_overflow_bignum() {
        // S(u64::MAX) with bignum should return Value(2^64), not ValueOverflow.
        let big_max = BigNat::from(u64::MAX);
        let (result, _) = simulate_big(&Grf::succ_atom(), &[big_max], 100);
        let expected = BigNat::from(1u64) << 64u32;
        assert_eq!(result, SimResult::Value(expected));
    }

    // --- rec_fast_forward tests ---

    fn no_ff() -> SimOpts {
        SimOpts { use_closed_form: false, rec_fast_forward: false, min_fast_forward: false, min_rec_fuse: false }
    }

    fn no_min_ff() -> SimOpts {
        SimOpts { min_fast_forward: false, ..SimOpts::default() }
    }

    #[test]
    fn test_rec_ff_simple() {
        // Pred: R(Z0, P(2,1))
        // Ignores accumulator
        let r = Grf::rec(Grf::zero_atom(0), Grf::proj_atom(2, 1));
        for n in (0 as SmallNat)..=10 {
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
        let inner = Grf::rec(Grf::zero_atom(1), Grf::proj_atom(3, 1));
        // Monus2 = R(Z0, Pred)
        Grf::rec(Grf::zero_atom(0), inner)
    }

    #[test]
    fn test_rec_ff_nested_correctness() {
        let f = nested_rec();
        // Both with and without fast-forward must give the same answer.
        for n in (0 as SmallNat)..=20 {
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
        let n : SmallNat = 1000;
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
        // R(Z0, P(2,2)): h is Proj(_, 2) so the rec ff fires: result = g(rest) = Z0() = 0.
        // Step counts tested with use_closed_form=false so the Rec is evaluated structurally.
        // With rec_ff:    steps = 1(Rec) + 1(Z0) = 2.
        // Without any ff: steps = 1(Rec) + 1(Z0) + 3*1(P) = 5.
        let r = Grf::rec(Grf::zero_atom(0), Grf::proj_atom(2, 2));
        for n in (0 as SmallNat)..=10 {
            let (v_ff, _) = simulate(&r, &[n], 1_000_000);
            let (v_no, _) = simulate_opts(&r, &[n], Some(1_000_000), no_ff());
            assert_eq!(v_ff.into_value(), Some(0), "ff wrong at n={n}");
            assert_eq!(v_no.into_value(), Some(0), "no_ff wrong at n={n}");
        }
        let no_cf = SimOpts { use_closed_form: false, ..SimOpts::default() };
        let (_, steps_ff) = simulate_opts(&r, &[3], Some(1_000_000), no_cf);
        let (_, steps_no) = simulate_opts(&r, &[3], Some(1_000_000), no_ff());
        assert_eq!(steps_ff.sim, 2, "ff should skip the loop");
        assert_eq!(steps_no.sim, 5);
        assert_eq!(steps_ff.base_approx, steps_no.base_approx);
    }

    #[test]
    fn test_rec_ff_proj_acc_identity_arity2() {
        // R(P(1,1), P(3,2))(n, m): h = P(3,2) returns acc; result = P(1,1)(m) = m for all n.
        let r = Grf::rec(Grf::proj_atom(1, 1), Grf::proj_atom(3, 2));
        for n in (0 as SmallNat)..=5 {
            for m in (0 as SmallNat)..=5 {
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
        for n in (0 as SmallNat)..=8 {
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
        let f = Grf::min(Grf::zero_atom(1));
        let (r, _) = simulate(&f, &[], 1_000_000);
        assert_eq!(r, SimResult::Value(0));
    }

    #[test]
    fn test_min_ff_proj_outer_arg_zero() {
        // M(P(2,2))(0): P(2,2) ignores arg 1 (search var). f(0,0)=0 → Value(0).
        let f = Grf::min(Grf::proj_atom(2, 2));
        let (r, _) = simulate(&f, &[0], 1_000_000);
        assert_eq!(r, SimResult::Value(0));
    }

    #[test]
    fn test_min_ff_proj_outer_arg_diverges() {
        // M(P(2,2))(3): f(0,3)=3≠0 → Diverge.
        let f = Grf::min(Grf::proj_atom(2, 2));
        let (r, _) = simulate(&f, &[3], 1_000_000);
        assert_eq!(r, SimResult::Diverge);
    }

    #[test]
    fn test_min_ff_diverge_vs_oos() {
        // M(P(2,2))(3): P(2,2) ignores arg 1. f(0,3)=3≠0 → Diverge (with ff).
        // Without ff + small budget → OutOfSteps (budget exhausted, not proven diverge).
        // P(2,2).is_never_zero() is false so the is_never_zero short-circuit doesn't fire.
        let f = Grf::min(Grf::proj_atom(2, 2));
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
        let f = Grf::min(Grf::succ_atom());
        let (r_ff, _) = simulate_opts::<SmallNat>(&f, &[], Some(1000), SimOpts::default());
        let (r_no, _) = simulate_opts::<SmallNat>(&f, &[], Some(1000), no_min_ff());
        assert_eq!(r_ff, SimResult::Diverge);
        assert_eq!(r_no, SimResult::Diverge);
    }

    #[test]
    fn test_min_ff_fewer_steps() {
        // M(P(2,2))(3): ff detects divergence in one eval; without ff exhausts budget.
        // P(2,2).is_never_zero() is false so is_never_zero doesn't short-circuit.
        let f = Grf::min(Grf::proj_atom(2, 2));
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
        assert_eq!(simulate_opts::<SmallNat>(&grf, &[], Some(1_000_000), no_rec_fuse()).0, SimResult::Value(0));
    }

    #[test]
    fn test_min_rec_fuse_step_zero() {
        // M(R(C(S,Z0), Z2))(): base=1, h=Z2 always returns 0.
        // Fuse: acc=1 ≠ 0, k=0: h(0,1)=0 → return Value(1).
        let grf = grf!("M(R(C(S,Z0), Z2))");
        assert_eq!(simulate(&grf, &[], 1_000_000).0, SimResult::Value(1));
        assert_eq!(simulate_opts::<SmallNat>(&grf, &[], Some(1_000_000), no_rec_fuse()).0, SimResult::Value(1));
    }

    #[test]
    fn test_min_rec_fuse_correctness() {
        // M(R(P(1,1), C(R(Z0,P(2,1)), P(3,2))))(x) = x.
        // R counts down: base=x, step=pred(acc), reaches 0 at iteration x.
        let grf = grf!("M(R(P(1,1), C(R(Z0,P(2,1)),P(3,2))))");
        let mut opts_fuse = SimOpts::default();
        opts_fuse.use_closed_form = false;
        let mut opts_no = no_rec_fuse();
        opts_no.use_closed_form = false;

        for x in (0 as SmallNat)..=10 {
            let (r_fuse, steps_fuse) = simulate_opts(&grf, &[x], Some(1_000_000), opts_fuse.clone());
            let (r_no, steps_no) = simulate_opts(&grf, &[x], Some(1_000_000), opts_no.clone());
            assert_eq!(r_fuse, SimResult::Value(x), "fuse wrong at x={x}");
            assert_eq!(r_no, SimResult::Value(x), "no_fuse wrong at x={x}");
            // The simulation step counts will differ, but only for x > 0 where loops actually happen.
            if x > 0 {
                assert!(steps_fuse.sim < steps_no.sim);
            }
            assert_eq!(steps_fuse.base_approx, steps_no.base_approx);
        }
    }

    #[test]
    fn test_min_rec_fuse_fewer_steps() {
        // Same GRF as above with x=50: naive is O(x²), fused is O(x).
        let grf = grf!("M(R(P(1,1), C(R(Z0,P(2,1)),P(3,2))))");
        let mut opts_fuse = SimOpts::default();
        opts_fuse.use_closed_form = false;
        let mut opts_no = no_rec_fuse();
        opts_no.use_closed_form = false;

        let (r_fuse, steps_fuse) = simulate_opts(&grf, &[50], None, opts_fuse);
        let (r_no, steps_no) = simulate_opts(&grf, &[50], None, opts_no);
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
        // use_closed_form=false so structural step counts are measured.
        let no_cf = SimOpts { use_closed_form: false, ..SimOpts::default() };
        let r = Grf::rec(Grf::zero_atom(0), Grf::proj_atom(2, 2));
        let (_, s) = simulate_opts(&r, &[3], None, no_cf);
        assert_eq!(s.sim, 2, "sim steps");
        assert_eq!(s.base_approx, 5, "base_approx steps");
        let (_, s_noff) = simulate_opts(&r, &[3], None, no_ff());
        assert_eq!(s.base_approx, s_noff.sim, "base_approx should match no_ff sim");
    }

    #[test]
    fn test_base_approx_min_rec_fuse_exact() {
        // base_approx accuracy is only guaranteed when use_closed_form=false, because CF
        // fast-path collapses sub-call step counts to 1, lowering base_approx.
        let no_cf = SimOpts { use_closed_form: false, ..SimOpts::default() };

        // M(R(C(S,Z0), Z2))(): g()=1, h(k,acc)=0 (atom, no inner Rec → base_approx exact).
        // Fused: acc=1, k=0: h returns 0 → result=1. One loop iteration.
        let grf_0 = grf!("M(R(C(S,Z0), Z2))");
        let (_, s) = simulate_opts::<SmallNat>(&grf_0, &[], None, no_cf);
        let (_, s_noff) = simulate_opts::<SmallNat>(&grf_0, &[], None, no_ff());
        assert_eq!(s.base_approx, s_noff.sim, "M(R(C(S,Z0),Z2)): base_approx={} no_ff={}", s.base_approx, s_noff.sim);

        // M(R(Z0, Z2))(): g()=0 → base case, acc=0 immediately, result=0.
        // base_extra = 1 (skipped Rec node for i=0).
        let grf_base = grf!("M(R(Z0, Z2))");
        let (_, s2) = simulate_opts::<SmallNat>(&grf_base, &[], None, no_cf);
        let (_, s2_noff) = simulate_opts::<SmallNat>(&grf_base, &[], None, no_ff());
        assert_eq!(s2.base_approx, s2_noff.sim, "M(R(Z0,Z2)) base case: base_approx={} no_ff={}", s2.base_approx, s2_noff.sim);

        // For M(R(P(1,1),C(R(Z0,P(2,1)),P(3,2)))):
        // x=0 is exact (acc=0 base case, inner h never evaluated).
        // x>0 is a lower bound because h contains acc-ignored rec_ff inside R(Z0,P(2,1)).
        let grf_plan = grf!("M(R(P(1,1),C(R(Z0,P(2,1)),P(3,2))))");
        let (_, s3) = simulate_opts::<SmallNat>(&grf_plan, &[0], None, no_cf);
        let (_, s3_noff) = simulate_opts(&grf_plan, &[0], None, no_ff());
        assert_eq!(s3.base_approx, s3_noff.sim, "x=0 exact: base_approx={} no_ff={}", s3.base_approx, s3_noff.sim);
        for x in (1 as SmallNat)..=10 {
            let (_, sx) = simulate_opts(&grf_plan, &[x], None, no_cf);
            let (_, sx_noff) = simulate_opts(&grf_plan, &[x], None, no_ff());
            assert!(sx.base_approx >= sx.sim, "x={x}: base_approx must be >= sim");
            assert!(sx.base_approx <= sx_noff.sim, "x={x}: base_approx={} must be <= no_ff={}", sx.base_approx, sx_noff.sim);
        }
    }
}
