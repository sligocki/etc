use crate::grf::{Grf, GrfKind};
use crate::sim_nat::SimNat;
use crate::simulate::SimResult;

/// Affine function over natural numbers: c0 + c1*x1 + ... + ck*xk.
///
/// All coefficients are non-negative (this is an invariant maintained by `closed_form_of`).
/// `eval` returns `None` on arithmetic overflow of `N`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct AffineFn {
    pub arity: usize,
    /// Length arity+1. coeffs[0] = constant term; coeffs[i] = coefficient of xi (1-based).
    pub coeffs: Vec<u64>,
}

impl AffineFn {
    /// Constant-zero function of the given arity.
    pub fn zero(arity: usize) -> Self {
        AffineFn {
            arity,
            coeffs: vec![0; arity + 1],
        }
    }

    /// The successor function S(x) = x + 1.
    pub fn succ() -> Self {
        AffineFn {
            arity: 1,
            coeffs: vec![1, 1],
        }
    }

    /// The projection P^k_i(x1,...,xk) = xi (i is 1-based).
    pub fn proj(arity: usize, i: usize) -> Self {
        debug_assert!(i >= 1 && i <= arity);
        let mut coeffs = vec![0u64; arity + 1];
        coeffs[i] = 1;
        AffineFn { arity, coeffs }
    }

    /// Evaluate the affine function on concrete arguments.
    ///
    /// Returns `None` on arithmetic overflow of `N`.
    pub fn eval<N: SimNat>(&self, args: &[N]) -> Option<N> {
        debug_assert_eq!(args.len(), self.arity);
        let mut acc: N = N::from_u64(self.coeffs[0]);
        for (i, arg) in args.iter().enumerate() {
            let c = self.coeffs[i + 1];
            if c == 0 {
                continue;
            }
            acc = acc.checked_add(arg.clone().checked_mul_u64(c)?)?;
        }
        Some(acc)
    }

    pub fn lift(&self, arity: usize) -> Self {
        assert!(arity >= self.arity);
        let mut coeffs = self.coeffs.clone();
        coeffs.resize(arity + 1, 0);
        AffineFn { arity, coeffs }
    }
}

/// Piecewise function branching on whether the first argument is zero.
///
/// `f(0, x2, ..., xk)   = zero_branch(x2, ..., xk)`  (zero_branch has arity k-1)
/// `f(n, x2, ..., xk)   = pos_branch(n-1, x2, ..., xk)` for n > 0  (pos_branch has arity k)
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct PiecewiseFn {
    pub arity: usize,
    pub branch_index: usize,
    pub zero_branch: Box<ClosedForm>,
    pub pos_branch: Box<ClosedForm>,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct PeriodicFn {
    pub arity: usize,
    pub branch_index: usize,
    pub branches: Vec<Box<ClosedForm>>,
}

impl PiecewiseFn {
    pub fn eval<N: SimNat>(&self, args: &[N]) -> Option<N> {
        assert_eq!(args.len(), self.arity);
        let bi = self.branch_index;
        if args[bi].is_zero() {
            let zero_args: Vec<N> = args[..bi].iter().chain(&args[bi + 1..]).cloned().collect();
            self.zero_branch.eval(&zero_args)
        } else {
            let mut new_args = args.to_vec();
            new_args[bi] = new_args[bi].clone().pred();
            self.pos_branch.eval(&new_args)
        }
    }

    pub fn lift(&self, arity: usize) -> Self {
        assert!(arity >= self.arity);
        PiecewiseFn {
            arity,
            branch_index: self.branch_index,
            zero_branch: Box::new(self.zero_branch.lift(arity - 1)),
            pos_branch: Box::new(self.pos_branch.lift(arity)),
        }
    }
}

/// Semantic representation of a GRF subtree.
///
/// When `closed_form_of(grf)` returns `Some(sem)`, evaluating `sem.eval(args)` gives exactly
/// the same result as simulating `grf` on those args and is guaranteed to be total.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ClosedForm {
    Affine(AffineFn),
    Piecewise(PiecewiseFn),
    NegMod(AffineFn, AffineFn, AffineFn),
    Periodic(PeriodicFn),
}

impl ClosedForm {
    pub fn arity(&self) -> usize {
        match self {
            ClosedForm::Affine(af) => af.arity,
            ClosedForm::Piecewise(pw) => pw.arity,
            ClosedForm::NegMod(a1, _, _) => a1.arity,
            ClosedForm::Periodic(p) => p.arity,
        }
    }

    /// Evaluate the semantic function on concrete arguments.
    ///
    /// Returns `None` if the result would be negative (e.g. affine with negative sum),
    /// or on arithmetic overflow of `N`.
    ///
    /// Iterative: follows the Piecewise tree with in-place mutations on a single
    /// owned buffer, avoiding per-level Vec allocations and deep recursion.
    pub fn eval<N: SimNat>(&self, args: &[N]) -> Option<N> {
        let mut current: &ClosedForm = self;
        let mut buf: Vec<N> = args.to_vec();
        loop {
            match current {
                ClosedForm::Affine(af) => return af.eval(&buf),
                ClosedForm::NegMod(a1, a2, a3) => {
                    let v1 = a1.eval(&buf)?;
                    let v2 = a2.eval(&buf)?;
                    let v3 = a3.eval(&buf)?.checked_add(N::one())?;
                    if v1 >= v2 {
                        return Some(v1.checked_sub(v2).unwrap());
                    } else {
                        let diff = v2.checked_sub(v1).unwrap();
                        let rem = diff.checked_rem(v3.clone())?;
                        return if rem.is_zero() {
                            Some(N::zero())
                        } else {
                            Some(v3.checked_sub(rem)?)
                        };
                    }
                }
                ClosedForm::Periodic(p) => {
                    let val = buf[p.branch_index].to_u64_sat() as usize;
                    current = &p.branches[val % p.branches.len()];
                }
                ClosedForm::Piecewise(pw) => {
                    let bi = pw.branch_index;
                    if buf[bi].is_zero() {
                        buf.remove(bi);
                        current = &pw.zero_branch;
                    } else {
                        buf[bi] = buf[bi].clone().pred();
                        current = &pw.pos_branch;
                    }
                }
            }
        }
    }

    /// Find the minimum i ≥ 0 such that self(i, outer_args) = 0.
    /// Returns `Some(i)` if found, `None` if M(self)(outer_args) diverges.
    ///
    /// - AffineFn: non-negative coefficients → non-decreasing in i → decisive at i=0.
    /// - Piecewise on outer arg (bi ≥ 1): the branch chosen by the outer arg is fixed for
    ///   all i, so we just pick it. Handled iteratively to avoid O(n) stack depth.
    /// - Piecewise on search var (bi = 0): check i=0 via zero_branch; if nonzero,
    ///   M = 1 + M(pos_branch) for the i>0 case.
    pub fn compute_min<N: SimNat>(&self, outer_args: &[N]) -> SimResult<N> {
        let mut cf: &ClosedForm = self;
        let mut outer: Vec<N> = outer_args.to_vec();
        loop {
            match cf {
                ClosedForm::Affine(af) => {
                    // Evaluate at i=0. Non-negative coefficients mean f is non-decreasing
                    // in i, so f(0, outer) > 0 implies f(i, outer) > 0 for all i.
                    let mut full = Vec::with_capacity(outer.len() + 1);
                    full.push(N::zero());
                    full.extend(outer.iter().cloned());
                    return match af.eval(&full) {
                        Some(v) if v.is_zero() => SimResult::Value(N::zero()),
                        _ => SimResult::Diverge,
                    };
                }
                ClosedForm::NegMod(af1, af2, af3) => {
                    let a = af1.coeffs[1];
                    let c = af2.coeffs[1];
                    let e = af3.coeffs[1];

                    let mut full = Vec::with_capacity(outer.len() + 1);
                    full.push(N::zero());
                    full.extend(outer.iter().cloned());

                    let b = match af1.eval(&full) {
                        Some(v) => v,
                        None => return SimResult::ValueOverflow,
                    };
                    let d = match af2.eval(&full) {
                        Some(v) => v,
                        None => return SimResult::ValueOverflow,
                    };
                    let f_raw = match af3.eval(&full) {
                        Some(v) => v,
                        None => return SimResult::ValueOverflow,
                    };
                    let f = match f_raw.clone().checked_add(N::one()) {
                        Some(v) => v,
                        None => return SimResult::ValueOverflow,
                    };

                    let mut min_i: Option<N> = None;

                    let mut update_min = |candidate: N| match &min_i {
                        Some(min) => {
                            if candidate < *min {
                                min_i = Some(candidate);
                            }
                        }
                        None => min_i = Some(candidate),
                    };

                    let (a_is_pos, a_val) = if c >= a {
                        (true, c - a)
                    } else {
                        (false, a - c)
                    };
                    let (b_is_pos, b_val) = if b >= d {
                        (true, b.clone().checked_sub(d.clone()).unwrap())
                    } else {
                        (false, d.clone().checked_sub(b.clone()).unwrap())
                    };

                    if e > 0 {
                        // Subcase 1: A - k*e > 0
                        if a_is_pos {
                            let max_k = a_val / e;
                            for k in 0..=max_k {
                                let den = a_val - k * e;
                                if den > 0 {
                                    let k_f = match f.clone().checked_mul_u64(k) {
                                        Some(v) => v,
                                        None => return SimResult::ValueOverflow,
                                    };
                                    let (num_is_pos, num_val) = if b_is_pos {
                                        (
                                            true,
                                            match b_val.clone().checked_add(k_f) {
                                                Some(v) => v,
                                                None => return SimResult::ValueOverflow,
                                            },
                                        )
                                    } else {
                                        if k_f >= b_val {
                                            (true, k_f.checked_sub(b_val.clone()).unwrap())
                                        } else {
                                            (false, b_val.clone().checked_sub(k_f).unwrap())
                                        }
                                    };

                                    if num_is_pos {
                                        if let Some(rem) =
                                            num_val.clone().checked_rem(N::from_u64(den))
                                        {
                                            if rem.is_zero() {
                                                if let Some(i) = num_val.checked_div_ceil_u64(den) {
                                                    update_min(i);
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }

                        // Subcase 2: A - k*e < 0
                        if !b_is_pos || b_val.is_zero() {
                            let mut k = 0;
                            loop {
                                let k_f = match f.clone().checked_mul_u64(k) {
                                    Some(v) => v,
                                    None => return SimResult::ValueOverflow,
                                };
                                if k_f > b_val {
                                    break;
                                }

                                let den_is_pos = if a_is_pos { a_val > k * e } else { false };

                                if !den_is_pos {
                                    let den_val = if a_is_pos {
                                        (k * e) - a_val
                                    } else {
                                        a_val + (k * e)
                                    };

                                    if den_val > 0 {
                                        let num_val = b_val.clone().checked_sub(k_f).unwrap();
                                        if let Some(rem) =
                                            num_val.clone().checked_rem(N::from_u64(den_val))
                                        {
                                            if rem.is_zero() {
                                                if let Some(i) =
                                                    num_val.checked_div_ceil_u64(den_val)
                                                {
                                                    update_min(i);
                                                }
                                            }
                                        }
                                    }
                                }
                                k += 1;
                            }
                        }

                        // Subcase 3: A - k*e == 0
                        if a_is_pos && a_val % e == 0 {
                            let k = a_val / e;
                            let k_f = match f.clone().checked_mul_u64(k) {
                                Some(v) => v,
                                None => return SimResult::ValueOverflow,
                            };
                            let num_is_zero = if b_is_pos {
                                b_val.is_zero() && k_f.is_zero()
                            } else {
                                b_val == k_f
                            };

                            if num_is_zero {
                                update_min(N::zero());
                            }
                        }
                    } else {
                        // e == 0
                        if a_is_pos && a_val == 0 {
                            if !b_is_pos || b_val.is_zero() {
                                if let Some(rem) = b_val.clone().checked_rem(f.clone()) {
                                    if rem.is_zero() {
                                        update_min(N::zero());
                                    }
                                }
                            }
                        } else if a_is_pos {
                            if a_val == 1 {
                                if b_is_pos {
                                    update_min(b_val);
                                } else {
                                    let rem = b_val.clone().checked_rem(f.clone()).unwrap();
                                    if rem.is_zero() {
                                        update_min(N::zero());
                                    } else {
                                        update_min(f.clone().checked_sub(rem).unwrap());
                                    }
                                }
                            } else {
                                let mut i = N::zero();
                                let mut steps = 0;
                                while steps < 10_000 {
                                    let v1 = match i
                                        .clone()
                                        .checked_mul_u64(a)
                                        .and_then(|m| m.checked_add(b.clone()))
                                    {
                                        Some(v) => v,
                                        None => return SimResult::ValueOverflow,
                                    };
                                    let v2 = match i
                                        .clone()
                                        .checked_mul_u64(c)
                                        .and_then(|m| m.checked_add(d.clone()))
                                    {
                                        Some(v) => v,
                                        None => return SimResult::ValueOverflow,
                                    };
                                    if v1 >= v2 {
                                        if v1 == v2 {
                                            update_min(i.clone());
                                            break;
                                        }
                                    } else {
                                        let diff = v2.checked_sub(v1).unwrap();
                                        if diff.checked_rem(f.clone()).unwrap().is_zero() {
                                            update_min(i.clone());
                                            break;
                                        }
                                    }
                                    i = match i.checked_add(N::one()) {
                                        Some(v) => v,
                                        None => return SimResult::ValueOverflow,
                                    };
                                    steps += 1;
                                }
                            }
                        } else {
                            if a_val == 1 {
                                if !b_is_pos || b_val.is_zero() {
                                    let rem = b_val.clone().checked_rem(f.clone()).unwrap();
                                    update_min(rem);
                                }
                            } else {
                                let mut i = N::zero();
                                let mut steps = 0;
                                while steps < 10_000 {
                                    let v1 = match i
                                        .clone()
                                        .checked_mul_u64(a)
                                        .and_then(|m| m.checked_add(b.clone()))
                                    {
                                        Some(v) => v,
                                        None => return SimResult::ValueOverflow,
                                    };
                                    let v2 = match i
                                        .clone()
                                        .checked_mul_u64(c)
                                        .and_then(|m| m.checked_add(d.clone()))
                                    {
                                        Some(v) => v,
                                        None => return SimResult::ValueOverflow,
                                    };
                                    if v1 >= v2 {
                                        if v1 == v2 {
                                            update_min(i.clone());
                                            break;
                                        }
                                    } else {
                                        let diff = v2.checked_sub(v1).unwrap();
                                        if diff.checked_rem(f.clone()).unwrap().is_zero() {
                                            update_min(i.clone());
                                            break;
                                        }
                                    }
                                    i = match i.checked_add(N::one()) {
                                        Some(v) => v,
                                        None => return SimResult::ValueOverflow,
                                    };
                                    steps += 1;
                                }
                            }
                        }
                    }

                    if let Some(i) = min_i {
                        return SimResult::Value(i);
                    } else if e > 0 || a_val == 1 || a_val == 0 {
                        return SimResult::Diverge;
                    } else {
                        return SimResult::OutOfSteps;
                    }
                }
                ClosedForm::Periodic(p) => {
                    let bi = p.branch_index;
                    if bi == 0 {
                        let mut all_pos = true;
                        let p_len = p.branches.len();
                        for (k, b) in p.branches.iter().enumerate() {
                            if !is_always_pos_on_branch_k(b, k, p_len) {
                                all_pos = false;
                                break;
                            }
                        }
                        if all_pos {
                            return SimResult::Diverge;
                        }
                        return SimResult::OutOfSteps;
                    } else {
                        let oi = bi - 1;
                        let val = outer[oi].to_u64_sat() as usize;
                        cf = &p.branches[val % p.branches.len()];
                    }
                }
                ClosedForm::Piecewise(pw) => {
                    let bi = pw.branch_index;
                    if bi == 0 {
                        // Branch on the search variable i.
                        // i=0: check if zero_branch(outer) = 0.
                        if let Some(v) = pw.zero_branch.eval(&outer) {
                            if v.is_zero() {
                                return SimResult::Value(N::zero());
                            }
                        }
                        // i>0: cf(i, outer) = pos_branch(i-1, outer), so M(cf) = 1 + M(pos_branch).
                        return match pw.pos_branch.compute_min(&outer) {
                            SimResult::Value(j) => match j.succ() {
                                Some(succ) => SimResult::Value(succ),
                                None => SimResult::ValueOverflow,
                            },
                            other => other,
                        };
                    } else {
                        // Branch on outer_args[bi-1] (0-based in outer). This outer arg
                        // is the same for all i, so we can choose the branch unconditionally.
                        let oi = bi - 1;
                        if outer[oi].is_zero() {
                            outer.remove(oi);
                            cf = &pw.zero_branch;
                        } else {
                            outer[oi] = outer[oi].clone().pred();
                            cf = &pw.pos_branch;
                        }
                        // Continue loop with updated cf and outer.
                    }
                }
            }
        }
    }

    pub fn lift(&self, arity: usize) -> Self {
        match self {
            ClosedForm::Affine(af) => ClosedForm::Affine(af.lift(arity)),
            ClosedForm::Piecewise(pw) => ClosedForm::Piecewise(pw.lift(arity)),
            ClosedForm::NegMod(a1, a2, a3) => {
                ClosedForm::NegMod(a1.lift(arity), a2.lift(arity), a3.lift(arity))
            }
            ClosedForm::Periodic(p) => ClosedForm::Periodic(PeriodicFn {
                arity,
                branch_index: p.branch_index,
                branches: p.branches.iter().map(|b| Box::new(b.lift(arity))).collect(),
            }),
        }
    }
}

/// Attempt to extract an exact semantic representation from a GRF.
///
/// Returns `Some(sem)` when the GRF's behavior can be captured algebraically.
/// Handles: all atoms, compositions (affine or piecewise), `R(g,h)` when
/// h = acc+k structurally or semantically (Case A → affine), or h ignores the
/// accumulator (Case B → piecewise, step may be affine or piecewise).
///
/// Returns `None` for `Min` or patterns not yet covered.
pub fn closed_form_of(grf: &Grf) -> Option<ClosedForm> {
    // Short-circuit if already cached (avoids recomputing sub-expressions).
    if let Some(cached) = grf.cf.get() {
        return cached.clone();
    }
    match &grf.kind {
        // Atoms are all Affine
        GrfKind::Zero(k) => Some(ClosedForm::Affine(AffineFn::zero(*k))),
        GrfKind::Succ => Some(ClosedForm::Affine(AffineFn::succ())),
        GrfKind::Proj(k, i) => Some(ClosedForm::Affine(AffineFn::proj(*k, *i))),

        GrfKind::Comp(g, hs, k) => {
            let sem_g = g.closed_form()?.clone();
            let sem_hs: Vec<ClosedForm> = hs
                .iter()
                .map(|h| h.closed_form().cloned())
                .collect::<Option<_>>()?;
            compose(&sem_g, &sem_hs, *k)
        }

        GrfKind::Rec(g, h) => {
            let k_outer = g.arity() + 1;
            let sem_g = g.closed_form()?.clone();
            let sem_h = h.closed_form()?.clone();
            closed_form_of_rec(&sem_g, &sem_h, k_outer)
        }

        GrfKind::Min(f_grf) => closed_form_of_min(f_grf),
    }
}

/// Compute the semantics of R(g, h) from their ClosedForm representations.
///
/// k_outer = R(g,h).arity() = sem_g.arity()+1 = sem_h.arity()-1.
///
/// Three cases (tried in order):
///   A: sem_h is Affine with acc+j pattern  →  affine result
///   B: sem_h ignores acc (arg 2)           →  Piecewise(zero=sem_g, pos=sem_h-without-acc)
///   C: sem_h is Piecewise on counter       →  recurse: new_g = B_z∘g, new_h = B_p
fn closed_form_of_rec(
    sem_g: &ClosedForm,
    sem_h: &ClosedForm,
    k_outer: usize,
) -> Option<ClosedForm> {
    closed_form_of_rec_internal(sem_g, sem_h, k_outer, 1)
}

pub fn closed_form_of_rec_internal(
    sem_g: &ClosedForm,
    sem_h: &ClosedForm,
    k_outer: usize,
    split_budget: usize,
) -> Option<ClosedForm> {
    // Case A: h(n, acc, rest) = j + acc  (j = coeffs[0], acc-coeff=1, rest-coeffs=0)
    if let ClosedForm::Affine(af_h) = sem_h {
        if af_h.coeffs[1] == 0 && af_h.coeffs[2] == 1 && af_h.coeffs[3..].iter().all(|&c| c == 0) {
            if let ClosedForm::Affine(g_af) = sem_g {
                let j = af_h.coeffs[0];
                let mut new_coeffs = Vec::with_capacity(k_outer + 1);
                new_coeffs.push(g_af.coeffs[0]);
                new_coeffs.push(j);
                new_coeffs.extend_from_slice(&g_af.coeffs[1..]);
                return Some(ClosedForm::Affine(AffineFn {
                    arity: k_outer,
                    coeffs: new_coeffs,
                }));
            }
        }
    }

    // Case B: h ignores accumulator (arg 2)  →  drop acc to get h': (counter, rest) → value
    if closed_form_ignores_arg(sem_h, 2) {
        if let Some(h_prime) = drop_arg(sem_h, 2) {
            return Some(make_piecewise(k_outer, 0, sem_g.clone(), h_prime));
        }
    }

    // Case Periodic: h ignores step counter (arg 1) -> sequence only depends on acc and rest.
    // If it falls into a cycle, we can represent it with PeriodicFn (and PiecewiseFn for pre-period).
    if sem_h.arity() == k_outer + 1 && closed_form_ignores_arg(sem_h, 1) {
        let mut seq = Vec::new();
        seq.push(sem_g.clone());
        let mut cycle_found = None;
        let k_rest = k_outer - 1;
        for step in 1..=50 {
            let prev = seq.last().unwrap().clone();
            let mut inners = Vec::with_capacity(k_outer + 1);
            inners.push(ClosedForm::Affine(AffineFn::zero(k_rest))); // i is ignored
            inners.push(prev); // acc
            for m in 1..=k_rest {
                inners.push(ClosedForm::Affine(AffineFn::proj(k_rest, m)));
            }
            if let Some(next_cf) = compose(sem_h, &inners, k_rest) {
                if let Some(j) = seq.iter().position(|x| x == &next_cf) {
                    cycle_found = Some((j, step));
                    break;
                }
                seq.push(next_cf);
            } else {
                break;
            }
        }
        if let Some((j, k)) = cycle_found {
            let cycle_branches = seq[j..k].to_vec();
            if cycle_branches.len() == 1 {
                let mut res = prepend_arg(&cycle_branches[0]);
                for m in (0..j).rev() {
                    res = make_piecewise(k_outer, 0, seq[m].clone(), res);
                }
                return Some(res);
            }
            let mut res = ClosedForm::Periodic(PeriodicFn {
                arity: k_outer,
                branch_index: 0,
                branches: cycle_branches
                    .into_iter()
                    .map(|b| Box::new(prepend_arg(&b)))
                    .collect(),
            });
            // Wrap in Piecewise for pre-period (in reverse order)
            for m in (0..j).rev() {
                res = make_piecewise(k_outer, 0, seq[m].clone(), res);
            }
            return Some(res);
        }
    }

    // Case C: h is Piecewise on counter (arg 1)  →  peel one Piecewise layer off h
    if let ClosedForm::Piecewise(pw_h) = sem_h {
        if pw_h.branch_index == 0 {
            // Build g'(rest) = B_z(g(rest), rest):
            //   B_z has arity k_outer (receives acc=g(rest), rest)
            //   We compose B_z with [sem_g, P(k-1,1), ..., P(k-1,k-1)]
            let b_z: &ClosedForm = &pw_h.zero_branch;
            let k_rest = k_outer - 1;
            let mut inner_for_g_prime: Vec<ClosedForm> = vec![sem_g.clone()];
            for i in 1..=k_rest {
                inner_for_g_prime.push(ClosedForm::Affine(AffineFn::proj(k_rest, i)));
            }
            if b_z.arity() == inner_for_g_prime.len() {
                if let Some(sem_g_prime) = compose(b_z, &inner_for_g_prime, k_rest) {
                    let b_p: &ClosedForm = &pw_h.pos_branch;
                    if let Some(pos_branch) =
                        closed_form_of_rec_internal(&sem_g_prime, b_p, k_outer, split_budget)
                    {
                        return Some(make_piecewise(k_outer, 0, sem_g.clone(), pos_branch));
                    }
                }
            }
        }
    }

    // Case D: h ignores counter (arg 1) and the step has a 1-step fixed point.
    // h'(acc, rest) = h with counter dropped.  Compute one_step = h'(g(rest), rest).
    // If h' is stable (each leaf Affine is either pure identity or ignores acc),
    // then one_step is a fixed point: f(n≥1, rest) = one_step(rest).
    if closed_form_ignores_arg(sem_h, 1) {
        if let Some(h_prime) = drop_arg(sem_h, 1) {
            if h_prime_is_stable(&h_prime) {
                let k_rest = k_outer - 1;
                let mut inners: Vec<ClosedForm> = vec![sem_g.clone()];
                for i in 1..=k_rest {
                    inners.push(ClosedForm::Affine(AffineFn::proj(k_rest, i)));
                }
                if let Some(one_step) = compose(&h_prime, &inners, k_rest) {
                    let pos_branch = prepend_arg(&one_step);
                    return Some(make_piecewise(k_outer, 0, sem_g.clone(), pos_branch));
                }
            }
        }
    }

    // Case E: h ignores counter (arg 1) and is Piecewise branching on acc (arg 2 in h, which is arg 1 in h_prime).
    if closed_form_ignores_arg(sem_h, 1) {
        if let Some(h_prime) = drop_arg(sem_h, 1) {
            if let ClosedForm::Piecewise(pw) = &h_prime {
                if pw.branch_index == 0 {
                    if let ClosedForm::Affine(af) = &*pw.pos_branch {
                        if af.coeffs[0] == 0
                            && af.coeffs[1] == 1
                            && af.coeffs[2..].iter().all(|&c| c == 0)
                        {
                            if let ClosedForm::Affine(g_af) = sem_g {
                                let g_lifted = prepend_arg_affine(g_af);
                                let n_proj = AffineFn::proj(k_outer, 1);
                                if let ClosedForm::Affine(reset_af) = &*pw.zero_branch {
                                    let reset_lifted = prepend_arg_affine(reset_af);
                                    return Some(make_neg_mod(g_lifted, n_proj, reset_lifted));
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    // Case G: h is Piecewise branching on acc (arg 2 in h), and pos_branch ignores acc.
    if let ClosedForm::Piecewise(pw) = sem_h {
        if pw.branch_index == 1 {
            let h_p = &pw.pos_branch;
            let h_z = &pw.zero_branch;

            if closed_form_ignores_arg(h_p, 2) {
                if let Some(h_p_no_acc) = drop_arg(h_p, 2) {
                    let mut cur_f = sem_g.clone();
                    let mut prefix = Vec::new();
                    let mut trapped = false;

                    for step in 0..10 {
                        prefix.push(cur_f.clone());
                        if is_always_pos(&cur_f) {
                            // Verify that h_p_no_acc(step) is strictly positive,
                            // to ensure it stays trapped forever.
                            let mut tail_inners = Vec::with_capacity(k_outer);
                            tail_inners.push(ClosedForm::Affine({
                                let mut af = AffineFn::zero(k_outer - 1);
                                af.coeffs[0] = step as u64;
                                af
                            }));
                            for i in 1..k_outer {
                                tail_inners
                                    .push(ClosedForm::Affine(AffineFn::proj(k_outer - 1, i)));
                            }
                            if let Some(tail_at_step) =
                                compose(&h_p_no_acc, &tail_inners, k_outer - 1)
                            {
                                if is_always_pos(&tail_at_step) {
                                    trapped = true;
                                    break;
                                }
                            }
                        }

                        if is_always_zero(&cur_f) {
                            let mut inners = Vec::with_capacity(k_outer);
                            inners.push(ClosedForm::Affine({
                                let mut af = AffineFn::zero(k_outer - 1);
                                af.coeffs[0] = step as u64;
                                af
                            }));
                            for i in 1..k_outer {
                                inners.push(ClosedForm::Affine(AffineFn::proj(k_outer - 1, i)));
                            }
                            if let Some(next_f) = compose(h_z, &inners, k_outer - 1) {
                                cur_f = next_f;
                            } else {
                                break;
                            }
                        } else {
                            break;
                        }
                    }

                    if trapped {
                        let shift = prefix.len() as u64 - 1;
                        let mut inners = Vec::with_capacity(k_outer);
                        inners.push(ClosedForm::Affine({
                            let mut af = AffineFn::proj(k_outer, 1);
                            af.coeffs[0] = shift;
                            af
                        }));
                        for i in 2..=k_outer {
                            inners.push(ClosedForm::Affine(AffineFn::proj(k_outer, i)));
                        }

                        if let Some(mut tail) = compose(&h_p_no_acc, &inners, k_outer) {
                            for p in prefix.into_iter().rev() {
                                tail = make_piecewise(k_outer, 0, p, tail);
                            }
                            return Some(tail);
                        }
                    }
                }
            }
        }
    }

    // Case G2: h is Piecewise branching on acc (arg 2 in h), and pos_branch is EXACTLY acc.
    if let ClosedForm::Piecewise(pw) = sem_h {
        if pw.branch_index == 1 {
            let h_p = &pw.pos_branch;
            let h_z = &pw.zero_branch;

            let is_acc_identity = if let ClosedForm::Affine(af) = h_p.as_ref() {
                af.coeffs.len() > 2
                    && af.coeffs[0] == 1
                    && af.coeffs[2] == 1
                    && af
                        .coeffs
                        .iter()
                        .enumerate()
                        .filter(|(i, &c)| c != 0 && *i != 0 && *i != 2)
                        .count()
                        == 0
            } else {
                false
            };

            if is_acc_identity {
                let mut cur_f = sem_g.clone();
                let mut prefix = Vec::new();
                let mut trapped = false;

                for step in 0..10 {
                    prefix.push(cur_f.clone());
                    if is_always_pos(&cur_f) {
                        trapped = true;
                        break;
                    }

                    if is_always_zero(&cur_f) {
                        let mut inners = Vec::with_capacity(k_outer);
                        inners.push(ClosedForm::Affine({
                            let mut af = AffineFn::zero(k_outer - 1);
                            af.coeffs[0] = step as u64;
                            af
                        }));
                        for i in 1..k_outer {
                            inners.push(ClosedForm::Affine(AffineFn::proj(k_outer - 1, i)));
                        }
                        if let Some(next_f) = compose(h_z, &inners, k_outer - 1) {
                            cur_f = next_f;
                        } else {
                            break;
                        }
                    } else {
                        break;
                    }
                }

                if trapped {
                    let mut tail = prepend_arg(&cur_f);
                    for p in prefix.into_iter().rev() {
                        tail = make_piecewise(k_outer, 0, p, tail);
                    }
                    return Some(tail);
                }
            }
        }
    }

    // Case F: h is Piecewise on an outer argument (branch_index ≥ 2, i.e. not counter/acc).
    //
    // h branches on outer arg j_b = bi (1-based in b's args).  Peel one Piecewise layer:
    //   zero-slice (b's arg j_b = 0): recurse with g_zero and h.zero_branch, arity k_outer-1.
    //   pos-slice  (b's arg j_b > 0): recurse with g (unchanged) and h.pos_branch, arity k_outer.
    // The outer result is Piecewise with branch_index = bi-1 (0-based in b's args).
    if let ClosedForm::Piecewise(pw_h) = sem_h {
        let bi = pw_h.branch_index;
        if bi >= 2 {
            // j_b is the 1-based index in b's args that h branches on.
            // h's arg bi+1 (1-based) = b's arg bi (1-based), since h's args are
            // (counter, acc, b_arg2, b_arg3, ...).
            let j_b = bi; // 1-based in b's full arg list

            // g has arity k_outer-1; its arg j_b-1 (1-based) = b's arg j_b.
            let g_zero = zero_face_at(sem_g, j_b - 1);
            // h.zero_branch has arity k_outer (counter + acc + rest-without-arg-j_b).
            let h_zero = pw_h.zero_branch.as_ref();
            if let Some(zero_b) =
                closed_form_of_rec_internal(&g_zero, h_zero, k_outer - 1, split_budget)
            {
                // h.pos_branch is called with b's arg j_b decremented by 1.  The base g is
                // evaluated in that same decremented context, so shift g to compensate:
                // g_pos(z') = g(z'+1).
                let g_pos = pos_face_at(sem_g, j_b - 1);
                let h_pos = pw_h.pos_branch.as_ref();
                if let Some(pos_b) =
                    closed_form_of_rec_internal(&g_pos, h_pos, k_outer, split_budget)
                {
                    return Some(make_piecewise(k_outer, j_b - 1, zero_b, pos_b));
                }
            }
        }
    }

    // Fallback: Split on rest variables if budget allows
    if split_budget > 0 {
        // j is the 1-based index in `g` (from 1 to k_outer - 1).
        // It corresponds to the 0-based branch_index `j` in `b`.
        // In `h`, the same rest variable is at 1-based index `j + 2` (since h has counter and acc).
        for j in 1..k_outer {
            let g_zero = zero_face_at(sem_g, j);
            let h_zero = zero_face_at(sem_h, j + 2);
            if let Some(zero_cf) =
                closed_form_of_rec_internal(&g_zero, &h_zero, k_outer - 1, split_budget - 1)
            {
                let g_pos = pos_face_at(sem_g, j);
                let h_pos = pos_face_at(sem_h, j + 2);
                if let Some(pos_cf) =
                    closed_form_of_rec_internal(&g_pos, &h_pos, k_outer, split_budget - 1)
                {
                    return Some(make_piecewise(k_outer, j, zero_cf, pos_cf));
                }
            }
        }
    }

    None
}

/// Compute the ClosedForm for M(f_grf) when possible.
///
/// Because all AffineFn coefficients are non-negative, f(i, args) >= f(0, args) for all i >= 0.
/// So M(f)(args) is finite iff f(0, args) = 0, and then M(f)(args) = 0.
/// If f(0, args) = 0 for ALL args, M(f) = 0 always.
fn closed_form_of_min(f_grf: &Grf) -> Option<ClosedForm> {
    let cf = closed_form_of(f_grf)?;
    let at_zero = zero_face_at(&cf, 1); // f with search variable (arg 1) set to 0
    if is_always_zero(&at_zero) {
        return Some(ClosedForm::Affine(AffineFn::zero(cf.arity() - 1)));
    }
    None
}

/// Returns true when `sem` ignores argument at 1-based `idx` for all inputs.
pub fn affine_ignores_arg(af: &AffineFn, idx: usize) -> bool {
    idx == 0 || idx > af.arity || af.coeffs[idx] == 0
}

pub fn closed_form_ignores_arg(sem: &ClosedForm, idx: usize) -> bool {
    match sem {
        ClosedForm::Affine(af) => af.arity < idx || af.coeffs[idx] == 0,
        ClosedForm::Piecewise(pw) => {
            let b = pw.branch_index + 1; // 1-based branch variable
            if idx == b {
                return false; // branch variable is always used for branching
            }
            // In zero_branch, x_b is dropped: positions < b map to same idx,
            // positions > b map to idx-1.
            let idx_in_zero = if idx < b { idx } else { idx - 1 };
            closed_form_ignores_arg(&pw.zero_branch, idx_in_zero)
                && closed_form_ignores_arg(&pw.pos_branch, idx)
        }
        ClosedForm::NegMod(a1, a2, a3) => {
            affine_ignores_arg(a1, idx)
                && affine_ignores_arg(a2, idx)
                && affine_ignores_arg(a3, idx)
        }
        ClosedForm::Periodic(p) => {
            if idx == p.branch_index + 1 {
                false
            } else {
                let j_inner = if idx <= p.branch_index { idx } else { idx - 1 };
                p.branches
                    .iter()
                    .all(|b| closed_form_ignores_arg(b, j_inner))
            }
        }
    }
}

/// General semantic composition: C(h, g1..gm)(x1..xk) = h(g1(x), ..., gm(x)).
///
/// Handles any mix of Affine/Piecewise components by distributing piecewise
/// branching on x1 through the composition. For Piecewise h, requires that g1
/// is semantically equivalent to the x1 projection (coeffs=[0,1,0..0]) so that
/// the branching condition g1(x)=0 aligns with x1=0.
///
/// Recursion terminates because each call either reaches the all-Affine base case
/// or reduces the maximum Piecewise nesting depth by one.
fn compose(h: &ClosedForm, inners: &[ClosedForm], arity: usize) -> Option<ClosedForm> {
    // Base case: 0-arity composition — h is a constant, no inputs consumed.
    if inners.is_empty() {
        return Some(h.lift(arity));
    }

    debug_assert_eq!(h.arity(), inners.len());
    debug_assert!(inners.iter().all(|s| s.arity() == arity));

    // First check if ANY inner is Piecewise. If so, we distribute on its branching variable.
    // Find j: the branching variable all Piecewise inners agree on.
    let mut j_opt: Option<usize> = None;
    for inner in inners {
        if let ClosedForm::Piecewise(pw) = inner {
            let j2 = pw.branch_index + 1;
            match j_opt {
                None => j_opt = Some(j2),
                Some(j1) if j1 != j2 => return None, // Piecewise inners disagree
                _ => {}
            }
        }
    }

    if let Some(j) = j_opt {
        if arity == 0 {
            return None;
        }
        // Correctness: pos_face_at for Affine adjusts the constant, so Affine
        // inners depending on xj are fine. Piecewise inners on a *different*
        // variable are returned unchanged by pos_face_at, which is only valid
        // when they do not depend on xj.
        for inner in inners {
            if let ClosedForm::Piecewise(pw) = inner {
                if pw.branch_index + 1 != j && !closed_form_ignores_arg(inner, j) {
                    return None;
                }
            }
        }
        let zero_inners: Vec<ClosedForm> = inners.iter().map(|s| zero_face_at(s, j)).collect();
        let pos_inners: Vec<ClosedForm> = inners.iter().map(|s| pos_face_at(s, j)).collect();
        let zero_sem = compose(h, &zero_inners, arity - 1)?;
        let pos_sem = compose(h, &pos_inners, arity)?;
        return Some(make_piecewise(arity, j - 1, zero_sem, pos_sem));
    }

    // At this point, NO inner is Piecewise. All inners are Affine!
    match h {
        ClosedForm::Affine(h_af) => {
            let mut inner_afs = Vec::with_capacity(inners.len());
            for s in inners {
                match s {
                    ClosedForm::Affine(af) => inner_afs.push(af.clone()),
                    _ => return None, // Cannot compose Affine outside of NegMod yet
                }
            }
            Some(ClosedForm::Affine(compose_affine(h_af, &inner_afs)?))
        }
        ClosedForm::Piecewise(pw) => {
            // If h always returns 0, so does the composition.
            if is_always_zero(h) {
                return Some(ClosedForm::Affine(AffineFn::zero(arity)));
            }

            // h branches on y_{bi+1} = inners[bi](x).
            let bi = pw.branch_index;
            let g_branch = &inners[bi];

            // Case 1: inners[bi] is identically 0 → always fire zero_branch on rest.
            if is_always_zero(g_branch) {
                let rest: Vec<ClosedForm> = inners
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| *i != bi)
                    .map(|(_, s)| s.clone())
                    .collect();
                let raw = if rest.is_empty() {
                    pw.zero_branch.as_ref().clone()
                } else {
                    compose(&pw.zero_branch, &rest, arity)?
                };
                return Some(raw.lift(arity));
            }

            // Case 2: inners[bi] ≥ 1 always → always fire pos_branch(inners[bi]-1, rest).
            if let Some(g_branch_m1) = always_pos_minus_one(g_branch) {
                let mut pos_inners: Vec<ClosedForm> = inners.to_vec();
                pos_inners[bi] = ClosedForm::Affine(g_branch_m1);
                return compose(&pw.pos_branch, &pos_inners, arity);
            }

            // Case 3: inners[bi] is a projection of xj → distribute on xj=0 boundary.
            if arity == 0 {
                return None;
            }
            let j = is_proj_of(g_branch)?;
            // Correctness: Piecewise inners on a different variable must not depend on xj
            // (their pos_face_at returns them unchanged, only valid when xj-independent).
            // Affine inners are fine: pos_face_at adjusts their constant to compensate.
            let others_ok =
                inners
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| *i != bi)
                    .all(|(_, inner)| {
                        if let ClosedForm::Piecewise(pw2) = inner {
                            pw2.branch_index + 1 == j || closed_form_ignores_arg(inner, j)
                        } else {
                            true
                        }
                    });
            if !others_ok {
                return None;
            }
            // Zero branch: compose zero_branch with all inners except inners[bi],
            // each substituted at xj=0.
            let zero_inners: Vec<ClosedForm> = inners
                .iter()
                .enumerate()
                .filter(|(i, _)| *i != bi)
                .map(|(_, inner)| zero_face_at(inner, j))
                .collect();
            let zero_arity = arity - 1;
            let zero_sem = if zero_inners.is_empty() {
                pw.zero_branch.as_ref().clone().lift(zero_arity)
            } else {
                compose(&pw.zero_branch, &zero_inners, zero_arity)?.lift(zero_arity)
            };
            // Pos branch: inners[bi]=xj delivers xj-1 ✓; apply pos_face_at to all
            // other inners so they evaluate to their caller-context value when xj is
            // decremented by the outer Piecewise.
            let mut pos_inners: Vec<ClosedForm> = inners.to_vec();
            for (i, inner) in pos_inners.iter_mut().enumerate() {
                if i != bi {
                    *inner = pos_face_at(inner, j);
                }
            }
            let pos_sem = compose(&pw.pos_branch, &pos_inners, arity)?;
            Some(make_piecewise(arity, j - 1, zero_sem, pos_sem))
        }
        ClosedForm::Periodic(p) => {
            let new_branch_expr = inners[p.branch_index].clone();
            if let ClosedForm::Affine(af) = new_branch_expr {
                if af.coeffs.iter().skip(1).all(|&c| c == 0) {
                    let val = af.coeffs[0] as usize;
                    return compose(&p.branches[val % p.branches.len()], &inners, arity);
                }
                let non_zeros: Vec<_> = af
                    .coeffs
                    .iter()
                    .enumerate()
                    .skip(1)
                    .filter(|(_, &c)| c != 0)
                    .collect();
                if non_zeros.len() == 1 && *non_zeros[0].1 == 1 {
                    let j = non_zeros[0].0;
                    let const_val = af.coeffs[0] as usize;
                    let p_len = p.branches.len();
                    let mut new_branches = Vec::with_capacity(p_len);
                    for i in 0..p_len {
                        let chosen = (i + const_val) % p_len;
                        new_branches.push(Box::new(compose(&p.branches[chosen], &inners, arity)?));
                    }
                    return Some(ClosedForm::Periodic(PeriodicFn {
                        arity,
                        branch_index: j - 1,
                        branches: new_branches,
                    }));
                }
            }
            return None;
        }
        ClosedForm::NegMod(a1, a2, a3) => {
            let inners_af: Option<Vec<AffineFn>> = inners
                .iter()
                .map(|cf| {
                    if let ClosedForm::Affine(af) = cf {
                        Some(af.clone())
                    } else {
                        None
                    }
                })
                .collect();
            let inners_af = inners_af?;
            let c1 = compose_affine(a1, &inners_af)?;
            let c2 = compose_affine(a2, &inners_af)?;
            let c3 = compose_affine(a3, &inners_af)?;
            Some(make_neg_mod(c1, c2, c3))
        }
    }
}

/// Substitute xj=0 (1-based `j`) and drop it from the argument list.
/// The result has arity one less than `sem`.

fn zero_face_at_affine(af: &AffineFn, j: usize) -> AffineFn {
    let new_coeffs = drop_index(&af.coeffs, j);
    AffineFn {
        arity: af.arity - 1,
        coeffs: new_coeffs,
    }
}

fn pos_face_at_affine(af: &AffineFn, j: usize) -> AffineFn {
    let mut new_coeffs = af.coeffs.clone();
    new_coeffs[0] = new_coeffs[0].saturating_add(new_coeffs[j]);
    AffineFn {
        arity: af.arity,
        coeffs: new_coeffs,
    }
}

fn zero_face_at(sem: &ClosedForm, j: usize) -> ClosedForm {
    match sem {
        ClosedForm::Affine(af) => {
            let new_coeffs = drop_index(&af.coeffs, j);
            ClosedForm::Affine(AffineFn {
                arity: af.arity - 1,
                coeffs: new_coeffs,
            })
        }
        ClosedForm::Piecewise(pw) => {
            let b = pw.branch_index + 1; // 1-based branch variable
            if j == b {
                // Setting the branch arg to 0 always fires the zero_branch,
                // which already has this arg dropped.
                *pw.zero_branch.clone()
            } else {
                // Recursively substitute xj=0 in both branches, adjusting index.
                let j_in_zero = if j < b { j } else { j - 1 };
                let new_zero = zero_face_at(&pw.zero_branch, j_in_zero);
                let new_pos = zero_face_at(&pw.pos_branch, j);
                let new_bi = if j < b {
                    pw.branch_index - 1
                } else {
                    pw.branch_index
                };
                make_piecewise(pw.arity - 1, new_bi, new_zero, new_pos)
            }
        }
        ClosedForm::NegMod(a1, a2, a3) => ClosedForm::NegMod(
            zero_face_at_affine(a1, j),
            zero_face_at_affine(a2, j),
            zero_face_at_affine(a3, j),
        ),
        ClosedForm::Periodic(p) => {
            let b = p.branch_index + 1;
            if j == b {
                zero_face_at(&p.branches[0], j)
            } else {
                let new_branches = p
                    .branches
                    .iter()
                    .map(|br| Box::new(zero_face_at(br, j)))
                    .collect();
                let new_bi = if j < b {
                    p.branch_index - 1
                } else {
                    p.branch_index
                };
                ClosedForm::Periodic(PeriodicFn {
                    arity: p.arity - 1,
                    branch_index: new_bi,
                    branches: new_branches,
                })
            }
        }
    }
}

/// The "pos branch" face when xj > 0 is decremented by an outer Piecewise.
///
/// In the pos-branch context xj represents xj_caller − 1.  Each sem must be
/// adjusted so that `pos_face_at(s, j)(x with xj = n)` equals `s(x with xj = n+1)`.
///
/// - Affine: add coeffs[j] to coeffs[0] (shifts the constant to compensate).
/// - Piecewise branching on xj: take pos_branch (already defined as "called with xj-1").
/// - Piecewise branching on xk (k≠j): recurse into both branches.  In the zero_branch
///   (where xk is absent) the index for xj shifts to j_in_zero = j if j<k else j-1.
fn pos_face_at(sem: &ClosedForm, j: usize) -> ClosedForm {
    match sem {
        ClosedForm::Affine(af) => {
            let mut new_coeffs = af.coeffs.clone();
            new_coeffs[0] = new_coeffs[0].saturating_add(new_coeffs[j]);
            ClosedForm::Affine(AffineFn {
                arity: af.arity,
                coeffs: new_coeffs,
            })
        }
        ClosedForm::Piecewise(pw) => {
            let b = pw.branch_index + 1; // 1-based branch variable
            if b == j {
                *pw.pos_branch.clone()
            } else {
                let j_in_zero = if j < b { j } else { j - 1 };
                let new_zero = pos_face_at(&pw.zero_branch, j_in_zero);
                let new_pos = pos_face_at(&pw.pos_branch, j);
                make_piecewise(pw.arity, pw.branch_index, new_zero, new_pos)
            }
        }
        ClosedForm::NegMod(a1, a2, a3) => ClosedForm::NegMod(
            pos_face_at_affine(a1, j),
            pos_face_at_affine(a2, j),
            pos_face_at_affine(a3, j),
        ),
        ClosedForm::Periodic(p) => {
            let b = p.branch_index + 1;
            if j == b {
                let p_len = p.branches.len();
                let mut shifted = Vec::with_capacity(p_len);
                for i in 0..p_len {
                    shifted.push(Box::new(pos_face_at(&p.branches[(i + 1) % p_len], j)));
                }
                ClosedForm::Periodic(PeriodicFn {
                    arity: p.arity,
                    branch_index: p.branch_index,
                    branches: shifted,
                })
            } else {
                let new_branches = p
                    .branches
                    .iter()
                    .map(|br| Box::new(pos_face_at(br, j)))
                    .collect();
                ClosedForm::Periodic(PeriodicFn {
                    arity: p.arity,
                    branch_index: p.branch_index,
                    branches: new_branches,
                })
            }
        }
    }
}

/// If `sem` is a pure projection f(x) = xj (1-based j), return `Some(j)`.
fn is_proj_of(sem: &ClosedForm) -> Option<usize> {
    match sem {
        ClosedForm::Affine(af) if af.coeffs[0] == 0 => {
            let mut found: Option<usize> = None;
            for (i, &c) in af.coeffs[1..].iter().enumerate() {
                if c != 0 {
                    if c != 1 || found.is_some() {
                        return None; // non-unit coefficient or multiple non-zero
                    }
                    found = Some(i + 1); // 1-based
                }
            }
            found
        }
        _ => None,
    }
}

/// Prepend one ignored argument at position 1, shifting all existing arg indices right.
/// Used to turn a (rest)-indexed ClosedForm into a (counter, rest)-indexed ClosedForm.

fn prepend_arg_affine(af: &AffineFn) -> AffineFn {
    let mut new_coeffs = vec![af.coeffs[0], 0];
    new_coeffs.extend_from_slice(&af.coeffs[1..]);
    AffineFn {
        arity: af.arity + 1,
        coeffs: new_coeffs,
    }
}

fn prepend_arg(sem: &ClosedForm) -> ClosedForm {
    match sem {
        ClosedForm::Affine(af) => {
            let mut new_coeffs = vec![af.coeffs[0], 0]; // constant, then new ignored arg
            new_coeffs.extend_from_slice(&af.coeffs[1..]);
            ClosedForm::Affine(AffineFn {
                arity: af.arity + 1,
                coeffs: new_coeffs,
            })
        }
        ClosedForm::Piecewise(pw) => ClosedForm::Piecewise(PiecewiseFn {
            arity: pw.arity + 1,
            branch_index: pw.branch_index + 1, // all indices shift right by 1
            zero_branch: Box::new(prepend_arg(&pw.zero_branch)),
            pos_branch: Box::new(prepend_arg(&pw.pos_branch)),
        }),
        ClosedForm::NegMod(a1, a2, a3) => ClosedForm::NegMod(
            prepend_arg_affine(a1),
            prepend_arg_affine(a2),
            prepend_arg_affine(a3),
        ),
        ClosedForm::Periodic(p) => ClosedForm::Periodic(PeriodicFn {
            arity: p.arity + 1,
            branch_index: p.branch_index + 1,
            branches: p.branches.clone(),
        }),
    }
}

/// Returns true when iterating h'(acc, rest) from any starting point reaches a fixed
/// point after at most one step.  h' has args (acc, rest1, ...).
///
/// The condition: every Affine leaf must either
///   (a) be pure identity on acc: acc-coeff=1 and all rest-coeffs=0, OR
///   (b) ignore acc entirely: acc-coeff=0.
/// Piecewise branching on acc (bi=0) is rejected (too complex).
fn h_prime_is_stable(h_prime: &ClosedForm) -> bool {
    match h_prime {
        ClosedForm::Affine(af) => {
            let acc_coeff = if af.arity >= 1 { af.coeffs[1] } else { 0 };
            match acc_coeff {
                0 => true, // constant after 1 step
                // Pure identity: f(acc, rest) = acc exactly (no constant shift, no rest terms).
                // A constant term like acc+1 is NOT stable — it grows without bound.
                1 => af.coeffs[0] == 0 && af.coeffs[2..].iter().all(|&c| c == 0),
                _ => false,
            }
        }
        ClosedForm::Piecewise(pw) => {
            if pw.branch_index == 0 {
                return false; // branches on acc — too complex
            }
            h_prime_is_stable(&pw.zero_branch) && h_prime_is_stable(&pw.pos_branch)
        }
        ClosedForm::NegMod(_, _, _) => false,
        ClosedForm::Periodic(p) => false,
    }
}

/// Returns true when `sem` evaluates to 0 for all natural-number inputs.
fn is_always_pos(sem: &ClosedForm) -> bool {
    match sem {
        ClosedForm::Affine(af) => af.coeffs[0] > 0,
        ClosedForm::Piecewise(pw) => {
            is_always_pos(&pw.zero_branch) && is_always_pos(&pw.pos_branch)
        }
        ClosedForm::NegMod(_, _, _) => false,
        ClosedForm::Periodic(p) => p.branches.iter().all(|b| is_always_pos(b)),
    }
}

fn is_always_pos_on_branch_k(sem: &ClosedForm, k: usize, p_len: usize) -> bool {
    match sem {
        ClosedForm::Affine(af) => {
            if af.coeffs[0] > 0 {
                true
            } else {
                if k != 0 {
                    if af.coeffs.len() > 1
                        && af.coeffs[1] > 0
                        && af.coeffs.iter().skip(2).all(|&c| c == 0)
                    {
                        return true;
                    }
                }
                false
            }
        }
        ClosedForm::Piecewise(pw) => {
            if pw.branch_index == 0 {
                let zero_ok = if k == 0 {
                    is_always_pos_on_branch_k(&pw.zero_branch, 0, 1)
                } else {
                    true
                };
                let pos_ok =
                    is_always_pos_on_branch_k(&pw.pos_branch, (p_len + k - 1) % p_len, p_len);
                zero_ok && pos_ok
            } else {
                is_always_pos_on_branch_k(&pw.zero_branch, k, p_len)
                    && is_always_pos_on_branch_k(&pw.pos_branch, k, p_len)
            }
        }
        ClosedForm::Periodic(p) => {
            if p.branch_index == 0 {
                is_always_pos_on_branch_k(&p.branches[k % p.branches.len()], k, p_len)
            } else {
                p.branches
                    .iter()
                    .all(|b| is_always_pos_on_branch_k(b, k, p_len))
            }
        }
        ClosedForm::NegMod(_, _, _) => false,
    }
}

fn is_always_zero(sem: &ClosedForm) -> bool {
    match sem {
        ClosedForm::Affine(af) => af.coeffs.iter().all(|&c| c == 0),
        ClosedForm::Piecewise(pw) => {
            is_always_zero(&pw.zero_branch) && is_always_zero(&pw.pos_branch)
        }
        ClosedForm::NegMod(_, _, _) => false,
        ClosedForm::Periodic(p) => p.branches.iter().all(|b| is_always_zero(b)),
    }
}

/// If `sem` is guaranteed ≥ 1 for all natural-number inputs (Affine with constant ≥ 1),
/// returns `Some(sem - 1)`.
fn always_pos_minus_one(sem: &ClosedForm) -> Option<AffineFn> {
    match sem {
        ClosedForm::Affine(af) if af.coeffs[0] >= 1 => {
            let mut new_coeffs = af.coeffs.clone();
            new_coeffs[0] -= 1;
            Some(AffineFn {
                arity: af.arity,
                coeffs: new_coeffs,
            })
        }
        _ => None,
    }
}

/// Remove argument at 1-based position `idx` from `sem`, assuming it is unused.
///
/// For Affine: drops the coefficient at position `idx`.
/// For Piecewise: recursively removes the corresponding argument from both branches.
/// Returns `None` if asked to remove the branching variable of a Piecewise.

fn drop_arg_affine(af: &AffineFn, idx: usize) -> Option<AffineFn> {
    if idx > 0 && idx <= af.arity {
        if af.coeffs[idx] != 0 {
            return None;
        }
        Some(AffineFn {
            arity: af.arity - 1,
            coeffs: drop_index(&af.coeffs, idx),
        })
    } else {
        None
    }
}

fn drop_arg(sem: &ClosedForm, idx: usize) -> Option<ClosedForm> {
    debug_assert!(idx >= 1);
    match sem {
        ClosedForm::Affine(af) => {
            if af.coeffs[idx] != 0 {
                return None; // arg is used
            }
            let new_coeffs = drop_index(&af.coeffs, idx);
            Some(ClosedForm::Affine(AffineFn {
                arity: af.arity - 1,
                coeffs: new_coeffs,
            }))
        }
        ClosedForm::Piecewise(pw) => {
            let b = pw.branch_index + 1; // 1-based
            if idx == b {
                return None; // cannot remove the branching variable
            }
            // In zero_branch (arity pw.arity-1), x_b is absent:
            // idx < b → same position; idx > b → shifted down by 1.
            let idx_in_zero = if idx < b { idx } else { idx - 1 };
            let new_zero = drop_arg(&pw.zero_branch, idx_in_zero)?;
            let new_pos = drop_arg(&pw.pos_branch, idx)?;
            // If we drop an arg before b, the branch_index shifts down.
            let new_bi = if idx < b {
                pw.branch_index - 1
            } else {
                pw.branch_index
            };
            Some(ClosedForm::Piecewise(PiecewiseFn {
                arity: pw.arity - 1,
                branch_index: new_bi,
                zero_branch: Box::new(new_zero),
                pos_branch: Box::new(new_pos),
            }))
        }
        ClosedForm::NegMod(a1, a2, a3) => Some(ClosedForm::NegMod(
            drop_arg_affine(a1, idx)?,
            drop_arg_affine(a2, idx)?,
            drop_arg_affine(a3, idx)?,
        )),
        ClosedForm::Periodic(p) => {
            if idx == p.branch_index + 1 {
                None
            } else {
                let mut new_branches = Vec::new();
                for b in &p.branches {
                    new_branches.push(Box::new(drop_arg(b, idx)?));
                }
                let new_bi = if idx <= p.branch_index {
                    p.branch_index - 1
                } else {
                    p.branch_index
                };
                Some(ClosedForm::Periodic(PeriodicFn {
                    arity: p.arity - 1,
                    branch_index: new_bi,
                    branches: new_branches,
                }))
            }
        }
    }
}

/// Build a PiecewiseFn, but simplify if both branches agree semantically.
///
/// Case 1: pos_branch ignores the branched arg entirely — both branches return the same
/// value regardless of the arg's value, so return pos_branch directly.
///
/// Case 2: both branches are Affine and the piecewise is "smooth" at the boundary:
/// pos_branch(args_with_bi=0) == zero_branch(args_without_bi) for all other args.
/// The piecewise is then a pure affine: the same as pos_branch but with the constant
/// adjusted to pos_branch.c0 − pos_branch.coeffs[bi+1].

fn make_neg_mod(af1: AffineFn, af2: AffineFn, af3: AffineFn) -> ClosedForm {
    if af1.arity == 0 && af2.arity == 0 && af3.arity == 0 {
        let v1 = af1.coeffs[0];
        let v2 = af2.coeffs[0];
        let v3 = af3.coeffs[0] + 1;
        let res = if v1 >= v2 {
            v1 - v2
        } else {
            let diff = v2 - v1;
            let rem = diff % v3;
            if rem == 0 {
                0
            } else {
                v3 - rem
            }
        };
        return ClosedForm::Affine(AffineFn {
            arity: 0,
            coeffs: vec![res],
        });
    }
    ClosedForm::NegMod(af1, af2, af3)
}

fn make_piecewise(
    arity: usize,
    branch_index: usize,
    zero_branch: ClosedForm,
    pos_branch: ClosedForm,
) -> ClosedForm {
    if let Some(dropped) = drop_arg(&pos_branch, branch_index + 1) {
        if dropped == zero_branch {
            return pos_branch;
        }
    }
    if let (ClosedForm::Affine(z), ClosedForm::Affine(p)) = (&zero_branch, &pos_branch) {
        let bi1 = branch_index + 1; // 1-based index of the branched arg
                                    // Adjusted constant: A.c0 = p.c0 - p.coeffs[bi1] (from the pos-branch shift by -1)
        let c0_ok = p.coeffs[0]
            .checked_sub(p.coeffs[bi1])
            .map_or(false, |c0| c0 == z.coeffs[0]);
        // Non-branched args must have matching coefficients between p and z
        // (z skips the bi1 slot, so z.coeffs[j] matches p.coeffs[j] for j<bi1,
        //  and z.coeffs[j-1] matches p.coeffs[j] for j>bi1).
        let coeffs_ok = c0_ok
            && (1..bi1).all(|j| p.coeffs[j] == z.coeffs[j])
            && (bi1 + 1..=arity).all(|j| p.coeffs[j] == z.coeffs[j - 1]);
        if coeffs_ok {
            let mut new_coeffs = p.coeffs.clone();
            new_coeffs[0] = z.coeffs[0];
            return ClosedForm::Affine(AffineFn {
                arity,
                coeffs: new_coeffs,
            });
        }
    }
    // If pos_branch is itself a Piecewise on a different axis bi2, try reordering the two
    // levels of branching into a single Piecewise on bi2.  For each slice of bi2 we form a
    // new inner piecewise on bi1; if *both* slices simplify to Affine (via the checks above)
    // we can replace the nested structure with a flat Piecewise on bi2.  The "both Affine"
    // guard ensures termination: if a slice can't collapse we leave the original form as-is.
    if let ClosedForm::Piecewise(pp) = &pos_branch {
        let bi2 = pp.branch_index;
        if bi2 != branch_index {
            // bi2 in zero_branch's arg space (bi1 was dropped, so indices after bi1 shift down).
            let bi2_in_zero = if bi2 < branch_index { bi2 } else { bi2 - 1 };
            // bi1 in new_zero's arg space (bi2 was dropped, so indices after bi2 shift down).
            let bi1_in_new_zero = if bi2 < branch_index {
                branch_index - 1
            } else {
                branch_index
            };
            let pz: ClosedForm = *pp.zero_branch.clone();
            let pp_pos: ClosedForm = *pp.pos_branch.clone();
            // Slice zero_branch at bi2=0 (substitute & drop) and bi2>0 (shift for decrement).
            let z0 = zero_face_at(&zero_branch, bi2_in_zero + 1);
            let z_pos = pos_face_at(&zero_branch, bi2_in_zero + 1);
            let new_zero = make_piecewise(arity - 1, bi1_in_new_zero, z0, pz);
            let new_pos = make_piecewise(arity, branch_index, z_pos, pp_pos);
            if matches!(new_zero, ClosedForm::Affine(_)) && matches!(new_pos, ClosedForm::Affine(_))
            {
                return make_piecewise(arity, bi2, new_zero, new_pos);
            }
        }
    }
    ClosedForm::Piecewise(PiecewiseFn {
        arity,
        branch_index,
        zero_branch: Box::new(zero_branch),
        pos_branch: Box::new(pos_branch),
    })
}

/// Compose an outer affine function with a slice of inner affine functions.
///
/// `outer` must have arity == inners.len(); all inners must have the same arity.
/// The result has arity == inner_arity.  Returns `None` on u64 overflow.
fn compose_affine(outer: &AffineFn, inners: &[AffineFn]) -> Option<AffineFn> {
    debug_assert_eq!(outer.arity, inners.len());
    if inners.is_empty() {
        // 0-arg compose handled separately in closed_form_of; this shouldn't be reached.
        return None;
    }
    let inner_arity = inners[0].arity;
    debug_assert!(inners.iter().all(|f| f.arity == inner_arity));

    let mut new_coeffs = vec![0u64; inner_arity + 1];
    new_coeffs[0] = outer.coeffs[0];

    for (i, inner) in inners.iter().enumerate() {
        let c_i = outer.coeffs[i + 1];
        if c_i == 0 {
            continue;
        }
        new_coeffs[0] = new_coeffs[0].checked_add(c_i.checked_mul(inner.coeffs[0])?)?;
        for j in 1..=inner_arity {
            new_coeffs[j] = new_coeffs[j].checked_add(c_i.checked_mul(inner.coeffs[j])?)?;
        }
    }

    Some(AffineFn {
        arity: inner_arity,
        coeffs: new_coeffs,
    })
}

/// Return a copy of `coeffs` with the element at `idx` removed.
fn drop_index(coeffs: &[u64], idx: usize) -> Vec<u64> {
    coeffs
        .iter()
        .enumerate()
        .filter(|&(i, _)| i != idx)
        .map(|(_, &c)| c)
        .collect()
}

// --- Formatting ---

static ARG_NAMES: &[&str] = &["x", "y", "z", "w", "v", "u", "t", "s", "r", "q", "p"];

pub fn default_arg_names(arity: usize) -> Vec<String> {
    if arity <= ARG_NAMES.len() {
        (0..arity).map(|i| ARG_NAMES[i].to_string()).collect()
    } else {
        (1..=arity).map(|i| format!("x{i}")).collect()
    }
}

pub fn default_arg_names_x(arity: usize) -> Vec<String> {
    (1..=arity).map(|i| format!("x{i}")).collect()
}

fn decrement_n(v: &str, n: usize) -> String {
    match n {
        0 => v.to_string(),
        1 => format!("{}-1", v),
        n => format!("{}-{}", v, n),
    }
}

fn term_str(c: u64, v: &str) -> String {
    if c == 1 {
        v.to_string()
    } else {
        format!("{c}·{v}")
    }
}

impl AffineFn {
    pub fn format_expr(&self, vars: &[String]) -> String {
        let mut parts: Vec<String> = Vec::new();
        if self.coeffs[0] != 0 || self.arity == 0 {
            parts.push(self.coeffs[0].to_string());
        }
        for (i, &c) in self.coeffs[1..].iter().enumerate() {
            if c != 0 {
                parts.push(term_str(c, &vars[i]));
            }
        }
        if parts.is_empty() {
            "0".to_string()
        } else {
            parts.join(" + ")
        }
    }
}

impl ClosedForm {
    /// Format this form as a single-line inline string (e.g. for `closed_form list`)
    pub fn format_inline(&self, vars: &[String]) -> String {
        match self {
            ClosedForm::Affine(af) => af.format_expr(vars),
            ClosedForm::Piecewise(pw) => {
                let bi = pw.branch_index;
                let x = vars[bi].as_str();
                let zero_vars: Vec<String> = vars
                    .iter()
                    .enumerate()
                    .filter(|&(j, _)| j != bi)
                    .map(|(_, v)| v.clone())
                    .collect();
                let zero_rhs = pw.zero_branch.format_inline(&zero_vars);
                let mut pos_vars = vars.to_vec();
                pos_vars[bi] = decrement_n(x, 1);
                let pos_rhs = pw.pos_branch.format_inline(&pos_vars);
                format!("({x}=0 ? {zero_rhs} : {pos_rhs})")
            }
            ClosedForm::Periodic(p) => {
                let mut cases = Vec::new();
                for (i, b) in p.branches.iter().enumerate() {
                    cases.push(format!(
                        "{}@{}%{}",
                        b.format_inline(vars),
                        i,
                        p.branches.len()
                    ));
                }
                format!("Periodic({}; {})", vars[p.branch_index], cases.join(", "))
            }
            ClosedForm::NegMod(a1, a2, a3) => {
                let s1 = a1.format_expr(vars);
                let s2 = a2.format_expr(vars);

                if a3.coeffs.iter().all(|&c| c == 0) {
                    return format!("({s1} ∸ {s2})");
                }

                let mut a3_plus = a3.clone();
                a3_plus.coeffs[0] += 1;
                let s3 = if a3_plus.coeffs[1..].iter().filter(|&&c| c != 0).count()
                    + (if a3_plus.coeffs[0] != 0 { 1 } else { 0 })
                    > 1
                {
                    format!("({})", a3_plus.format_expr(vars))
                } else {
                    a3_plus.format_expr(vars)
                };
                format!("({s1} - {s2}) %< {s3}")
            }
        }
    }

    /// Print multi-line pattern-matching rules for this form (e.g. for `explore`)
    pub fn print_rules(&self, fn_name: &str) {
        let args = default_arg_names(self.arity());
        let depths = vec![0usize; self.arity()];
        self.emit_rules(fn_name, &args, &depths);
    }

    fn emit_rules(&self, fn_name: &str, args: &[String], depths: &[usize]) {
        match self {
            ClosedForm::Affine(af) => {
                let formula_args: Vec<String> = args
                    .iter()
                    .zip(depths.iter())
                    .map(|(name, &d)| decrement_n(name, d))
                    .collect();
                let lhs: Vec<String> = args
                    .iter()
                    .enumerate()
                    .map(|(j, name)| {
                        if closed_form_ignores_arg(self, j + 1) {
                            "_".to_string()
                        } else {
                            name.clone()
                        }
                    })
                    .collect();
                println!(
                    "  {}({}) = {}",
                    fn_name,
                    lhs.join(", "),
                    af.format_expr(&formula_args)
                );
            }
            ClosedForm::Piecewise(pw) => {
                let bi = pw.branch_index;
                let zero_lhs: Vec<String> = args
                    .iter()
                    .enumerate()
                    .map(|(j, name)| {
                        if j == bi {
                            depths[bi].to_string()
                        } else {
                            let j_in_zero = if j < bi { j } else { j - 1 };
                            if closed_form_ignores_arg(&pw.zero_branch, j_in_zero + 1) {
                                "_".to_string()
                            } else {
                                name.clone()
                            }
                        }
                    })
                    .collect();
                let zero_vars: Vec<String> = args
                    .iter()
                    .enumerate()
                    .filter(|&(j, _)| j != bi)
                    .map(|(_, name)| name.clone())
                    .collect();
                println!(
                    "  {}({}) = {}",
                    fn_name,
                    zero_lhs.join(", "),
                    pw.zero_branch.format_inline(&zero_vars)
                );
                let mut new_depths = depths.to_vec();
                new_depths[bi] += 1;
                pw.pos_branch.emit_rules(fn_name, args, &new_depths);
            }
            ClosedForm::Periodic(p) => {
                let bi = p.branch_index;
                let p_len = p.branches.len();
                for i in 0..p_len {
                    let lhs: Vec<String> = args
                        .iter()
                        .enumerate()
                        .map(|(j, name)| {
                            if j == bi {
                                format!("{} + {}k", i, p_len)
                            } else {
                                if closed_form_ignores_arg(&p.branches[i], j + 1) {
                                    "_".to_string()
                                } else {
                                    name.clone()
                                }
                            }
                        })
                        .collect();
                    println!(
                        "  {}({}) = {}",
                        fn_name,
                        lhs.join(", "),
                        p.branches[i].format_inline(args)
                    );
                }
            }
            ClosedForm::NegMod(a1, a2, a3) => {
                if a3.coeffs.iter().all(|&c| c == 0) {
                    println!(
                        "  {}({}) = ({} ∸ {})",
                        fn_name,
                        args.join(", "),
                        a1.format_expr(args),
                        a2.format_expr(args)
                    );
                    return;
                }

                let mut a3_plus = a3.clone();
                a3_plus.coeffs[0] += 1;
                let s3 = if a3_plus.coeffs[1..].iter().filter(|&&c| c != 0).count()
                    + (if a3_plus.coeffs[0] != 0 { 1 } else { 0 })
                    > 1
                {
                    format!("({})", a3_plus.format_expr(args))
                } else {
                    a3_plus.format_expr(args)
                };
                println!(
                    "  {}({}) = ({} - {}) %< {}",
                    fn_name,
                    args.join(", "),
                    a1.format_expr(args),
                    a2.format_expr(args),
                    s3
                );
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::enumerate::stream_grf;
    use crate::pruning::PruningOpts;
    use crate::sim_nat::SmallNat;
    use crate::simulate::{simulate, SimResult};

    fn grf(s: &str) -> Grf {
        s.parse().unwrap()
    }

    /// Assert closed_form_of matches simulate on a grid of inputs 0..=max_val per dimension.
    fn check_vs_sim(grf_str: &str, max_val: SmallNat) {
        let f = grf(grf_str);
        let sem = closed_form_of(&f)
            .unwrap_or_else(|| panic!("closed_form_of returned None for {grf_str}"));
        let arity = f.arity();
        if arity == 0 {
            let sim_val = simulate(&f, &[], 0).0.into_value();
            let sem_val = sem.eval(&[]);
            assert_eq!(sem_val, sim_val, "mismatch for {grf_str} on []");
            return;
        }
        // iterate over all tuples in [0, max_val]^arity
        let n = (max_val + 1) as usize;
        let total = n.pow(arity as u32);
        for idx in 0..total {
            let mut args: Vec<SmallNat> = vec![0; arity];
            let mut rem = idx;
            for a in args.iter_mut().rev() {
                *a = (rem % n) as SmallNat;
                rem /= n;
            }
            let sim_val = simulate(&f, &args, 0).0.into_value();
            let sem_val = sem.eval(&args);
            assert_eq!(
                sem_val, sim_val,
                "mismatch for {grf_str} on {args:?}: sim={sim_val:?} sem={sem_val:?}"
            );
        }
    }

    // --- Atoms ---

    #[test]
    fn test_zero() {
        let s = closed_form_of(&grf("Z0")).unwrap();
        assert_eq!(
            s,
            ClosedForm::Affine(AffineFn {
                arity: 0,
                coeffs: vec![0]
            })
        );
        assert_eq!(s.eval::<SmallNat>(&[]), Some(0));

        let s3 = closed_form_of(&grf("Z3")).unwrap();
        assert_eq!(s3.arity(), 3);
        assert_eq!(s3.eval(&[1u64, 2, 3]), Some(0));
    }

    #[test]
    fn test_succ() {
        let s = closed_form_of(&grf("S")).unwrap();
        assert_eq!(
            s,
            ClosedForm::Affine(AffineFn {
                arity: 1,
                coeffs: vec![1, 1]
            })
        );
        assert_eq!(s.eval(&[0u64]), Some(1));
        assert_eq!(s.eval(&[5u64]), Some(6));
    }

    #[test]
    fn test_proj() {
        let s = closed_form_of(&grf("P(2,1)")).unwrap();
        assert_eq!(s.eval(&[5u64, 3]), Some(5));

        let s2 = closed_form_of(&grf("P(2,2)")).unwrap();
        assert_eq!(s2.eval(&[5u64, 3]), Some(3));

        let s3 = closed_form_of(&grf("P(3,2)")).unwrap();
        assert_eq!(s3.eval(&[1u64, 7, 9]), Some(7));
    }

    // --- Compositions ---

    #[test]
    fn test_comp_succ_zero() {
        // C(S, Z0) = constant 1, arity 0
        let s = closed_form_of(&grf("C(S, Z0)")).unwrap();
        assert_eq!(s.arity(), 0);
        assert_eq!(s.eval::<SmallNat>(&[]), Some(1));
    }

    #[test]
    fn test_comp_succ_proj() {
        // C(S, P(2,1)) = x1 + 1, arity 1... wait, P(2,1) has arity 2 so C has arity 2
        check_vs_sim("C(S, P(2,1))", 5);
        // C(S, P(1,1)) = x + 1, arity 1
        check_vs_sim("C(S, P(1,1))", 8);
    }

    #[test]
    fn test_comp_succ_succ() {
        // C(S, C(S, Z0)) = constant 2
        let s = closed_form_of(&grf("C(S, C(S, Z0))")).unwrap();
        assert_eq!(s.arity(), 0);
        assert_eq!(s.eval::<SmallNat>(&[]), Some(2));
    }

    #[test]
    fn test_comp0_lift() {
        // C2(Z0): lift arity-0 zero to arity 2
        let s = closed_form_of(&grf("C2(Z0)")).unwrap();
        assert_eq!(s.arity(), 2);
        assert_eq!(s.eval(&[3u64, 7]), Some(0));
    }

    // --- Rec Case A: h = acc + k ---

    #[test]
    fn test_rec_identity() {
        // R(Z0, C(S, P(2,2))) = identity: f(n) = n
        check_vs_sim("R(Z0, C(S, P(2,2)))", 10);
        let s = closed_form_of(&grf("R(Z0, C(S, P(2,2)))")).unwrap();
        assert_eq!(
            s,
            ClosedForm::Affine(AffineFn {
                arity: 1,
                coeffs: vec![0, 1]
            })
        );
    }

    #[test]
    fn test_rec_addition() {
        // R(P(1,1), C(S, P(3,2))) = addition: f(n, m) = n + m
        check_vs_sim("R(P(1,1), C(S, P(3,2)))", 5);
        let s = closed_form_of(&grf("R(P(1,1), C(S, P(3,2)))")).unwrap();
        assert_eq!(
            s,
            ClosedForm::Affine(AffineFn {
                arity: 2,
                coeffs: vec![0, 1, 1]
            })
        );
    }

    #[test]
    fn test_rec_affine_step2() {
        // R(S, C(S, C(S, P(3,2)))) = f(n, x) = 1 + 2n + x
        check_vs_sim("R(S, C(S, C(S, P(3,2))))", 5);
        let s = closed_form_of(&grf("R(S, C(S, C(S, P(3,2))))")).unwrap();
        assert_eq!(
            s,
            ClosedForm::Affine(AffineFn {
                arity: 2,
                coeffs: vec![1, 2, 1]
            })
        );
    }

    // --- Rec Case B: h ignores accumulator ---

    #[test]
    fn test_rec_predecessor() {
        // R(Z0, P(2,1)) = predecessor (saturating at 0): f(0)=0, f(n)=n-1
        let s = closed_form_of(&grf("R(Z0, P(2,1))")).unwrap();
        assert!(matches!(s, ClosedForm::Piecewise(_)));
        check_vs_sim("R(Z0, P(2,1))", 10);
    }

    #[test]
    fn test_rec_piecewise_arity2() {
        // R(Z1, P(3,1)): g=Z1 (arity 1), h=P(3,1) ignores acc
        // f(0, x) = 0,  f(n, x) = n-1
        check_vs_sim("R(Z1, P(3,1))", 5);
    }

    // --- Comp with Piecewise components ---

    #[test]
    fn test_comp_piecewise_arg() {
        // C(S, R(Z0, P(2,1))): compose Succ with predecessor → identity on arity 1
        // pred(n)=n-1 for n>0; S(pred(n)) = n for n>0; S(pred(0))=S(0)=1 != 0
        // So this is: f(0)=1, f(n)=n for n>0
        check_vs_sim("C(S, R(Z0, P(2,1)))", 8);
    }

    #[test]
    fn test_comp_piecewise_head() {
        // C(R(Z0, P(2,1)), P(2,1)): predecessor composed with P(2,1) = predecessor on arity 2
        // f(0, x) = 0,  f(n, x) = n-1
        check_vs_sim("C(R(Z0, P(2,1)), P(2,1))", 6);
    }

    #[test]
    fn test_comp_piecewise_arg_plus_affine_dep() {
        // C(R(P(1,1),C(S,P(3,2))), R(Z0,P(2,1)), P(1,1)):
        //   h = add(arity 2), g1 = pred, g2 = x (both depend on x1)
        //   f(x) = pred(x) + x = {0 for x=0, 2x-1 for x>0}
        // Tests pos_face_at correction: Affine inner P(1,1) depends on xj=x1.
        check_vs_sim("C(R(P(1,1),C(S,P(3,2))),R(Z0,P(2,1)),P(1,1))", 8);
    }

    #[test]
    fn test_rec_case_e_outer_arg_piecewise() {
        // R(P(3,2), C(R(S,P(3,1)), P(5,3), P(5,2))): arity 4
        // h branches on outer x2 (b's arg 2, h's branch_index=2).
        // b(n,0,z,w)=n+z  b(n,y,z,w)=y-1 for y>0
        check_vs_sim("R(P(3,2), C(R(S, P(3,1)), P(5,3), P(5,2)))", 5);
    }

    #[test]
    fn test_pos_face_at_piecewise_depends_on_shifted_arg() {
        // Regression test for pos_face_at on a Piecewise that branches on xk but still
        // depends on xj (k != j).  Case E of closed_form_of_rec calls pos_face_at(sem_g, j)
        // where sem_g = R(S, P(3,3)) branches on x1 while depending on x2 (j=2).
        // The inner Rec f(n, x1, x2) = R(S,P(3,3))(x1,x2) = if x1=0 then x2+1 else x2.
        check_vs_sim("R(R(S, P(3,3)), C(R(P(1,1), P(3,3)), P(4,4), P(4,2)))", 5);
        // The reported mismatch: C(f, S, S, P(1,1)) at args=[3] gave cf=2, sim=3.
        check_vs_sim(
            "C(R(R(S, P(3,3)), C(R(P(1,1), P(3,3)), P(4,4), P(4,2))), S, S, P(1,1))",
            8,
        );
    }

    #[test]
    fn test_comp_double_piecewise_supported() {
        // pred(pred(n)) is now supported via nested piecewise collapsing.
        check_vs_sim("C(R(Z0, P(2,1)), R(Z0, P(2,1)))", 5);
        assert!(closed_form_of(&grf("C(R(Z0, P(2,1)), R(Z0, P(2,1)))")).is_some());
    }

    // --- Case A' (semantic acc+j detection) ---

    #[test]
    fn test_rec_case_a_semantic() {
        // C(P(2,1), P(2,2), P(2,1))(n,acc) = P(2,1)(acc, n) = acc  →  semantically acc+0
        // R(Z0, C(P(2,1), P(2,2), P(2,1))): f(n) = g() + 0*n = 0 for all n
        check_vs_sim("R(Z0, C(P(2,1), P(2,2), P(2,1)))", 8);
        let s = closed_form_of(&grf("R(Z0, C(P(2,1), P(2,2), P(2,1)))")).unwrap();
        assert_eq!(
            s,
            ClosedForm::Affine(AffineFn {
                arity: 1,
                coeffs: vec![0, 0]
            })
        );
    }

    // --- Case B with Piecewise step ---

    #[test]
    fn test_rec_case_b_piecewise_step() {
        // R(Z0, R(Z1, P(3,1))): h = R(Z1, P(3,1)) which ignores acc
        // h(counter, acc, x) = R(Z1, P(3,1))(counter, x): if counter=0 then x else counter-1
        // But h ignores acc. Let's verify closed_form_of works.
        // R(g=Z0, h=R(Z1,P(3,1))): g.arity=0, k_outer=1
        // f(0) = g() = 0; f(n) = h(n-1, f(n-1)) = R(Z1,P(3,1))(n-1, _, _) ignoring acc
        check_vs_sim("R(Z0, R(Z1, P(3,1)))", 8);
    }

    // --- Min ---

    #[test]
    fn test_min_always_zero() {
        // M(Z1): Z1(i)=0 always, so M=0 (arity 0)
        let s = closed_form_of(&grf("Z1")).unwrap();
        assert!(is_always_zero(&s));
        let m = closed_form_of(&grf("M(Z1)")).unwrap();
        assert_eq!(m, ClosedForm::Affine(AffineFn::zero(0)));
        assert_eq!(m.eval::<SmallNat>(&[]), Some(0));

        // M(P(2,1)): f(i,x)=i, so f(0,x)=0 for all x → M=0 (arity 1)
        let m = closed_form_of(&grf("M(P(2,1))")).unwrap();
        assert_eq!(m, ClosedForm::Affine(AffineFn::zero(1)));
        check_vs_sim("M(P(2,1))", 5);

        // M(P(1,1)): f(i)=i, so f(0)=0 → M=0 (arity 0)
        let m = closed_form_of(&grf("M(P(1,1))")).unwrap();
        assert_eq!(m, ClosedForm::Affine(AffineFn::zero(0)));
        check_vs_sim("M(P(1,1))", 5);
    }

    #[test]
    fn test_min_none() {
        // M(S): S(0)=1 → never zero → None
        assert!(closed_form_of(&grf("M(S)")).is_none());
        // M(P(2,2)): f(0,x)=x, not always zero → None
        assert!(closed_form_of(&grf("M(P(2,2))")).is_none());
    }

    #[test]
    fn test_compute_min_affine() {
        // AffineFn: f(i, x) = x. At i=0: f=x. If x=0 → min=0; else diverge.
        let cf = closed_form_of(&grf("P(2,2)")).unwrap(); // P(2,2)(i,x) = x
        assert!(matches!(cf, ClosedForm::Affine(_)));
        assert_eq!(cf.compute_min::<u64>(&[0]), SimResult::Value(0));
        assert_eq!(cf.compute_min::<u64>(&[3]), SimResult::Diverge);

        // f(i, x) = i + 1 (Succ of search var). f(0,...) = 1 always → diverge.
        let cf2 = closed_form_of(&grf("S")).unwrap(); // S(i) = i+1
        assert_eq!(cf2.compute_min::<u64>(&[]), SimResult::Diverge);
    }

    #[test]
    fn test_compute_min_piecewise_bi0() {
        // Predecessor R(Z0, P(2,1)) has arity 1: f(i)=pred(i). pred(0)=0 → M()=0.
        let cf = closed_form_of(&grf("R(Z0, P(2,1))")).unwrap();
        assert!(matches!(cf, ClosedForm::Piecewise(ref pw) if pw.branch_index == 0));
        assert_eq!(cf.compute_min::<u64>(&[]), SimResult::Value(0));

        // R(C(S,Z0), Z2): arity 1. base=1, step always returns 0 → f(0)=1, f(1)=0 → M()=1.
        let cf2 = closed_form_of(&grf("R(C(S,Z0), Z2)")).unwrap();
        assert!(matches!(cf2, ClosedForm::Piecewise(ref pw) if pw.branch_index == 0));
        assert_eq!(cf2.compute_min::<u64>(&[]), SimResult::Value(1));
    }

    #[test]
    fn test_compute_min_piecewise_outer_arg() {
        // C(pred, P(2,2)) = pred(y) for (x, y): arity 2, branches on bi=1 (the y arg).
        // f(i, y) = pred(y) regardless of i.
        // M(f)(y): pred(0)=0 → Some(0); pred(1)=0 → Some(0); pred(3)=2 → None.
        let cf = closed_form_of(&grf("C(R(Z0,P(2,1)),P(2,2))")).unwrap();
        assert!(matches!(cf, ClosedForm::Piecewise(ref pw) if pw.branch_index == 1));
        assert_eq!(cf.compute_min::<u64>(&[0]), SimResult::Value(0));
        assert_eq!(cf.compute_min::<u64>(&[1]), SimResult::Value(0));
        assert_eq!(cf.compute_min::<u64>(&[3]), SimResult::Diverge);
    }

    #[test]
    fn test_compute_min_nested() {
        // cf(0,y) = y+1
        // cf(1,y) = y
        // cf(_,_) = 0
        let cf = closed_form_of(&grf("R(S, R(P(2,2), Z4))")).unwrap();
        assert_eq!(cf.compute_min::<u64>(&[0]), SimResult::Value(1));
        assert_eq!(cf.compute_min::<u64>(&[1]), SimResult::Value(2));
    }

    #[test]
    fn test_compute_min_nested_diverge() {
        // cf(0,y) = y+1
        // cf(1,y) = y
        // cf(_,_) = 1
        let cf = closed_form_of(&grf("R(S, R(P(2,2), C(S, Z4)))")).unwrap();
        assert_eq!(cf.compute_min::<u64>(&[0]), SimResult::Value(1));
        assert_eq!(cf.compute_min::<u64>(&[1]), SimResult::Diverge);
    }

    #[test]
    fn test_rec_case_d_piecewise_on_rest_arg() {
        // b(z,y) = y when z<2, else z-2.  b = R(P(1,1), R(P(2,1), P(4,1)))
        // c = R(P(2,1), C(b, P(4,4), P(4,2))): arity 3, g=P(2,1)=y, h ignores counter
        // c(n,y,z): for z<2 → y; for z≥2 → z-2.  Counter n is irrelevant.
        check_vs_sim("R(P(2,1), C(R(P(1,1),R(P(2,1),P(4,1))),P(4,4),P(4,2)))", 5);
    }

    #[test]
    fn test_rec_piecewise_same_branches_simplified() {
        // R(Z0, Z2): base=Z0 (arity 0), step=Z2 (arity 2) always returns 0.
        // Both branches compute zero, so the result should be Affine, not Piecewise.
        let cf = closed_form_of(&grf("R(Z0, Z2)")).unwrap();
        assert!(
            matches!(cf, ClosedForm::Affine(_)),
            "expected Affine (not Piecewise), got {cf:?}"
        );
        assert_eq!(cf.arity(), 1);
        check_vs_sim("R(Z0, Z2)", 8);

        // Motivating example: R(b, P(5,2)) where b ignores its counter.
        // The outer piecewise (on the outermost counter) has equal branches and should collapse.
        let cf2 = closed_form_of(&grf("R(R(R(S, P(3,2)), P(4,1)), P(5,2))")).unwrap();
        if let ClosedForm::Piecewise(ref pw) = cf2 {
            assert_ne!(
                pw.branch_index, 0,
                "outer Piecewise should not branch on the counter"
            );
        }
        check_vs_sim("R(R(R(S, P(3,2)), P(4,1)), P(5,2))", 4);
    }

    #[test]
    fn test_make_piecewise_smooth_boundary_collapses_to_affine() {
        // Case B produces pos_branch that uses the branched arg, but pos_branch(bi=0) == zero_branch,
        // so the piecewise is a pure affine (smooth at the boundary).

        // R(Z0, C(S, P(2,1))): f(0)=0, f(n+1)=1+n → f(n)=n (identity).
        // pos_branch = 1+x1 uses x1; boundary: pos_branch(0)=1 ≠ z.c0=0, yet
        // p.c0 - p.coeffs[1] = 0 = z.c0, so it collapses to Affine x1.
        let cf = closed_form_of(&grf("R(Z0, C(S, P(2,1)))")).unwrap();
        assert_eq!(
            cf,
            ClosedForm::Affine(AffineFn {
                arity: 1,
                coeffs: vec![0, 1]
            })
        );
        check_vs_sim("R(Z0, C(S, P(2,1)))", 8);

        // R(C(S, Z0), C(S, C(S, P(2,1)))): f(0)=1, f(n+1)=2+n → f(n)=n+1 (successor).
        let cf2 = closed_form_of(&grf("R(C(S, Z0), C(S, C(S, P(2,1))))")).unwrap();
        assert_eq!(
            cf2,
            ClosedForm::Affine(AffineFn {
                arity: 1,
                coeffs: vec![1, 1]
            })
        );
        check_vs_sim("R(C(S, Z0), C(S, C(S, P(2,1))))", 8);

        // R(Z1, C(S, P(3,1))): arity 2, f(0,m)=0, f(n+1,m)=1+n → f(n,m)=n (project first arg).
        let cf3 = closed_form_of(&grf("R(Z1, C(S, P(3,1)))")).unwrap();
        assert_eq!(
            cf3,
            ClosedForm::Affine(AffineFn {
                arity: 2,
                coeffs: vec![0, 1, 0]
            })
        );
        check_vs_sim("R(Z1, C(S, P(3,1)))", 4);
    }

    #[test]
    fn test_rec_mul_none() {
        // Multiplication: h = add(acc, m), not a constant step — None
        // R(Z0, C(R(P(1,1),C(S,P(3,2))), P(3,2), P(3,3)))
        assert!(closed_form_of(&grf("R(Z0, C(R(P(1,1),C(S,P(3,2))),P(3,2),P(3,3)))")).is_none());
    }

    #[test]
    fn test_make_piecewise_reorder_collapses_nested_piecewise() {
        // R(Z1, C(R(S, Z3), P(3,3), P(3,1))): arity 2.
        // closed_form_of produces (x1=0 ? 0 : (x2=0 ? 1+x1 : 0@x2-1)@x1-1).
        // The reorder check should collapse this to (x2=0 ? x1 : 0@x2-1).
        //
        // Semantics: f(0,m)=0, f(n>0,0)=n, f(n>0,m>0)=0.
        let cf = closed_form_of(&grf("R(Z1, C(R(S, Z3), P(3,3), P(3,1)))")).unwrap();
        assert_eq!(
            cf,
            ClosedForm::Piecewise(PiecewiseFn {
                arity: 2,
                branch_index: 1,
                zero_branch: Box::new(ClosedForm::Affine(AffineFn {
                    arity: 1,
                    coeffs: vec![0, 1]
                })),
                pos_branch: Box::new(ClosedForm::Affine(AffineFn {
                    arity: 2,
                    coeffs: vec![0, 0, 0]
                })),
            }),
            "expected (x2=0 ? x1 : 0@x2-1), got {cf:?}"
        );
        check_vs_sim("R(Z1, C(R(S, Z3), P(3,3), P(3,1)))", 4);
    }

    // --- AffineFn arithmetic safety ---

    #[test]
    fn test_affine_overflow() {
        // Coefficient that overflows when multiplied by 3: i64::MAX as u64 * 3 > u64::MAX.
        let af = AffineFn {
            arity: 1,
            coeffs: vec![0u64, i64::MAX as u64],
        };
        assert_eq!(af.eval(&[3u64]), None);
        // i64::MAX * 2 = u64::MAX - 1: valid u64, should return Some.
        assert_eq!(af.eval(&[2u64]), Some(u64::MAX - 1));
    }

    // ── Exhaustive closed_form_of vs simulate validation ──────────────────────

    /// Canonical test inputs for arity k: small exhaustive grid.
    pub fn test_inputs(arity: usize) -> Vec<Vec<SmallNat>> {
        if arity == 0 {
            return vec![vec![]];
        }
        let vals: &[SmallNat] = &[0, 1, 2, 3, 5, 8];
        let mut result: Vec<Vec<SmallNat>> = vec![vec![]];
        for _ in 0..arity {
            let mut next = Vec::new();
            for prefix in &result {
                for &v in vals {
                    let mut row = prefix.clone();
                    row.push(v);
                    next.push(row);
                }
            }
            result = next;
        }
        result
    }

    pub fn check_all(max_arity: usize, max_size: usize) {
        check_all_opts(max_arity, max_size, 1_000_000);
    }

    pub fn check_all_opts(max_arity: usize, max_size: usize, max_steps: SmallNat) {
        let opts = PruningOpts::default();

        let mut checked = 0usize;
        let mut mismatches = 0usize;

        for arity in 0..=max_arity {
            let inputs = test_inputs(arity);
            for size in 1..=max_size {
                stream_grf(size, arity, false, opts, &mut |grf| {
                    let cf = match closed_form_of(grf) {
                        Some(cf) => cf,
                        None => return,
                    };
                    for args in &inputs {
                        let (sim_result, _) = simulate(grf, args, max_steps);
                        let sim_val = match sim_result {
                            SimResult::Value(v) => Some(v),
                            SimResult::Diverge | SimResult::OutOfSteps => None,
                            SimResult::ArityMismatch => {
                                panic!("arity mismatch for {} on {:?}", grf, args);
                            }
                            SimResult::ValueOverflow => None,
                        };
                        let cf_val = cf.eval(args);
                        checked += 1;
                        if cf_val != sim_val {
                            mismatches += 1;
                            if mismatches <= 5 {
                                eprintln!(
                                    "MISMATCH: {} args={:?}  cf={:?}  sim={:?}",
                                    grf, args, cf_val, sim_val
                                );
                            }
                        }
                    }
                });
            }
        }

        assert_eq!(
            mismatches, 0,
            "{mismatches} mismatches found (checked {checked} (grf, input) pairs)"
        );
        eprintln!(
            "closed_form validate_all: {checked} (grf, input) pairs matched \
             (arities 0..={max_arity}, sizes 1..={max_size})"
        );
    }

    // 0.37s
    #[test]
    fn validate_small() {
        check_all(2, 7);
    }

    // 143s
    #[test]
    #[ignore]
    fn validate_long() {
        check_all(2, 10);
    }

    // 50s
    #[test]
    #[ignore]
    fn validate_wide() {
        check_all(4, 7);
    }

    #[test]
    fn test_periodic_always_pos() {
        // Create an Affine fn: f(x) = 1 + x (coeffs: [1, 1])
        let f1 = ClosedForm::Affine(AffineFn {
            arity: 1,
            coeffs: vec![1, 1],
        });
        // f(x) = x (coeffs: [0, 1])
        let f2 = ClosedForm::Affine(AffineFn {
            arity: 1,
            coeffs: vec![0, 1],
        });

        // Piecewise: x=0 ? 1 : x
        let pw = ClosedForm::Piecewise(PiecewiseFn {
            arity: 1,
            branch_index: 0,
            zero_branch: Box::new(ClosedForm::Affine(AffineFn {
                arity: 0,
                coeffs: vec![1],
            })),
            pos_branch: Box::new(f2.clone()),
        });

        // Test is_always_pos_on_branch_k
        // f1 is 1+x. Always positive on any branch.
        assert!(is_always_pos_on_branch_k(&f1, 0, 2));
        assert!(is_always_pos_on_branch_k(&f1, 1, 2));

        // f2 is x. Positive on branch 1 (because i=0 is impossible when i % 2 == 1).
        assert!(is_always_pos_on_branch_k(&f2, 1, 2));
        // Not always positive on branch 0 (because i=0 is possible).
        assert!(!is_always_pos_on_branch_k(&f2, 0, 2));

        // pw is Piecewise(1, x). Positive on branch 0.
        // at i=0, it is 1 > 0.
        // at i>0, it is x-1. But branch is 0. So i % 2 == 0.
        // thus i >= 2. x-1 >= 1 > 0.
        assert!(is_always_pos_on_branch_k(&pw, 0, 2));

        // Create a PeriodicFn branching on x (index 0).
        let periodic = ClosedForm::Periodic(PeriodicFn {
            arity: 1,
            branch_index: 0,
            branches: vec![Box::new(pw), Box::new(f2)],
        });

        // Since both branches are always positive on their respective indices,
        // compute_min should correctly identify divergence.
        match periodic.compute_min::<SmallNat>(&[]) {
            SimResult::Diverge => (), // Correct!
            other => panic!("Expected Diverge, got {:?}", other),
        }
    }
}
