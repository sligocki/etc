use crate::sim_nat::SmallNat;
use crate::grf::{Grf, GrfKind};

/// Affine function over natural numbers: c0 + c1*x1 + ... + ck*xk.
///
/// Coefficients are i64 to allow intermediate negatives during composition.
/// `eval` returns `None` when the result would be negative (outside the natural-number domain)
/// or when i64 arithmetic overflows.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct AffineFn {
    pub arity: usize,
    /// Length arity+1. coeffs[0] = constant term; coeffs[i] = coefficient of xi (1-based).
    pub coeffs: Vec<i64>,
}

impl AffineFn {
    /// Constant-zero function of the given arity.
    pub fn zero(arity: usize) -> Self {
        AffineFn { arity, coeffs: vec![0; arity + 1] }
    }

    /// The successor function S(x) = x + 1.
    pub fn succ() -> Self {
        AffineFn { arity: 1, coeffs: vec![1, 1] }
    }

    /// The projection P^k_i(x1,...,xk) = xi (i is 1-based).
    pub fn proj(arity: usize, i: usize) -> Self {
        debug_assert!(i >= 1 && i <= arity);
        let mut coeffs = vec![0i64; arity + 1];
        coeffs[i] = 1;
        AffineFn { arity, coeffs }
    }

    /// Evaluate the affine function on concrete arguments.
    ///
    /// Returns `None` if the result would be negative, or if i64 arithmetic overflows.
    pub fn eval(&self, args: &[SmallNat]) -> Option<SmallNat> {
        debug_assert_eq!(args.len(), self.arity);
        let mut result: i64 = self.coeffs[0];
        for (i, &arg) in args.iter().enumerate() {
            let c = self.coeffs[i + 1];
            if c == 0 {
                continue;
            }
            let arg_i64 = i64::try_from(arg).ok()?;
            let term = c.checked_mul(arg_i64)?;
            result = result.checked_add(term)?;
        }
        if result < 0 { None } else { Some(result as SmallNat) }
    }

    pub fn lift(&self, arity: usize) -> Self {
        assert!(arity >= self.arity);
        let mut coeffs = self.coeffs.clone();
        coeffs.resize(arity+1, 0);
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

impl PiecewiseFn {
    pub fn eval(&self, args: &[SmallNat]) -> Option<SmallNat> {
        assert_eq!(args.len(), self.arity);
        let bi = self.branch_index;
        if args[bi] == 0 {
            let zero_args: Vec<SmallNat> =
                args[..bi].iter().chain(&args[bi + 1..]).copied().collect();
            self.zero_branch.eval(&zero_args)
        } else {
            let mut new_args = args.to_vec();
            new_args[bi] -= 1;
            self.pos_branch.eval(&new_args)
        }
    }

    pub fn lift(&self, arity: usize) -> Self {
        assert!(arity >= self.arity);
        PiecewiseFn {
            arity,
            branch_index: self.branch_index,
            zero_branch: Box::new(self.zero_branch.lift(arity-1)),
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
}

impl ClosedForm {
    pub fn arity(&self) -> usize {
        match self {
            ClosedForm::Affine(af) => af.arity,
            ClosedForm::Piecewise(pw) => pw.arity,
        }
    }

    /// Evaluate the semantic function on concrete arguments.
    ///
    /// Returns `None` if the result would be negative (e.g. affine with negative sum),
    /// or on arithmetic overflow.
    pub fn eval(&self, args: &[SmallNat]) -> Option<SmallNat> {
        match self {
            ClosedForm::Affine(af) => af.eval(args),
            ClosedForm::Piecewise(pw) => pw.eval(args),
        }
    }

    pub fn lift(&self, arity: usize) -> Self {
        match self {
            ClosedForm::Affine(af) => ClosedForm::Affine(af.lift(arity)),
            ClosedForm::Piecewise(pw) => ClosedForm::Piecewise(pw.lift(arity)),
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
            let sem_hs: Vec<ClosedForm> = hs.iter().map(|h| h.closed_form().cloned()).collect::<Option<_>>()?;
            compose(&sem_g, &sem_hs, *k)
        }

        GrfKind::Rec(g, h) => {
            let k_outer = g.arity() + 1;
            let sem_g = g.closed_form()?.clone();
            let sem_h = h.closed_form()?.clone();
            closed_form_of_rec(&sem_g, &sem_h, k_outer)
        }

        // Not yet supported
        GrfKind::Min(_) => None,
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
fn closed_form_of_rec(sem_g: &ClosedForm, sem_h: &ClosedForm, k_outer: usize) -> Option<ClosedForm> {
    // Case A: h(n, acc, rest) = j + acc  (j = coeffs[0], acc-coeff=1, rest-coeffs=0)
    if let ClosedForm::Affine(af_h) = sem_h {
        if af_h.coeffs[1] == 0
            && af_h.coeffs[2] == 1
            && af_h.coeffs[3..].iter().all(|&c| c == 0)
            && af_h.coeffs[0] >= 0
        {
            if let ClosedForm::Affine(g_af) = sem_g {
                let j = af_h.coeffs[0];
                let mut new_coeffs = Vec::with_capacity(k_outer + 1);
                new_coeffs.push(g_af.coeffs[0]);
                new_coeffs.push(j);
                new_coeffs.extend_from_slice(&g_af.coeffs[1..]);
                return Some(ClosedForm::Affine(AffineFn { arity: k_outer, coeffs: new_coeffs }));
            }
        }
    }

    // Case B: h ignores accumulator (arg 2)  →  drop acc to get h': (counter, rest) → value
    if closed_form_ignores_arg(sem_h, 2) {
        if let Some(h_prime) = drop_arg(sem_h, 2) {
            return Some(make_piecewise(k_outer, 0, sem_g.clone(), h_prime));
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
                    if let Some(pos_branch) = closed_form_of_rec(&sem_g_prime, b_p, k_outer) {
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

    // Case E: h is Piecewise on an outer argument (branch_index ≥ 2, i.e. not counter/acc).
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
            if let Some(zero_b) = closed_form_of_rec(&g_zero, h_zero, k_outer - 1) {
                // h.pos_branch is called with b's arg j_b decremented by 1.  The base g is
                // evaluated in that same decremented context, so shift g to compensate:
                // g_pos(z') = g(z'+1).
                let g_pos = pos_face_at(sem_g, j_b - 1);
                let h_pos = pw_h.pos_branch.as_ref();
                if let Some(pos_b) = closed_form_of_rec(&g_pos, h_pos, k_outer) {
                    return Some(make_piecewise(k_outer, j_b - 1, zero_b, pos_b));
                }
            }
        }
    }

    None
}

/// Returns true when `sem` ignores argument at 1-based `idx` for all inputs.
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

    // Base case: all Affine
    if let ClosedForm::Affine(h_af) = h {
        if let Some(inner_afs) = inners
            .iter()
            .map(|s| if let ClosedForm::Affine(af) = s { Some(af.clone()) } else { None })
            .collect::<Option<Vec<_>>>()
        {
            return Some(ClosedForm::Affine(compose_affine(h_af, &inner_afs)?));
        }
    }

    match h {
        ClosedForm::Affine(_) => {
            // h is affine but some inner is Piecewise.
            // Find j: the branching variable all Piecewise inners agree on.
            if arity == 0 {
                return None;
            }
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
            let j = j_opt.unwrap_or(1);
            // Correctness: pos_face_at for Affine adjusts the constant, so Affine
            // inners depending on xj are fine.  Piecewise inners on a *different*
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
            Some(make_piecewise(arity, j - 1, zero_sem, pos_sem))
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
                let rest: Vec<ClosedForm> = inners.iter().enumerate()
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
            let others_ok = inners.iter().enumerate()
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
            let zero_inners: Vec<ClosedForm> = inners.iter().enumerate()
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
    }
}

/// Substitute xj=0 (1-based `j`) and drop it from the argument list.
/// The result has arity one less than `sem`.
fn zero_face_at(sem: &ClosedForm, j: usize) -> ClosedForm {
    match sem {
        ClosedForm::Affine(af) => {
            let new_coeffs = drop_index(&af.coeffs, j);
            ClosedForm::Affine(AffineFn { arity: af.arity - 1, coeffs: new_coeffs })
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
                let new_bi = if j < b { pw.branch_index - 1 } else { pw.branch_index };
                ClosedForm::Piecewise(PiecewiseFn {
                    arity: pw.arity - 1,
                    branch_index: new_bi,
                    zero_branch: Box::new(new_zero),
                    pos_branch: Box::new(new_pos),
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
            new_coeffs[0] += new_coeffs[j];
            ClosedForm::Affine(AffineFn { arity: af.arity, coeffs: new_coeffs })
        }
        ClosedForm::Piecewise(pw) => {
            let b = pw.branch_index + 1; // 1-based branch variable
            if b == j {
                *pw.pos_branch.clone()
            } else {
                let j_in_zero = if j < b { j } else { j - 1 };
                let new_zero = pos_face_at(&pw.zero_branch, j_in_zero);
                let new_pos = pos_face_at(&pw.pos_branch, j);
                ClosedForm::Piecewise(PiecewiseFn {
                    arity: pw.arity,
                    branch_index: pw.branch_index,
                    zero_branch: Box::new(new_zero),
                    pos_branch: Box::new(new_pos),
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
fn prepend_arg(sem: &ClosedForm) -> ClosedForm {
    match sem {
        ClosedForm::Affine(af) => {
            let mut new_coeffs = vec![af.coeffs[0], 0]; // constant, then new ignored arg
            new_coeffs.extend_from_slice(&af.coeffs[1..]);
            ClosedForm::Affine(AffineFn { arity: af.arity + 1, coeffs: new_coeffs })
        }
        ClosedForm::Piecewise(pw) => ClosedForm::Piecewise(PiecewiseFn {
            arity: pw.arity + 1,
            branch_index: pw.branch_index + 1, // all indices shift right by 1
            zero_branch: Box::new(prepend_arg(&pw.zero_branch)),
            pos_branch: Box::new(prepend_arg(&pw.pos_branch)),
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
    }
}

/// Returns true when `sem` evaluates to 0 for all natural-number inputs.
fn is_always_zero(sem: &ClosedForm) -> bool {
    match sem {
        ClosedForm::Affine(af) => af.coeffs.iter().all(|&c| c == 0),
        ClosedForm::Piecewise(pw) => is_always_zero(&pw.zero_branch) && is_always_zero(&pw.pos_branch),
    }
}

/// If `sem` is guaranteed ≥ 1 for all natural-number inputs (Affine with constant ≥ 1
/// and all variable coefficients ≥ 0), returns `Some(sem - 1)`.
fn always_pos_minus_one(sem: &ClosedForm) -> Option<AffineFn> {
    match sem {
        ClosedForm::Affine(af)
            if af.coeffs[0] >= 1 && af.coeffs[1..].iter().all(|&c| c >= 0) =>
        {
            let mut new_coeffs = af.coeffs.clone();
            new_coeffs[0] -= 1;
            Some(AffineFn { arity: af.arity, coeffs: new_coeffs })
        }
        _ => None,
    }
}


/// Remove argument at 1-based position `idx` from `sem`, assuming it is unused.
///
/// For Affine: drops the coefficient at position `idx`.
/// For Piecewise: recursively removes the corresponding argument from both branches.
/// Returns `None` if asked to remove the branching variable of a Piecewise.
fn drop_arg(sem: &ClosedForm, idx: usize) -> Option<ClosedForm> {
    debug_assert!(idx >= 1);
    match sem {
        ClosedForm::Affine(af) => {
            if af.coeffs[idx] != 0 {
                return None; // arg is used
            }
            let new_coeffs = drop_index(&af.coeffs, idx);
            Some(ClosedForm::Affine(AffineFn { arity: af.arity - 1, coeffs: new_coeffs }))
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
            let new_bi = if idx < b { pw.branch_index - 1 } else { pw.branch_index };
            Some(ClosedForm::Piecewise(PiecewiseFn {
                arity: pw.arity - 1,
                branch_index: new_bi,
                zero_branch: Box::new(new_zero),
                pos_branch: Box::new(new_pos),
            }))
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
fn make_piecewise(arity: usize, branch_index: usize, zero_branch: ClosedForm, pos_branch: ClosedForm) -> ClosedForm {
    if let Some(dropped) = drop_arg(&pos_branch, branch_index + 1) {
        if dropped == zero_branch {
            return pos_branch;
        }
    }
    if let (ClosedForm::Affine(z), ClosedForm::Affine(p)) = (&zero_branch, &pos_branch) {
        let bi1 = branch_index + 1; // 1-based index of the branched arg
        // Adjusted constant: A.c0 = p.c0 - p.coeffs[bi1] (from the pos-branch shift by -1)
        let c0_ok = p.coeffs[0].checked_sub(p.coeffs[bi1])
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
            return ClosedForm::Affine(AffineFn { arity, coeffs: new_coeffs });
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
            let bi1_in_new_zero = if bi2 < branch_index { branch_index - 1 } else { branch_index };
            let pz: ClosedForm = *pp.zero_branch.clone();
            let pp_pos: ClosedForm = *pp.pos_branch.clone();
            // Slice zero_branch at bi2=0 (substitute & drop) and bi2>0 (shift for decrement).
            let z0 = zero_face_at(&zero_branch, bi2_in_zero + 1);
            let z_pos = pos_face_at(&zero_branch, bi2_in_zero + 1);
            let new_zero = make_piecewise(arity - 1, bi1_in_new_zero, z0, pz);
            let new_pos = make_piecewise(arity, branch_index, z_pos, pp_pos);
            if matches!(new_zero, ClosedForm::Affine(_)) && matches!(new_pos, ClosedForm::Affine(_)) {
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
/// The result has arity == inner_arity.  Returns `None` on i64 overflow.
fn compose_affine(outer: &AffineFn, inners: &[AffineFn]) -> Option<AffineFn> {
    debug_assert_eq!(outer.arity, inners.len());
    if inners.is_empty() {
        // 0-arg compose handled separately in closed_form_of; this shouldn't be reached.
        return None;
    }
    let inner_arity = inners[0].arity;
    debug_assert!(inners.iter().all(|f| f.arity == inner_arity));

    let mut new_coeffs = vec![0i64; inner_arity + 1];
    new_coeffs[0] = outer.coeffs[0];

    for (i, inner) in inners.iter().enumerate() {
        let c_i = outer.coeffs[i + 1];
        if c_i == 0 {
            continue;
        }
        new_coeffs[0] = new_coeffs[0].checked_add(c_i.checked_mul(inner.coeffs[0])?)?;
        for j in 1..=inner_arity {
            new_coeffs[j] =
                new_coeffs[j].checked_add(c_i.checked_mul(inner.coeffs[j])?)?;
        }
    }

    Some(AffineFn { arity: inner_arity, coeffs: new_coeffs })
}

/// Return a copy of `coeffs` with the element at `idx` removed.
fn drop_index(coeffs: &[i64], idx: usize) -> Vec<i64> {
    coeffs
        .iter()
        .enumerate()
        .filter(|&(i, _)| i != idx)
        .map(|(_, &c)| c)
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::enumerate::stream_grf;
    use crate::pruning::PruningOpts;
    use crate::simulate::{simulate, SimResult};

    fn grf(s: &str) -> Grf {
        s.parse().unwrap()
    }

    /// Assert closed_form_of matches simulate on a grid of inputs 0..=max_val per dimension.
    fn check_vs_sim(grf_str: &str, max_val: SmallNat) {
        let f = grf(grf_str);
        let sem = closed_form_of(&f).unwrap_or_else(|| panic!("closed_form_of returned None for {grf_str}"));
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
            let mut args : Vec<SmallNat> = vec![0; arity];
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
        assert_eq!(s, ClosedForm::Affine(AffineFn { arity: 0, coeffs: vec![0] }));
        assert_eq!(s.eval(&[]), Some(0));

        let s3 = closed_form_of(&grf("Z3")).unwrap();
        assert_eq!(s3.arity(), 3);
        assert_eq!(s3.eval(&[1, 2, 3]), Some(0));
    }

    #[test]
    fn test_succ() {
        let s = closed_form_of(&grf("S")).unwrap();
        assert_eq!(s, ClosedForm::Affine(AffineFn { arity: 1, coeffs: vec![1, 1] }));
        assert_eq!(s.eval(&[0]), Some(1));
        assert_eq!(s.eval(&[5]), Some(6));
    }

    #[test]
    fn test_proj() {
        let s = closed_form_of(&grf("P(2,1)")).unwrap();
        assert_eq!(s.eval(&[5, 3]), Some(5));

        let s2 = closed_form_of(&grf("P(2,2)")).unwrap();
        assert_eq!(s2.eval(&[5, 3]), Some(3));

        let s3 = closed_form_of(&grf("P(3,2)")).unwrap();
        assert_eq!(s3.eval(&[1, 7, 9]), Some(7));
    }

    // --- Compositions ---

    #[test]
    fn test_comp_succ_zero() {
        // C(S, Z0) = constant 1, arity 0
        let s = closed_form_of(&grf("C(S, Z0)")).unwrap();
        assert_eq!(s.arity(), 0);
        assert_eq!(s.eval(&[]), Some(1));
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
        assert_eq!(s.eval(&[]), Some(2));
    }

    #[test]
    fn test_comp0_lift() {
        // C2(Z0): lift arity-0 zero to arity 2
        let s = closed_form_of(&grf("C2(Z0)")).unwrap();
        assert_eq!(s.arity(), 2);
        assert_eq!(s.eval(&[3, 7]), Some(0));
    }

    // --- Rec Case A: h = acc + k ---

    #[test]
    fn test_rec_identity() {
        // R(Z0, C(S, P(2,2))) = identity: f(n) = n
        check_vs_sim("R(Z0, C(S, P(2,2)))", 10);
        let s = closed_form_of(&grf("R(Z0, C(S, P(2,2)))")).unwrap();
        assert_eq!(s, ClosedForm::Affine(AffineFn { arity: 1, coeffs: vec![0, 1] }));
    }

    #[test]
    fn test_rec_addition() {
        // R(P(1,1), C(S, P(3,2))) = addition: f(n, m) = n + m
        check_vs_sim("R(P(1,1), C(S, P(3,2)))", 5);
        let s = closed_form_of(&grf("R(P(1,1), C(S, P(3,2)))")).unwrap();
        assert_eq!(s, ClosedForm::Affine(AffineFn { arity: 2, coeffs: vec![0, 1, 1] }));
    }

    #[test]
    fn test_rec_affine_step2() {
        // R(S, C(S, C(S, P(3,2)))) = f(n, x) = 1 + 2n + x
        check_vs_sim("R(S, C(S, C(S, P(3,2))))", 5);
        let s = closed_form_of(&grf("R(S, C(S, C(S, P(3,2))))")).unwrap();
        assert_eq!(s, ClosedForm::Affine(AffineFn { arity: 2, coeffs: vec![1, 2, 1] }));
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
        check_vs_sim("C(R(R(S, P(3,3)), C(R(P(1,1), P(3,3)), P(4,4), P(4,2))), S, S, P(1,1))", 8);
    }

    #[test]
    fn test_comp_double_piecewise_none() {
        // pred(pred(n)) branches at n=2, not n=1 — not representable in our Piecewise.
        assert!(closed_form_of(&grf("C(R(Z0, P(2,1)), R(Z0, P(2,1)))")).is_none());
    }

    // --- Case A' (semantic acc+j detection) ---

    #[test]
    fn test_rec_case_a_semantic() {
        // C(P(2,1), P(2,2), P(2,1))(n,acc) = P(2,1)(acc, n) = acc  →  semantically acc+0
        // R(Z0, C(P(2,1), P(2,2), P(2,1))): f(n) = g() + 0*n = 0 for all n
        check_vs_sim("R(Z0, C(P(2,1), P(2,2), P(2,1)))", 8);
        let s = closed_form_of(&grf("R(Z0, C(P(2,1), P(2,2), P(2,1)))")).unwrap();
        assert_eq!(s, ClosedForm::Affine(AffineFn { arity: 1, coeffs: vec![0, 0] }));
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

    // --- None cases ---

    #[test]
    fn test_min_none() {
        assert!(closed_form_of(&grf("M(P(1,1))")).is_none());
        assert!(closed_form_of(&grf("M(S)")).is_none());
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
            assert_ne!(pw.branch_index, 0, "outer Piecewise should not branch on the counter");
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
        assert_eq!(cf, ClosedForm::Affine(AffineFn { arity: 1, coeffs: vec![0, 1] }));
        check_vs_sim("R(Z0, C(S, P(2,1)))", 8);

        // R(C(S, Z0), C(S, C(S, P(2,1)))): f(0)=1, f(n+1)=2+n → f(n)=n+1 (successor).
        let cf2 = closed_form_of(&grf("R(C(S, Z0), C(S, C(S, P(2,1))))")).unwrap();
        assert_eq!(cf2, ClosedForm::Affine(AffineFn { arity: 1, coeffs: vec![1, 1] }));
        check_vs_sim("R(C(S, Z0), C(S, C(S, P(2,1))))", 8);

        // R(Z1, C(S, P(3,1))): arity 2, f(0,m)=0, f(n+1,m)=1+n → f(n,m)=n (project first arg).
        let cf3 = closed_form_of(&grf("R(Z1, C(S, P(3,1)))")).unwrap();
        assert_eq!(cf3, ClosedForm::Affine(AffineFn { arity: 2, coeffs: vec![0, 1, 0] }));
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
                zero_branch: Box::new(ClosedForm::Affine(AffineFn { arity: 1, coeffs: vec![0, 1] })),
                pos_branch: Box::new(ClosedForm::Affine(AffineFn { arity: 2, coeffs: vec![0, 0, 0] })),
            }),
            "expected (x2=0 ? x1 : 0@x2-1), got {cf:?}"
        );
        check_vs_sim("R(Z1, C(R(S, Z3), P(3,3), P(3,1)))", 4);
    }

    // --- AffineFn arithmetic safety ---

    #[test]
    fn test_affine_negative_eval() {
        // Constant -1: returns None
        let af = AffineFn { arity: 0, coeffs: vec![-1] };
        assert_eq!(af.eval(&[]), None);
    }

    #[test]
    fn test_affine_negative_coeff() {
        // f(x) = 5 - x: None when x > 5
        let af = AffineFn { arity: 1, coeffs: vec![5, -1] };
        assert_eq!(af.eval(&[3]), Some(2));
        assert_eq!(af.eval(&[5]), Some(0));
        assert_eq!(af.eval(&[6]), None);
    }

    #[test]
    fn test_affine_overflow() {
        // i64::MAX * 2 overflows — should return None
        let af = AffineFn { arity: 1, coeffs: vec![0, i64::MAX] };
        assert_eq!(af.eval(&[2]), None);
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
}
