use crate::base::Num;
use crate::grf::Grf;

/// Affine function over natural numbers: c0 + c1*x1 + ... + ck*xk.
///
/// Coefficients are i64 to allow intermediate negatives during composition.
/// `eval` returns `None` when the result would be negative (outside the natural-number domain)
/// or when i64 arithmetic overflows.
#[derive(Clone, Debug, PartialEq, Eq)]
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
    pub fn eval(&self, args: &[Num]) -> Option<Num> {
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
        if result < 0 { None } else { Some(result as Num) }
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
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PiecewiseFn {
    pub arity: usize,
    pub branch_index: usize,
    pub zero_branch: Box<Sem>,
    pub pos_branch: Box<Sem>,
}

impl PiecewiseFn {
    pub fn eval(&self, args: &[Num]) -> Option<Num> {
        assert_eq!(args.len(), self.arity);
        let bi = self.branch_index;
        if args[bi] == 0 {
            let zero_args: Vec<Num> =
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
/// When `sem_of(grf)` returns `Some(sem)`, evaluating `sem.eval(args)` gives exactly
/// the same result as simulating `grf` on those args and is guaranteed to be total.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Sem {
    Affine(AffineFn),
    Piecewise(PiecewiseFn),
}

impl Sem {
    pub fn arity(&self) -> usize {
        match self {
            Sem::Affine(af) => af.arity,
            Sem::Piecewise(pw) => pw.arity,
        }
    }

    /// Evaluate the semantic function on concrete arguments.
    ///
    /// Returns `None` if the result would be negative (e.g. affine with negative sum),
    /// or on arithmetic overflow.
    pub fn eval(&self, args: &[Num]) -> Option<Num> {
        match self {
            Sem::Affine(af) => af.eval(args),
            Sem::Piecewise(pw) => pw.eval(args),
        }
    }

    pub fn lift(&self, arity: usize) -> Self {
        match self {
            Sem::Affine(af) => Sem::Affine(af.lift(arity)),
            Sem::Piecewise(pw) => Sem::Piecewise(pw.lift(arity)),
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
pub fn sem_of(grf: &Grf) -> Option<Sem> {
    match grf {
        // Atoms are all Affine
        Grf::Zero(k) => Some(Sem::Affine(AffineFn::zero(*k))),
        Grf::Succ => Some(Sem::Affine(AffineFn::succ())),
        Grf::Proj(k, i) => Some(Sem::Affine(AffineFn::proj(*k, *i))),

        Grf::Comp(g, hs, k) => {
            let sem_g = sem_of(g)?;
            let sem_hs: Vec<Sem> = hs.iter().map(sem_of).collect::<Option<_>>()?;
            sem_compose_general(&sem_g, &sem_hs, *k)
        }

        Grf::Rec(g, h) => {
            let k_outer = g.arity() + 1;
            let sem_g = sem_of(g)?;
            let sem_h = sem_of(h)?;
            sem_of_rec(&sem_g, &sem_h, k_outer)
        }

        // Not yet supported
        Grf::Min(_) => None,
    }
}

/// Compute the semantics of R(g, h) from their Sem representations.
///
/// k_outer = R(g,h).arity() = sem_g.arity()+1 = sem_h.arity()-1.
///
/// Three cases (tried in order):
///   A: sem_h is Affine with acc+j pattern  →  affine result
///   B: sem_h ignores acc (arg 2)           →  Piecewise(zero=sem_g, pos=sem_h-without-acc)
///   C: sem_h is Piecewise on counter       →  recurse: new_g = B_z∘g, new_h = B_p
fn sem_of_rec(sem_g: &Sem, sem_h: &Sem, k_outer: usize) -> Option<Sem> {
    // Case A: h(n, acc, rest) = j + acc  (j = coeffs[0], acc-coeff=1, rest-coeffs=0)
    if let Sem::Affine(af_h) = sem_h {
        if af_h.coeffs[1] == 0
            && af_h.coeffs[2] == 1
            && af_h.coeffs[3..].iter().all(|&c| c == 0)
            && af_h.coeffs[0] >= 0
        {
            if let Sem::Affine(g_af) = sem_g {
                let j = af_h.coeffs[0];
                let mut new_coeffs = Vec::with_capacity(k_outer + 1);
                new_coeffs.push(g_af.coeffs[0]);
                new_coeffs.push(j);
                new_coeffs.extend_from_slice(&g_af.coeffs[1..]);
                return Some(Sem::Affine(AffineFn { arity: k_outer, coeffs: new_coeffs }));
            }
        }
    }

    // Case B: h ignores accumulator (arg 2)  →  drop acc to get h': (counter, rest) → value
    if sem_ignores_arg(sem_h, 2) {
        if let Some(h_prime) = sem_drop_arg(sem_h, 2) {
            return Some(Sem::Piecewise(PiecewiseFn {
                arity: k_outer,
                branch_index: 0,
                zero_branch: Box::new(sem_g.clone()),
                pos_branch: Box::new(h_prime),
            }));
        }
    }

    // Case C: h is Piecewise on counter (arg 1)  →  peel one Piecewise layer off h
    if let Sem::Piecewise(pw_h) = sem_h {
        if pw_h.branch_index == 0 {
            // Build g'(rest) = B_z(g(rest), rest):
            //   B_z has arity k_outer (receives acc=g(rest), rest)
            //   We compose B_z with [sem_g, P(k-1,1), ..., P(k-1,k-1)]
            let b_z: &Sem = &pw_h.zero_branch;
            let k_rest = k_outer - 1;
            let mut inner_for_g_prime: Vec<Sem> = vec![sem_g.clone()];
            for i in 1..=k_rest {
                inner_for_g_prime.push(Sem::Affine(AffineFn::proj(k_rest, i)));
            }
            if b_z.arity() == inner_for_g_prime.len() {
                if let Some(sem_g_prime) = sem_compose_general(b_z, &inner_for_g_prime, k_rest) {
                    let b_p: &Sem = &pw_h.pos_branch;
                    if let Some(pos_branch) = sem_of_rec(&sem_g_prime, b_p, k_outer) {
                        return Some(Sem::Piecewise(PiecewiseFn {
                            arity: k_outer,
                            branch_index: 0,
                            zero_branch: Box::new(sem_g.clone()),
                            pos_branch: Box::new(pos_branch),
                        }));
                    }
                }
            }
        }
    }

    // Case D: h ignores counter (arg 1) and the step has a 1-step fixed point.
    // h'(acc, rest) = h with counter dropped.  Compute one_step = h'(g(rest), rest).
    // If h' is stable (each leaf Affine is either pure identity or ignores acc),
    // then one_step is a fixed point: f(n≥1, rest) = one_step(rest).
    if sem_ignores_arg(sem_h, 1) {
        if let Some(h_prime) = sem_drop_arg(sem_h, 1) {
            if h_prime_is_stable(&h_prime) {
                let k_rest = k_outer - 1;
                let mut inners: Vec<Sem> = vec![sem_g.clone()];
                for i in 1..=k_rest {
                    inners.push(Sem::Affine(AffineFn::proj(k_rest, i)));
                }
                if let Some(one_step) = sem_compose_general(&h_prime, &inners, k_rest) {
                    let pos_branch = sem_prepend_arg(&one_step);
                    return Some(Sem::Piecewise(PiecewiseFn {
                        arity: k_outer,
                        branch_index: 0,
                        zero_branch: Box::new(sem_g.clone()),
                        pos_branch: Box::new(pos_branch),
                    }));
                }
            }
        }
    }

    None
}

/// Returns true when `sem` ignores argument at 1-based `idx` for all inputs.
pub fn sem_ignores_arg(sem: &Sem, idx: usize) -> bool {
    match sem {
        Sem::Affine(af) => af.arity < idx || af.coeffs[idx] == 0,
        Sem::Piecewise(pw) => {
            let b = pw.branch_index + 1; // 1-based branch variable
            if idx == b {
                return false; // branch variable is always used for branching
            }
            // In zero_branch, x_b is dropped: positions < b map to same idx,
            // positions > b map to idx-1.
            let idx_in_zero = if idx < b { idx } else { idx - 1 };
            sem_ignores_arg(&pw.zero_branch, idx_in_zero)
                && sem_ignores_arg(&pw.pos_branch, idx)
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
fn sem_compose_general(h: &Sem, inners: &[Sem], arity: usize) -> Option<Sem> {
    // Base case: 0-arity composition — h is a constant, no inputs consumed.
    if inners.is_empty() {
        return Some(h.lift(arity));
    }

    debug_assert_eq!(h.arity(), inners.len());
    debug_assert!(inners.iter().all(|s| s.arity() == arity));

    // Base case: all Affine
    if let Sem::Affine(h_af) = h {
        if let Some(inner_afs) = inners
            .iter()
            .map(|s| if let Sem::Affine(af) = s { Some(af.clone()) } else { None })
            .collect::<Option<Vec<_>>>()
        {
            return Some(Sem::Affine(compose_affine(h_af, &inner_afs)?));
        }
    }

    match h {
        Sem::Affine(_) => {
            // h is affine but some inner is Piecewise.
            // Find j: the branching variable all Piecewise inners agree on.
            if arity == 0 {
                return None;
            }
            let mut j_opt: Option<usize> = None;
            for inner in inners {
                if let Sem::Piecewise(pw) = inner {
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
                if let Sem::Piecewise(pw) = inner {
                    if pw.branch_index + 1 != j && !sem_ignores_arg(inner, j) {
                        return None;
                    }
                }
            }
            let zero_inners: Vec<Sem> = inners.iter().map(|s| zero_face_at(s, j)).collect();
            let pos_inners: Vec<Sem> = inners.iter().map(|s| pos_face_at(s, j)).collect();
            let zero_sem = sem_compose_general(h, &zero_inners, arity - 1)?;
            let pos_sem = sem_compose_general(h, &pos_inners, arity)?;
            Some(Sem::Piecewise(PiecewiseFn {
                arity,
                branch_index: j - 1,
                zero_branch: Box::new(zero_sem),
                pos_branch: Box::new(pos_sem),
            }))
        }
        Sem::Piecewise(pw) => {
            // If h always returns 0, so does the composition.
            if is_always_zero(h) {
                return Some(Sem::Affine(AffineFn::zero(arity)));
            }

            // h branches on y_{bi+1} = inners[bi](x).
            let bi = pw.branch_index;
            let g_branch = &inners[bi];

            // Case 1: inners[bi] is identically 0 → always fire zero_branch on rest.
            if is_always_zero(g_branch) {
                let rest: Vec<Sem> = inners.iter().enumerate()
                    .filter(|(i, _)| *i != bi)
                    .map(|(_, s)| s.clone())
                    .collect();
                let raw = if rest.is_empty() {
                    pw.zero_branch.as_ref().clone()
                } else {
                    sem_compose_general(&pw.zero_branch, &rest, arity)?
                };
                return Some(raw.lift(arity));
            }

            // Case 2: inners[bi] ≥ 1 always → always fire pos_branch(inners[bi]-1, rest).
            if let Some(g_branch_m1) = always_pos_minus_one(g_branch) {
                let mut pos_inners: Vec<Sem> = inners.to_vec();
                pos_inners[bi] = Sem::Affine(g_branch_m1);
                return sem_compose_general(&pw.pos_branch, &pos_inners, arity);
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
                    if let Sem::Piecewise(pw2) = inner {
                        pw2.branch_index + 1 == j || sem_ignores_arg(inner, j)
                    } else {
                        true
                    }
                });
            if !others_ok {
                return None;
            }
            // Zero branch: compose zero_branch with all inners except inners[bi],
            // each substituted at xj=0.
            let zero_inners: Vec<Sem> = inners.iter().enumerate()
                .filter(|(i, _)| *i != bi)
                .map(|(_, inner)| zero_face_at(inner, j))
                .collect();
            let zero_arity = arity - 1;
            let zero_sem = if zero_inners.is_empty() {
                pw.zero_branch.as_ref().clone().lift(zero_arity)
            } else {
                sem_compose_general(&pw.zero_branch, &zero_inners, zero_arity)?.lift(zero_arity)
            };
            // Pos branch: inners[bi]=xj delivers xj-1 ✓; apply pos_face_at to all
            // other inners so they evaluate to their caller-context value when xj is
            // decremented by the outer Piecewise.
            let mut pos_inners: Vec<Sem> = inners.to_vec();
            for (i, inner) in pos_inners.iter_mut().enumerate() {
                if i != bi {
                    *inner = pos_face_at(inner, j);
                }
            }
            let pos_sem = sem_compose_general(&pw.pos_branch, &pos_inners, arity)?;
            Some(Sem::Piecewise(PiecewiseFn {
                arity,
                branch_index: j - 1,
                zero_branch: Box::new(zero_sem),
                pos_branch: Box::new(pos_sem),
            }))
        }
    }
}

/// Substitute xj=0 (1-based `j`) and drop it from the argument list.
/// The result has arity one less than `sem`.
fn zero_face_at(sem: &Sem, j: usize) -> Sem {
    match sem {
        Sem::Affine(af) => {
            let new_coeffs = drop_index(&af.coeffs, j);
            Sem::Affine(AffineFn { arity: af.arity - 1, coeffs: new_coeffs })
        }
        Sem::Piecewise(pw) => {
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
                Sem::Piecewise(PiecewiseFn {
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
/// - Piecewise branching on a different variable: unchanged (only valid when xj-independent).
fn pos_face_at(sem: &Sem, j: usize) -> Sem {
    match sem {
        Sem::Affine(af) => {
            let mut new_coeffs = af.coeffs.clone();
            new_coeffs[0] += new_coeffs[j];
            Sem::Affine(AffineFn { arity: af.arity, coeffs: new_coeffs })
        }
        Sem::Piecewise(pw) => {
            if pw.branch_index + 1 == j {
                *pw.pos_branch.clone()
            } else {
                sem.clone()
            }
        }
    }
}


/// If `sem` is a pure projection f(x) = xj (1-based j), return `Some(j)`.
fn is_proj_of(sem: &Sem) -> Option<usize> {
    match sem {
        Sem::Affine(af) if af.coeffs[0] == 0 => {
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
/// Used to turn a (rest)-indexed Sem into a (counter, rest)-indexed Sem.
fn sem_prepend_arg(sem: &Sem) -> Sem {
    match sem {
        Sem::Affine(af) => {
            let mut new_coeffs = vec![af.coeffs[0], 0]; // constant, then new ignored arg
            new_coeffs.extend_from_slice(&af.coeffs[1..]);
            Sem::Affine(AffineFn { arity: af.arity + 1, coeffs: new_coeffs })
        }
        Sem::Piecewise(pw) => Sem::Piecewise(PiecewiseFn {
            arity: pw.arity + 1,
            branch_index: pw.branch_index + 1, // all indices shift right by 1
            zero_branch: Box::new(sem_prepend_arg(&pw.zero_branch)),
            pos_branch: Box::new(sem_prepend_arg(&pw.pos_branch)),
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
fn h_prime_is_stable(h_prime: &Sem) -> bool {
    match h_prime {
        Sem::Affine(af) => {
            let acc_coeff = if af.arity >= 1 { af.coeffs[1] } else { 0 };
            match acc_coeff {
                0 => true, // constant after 1 step
                1 => af.coeffs[2..].iter().all(|&c| c == 0), // pure identity
                _ => false,
            }
        }
        Sem::Piecewise(pw) => {
            if pw.branch_index == 0 {
                return false; // branches on acc — too complex
            }
            h_prime_is_stable(&pw.zero_branch) && h_prime_is_stable(&pw.pos_branch)
        }
    }
}

/// Returns true when `sem` evaluates to 0 for all natural-number inputs.
fn is_always_zero(sem: &Sem) -> bool {
    match sem {
        Sem::Affine(af) => af.coeffs.iter().all(|&c| c == 0),
        Sem::Piecewise(pw) => is_always_zero(&pw.zero_branch) && is_always_zero(&pw.pos_branch),
    }
}

/// If `sem` is guaranteed ≥ 1 for all natural-number inputs (Affine with constant ≥ 1
/// and all variable coefficients ≥ 0), returns `Some(sem - 1)`.
fn always_pos_minus_one(sem: &Sem) -> Option<AffineFn> {
    match sem {
        Sem::Affine(af)
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
fn sem_drop_arg(sem: &Sem, idx: usize) -> Option<Sem> {
    debug_assert!(idx >= 1);
    match sem {
        Sem::Affine(af) => {
            if af.coeffs[idx] != 0 {
                return None; // arg is used
            }
            let new_coeffs = drop_index(&af.coeffs, idx);
            Some(Sem::Affine(AffineFn { arity: af.arity - 1, coeffs: new_coeffs }))
        }
        Sem::Piecewise(pw) => {
            let b = pw.branch_index + 1; // 1-based
            if idx == b {
                return None; // cannot remove the branching variable
            }
            // In zero_branch (arity pw.arity-1), x_b is absent:
            // idx < b → same position; idx > b → shifted down by 1.
            let idx_in_zero = if idx < b { idx } else { idx - 1 };
            let new_zero = sem_drop_arg(&pw.zero_branch, idx_in_zero)?;
            let new_pos = sem_drop_arg(&pw.pos_branch, idx)?;
            // If we drop an arg before b, the branch_index shifts down.
            let new_bi = if idx < b { pw.branch_index - 1 } else { pw.branch_index };
            Some(Sem::Piecewise(PiecewiseFn {
                arity: pw.arity - 1,
                branch_index: new_bi,
                zero_branch: Box::new(new_zero),
                pos_branch: Box::new(new_pos),
            }))
        }
    }
}

/// Compose an outer affine function with a slice of inner affine functions.
///
/// `outer` must have arity == inners.len(); all inners must have the same arity.
/// The result has arity == inner_arity.  Returns `None` on i64 overflow.
fn compose_affine(outer: &AffineFn, inners: &[AffineFn]) -> Option<AffineFn> {
    debug_assert_eq!(outer.arity, inners.len());
    if inners.is_empty() {
        // 0-arg compose handled separately in sem_of; this shouldn't be reached.
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
    use crate::simulate::simulate;

    fn grf(s: &str) -> Grf {
        s.parse().unwrap()
    }

    /// Assert sem_of matches simulate on a grid of inputs 0..=max_val per dimension.
    fn check_vs_sim(grf_str: &str, max_val: u64) {
        let f = grf(grf_str);
        let sem = sem_of(&f).unwrap_or_else(|| panic!("sem_of returned None for {grf_str}"));
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
            let mut args = vec![0u64; arity];
            let mut rem = idx;
            for a in args.iter_mut().rev() {
                *a = (rem % n) as u64;
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
        let s = sem_of(&grf("Z0")).unwrap();
        assert_eq!(s, Sem::Affine(AffineFn { arity: 0, coeffs: vec![0] }));
        assert_eq!(s.eval(&[]), Some(0));

        let s3 = sem_of(&grf("Z3")).unwrap();
        assert_eq!(s3.arity(), 3);
        assert_eq!(s3.eval(&[1, 2, 3]), Some(0));
    }

    #[test]
    fn test_succ() {
        let s = sem_of(&grf("S")).unwrap();
        assert_eq!(s, Sem::Affine(AffineFn { arity: 1, coeffs: vec![1, 1] }));
        assert_eq!(s.eval(&[0]), Some(1));
        assert_eq!(s.eval(&[5]), Some(6));
    }

    #[test]
    fn test_proj() {
        let s = sem_of(&grf("P(2,1)")).unwrap();
        assert_eq!(s.eval(&[5, 3]), Some(5));

        let s2 = sem_of(&grf("P(2,2)")).unwrap();
        assert_eq!(s2.eval(&[5, 3]), Some(3));

        let s3 = sem_of(&grf("P(3,2)")).unwrap();
        assert_eq!(s3.eval(&[1, 7, 9]), Some(7));
    }

    // --- Compositions ---

    #[test]
    fn test_comp_succ_zero() {
        // C(S, Z0) = constant 1, arity 0
        let s = sem_of(&grf("C(S, Z0)")).unwrap();
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
        let s = sem_of(&grf("C(S, C(S, Z0))")).unwrap();
        assert_eq!(s.arity(), 0);
        assert_eq!(s.eval(&[]), Some(2));
    }

    #[test]
    fn test_comp0_lift() {
        // C2(Z0): lift arity-0 zero to arity 2
        let s = sem_of(&grf("C2(Z0)")).unwrap();
        assert_eq!(s.arity(), 2);
        assert_eq!(s.eval(&[3, 7]), Some(0));
    }

    // --- Rec Case A: h = acc + k ---

    #[test]
    fn test_rec_identity() {
        // R(Z0, C(S, P(2,2))) = identity: f(n) = n
        check_vs_sim("R(Z0, C(S, P(2,2)))", 10);
        let s = sem_of(&grf("R(Z0, C(S, P(2,2)))")).unwrap();
        assert_eq!(s, Sem::Affine(AffineFn { arity: 1, coeffs: vec![0, 1] }));
    }

    #[test]
    fn test_rec_addition() {
        // R(P(1,1), C(S, P(3,2))) = addition: f(n, m) = n + m
        check_vs_sim("R(P(1,1), C(S, P(3,2)))", 5);
        let s = sem_of(&grf("R(P(1,1), C(S, P(3,2)))")).unwrap();
        assert_eq!(s, Sem::Affine(AffineFn { arity: 2, coeffs: vec![0, 1, 1] }));
    }

    #[test]
    fn test_rec_affine_step2() {
        // R(S, C(S, C(S, P(3,2)))) = f(n, x) = 1 + 2n + x
        check_vs_sim("R(S, C(S, C(S, P(3,2))))", 5);
        let s = sem_of(&grf("R(S, C(S, C(S, P(3,2))))")).unwrap();
        assert_eq!(s, Sem::Affine(AffineFn { arity: 2, coeffs: vec![1, 2, 1] }));
    }

    // --- Rec Case B: h ignores accumulator ---

    #[test]
    fn test_rec_predecessor() {
        // R(Z0, P(2,1)) = predecessor (saturating at 0): f(0)=0, f(n)=n-1
        let s = sem_of(&grf("R(Z0, P(2,1))")).unwrap();
        assert!(matches!(s, Sem::Piecewise(_)));
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
    fn test_comp_double_piecewise_none() {
        // pred(pred(n)) branches at n=2, not n=1 — not representable in our Piecewise.
        assert!(sem_of(&grf("C(R(Z0, P(2,1)), R(Z0, P(2,1)))")).is_none());
    }

    // --- Case A' (semantic acc+j detection) ---

    #[test]
    fn test_rec_case_a_semantic() {
        // C(P(2,1), P(2,2), P(2,1))(n,acc) = P(2,1)(acc, n) = acc  →  semantically acc+0
        // R(Z0, C(P(2,1), P(2,2), P(2,1))): f(n) = g() + 0*n = 0 for all n
        check_vs_sim("R(Z0, C(P(2,1), P(2,2), P(2,1)))", 8);
        let s = sem_of(&grf("R(Z0, C(P(2,1), P(2,2), P(2,1)))")).unwrap();
        assert_eq!(s, Sem::Affine(AffineFn { arity: 1, coeffs: vec![0, 0] }));
    }

    // --- Case B with Piecewise step ---

    #[test]
    fn test_rec_case_b_piecewise_step() {
        // R(Z0, R(Z1, P(3,1))): h = R(Z1, P(3,1)) which ignores acc
        // h(counter, acc, x) = R(Z1, P(3,1))(counter, x): if counter=0 then x else counter-1
        // But h ignores acc. Let's verify sem_of works.
        // R(g=Z0, h=R(Z1,P(3,1))): g.arity=0, k_outer=1
        // f(0) = g() = 0; f(n) = h(n-1, f(n-1)) = R(Z1,P(3,1))(n-1, _, _) ignoring acc
        check_vs_sim("R(Z0, R(Z1, P(3,1)))", 8);
    }

    // --- None cases ---

    #[test]
    fn test_min_none() {
        assert!(sem_of(&grf("M(P(1,1))")).is_none());
        assert!(sem_of(&grf("M(S)")).is_none());
    }

    #[test]
    fn test_rec_case_d_piecewise_on_rest_arg() {
        // b(z,y) = y when z<2, else z-2.  b = R(P(1,1), R(P(2,1), P(4,1)))
        // c = R(P(2,1), C(b, P(4,4), P(4,2))): arity 3, g=P(2,1)=y, h ignores counter
        // c(n,y,z): for z<2 → y; for z≥2 → z-2.  Counter n is irrelevant.
        check_vs_sim("R(P(2,1), C(R(P(1,1),R(P(2,1),P(4,1))),P(4,4),P(4,2)))", 5);
    }

    #[test]
    fn test_rec_mul_none() {
        // Multiplication: h = add(acc, m), not a constant step — None
        // R(Z0, C(R(P(1,1),C(S,P(3,2))), P(3,2), P(3,3)))
        assert!(sem_of(&grf("R(Z0, C(R(P(1,1),C(S,P(3,2))),P(3,2),P(3,3)))")).is_none());
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
}
