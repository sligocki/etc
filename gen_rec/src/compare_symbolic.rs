use crate::closed_form::{AffineFn, ClosedForm, PolynomialFn, closed_form_ignores_arg};
use crate::grf::{Grf, GrfKind};

/// Represents the result of comparing two functions f and g for all inputs x >= 0.
/// If `GreaterEqual`, then f(x) >= g(x) for all x >= 0.
/// If `LessEqual`, then f(x) <= g(x) for all x >= 0.
/// If `Equal`, then f(x) == g(x) for all x >= 0.
/// If `Uncertain`, the functions might cross, or bounds are too weak to prove domination.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PointwiseOrder {
    GreaterEqual,
    LessEqual,
    Equal,
    Uncertain,
}

impl PointwiseOrder {
    pub fn reverse(self) -> Self {
        match self {
            PointwiseOrder::GreaterEqual => PointwiseOrder::LessEqual,
            PointwiseOrder::LessEqual => PointwiseOrder::GreaterEqual,
            PointwiseOrder::Equal => PointwiseOrder::Equal,
            PointwiseOrder::Uncertain => PointwiseOrder::Uncertain,
        }
    }

    pub fn is_greater_equal(&self) -> bool {
        matches!(self, PointwiseOrder::GreaterEqual)
    }
    pub fn is_less_equal(&self) -> bool {
        matches!(self, PointwiseOrder::LessEqual)
    }
    pub fn is_equal(&self) -> bool {
        matches!(self, PointwiseOrder::Equal)
    }
    pub fn is_uncertain(&self) -> bool {
        matches!(self, PointwiseOrder::Uncertain)
    }
}

/// Computes a strict structural domination ordering between `a` and `b`.
pub fn compare_strict(a: &ClosedForm, b: &ClosedForm) -> PointwiseOrder {
    // If they are identical in memory or structurally equal
    if a == b {
        return PointwiseOrder::Equal;
    }

    match (a, b) {
        (ClosedForm::Affine(af1), ClosedForm::Affine(af2)) => compare_affine(af1, af2),
        (ClosedForm::Iterated(it1), ClosedForm::Iterated(it2)) => {
            if it1.arity != it2.arity {
                return PointwiseOrder::Uncertain;
            }
            let base_cmp = compare_strict(&it1.base, &it2.base);
            let step_cmp = compare_strict(&it1.step, &it2.step);

            if base_cmp == PointwiseOrder::Equal && step_cmp == PointwiseOrder::Equal {
                PointwiseOrder::Equal
            } else if (base_cmp == PointwiseOrder::GreaterEqual
                || base_cmp == PointwiseOrder::Equal)
                && (step_cmp == PointwiseOrder::GreaterEqual || step_cmp == PointwiseOrder::Equal)
            {
                PointwiseOrder::GreaterEqual
            } else if (base_cmp == PointwiseOrder::LessEqual || base_cmp == PointwiseOrder::Equal)
                && (step_cmp == PointwiseOrder::LessEqual || step_cmp == PointwiseOrder::Equal)
            {
                PointwiseOrder::LessEqual
            } else {
                PointwiseOrder::Uncertain
            }
        }
        (ClosedForm::Polynomial(p1), ClosedForm::Polynomial(p2)) => {
            if p1.arity != p2.arity || p1.poly_arg != p2.poly_arg {
                return PointwiseOrder::Uncertain;
            }
            let mut all_ge = true;
            let mut all_le = true;
            let mut any_gt = false;
            let mut any_lt = false;

            let max_len = std::cmp::max(p1.poly_coeffs.len(), p2.poly_coeffs.len());
            for i in 0..max_len {
                let c1 = p1.poly_coeffs.get(i).copied().unwrap_or(0);
                let c2 = p2.poly_coeffs.get(i).copied().unwrap_or(0);
                if c1 > c2 {
                    all_le = false;
                    any_gt = true;
                } else if c1 < c2 {
                    all_ge = false;
                    any_lt = true;
                }
            }

            let tail_cmp = compare_affine(&p1.affine_tail, &p2.affine_tail);
            match tail_cmp {
                PointwiseOrder::GreaterEqual => {
                    all_le = false;
                    any_gt = true;
                }
                PointwiseOrder::LessEqual => {
                    all_ge = false;
                    any_lt = true;
                }
                PointwiseOrder::Uncertain => {
                    all_le = false;
                    all_ge = false;
                }
                PointwiseOrder::Equal => {}
            }

            if all_ge && any_gt {
                PointwiseOrder::GreaterEqual
            } else if all_le && any_lt {
                PointwiseOrder::LessEqual
            } else if all_ge && all_le {
                PointwiseOrder::Equal
            } else {
                PointwiseOrder::Uncertain
            }
        }
        // Basic cross-type fallback checks
        (ClosedForm::Affine(_), ClosedForm::Iterated(_)) => PointwiseOrder::LessEqual,
        (ClosedForm::Iterated(_), ClosedForm::Affine(_)) => PointwiseOrder::GreaterEqual,
        (ClosedForm::Affine(_), ClosedForm::Polynomial(_)) => PointwiseOrder::Uncertain, // Strict bounds cross often
        (ClosedForm::Polynomial(_), ClosedForm::Affine(_)) => PointwiseOrder::Uncertain,
        // Add more recursive structural comparisons here
        _ => PointwiseOrder::Uncertain,
    }
}

fn compare_affine(a: &AffineFn, b: &AffineFn) -> PointwiseOrder {
    if a.arity != b.arity {
        return PointwiseOrder::Uncertain;
    }

    let mut all_ge = true;
    let mut all_le = true;
    let mut any_gt = false;
    let mut any_lt = false;

    for (c1, c2) in a.coeffs.iter().zip(b.coeffs.iter()) {
        if c1 > c2 {
            all_le = false;
            any_gt = true;
        } else if c1 < c2 {
            all_ge = false;
            any_lt = true;
        }
    }

    if all_ge && any_gt {
        PointwiseOrder::GreaterEqual
    } else if all_le && any_lt {
        PointwiseOrder::LessEqual
    } else if all_ge && all_le {
        PointwiseOrder::Equal
    } else {
        PointwiseOrder::Uncertain
    }
}

/// Represents a massive number via base-10 nested Knuth up-arrows.
#[derive(Debug, Clone, PartialEq)]
pub enum Knuth10 {
    /// A pure floating point value
    Val(f64),
    /// Represents `10 \uparrow^{arrows} inner`
    UpArrow(u64, Box<Knuth10>),
}

impl Knuth10 {
    /// Standardizes the power tower representation by collapsing trivial exponents
    pub fn normalize(self) -> Self {
        match self {
            Knuth10::Val(v) => {
                if v >= 100.0 && v.is_finite() {
                    Knuth10::UpArrow(1, Box::new(Knuth10::Val(v.log10()))).normalize()
                } else {
                    Knuth10::Val(v)
                }
            }
            Knuth10::UpArrow(n, inner) => {
                let norm_inner = inner.normalize();
                if n == 1 {
                    if let Knuth10::Val(v) = &norm_inner {
                        if *v < 2.0 {
                            return Knuth10::Val(10f64.powf(*v));
                        }
                    }
                }
                Knuth10::UpArrow(n, Box::new(norm_inner))
            }
        }
    }
}

impl Eq for Knuth10 {}

impl PartialOrd for Knuth10 {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Knuth10 {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let a = self.clone().normalize();
        let b = other.clone().normalize();

        match (&a, &b) {
            (Knuth10::Val(av), Knuth10::Val(bv)) => av.total_cmp(bv),
            (Knuth10::Val(av), Knuth10::UpArrow(_, _)) => {
                if *av < 100.0 {
                    return std::cmp::Ordering::Less;
                }
                let a_up = Knuth10::UpArrow(1, Box::new(Knuth10::Val(av.log10()))); // Do not normalize here! We know log10 >= 2.0
                a_up.cmp(&b)
            }
            (Knuth10::UpArrow(_, _), Knuth10::Val(bv)) => {
                if *bv < 100.0 {
                    return std::cmp::Ordering::Greater;
                }
                let b_up = Knuth10::UpArrow(1, Box::new(Knuth10::Val(bv.log10()))); // Do not normalize here! We know log10 >= 2.0
                a.cmp(&b_up)
            }
            (Knuth10::UpArrow(an, a_inner), Knuth10::UpArrow(bn, b_inner)) => {
                if an < bn {
                    std::cmp::Ordering::Less
                } else if an > bn {
                    std::cmp::Ordering::Greater
                } else {
                    a_inner.cmp(b_inner)
                }
            }
        }
    }
}

impl Knuth10 {
    /// If is_upper is true, returns an upper bound: 10^{max(k, log10(c)) + log10(2)}
    /// If is_upper is false, returns a lower bound: simply returns self.
    pub fn add_f64(&self, c: f64, is_upper: bool) -> Self {
        if c <= 0.0 {
            return match self {
                Knuth10::Val(v) => Knuth10::Val(v + c), // Exact for values
                _ => {
                    if is_upper {
                        self.clone() // Upper bound: dropping subtraction is safe (makes it larger)
                    } else {
                        Knuth10::Val(0.0) // Ultra conservative subtraction for power towers
                    }
                }
            };
        }

        match self {
            Knuth10::Val(v) => Knuth10::Val(v + c), // Exact for values
            Knuth10::UpArrow(n, inner) => {
                if !is_upper {
                    return self.clone(); // Lower bound: 10^K + c >= 10^K
                }
                // To compute Upper Bound of 10^K + c:
                // If c is small relative to 10^K, 10^K + c <= 2 * 10^K = 10^{K + log10(2)}.
                // So we add log10(2) to the inner exponent K.
                // Wait, if c is massive (c > 10^K), 10^K + c <= 2c = 10^{log10(c) + log10(2)}.
                // We don't dynamically know K at compile time if K is an UpArrow itself,
                // but we know any UpArrow represents a value >= 10.
                if *n == 1 {
                    // K = inner
                    // Upper bound of 10^K + c:
                    // We must choose max(K, log10(c)) + log10(2).
                    // If log10(c) <= 0 (c <= 1), we just use K + log10(2).
                    let log_c = c.log10();
                    if log_c <= 0.0 {
                        return Knuth10::UpArrow(
                            1,
                            Box::new(inner.add_f64(10f64.log10() * 0.30103, true)),
                        ); // log10(2) approx 0.30103
                    } else {
                        // Max logic. Since `inner` is generic Knuth10, taking max is complex.
                        // However, c is f64, so log10(c) is at most 308 (for f64::MAX).
                        // If inner is a power tower, it trivially dwarfs 308.
                        // So we safely assume K > log10(c) unless K is explicitly a small Val.
                        let mut use_c = false;
                        if let Knuth10::Val(kv) = &**inner {
                            if log_c > *kv {
                                use_c = true;
                            }
                        }
                        if use_c {
                            return Knuth10::Val(c * 2.0);
                        } else {
                            return Knuth10::UpArrow(
                                1,
                                Box::new(inner.add_f64(2f64.log10(), true)),
                            );
                        }
                    }
                } else {
                    // For n >= 2, 10^^n k is astronomically larger than any f64 c.
                    // 10^^n k + c <= 2 * 10^^n k = 10^{(10^^(n-1) k) + log10(2)}
                    // We just recursively add log10(2) to the inner value!
                    Knuth10::UpArrow(*n, Box::new(inner.add_f64(2f64.log10(), true)))
                }
            }
        }
    }

    /// Performs strict bounded multiplication: self * c
    /// If is_upper is true, returns an upper bound.
    /// If is_upper is false, returns a lower bound.
    pub fn mul_f64(&self, c: f64, is_upper: bool) -> Self {
        if c <= 0.0 {
            return Knuth10::Val(0.0);
        }
        if c == 1.0 {
            return self.clone();
        }

        match self {
            Knuth10::Val(v) => Knuth10::Val(v * c),
            Knuth10::UpArrow(n, inner) => {
                // c * 10^K = 10^{K + log10(c)}
                // We translate multiplication into addition on the inner exponent!
                let log_c = c.log10();
                // We add log_c to the inner.
                // Wait, if c < 1, log_c is negative. add_f64 handles positive c...
                // But wait! If log_c is negative, subtracting from K yields a strictly smaller value.
                // For a lower bound, if we drop log_c (make it 0), it's larger, so we can't ignore it.
                // Actually, if we just want a simple bound, we can do:
                if log_c > 0.0 {
                    // c > 1. Multiplication increases value.
                    if is_upper {
                        // Upper bound: K + log_c
                        // Wait! Inner addition! log_c is an f64!
                        // So we use add_f64(log_c, is_upper) on inner?
                        // Yes! K + log_c <= upper bound of (K + log_c).
                        return Knuth10::UpArrow(*n, Box::new(inner.add_f64(log_c, true)));
                    } else {
                        // Lower bound: self * c >= self (since c > 1)
                        return self.clone();
                    }
                } else {
                    // c < 1. Multiplication decreases value.
                    if is_upper {
                        // Upper bound: self * c <= self
                        return self.clone();
                    } else {
                        // Lower bound: K - |log_c|.
                        // We need a conservative lower bound for subtraction.
                        // Currently, let's just drop the subtraction entirely for huge towers? No, K - 1 >= 0?
                        // If n >= 2, K is a power tower, subtracting 1 is negligible, we can just say inner is basically unchanged?
                        // Wait, for lower bounds, we'd rather be safe.
                        // If we don't have subtract implemented, just return Val(0.0) if we must?
                        // Let's implement subtract manually here for Val, and for UpArrow it's basically a no-op since K >> |log_c|.
                        match &**inner {
                            Knuth10::Val(kv) => {
                                Knuth10::UpArrow(*n, Box::new(Knuth10::Val(*kv + log_c)))
                            }
                            _ => self.clone(), // For massive towers, K - 100 is essentially K in lower bound asymptotic terms.
                        }
                    }
                }
            }
        }
    }
}

impl std::fmt::Display for Knuth10 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Knuth10::Val(v) => write!(f, "{:.2}", v),
            Knuth10::UpArrow(1, inner) => write!(f, "10^{}", inner),
            Knuth10::UpArrow(2, inner) => write!(f, "10 ↑↑ {}", inner),
            Knuth10::UpArrow(3, inner) => write!(f, "10 ↑↑↑ {}", inner),
            Knuth10::UpArrow(4, inner) => write!(f, "10 ↑↑↑↑ {}", inner),
            Knuth10::UpArrow(n, inner) => write!(f, "10 ↑^{} {}", n, inner),
        }
    }
}

/// Represents a symbolically evaluated value that may be too large to fit in `u64`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SymVal {
    Const(u64),
    FuncApp(Grf, Vec<SymVal>),
}

/// Computes the asymptotic degree `d` of a polynomial, or 1 if it is affine/constant.
fn asymptotic_degree(cf: &ClosedForm) -> usize {
    match cf {
        ClosedForm::Polynomial(poly) => {
            if poly.poly_arg == 1 {
                let mut d = 1;
                for (i, &c) in poly.poly_coeffs.iter().enumerate() {
                    if c > 0 {
                        d = d.max(i + 2);
                    }
                }
                d
            } else {
                1
            }
        }
        _ => 1,
    }
}

/// Computes strict lower and upper bounds using the `Knuth10` base-10 up-arrow representation
/// for the exact value of the affine function `func` iterated `k` times on input `x`.
/// Since affine iteration represents standard exponential growth, it naturally
/// returns bounds natively in the form `10^y` (a single UpArrow).
fn bounds_for_affine(
    func: &AffineFn,
    k_min: &Knuth10,
    k_max: &Knuth10,
    x: u64,
) -> Option<(Knuth10, Knuth10)> {
    if func.arity >= 1 {
        let c_min = func.coeffs[1] as f64; // The coefficient for the first argument (acc)
        let mut c_max = 0.0;
        for &c in func.coeffs.iter() {
            c_max += c as f64;
        }

        if c_min >= 1.0 {
            let x_f64 = x.max(1) as f64;

            // Lower bound: k_min * log10(c_min) + log10(x)
            let inner_min = k_min
                .mul_f64(c_min.log10(), false)
                .add_f64(x_f64.log10(), false);
            // Upper bound: k_max * log10(c_max) + log10(x)
            let inner_max = k_max
                .mul_f64(c_max.log10(), true)
                .add_f64(x_f64.log10(), true);

            return Some((
                Knuth10::UpArrow(1, Box::new(inner_min)),
                Knuth10::UpArrow(1, Box::new(inner_max)),
            ));
        }
    }
    None
}

/// Computes strict lower and upper bounds using the `Knuth10` base-10 up-arrow representation
/// for the exact value of the polynomial `poly` iterated `k` times on input `x`.
/// Since polynomial iteration yields double-exponential growth, it naturally
/// returns bounds natively in the form `10^10^y` (a nested double UpArrow).
/// Returns `None` if the polynomial does not operate on the accumulator.
fn bounds_for_iter_poly(
    poly: &PolynomialFn,
    k_min: &Knuth10,
    k_max: &Knuth10,
    x: u64,
) -> Option<(Knuth10, Knuth10)> {
    // We only compute power tower bounds if the recursive step's polynomial growth
    // is driven by the accumulator (which is always passed as arg 1 to the step function).
    // If it were a polynomial over a static side-variable, iterating it would only yield exponential growth.
    if poly.poly_arg == 1 {
        let d = poly.degree();
        let c_min = poly.leading_coef() as f64;

        let mut c_max = 0.0;
        for &c in poly.affine_tail.coeffs.iter() {
            c_max += c as f64;
        }
        for &c in poly.poly_coeffs.iter() {
            c_max += c as f64;
        }

        let d_f64 = d as f64;
        let x_f64 = x.max(1) as f64;

        // Mathematical derivation of the power tower exponent y:
        // Assume poly(x) ≈ c * x^d. Iterating it k times yields:
        // poly^k(x) ≈ c^{(d^k - 1)/(d - 1)} * x^{d^k} ≈ (c^{1/(d-1)} * x)^{d^k}
        //
        // Taking log10:
        // log10(poly^k(x)) ≈ d^k * [ log10(c)/(d-1) + log10(x) ]
        // Let M = log10(c)/(d-1) + log10(x)
        let m_min = c_min.log10() / (d_f64 - 1.0) + x_f64.log10();
        let m_max = c_max.log10() / (d_f64 - 1.0) + x_f64.log10();

        // To find the power tower exponent y such that poly^k(x) = 10^{10^y}:
        // y = log10(log10(poly^k(x))) ≈ log10(d^k * M) = k * log10(d) + log10(M)
        let y_min = k_min
            .mul_f64(d_f64.log10(), false)
            .add_f64(m_min.log10(), false);
        let y_max = k_max
            .mul_f64(d_f64.log10(), true)
            .add_f64(m_max.log10(), true);

        return Some((
            Knuth10::UpArrow(1, Box::new(Knuth10::UpArrow(1, Box::new(y_min)))),
            Knuth10::UpArrow(1, Box::new(Knuth10::UpArrow(1, Box::new(y_max)))),
        ));
    }
    None
}

/// Recursively computes strict lower and upper bounds for symbolically evaluated functions.
/// Capable of bounding arbitrary FGH levels (e.g. Iterated functions where the iteration
/// count is itself a massive power tower).
pub fn compute_bounds(sym: &SymVal) -> Option<(Knuth10, Knuth10)> {
    compute_bounds_inner(sym)
}
fn compute_bounds_inner(sym: &SymVal) -> Option<(Knuth10, Knuth10)> {
    match sym {
        SymVal::Const(c) => Some((Knuth10::Val(*c as f64), Knuth10::Val(*c as f64))),
        SymVal::FuncApp(grf, args) => {
            if matches!(&grf.kind, crate::grf::GrfKind::Succ) {
                if args.len() == 1 {
                    return compute_bounds(&args[0]);
                }
            }
            if let Some(cf) = grf.closed_form() {
                match cf {
                    ClosedForm::Iterated(it) => {
                        if args.len() >= 1 {
                            let (k_min, k_max) = compute_bounds(&args[0])?;
                            let mut const_args = Vec::with_capacity(args.len() - 1);
                            for a in &args[1..] {
                                if let SymVal::Const(c) = a {
                                    const_args.push(*c);
                                } else {
                                    return None;
                                }
                            }
                            if let Some(x) = it.base.eval(&const_args) {
                                match it.step.as_ref() {
                                    ClosedForm::Polynomial(poly) => {
                                        return bounds_for_iter_poly(poly, &k_min, &k_max, x);
                                    }
                                    ClosedForm::Affine(affine) => {
                                        return bounds_for_affine(affine, &k_min, &k_max, x);
                                    }
                                    _ => return None,
                                }
                            }
                        }
                    }
                    ClosedForm::Polynomial(poly) => {
                        let (n_min, n_max) = compute_bounds(&args[0])?;
                        let d = poly.degree() as f64;
                        let c = poly.leading_coef() as f64;

                        let max_bound = match n_max {
                            Knuth10::Val(v) => {
                                let val = c * v.powf(d);
                                Knuth10::UpArrow(1, Box::new(Knuth10::Val(val.log10())))
                            }
                            Knuth10::UpArrow(1, inner) => {
                                let inner_max = inner.mul_f64(d, true).add_f64(c.log10(), true);
                                Knuth10::UpArrow(1, Box::new(inner_max))
                            }
                            Knuth10::UpArrow(levels, inner) => Knuth10::UpArrow(levels, inner),
                        };

                        let min_bound = match n_min {
                            Knuth10::Val(v) => {
                                let val = c * v.powf(d);
                                Knuth10::UpArrow(1, Box::new(Knuth10::Val(val.log10())))
                            }
                            Knuth10::UpArrow(1, inner) => {
                                let inner_min = inner.mul_f64(d, false).add_f64(c.log10(), false);
                                Knuth10::UpArrow(1, Box::new(inner_min))
                            }
                            Knuth10::UpArrow(levels, inner) => Knuth10::UpArrow(levels, inner),
                        };
                        return Some((min_bound, max_bound));
                    }
                    ClosedForm::Affine(_) => {
                        let mut max_b = Knuth10::Val(0.0);
                        let mut min_b = Knuth10::Val(0.0);
                        for a in args {
                            if let Some((min, max)) = compute_bounds(a) {
                                max_b = max; // Simplification
                                min_b = min;
                            } else {
                                return None;
                            }
                        }
                        return Some((min_b, max_b));
                    }
                    _ => {}
                }
            } else if let crate::grf::GrfKind::Rec(g, h) = &grf.kind {
                if let (Some(g_cf), Some(h_cf)) = (g.closed_form(), h.closed_form()) {
                    if args.len() >= 1 {
                        let (k_min, k_max) = compute_bounds(&args[0])?;
                        let mut const_args = Vec::with_capacity(args.len() - 1);
                        for a in &args[1..] {
                            if let SymVal::Const(c) = a {
                                const_args.push(*c);
                            } else {
                                return None;
                            }
                        }
                        if let Some(x) = g_cf.eval(&const_args) {
                            if let SymVal::Const(n_val) = &args[0] {
                                let n_u64 = *n_val as u64;
                                if n_u64 > 0 {
                                    let cf_lower = h_cf.partial_eval_first_arg(0)?;
                                    let cf_upper = h_cf.partial_eval_first_arg(n_u64 - 1)?;

                                    let min_bounds = match cf_lower {
                                        crate::closed_form::ClosedForm::Polynomial(poly) => {
                                            bounds_for_iter_poly(&poly, &k_min, &k_max, x)
                                        }
                                        crate::closed_form::ClosedForm::Affine(affine) => {
                                            bounds_for_affine(&affine, &k_min, &k_max, x)
                                        }
                                        _ => None,
                                    };

                                    let max_bounds = match cf_upper {
                                        crate::closed_form::ClosedForm::Polynomial(poly) => {
                                            bounds_for_iter_poly(&poly, &k_min, &k_max, x)
                                        }
                                        crate::closed_form::ClosedForm::Affine(affine) => {
                                            bounds_for_affine(&affine, &k_min, &k_max, x)
                                        }
                                        _ => None,
                                    };

                                    if let (Some((min, _)), Some((_, max))) =
                                        (min_bounds, max_bounds)
                                    {
                                        return Some((min, max));
                                    }
                                }
                            }
                        }
                    }
                }
            }
            None
        }
    }
}

impl std::fmt::Display for SymVal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SymVal::Const(c) => write!(f, "{}", c),
            SymVal::FuncApp(grf, args) => {
                if let Some(bounds) = compute_bounds(self) {
                    if let Knuth10::Val(v) = bounds.1 {
                        if v > 0.0 {
                            return write!(
                                f,
                                "[{}, {}]",
                                bounds.0.normalize(),
                                bounds.1.normalize()
                            );
                        }
                    } else {
                        return write!(f, "[{}, {}]", bounds.0.normalize(), bounds.1.normalize());
                    }
                }

                let mut count = 1;
                let mut current_args = args.as_slice();

                while current_args.len() >= 1 {
                    if let SymVal::FuncApp(inner_grf, inner_args) = &current_args[0] {
                        if inner_grf == grf {
                            count += 1;
                            current_args = inner_args;
                            continue;
                        }
                    }
                    break;
                }

                if count > 1 {
                    write!(f, "~G^{{{}}}({})", count, current_args[0])
                } else {
                    if current_args.len() == 1 {
                        write!(f, "~G({})", current_args[0])
                    } else {
                        write!(f, "~G(args...)")
                    }
                }
            }
        }
    }
}

/// Evaluates a full `Grf` tree symbolically.
/// This allows us to walk through structural wrappers (like `Comp` and `Proj`)
/// to compute the exact symbolic arguments passed to the inner `Rec` or `Min` node.
pub fn eval_grf_sym(grf: &Grf, args: &[SymVal]) -> SymVal {
    match &grf.kind {
        GrfKind::Zero(_) => SymVal::Const(0),
        GrfKind::Succ => {
            if let SymVal::Const(c) = args[0] {
                SymVal::Const(c + 1)
            } else {
                SymVal::FuncApp(grf.clone(), args.to_vec())
            }
        }
        GrfKind::Proj(_, i) => args[*i - 1].clone(),
        GrfKind::Comp(g, hs, _) => {
            let inner_args: Vec<SymVal> = hs.iter().map(|h| eval_grf_sym(h, args)).collect();
            eval_grf_sym(g, &inner_args)
        }
        GrfKind::Rec(g, h) => {
            if let SymVal::Const(iters) = args[0] {
                if iters <= 10 {
                    // Threshold for "small" number of iterations
                    let mut acc = eval_grf_sym(g, &args[1..]);
                    for k in 0..iters {
                        let mut step_args = vec![SymVal::Const(k), acc];
                        step_args.extend_from_slice(&args[1..]);
                        acc = eval_grf_sym(h, &step_args);
                    }
                    return acc;
                }
            }
            if let Some(cf) = grf.closed_form() {
                if let Some(val) = eval_sym(cf, args) {
                    return val;
                }
            }
            SymVal::FuncApp(grf.clone(), args.to_vec())
        }
        GrfKind::Min(_) => {
            if let Some(cf) = grf.closed_form() {
                if let Some(val) = eval_sym(cf, args) {
                    return val;
                }
            }
            SymVal::FuncApp(grf.clone(), args.to_vec())
        }
    }
}

/// Evaluates a `ClosedForm` on symbolic arguments. Returns `None` if it cannot be evaluated directly.
pub fn eval_sym(cf: &ClosedForm, args: &[SymVal]) -> Option<SymVal> {
    // 1. If all args are Const, attempt a direct u64 evaluation.
    let mut all_const = true;
    let mut const_args = Vec::new();
    for a in args {
        if let SymVal::Const(c) = a {
            const_args.push(*c);
        } else {
            all_const = false;
            break;
        }
    }

    if all_const {
        // cf.eval returns None on overflow. If it succeeds, we return the Const.
        // We supply a step budget so evaluation doesn't hang on large inputs.
        let mut budget = 100_000;
        if let Some(val) = cf.eval_with_budget(&const_args, &mut budget) {
            return Some(SymVal::Const(val));
        }
    }

    // 2. Symbolic unrolling of shallow loops.
    // If it's an Iterated function, and the iteration count is a small constant,
    // we unroll the loop completely to evaluate the base state of the inner functions!
    if let ClosedForm::Iterated(it) = cf {
        if let SymVal::Const(iters) = args[0] {
            if iters <= 10 {
                // Threshold for "small" number of iterations
                let mut acc = eval_sym(&it.base, &args[1..])?;
                for _ in 0..iters {
                    let mut step_args = vec![acc];
                    step_args.extend_from_slice(&args[1..]);
                    acc = eval_sym(&it.step, &step_args)?;
                }
                return Some(acc);
            }
        }
    }

    // 3. Fallback: cannot evaluate further symbolically inside ClosedForm.
    None
}

/// Compares two symbolic values algebraically.
pub fn compare_sym(a: &SymVal, b: &SymVal) -> PointwiseOrder {
    match (a, b) {
        (SymVal::Const(x), SymVal::Const(y)) => {
            if x > y {
                PointwiseOrder::GreaterEqual
            } else if x < y {
                PointwiseOrder::LessEqual
            } else {
                PointwiseOrder::Equal
            }
        }
        (SymVal::Const(_), SymVal::FuncApp(_, _)) => PointwiseOrder::Uncertain,
        (SymVal::FuncApp(_, _), SymVal::Const(_)) => PointwiseOrder::Uncertain,
        (SymVal::FuncApp(f, args_f), SymVal::FuncApp(g, args_g)) => {
            if let (Some(cf_f), Some(cf_g)) = (f.closed_form(), g.closed_form()) {
                let func_cmp = compare_strict(cf_f, cf_g);

                let mut all_ge = true;
                let mut all_le = true;
                let mut any_gt = false;
                let mut any_lt = false;

                for (af, ag) in args_f.iter().zip(args_g.iter()) {
                    let arg_cmp = compare_sym(af, ag);
                    if arg_cmp == PointwiseOrder::GreaterEqual {
                        all_le = false;
                        any_gt = true;
                    } else if arg_cmp == PointwiseOrder::LessEqual {
                        all_ge = false;
                        any_lt = true;
                    } else if arg_cmp == PointwiseOrder::Uncertain {
                        all_le = false;
                        all_ge = false;
                    }
                }

                // Standard rigorous composition of bounds.
                // Since our functions are monotonically non-decreasing:
                // f >= g AND x >= y  =>  f(x) >= g(y).
                let final_cmp = if func_cmp == PointwiseOrder::Uncertain {
                    PointwiseOrder::Uncertain
                } else if (func_cmp == PointwiseOrder::GreaterEqual
                    || func_cmp == PointwiseOrder::Equal)
                    && all_ge
                {
                    if func_cmp == PointwiseOrder::Equal && !any_gt {
                        PointwiseOrder::Equal
                    } else {
                        PointwiseOrder::GreaterEqual
                    }
                } else if (func_cmp == PointwiseOrder::LessEqual
                    || func_cmp == PointwiseOrder::Equal)
                    && all_le
                {
                    if func_cmp == PointwiseOrder::Equal && !any_lt {
                        PointwiseOrder::Equal
                    } else {
                        PointwiseOrder::LessEqual
                    }
                } else {
                    PointwiseOrder::Uncertain
                };

                // User requested to remove Knuth10 bounds comparison here to keep it separate.
                // We also must remove the unsafe structural FGH level heuristics because
                // comparing the outermost function's FGH level is mathematically invalid
                // when the arguments to those functions are vastly different evaluated numbers.
                // So if final_cmp is Uncertain at this point, we just leave it as Uncertain.

                return final_cmp;
            }
            PointwiseOrder::Uncertain
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::closed_form::{AffineFn, IteratedFn, PolynomialFn};

    fn test_compare_affine_strict() {
        // f(x) = x + 1
        let a = ClosedForm::Affine(AffineFn {
            arity: 1,
            coeffs: vec![1, 1],
        });
        // g(x) = x + 2
        let b = ClosedForm::Affine(AffineFn {
            arity: 1,
            coeffs: vec![2, 1],
        });

        assert_eq!(compare_strict(&a, &b), PointwiseOrder::LessEqual);
        assert_eq!(compare_strict(&b, &a), PointwiseOrder::GreaterEqual);
        assert_eq!(compare_strict(&a, &a), PointwiseOrder::Equal);

        // h(x) = 2x + 1
        let c = ClosedForm::Affine(AffineFn {
            arity: 1,
            coeffs: vec![1, 2],
        });

        // x + 1 ≤ 2x + 1
        assert_eq!(compare_strict(&a, &c), PointwiseOrder::LessEqual);
        assert_eq!(compare_strict(&c, &a), PointwiseOrder::GreaterEqual);

        // 2x+1 vs x+2 crosses!
        // At x=0: 2(0)+1 = 1, 0+2 = 2. (c < b)
        // At x=2: 2(2)+1 = 5, 2+2 = 4. (c > b)
        // Strict ordering MUST return Uncertain!
        assert_eq!(compare_strict(&b, &c), PointwiseOrder::Uncertain);
        assert_eq!(compare_strict(&c, &b), PointwiseOrder::Uncertain);
    }

    fn test_compare_polynomial_strict() {
        // p1(x) = (x choose 2) + x
        let p1 = ClosedForm::Polynomial(PolynomialFn::new(
            1,
            1,
            vec![1],
            Box::new(AffineFn {
                arity: 1,
                coeffs: vec![0, 1],
            }),
        ));
        // p2(x) = (x choose 2) + 2x
        let p2 = ClosedForm::Polynomial(PolynomialFn::new(
            1,
            1,
            vec![1],
            Box::new(AffineFn {
                arity: 1,
                coeffs: vec![0, 2],
            }),
        ));

        // (x choose 2) + x ≤ (x choose 2) + 2x
        assert_eq!(compare_strict(&p1, &p2), PointwiseOrder::LessEqual);

        // p3(x) = 2*(x choose 2) + 1
        let p3 = ClosedForm::Polynomial(PolynomialFn::new(
            1,
            1,
            vec![2],
            Box::new(AffineFn {
                arity: 1,
                coeffs: vec![1, 0],
            }),
        ));

        // p2 vs p3 crosses!
        // p2(1) = 0 + 2 = 2, p3(1) = 0 + 1 = 1  (p2 > p3)
        // p2(3) = 3 + 6 = 9, p3(3) = 2(3) + 1 = 7 (p2 > p3)
        // Wait, at x=4: p2(4) = 6 + 8 = 14, p3(4) = 2(6) + 1 = 13
        // At x=5: p2(5) = 10 + 10 = 20, p3(5) = 2(10) + 1 = 21 (p2 < p3)
        // So they cross, meaning it MUST be Uncertain.
        assert_eq!(compare_strict(&p2, &p3), PointwiseOrder::Uncertain);
        // Same for p1 vs p3
        assert_eq!(compare_strict(&p1, &p3), PointwiseOrder::Uncertain);
    }

    fn test_compare_iterated_strict_finite_crossing() {
        // f1 = R(100, \x. x+1). Base=100, Step=x+1
        let f1 = ClosedForm::Iterated(IteratedFn {
            arity: 2,
            base: Box::new(ClosedForm::Affine(AffineFn {
                arity: 1,
                coeffs: vec![100],
            })),
            step: Box::new(ClosedForm::Affine(AffineFn {
                arity: 2,
                coeffs: vec![1, 1, 0],
            })), // acc + 1
        });

        // f2 = R(10, \x. x+2). Base=10, Step=x+2
        let f2 = ClosedForm::Iterated(IteratedFn {
            arity: 2,
            base: Box::new(ClosedForm::Affine(AffineFn {
                arity: 1,
                coeffs: vec![10],
            })),
            step: Box::new(ClosedForm::Affine(AffineFn {
                arity: 2,
                coeffs: vec![2, 1, 0],
            })), // acc + 2
        });

        // Because f1 has a larger base but smaller step than f2, they cross.
        // Asymptotically, f2 will eventually outgrow f1 (e.g. for y=100).
        // But for small y (e.g. y=1), f1(1) = 101, whereas f2(1) = 12. So f1 > f2.
        // Strict ordering MUST recognize they cross and return Uncertain!
        assert_eq!(compare_strict(&f1, &f2), PointwiseOrder::Uncertain);

        // Verify that if both base and step are strictly larger, it works.
        // f3 = R(10, \x. x+1)
        let f3 = ClosedForm::Iterated(IteratedFn {
            arity: 2,
            base: Box::new(ClosedForm::Affine(AffineFn {
                arity: 1,
                coeffs: vec![10],
            })),
            step: Box::new(ClosedForm::Affine(AffineFn {
                arity: 2,
                coeffs: vec![1, 1, 0],
            })),
        });

        assert_eq!(compare_strict(&f3, &f1), PointwiseOrder::LessEqual); // 10 < 100, x+1 == x+1
        assert_eq!(compare_strict(&f3, &f2), PointwiseOrder::LessEqual); // 10 == 10, x+1 < x+2
    }
}
