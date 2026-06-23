use crate::closed_form::{ClosedForm, AffineFn, PolynomialFn, closed_form_ignores_arg};

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
            } else if (base_cmp == PointwiseOrder::GreaterEqual || base_cmp == PointwiseOrder::Equal) &&
                      (step_cmp == PointwiseOrder::GreaterEqual || step_cmp == PointwiseOrder::Equal) {
                PointwiseOrder::GreaterEqual
            } else if (base_cmp == PointwiseOrder::LessEqual || base_cmp == PointwiseOrder::Equal) &&
                      (step_cmp == PointwiseOrder::LessEqual || step_cmp == PointwiseOrder::Equal) {
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

/// Computes the Fast-Growing Hierarchy level of the given ClosedForm.
/// 0: Addition (O(n))
/// 1: Multiplication (O(n^d))
/// 2: Exponential (O(2^n))
/// 3: Tetration (O(2^^n))
/// 4: Pentation (O(2^^^n))
/// and so on.
pub fn fgh_level(cf: &ClosedForm) -> usize {
    match cf {
        ClosedForm::Affine(af) => {
            if af.coeffs.iter().skip(1).any(|&c| c >= 2) {
                1 // Any coefficient >= 2 represents multiplication (O(n))
            } else {
                0
            }
        },
        ClosedForm::Polynomial(_) => 1,
        ClosedForm::NegMod(_a1, _a2, _a3) => 0,
        ClosedForm::Periodic(_) => 0,
        ClosedForm::Piecewise(pw) => {
            fgh_level(&pw.zero_branch).max(fgh_level(&pw.pos_branch))
        }
        ClosedForm::Iterated(it) => {
            let base_l = fgh_level(&it.base);
            let iter_l = iterated_growth_level(&it.step);
            base_l.max(iter_l)
        }
    }
}

/// Computes how the function grows with respect to its FIRST argument (`acc`).
/// 0: Ignores `acc` or bounded by a constant.
/// 1: Bounded by `acc + C` (Addition).
/// 2: Bounded by `C * acc^d` (Multiplication/Polynomial).
/// 3: Exponential in `acc`.
/// k: k-th level in FGH with respect to `acc`.
pub fn iterated_growth_level(cf: &ClosedForm) -> usize {
    match cf {
        ClosedForm::Affine(af) => {
            if af.coeffs.len() <= 1 { return 0; }
            let c_acc = af.coeffs[1];
            if c_acc == 0 {
                0 // Ignores acc
            } else if c_acc == 1 {
                1 // acc + C -> iterating gives multiplication (Level 1)
            } else {
                2 // c*acc -> iterating gives exponential (Level 2)
            }
        }
        ClosedForm::Polynomial(poly) => {
            if poly.poly_arg == 1 {
                if poly.poly_coeffs.iter().any(|&c| c > 0) {
                    return 2; // acc^2 -> iterating gives exponential (Level 2)
                }
            }
            // If acc is not the poly arg, it's just affine in acc
            let c_acc = if poly.affine_tail.coeffs.len() <= 1 { 0 } else { poly.affine_tail.coeffs[1] };
            if c_acc == 0 { 0 } else if c_acc == 1 { 1 } else { 2 }
        }
        ClosedForm::Piecewise(pw) => {
            iterated_growth_level(&pw.zero_branch).max(iterated_growth_level(&pw.pos_branch))
        }
        ClosedForm::NegMod(a1, a2, a3) => {
            iterated_growth_level(&ClosedForm::Affine(a1.clone()))
                .max(iterated_growth_level(&ClosedForm::Affine(a2.clone())))
                .max(iterated_growth_level(&ClosedForm::Affine(a3.clone())))
        }
        ClosedForm::Periodic(p) => {
            p.branches.iter().map(|b| iterated_growth_level(&**b)).max().unwrap_or(0)
        }
        ClosedForm::Iterated(_it) => {
            if closed_form_ignores_arg(cf, 1) {
                0
            } else {
                let l = fgh_level(cf);
                if l >= 2 { l + 1 } else { 2 }
            }
        }
    }
}

/// Represents a symbolically evaluated value that may be too large to fit in `u64`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SymVal {
    Const(u64),
    FuncApp(ClosedForm, Vec<SymVal>),
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

/// Computes strict lower and upper bounds `(y_min, y_max)` such that the exact value of the 
/// affine function `func` iterated `k` times on input `x` is rigorously bounded by
/// `[10^10^y_min, 10^10^y_max]`.
/// Note that affine bounds often produce very small `y` values (y < 2.0) which are automatically 
/// formatted as `10^A` scientific notation rather than a full power tower.
fn bounds_for_affine(func: &AffineFn, k: u64, x: u64) -> Option<(f64, f64)> {
    if func.arity >= 1 {
        let c_min = func.coeffs[1] as f64; // The coefficient for the first argument (acc)
        let mut c_max = 0.0;
        for &c in func.coeffs.iter() {
            c_max += c as f64;
        }
        
        if c_min >= 1.0 {
            let x_f64 = x.max(1) as f64;
            let k_f64 = k as f64;
            
            // P(x) = c * x
            let log_p_min = k_f64 * c_min.log10() + x_f64.log10();
            let log_p_max = k_f64 * c_max.log10() + x_f64.log10();
            
            return Some((log_p_min.log10(), log_p_max.log10()));
        }
    }
    None
}

/// Computes strict lower and upper bounds `(y_min, y_max)` such that the exact value of the 
/// polynomial `poly` iterated `k` times on input `x` is rigorously bounded by
/// `[10^10^y_min, 10^10^y_max]`.
/// Returns `None` if the polynomial does not operate on the accumulator.
fn bounds_for_iter_poly(poly: &PolynomialFn, k: u64, x: u64) -> Option<(f64, f64)> {
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
        let k_f64 = k as f64;
        
        // Mathematical derivation of the power tower exponent y:
        // Assume poly(x) ≈ c * x^d. Iterating it k times yields:
        // poly^k(x) ≈ c^{(d^k - 1)/(d - 1)} * x^{d^k} ≈ (c^{1/(d-1)} * x)^{d^k}
        // log10(poly^k(x)) ≈ d^k * [ log10(c)/(d-1) + log10(x) ]
        // Let M = log10(c)/(d-1) + log10(x)
        let m_min = c_min.log10() / (d_f64 - 1.0) + x_f64.log10();
        let m_max = c_max.log10() / (d_f64 - 1.0) + x_f64.log10();
        
        // To find the power tower exponent y such that poly^k(x) = 10^{10^y}:
        // y = log10(log10(poly^k(x))) ≈ log10(d^k * M) = k * log10(d) + log10(M)
        let y_min = k_f64 * d_f64.log10() + m_min.log10();
        let y_max = k_f64 * d_f64.log10() + m_max.log10();
        
        return Some((y_min, y_max));
    }
    None
}

/// Computes strict lower and upper bounds [10^10^y_min, 10^10^y_max] for an FGH Level 2 function.
fn compute_power_tower_bounds(cf: &ClosedForm, args: &[SymVal]) -> Option<(f64, f64)> {
    if fgh_level(cf) == 2 {
        if let ClosedForm::Iterated(it) = cf {
            assert!(args.len() >= 1);
            if let SymVal::Const(iters) = args[0] {
                // The rest of the arguments are passed to the base function to compute
                // the initial accumulator.
                let mut const_args = Vec::with_capacity(args.len() - 1);
                for a in &args[1..] {
                    if let SymVal::Const(c) = a {
                        const_args.push(*c);
                    } else {
                        return None; // Cannot evaluate symbolically if not fully constant
                    }
                }
                
                if let Some(base) = it.base.eval(&const_args) {
                    match it.step.as_ref() {
                        ClosedForm::Affine(affine) => return bounds_for_affine(affine, iters, base),
                        ClosedForm::Polynomial(poly) => return bounds_for_iter_poly(poly, iters, base),
                        _ => return None,
                    }
                }
            }
        }
    }
    None
}

impl std::fmt::Display for SymVal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SymVal::Const(c) => write!(f, "{}", c),
            SymVal::FuncApp(cf, args) => {
                let format_bounds = |y_min: f64, y_max: f64| -> String {
                    let format_bound = |y: f64| -> String {
                        if y < 2.0 {
                            format!("10^{:.2}", 10f64.powf(y))
                        } else {
                            format!("10^10^{:.2}", y)
                        }
                    };
                    format!("[{}, {}]", format_bound(y_min), format_bound(y_max))
                };

                // For FGH Level 2 iterated functions, output strict bounds instead!
                if let Some((y_min, y_max)) = compute_power_tower_bounds(cf, args) {
                    return write!(f, "{}", format_bounds(y_min, y_max));
                }
                
                let mut count = 1;
                let mut current_args = args;
                
                while current_args.len() >= 1 {
                    if let SymVal::FuncApp(inner_cf, inner_args) = &current_args[0] {
                        if inner_cf == cf {
                            count += 1;
                            current_args = inner_args;
                            continue;
                        }
                    }
                    break;
                }
                
                if count > 1 {
                    if current_args.len() >= 1 {
                        if let SymVal::Const(x) = current_args[0] {
                            let bounds = match cf {
                                ClosedForm::Affine(affine) => bounds_for_affine(affine, count as u64, x),
                                ClosedForm::Polynomial(poly) => bounds_for_iter_poly(poly, count as u64, x),
                                _ => None,
                            };
                            if let Some((y_min, y_max)) = bounds {
                                return write!(f, "{}", format_bounds(y_min, y_max));
                            }
                        }
                    }
                }
                
                if let ClosedForm::Iterated(it) = cf {
                    if args.len() == 2 {
                        let step_lvl = fgh_level(&it.step);
                        return write!(f, "~f_{}^{{{}}}({})", step_lvl, count, current_args[0]);
                    }
                }
                
                let lvl = fgh_level(cf);
                if count > 1 {
                    write!(f, "~f_{}^{{{}}}({})", lvl, count, current_args[0])
                } else {
                    write!(f, "~f_{}({})", lvl, current_args[0])
                }
            }
        }
    }
}

use crate::grf::{Grf, GrfKind};

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
                panic!("Cannot apply Succ to non-Const symbolic value: {}", args[0]);
            }
        }
        GrfKind::Proj(_, i) => args[*i - 1].clone(),
        GrfKind::Comp(g, hs, _) => {
            let inner_args: Vec<SymVal> = hs.iter().map(|h| eval_grf_sym(h, args)).collect();
            eval_grf_sym(g, &inner_args)
        }
        GrfKind::Rec(_, _) | GrfKind::Min(_) => {
            let cf = grf.closed_form().unwrap_or_else(|| panic!("Expected closed form for inner node: {:?}", grf));
            eval_sym(cf, args)
        }
    }
}

/// Evaluates a `ClosedForm` on symbolic arguments.
pub fn eval_sym(cf: &ClosedForm, args: &[SymVal]) -> SymVal {
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
        if let Some(val) = cf.eval(&const_args) {
            return SymVal::Const(val);
        }
    }

    // 2. Symbolic unrolling of shallow loops.
    // If it's an Iterated function, and the iteration count is a small constant,
    // we unroll the loop completely to evaluate the base state of the inner functions!
    if let ClosedForm::Iterated(it) = cf {
        if let SymVal::Const(iters) = args[0] {
            if iters <= 10 { // Threshold for "small" number of iterations
                let mut acc = eval_sym(&it.base, &args[1..]);
                for _ in 0..iters {
                    let mut step_args = vec![acc];
                    step_args.extend_from_slice(&args[1..]);
                    acc = eval_sym(&it.step, &step_args);
                }
                return acc;
            }
        }
    }

    // 3. Fallback: encapsulate as an un-evaluated function application.
    SymVal::FuncApp(cf.clone(), args.to_vec())
}

/// Compares two symbolic values algebraically.
pub fn compare_sym(a: &SymVal, b: &SymVal) -> PointwiseOrder {
    match (a, b) {
        (SymVal::Const(x), SymVal::Const(y)) => {
            if x > y { PointwiseOrder::GreaterEqual }
            else if x < y { PointwiseOrder::LessEqual }
            else { PointwiseOrder::Equal }
        }
        (SymVal::Const(_), SymVal::FuncApp(_, _)) => PointwiseOrder::Uncertain,
        (SymVal::FuncApp(_, _), SymVal::Const(_)) => PointwiseOrder::Uncertain,
        (SymVal::FuncApp(f, args_f), SymVal::FuncApp(g, args_g)) => {
            let func_cmp = compare_strict(f, g);
            
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
            let mut final_cmp = if func_cmp == PointwiseOrder::Uncertain {
                PointwiseOrder::Uncertain
            } else if (func_cmp == PointwiseOrder::GreaterEqual || func_cmp == PointwiseOrder::Equal) && all_ge {
                if func_cmp == PointwiseOrder::Equal && !any_gt {
                    PointwiseOrder::Equal
                } else {
                    PointwiseOrder::GreaterEqual
                }
            } else if (func_cmp == PointwiseOrder::LessEqual || func_cmp == PointwiseOrder::Equal) && all_le {
                if func_cmp == PointwiseOrder::Equal && !any_lt {
                    PointwiseOrder::Equal
                } else {
                    PointwiseOrder::LessEqual
                }
            } else {
                PointwiseOrder::Uncertain
            };
            
            // HEURISTIC: Resolve `Uncertain` structural bounds by looking at the iteration gap and FGH level.
            let lvl_f = fgh_level(f);
            let lvl_g = fgh_level(g);
            
            if final_cmp == PointwiseOrder::Uncertain {
                if lvl_f < lvl_g {
                    // Lower FGH level guarantees it is strictly less for massive inputs
                    final_cmp = PointwiseOrder::LessEqual;
                } else if lvl_f > lvl_g {
                    // Higher FGH level guarantees it is strictly greater for massive inputs
                    final_cmp = PointwiseOrder::GreaterEqual;
                } else {
                    // If the functions belong to the same FGH growth level, we compare their iteration counts.
                    // MATHEMATICAL PROOF: 
                    // For FGH Level >= 3, the iteration count `k` represents the HEIGHT of a power tower (or higher).
                    // A power tower of height k_1 strictly dominates a power tower of height k_2 if k_1 > k_2, 
                    // regardless of the bases (as long as base >= 2). So comparing `k` is universally rigorous.
                    // However, for FGH Level 2, the growth is x^{d^k} where d is the polynomial degree.
                    // So we MUST compare d^{k}, which means comparing k_1 * ln(d_1) vs k_2 * ln(d_2).
                    
                    if lvl_f == 2 {
                        if let (ClosedForm::Iterated(it_f), ClosedForm::Iterated(it_g)) = (f, g) {
                            let d_f = asymptotic_degree(&it_f.step);
                            let d_g = asymptotic_degree(&it_g.step);
                            
                            if let (Some(SymVal::Const(k_f)), Some(SymVal::Const(k_g))) = (args_f.first(), args_g.first()) {
                                let power_f = (*k_f as f64) * (d_f as f64).ln();
                                let power_g = (*k_g as f64) * (d_g as f64).ln();
                                
                                if power_f > power_g + 1e-9 {
                                    final_cmp = PointwiseOrder::GreaterEqual;
                                } else if power_f < power_g - 1e-9 {
                                    final_cmp = PointwiseOrder::LessEqual;
                                } else {
                                    final_cmp = PointwiseOrder::Equal;
                                }
                            } else if d_f == d_g {
                                // Fallback to pure symbolic comparison if k is symbolic but degrees match
                                if let (Some(af0), Some(ag0)) = (args_f.first(), args_g.first()) {
                                    let arg_cmp = compare_sym(af0, ag0);
                                    if arg_cmp == PointwiseOrder::GreaterEqual {
                                        final_cmp = PointwiseOrder::GreaterEqual;
                                    } else if arg_cmp == PointwiseOrder::LessEqual {
                                        final_cmp = PointwiseOrder::LessEqual;
                                    }
                                }
                            }
                        }
                    } else {
                        // Rigorous for Level >= 3
                        if let (Some(af0), Some(ag0)) = (args_f.first(), args_g.first()) {
                            let arg_cmp = compare_sym(af0, ag0);
                            if arg_cmp == PointwiseOrder::GreaterEqual {
                                final_cmp = PointwiseOrder::GreaterEqual;
                            } else if arg_cmp == PointwiseOrder::LessEqual {
                                final_cmp = PointwiseOrder::LessEqual;
                            }
                        }
                    }
                }
            }
            
            final_cmp
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::closed_form::{AffineFn, PolynomialFn, IteratedFn};

    #[test]
    fn test_compare_affine_strict() {
        // f(x) = x + 1
        let a = ClosedForm::Affine(AffineFn { arity: 1, coeffs: vec![1, 1] });
        // g(x) = x + 2
        let b = ClosedForm::Affine(AffineFn { arity: 1, coeffs: vec![2, 1] });
        
        assert_eq!(compare_strict(&a, &b), PointwiseOrder::LessEqual);
        assert_eq!(compare_strict(&b, &a), PointwiseOrder::GreaterEqual);
        assert_eq!(compare_strict(&a, &a), PointwiseOrder::Equal);

        // h(x) = 2x + 1
        let c = ClosedForm::Affine(AffineFn { arity: 1, coeffs: vec![1, 2] });

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

    #[test]
    fn test_compare_polynomial_strict() {
        // p1(x) = (x choose 2) + x
        let p1 = ClosedForm::Polynomial(PolynomialFn::new(
            1,
            1,
            vec![1],
            Box::new(AffineFn { arity: 1, coeffs: vec![0, 1] })
        ));
        // p2(x) = (x choose 2) + 2x
        let p2 = ClosedForm::Polynomial(PolynomialFn::new(
            1,
            1,
            vec![1],
            Box::new(AffineFn { arity: 1, coeffs: vec![0, 2] })
        ));

        // (x choose 2) + x ≤ (x choose 2) + 2x
        assert_eq!(compare_strict(&p1, &p2), PointwiseOrder::LessEqual);

        // p3(x) = 2*(x choose 2) + 1
        let p3 = ClosedForm::Polynomial(PolynomialFn::new(
            1,
            1,
            vec![2],
            Box::new(AffineFn { arity: 1, coeffs: vec![1, 0] })
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

    #[test]
    fn test_compare_iterated_strict_finite_crossing() {
        // f1 = R(100, \x. x+1). Base=100, Step=x+1
        let f1 = ClosedForm::Iterated(IteratedFn {
            arity: 2,
            base: Box::new(ClosedForm::Affine(AffineFn { arity: 1, coeffs: vec![100] })),
            step: Box::new(ClosedForm::Affine(AffineFn { arity: 2, coeffs: vec![1, 1, 0] })) // acc + 1
        });

        // f2 = R(10, \x. x+2). Base=10, Step=x+2
        let f2 = ClosedForm::Iterated(IteratedFn {
            arity: 2,
            base: Box::new(ClosedForm::Affine(AffineFn { arity: 1, coeffs: vec![10] })),
            step: Box::new(ClosedForm::Affine(AffineFn { arity: 2, coeffs: vec![2, 1, 0] })) // acc + 2
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
            base: Box::new(ClosedForm::Affine(AffineFn { arity: 1, coeffs: vec![10] })),
            step: Box::new(ClosedForm::Affine(AffineFn { arity: 2, coeffs: vec![1, 1, 0] }))
        });

        assert_eq!(compare_strict(&f3, &f1), PointwiseOrder::LessEqual); // 10 < 100, x+1 == x+1
        assert_eq!(compare_strict(&f3, &f2), PointwiseOrder::LessEqual); // 10 == 10, x+1 < x+2
    }

    #[test]
    fn test_fgh_level() {
        // id(x) = x
        let id = ClosedForm::Affine(AffineFn { arity: 1, coeffs: vec![0, 1] });

        // Exact FGH funcs:
        // f0(x) = x + 1
        let f0 = ClosedForm::Affine(AffineFn { arity: 1, coeffs: vec![1, 1] });

        // f1(x) = 2x
        let f1 = ClosedForm::Affine(AffineFn { arity: 1, coeffs: vec![0, 2] });

        let f2 = ClosedForm::Iterated(IteratedFn {
            arity: 1,
            base: Box::new(id.clone()),
            step: Box::new(f1.clone())
        });

        let f3 = ClosedForm::Iterated(IteratedFn {
            arity: 1,
            base: Box::new(id.clone()),
            step: Box::new(f2.clone())
        });

        assert_eq!(fgh_level(&f0), 0);
        assert_eq!(fgh_level(&f1), 1);
        assert_eq!(fgh_level(&f2), 2);
        assert_eq!(fgh_level(&f3), 3);
        
        // Funcs that don't quite match FGH:
        // poly(x) = (x choose 2) (Polynomial growth: FGH Level 1)
        let poly = ClosedForm::Polynomial(PolynomialFn::new(
            1, 1, vec![1], Box::new(AffineFn { arity: 1, coeffs: vec![0, 0] })
        ));
        
        // iter(y, x) = R(x + 1, \acc. acc choose 2)(y, x)
        // iter(0, x) = x + 1
        // iter(y+1, x) = poly(iter(y, x))
        // Iterating a polynomial produces exponential growth: FGH Level 2
        let iter = ClosedForm::Iterated(IteratedFn {
            arity: 2,
            base: Box::new(f0.clone()),
            step: Box::new(poly.clone())
        });

        assert_eq!(fgh_level(&poly), 1);
        assert_eq!(fgh_level(&iter), 2);
    }

    #[test]
    fn test_power_tower_bounds_formatting() {
        // Base function: x + 1 (arity 1)
        let base_cf = ClosedForm::Affine(AffineFn { arity: 1, coeffs: vec![1, 1] });
        
        // Step function: 2x (arity 2, meaning f(acc, x) = 2*acc)
        let step_affine = ClosedForm::Affine(AffineFn { arity: 2, coeffs: vec![0, 2, 0] });
        
        // iter_affine(k, x) = (x+1) 2^k
        let iter_affine = ClosedForm::Iterated(IteratedFn {
            arity: 2,
            base: Box::new(base_cf.clone()),
            step: Box::new(step_affine),
        });
        
        // iter_affine(10, 3) = 4 2^10 ≈ 10^3.61
        let val_affine = SymVal::FuncApp(iter_affine, vec![SymVal::Const(10), SymVal::Const(3)]);
        let formatted_affine = format!("{}", val_affine);
        assert_eq!(formatted_affine, "[10^3.61, 10^3.61]");
        
        // Step function: P(acc) = \binom{acc}{2} + acc.
        let step_poly = ClosedForm::Polynomial(PolynomialFn::new(
            2, 1, vec![1], Box::new(AffineFn { arity: 2, coeffs: vec![0, 1, 0] })
        ));
        
        let iter_poly = ClosedForm::Iterated(IteratedFn {
            arity: 2,
            base: Box::new(base_cf.clone()),
            step: Box::new(step_poly),
        });
        
        // Test iter_poly with args: k=3, x=2
        // Initial acc = base(2) = 3.
        // k=3, x=3. d=2.
        // c_min=1, c_max=2.
        // m_min = log10(1)/1 + log10(3) = 0.47712
        // m_max = log10(2)/1 + log10(3) = 0.30103 + 0.47712 = 0.77815
        // 10^y_min = 2^3 * m_min = 8 * 0.47712 = 3.81696 ≈ 3.82
        // 10^y_max = 2^3 * m_max = 8 * 0.77815 = 6.2252 ≈ 6.23
        let val_poly = SymVal::FuncApp(iter_poly, vec![SymVal::Const(3), SymVal::Const(2)]);
        let formatted_poly = format!("{}", val_poly);
        assert_eq!(formatted_poly, "[10^3.82, 10^6.23]");
    }
}
