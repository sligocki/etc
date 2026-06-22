use crate::closed_form::{ClosedForm, AffineFn};

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
            if crate::closed_form::closed_form_ignores_arg(cf, 1) {
                0
            } else {
                let l = fgh_level(cf);
                if l >= 2 { l + 1 } else { 2 }
            }
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
        let p1 = ClosedForm::Polynomial(PolynomialFn {
            arity: 1,
            poly_arg: 1,
            poly_coeffs: vec![1],
            affine_tail: Box::new(AffineFn { arity: 1, coeffs: vec![0, 1] })
        });
        // p2(x) = (x choose 2) + 2x
        let p2 = ClosedForm::Polynomial(PolynomialFn {
            arity: 1,
            poly_arg: 1,
            poly_coeffs: vec![1],
            affine_tail: Box::new(AffineFn { arity: 1, coeffs: vec![0, 2] })
        });

        // (x choose 2) + x ≤ (x choose 2) + 2x
        assert_eq!(compare_strict(&p1, &p2), PointwiseOrder::LessEqual);

        // p3(x) = 2*(x choose 2) + 1
        let p3 = ClosedForm::Polynomial(PolynomialFn {
            arity: 1,
            poly_arg: 1,
            poly_coeffs: vec![2],
            affine_tail: Box::new(AffineFn { arity: 1, coeffs: vec![1, 0] })
        });

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
        let poly = ClosedForm::Polynomial(PolynomialFn {
            arity: 1, poly_arg: 1, poly_coeffs: vec![1], affine_tail: Box::new(AffineFn { arity: 1, coeffs: vec![0, 0] })
        });
        
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
}
