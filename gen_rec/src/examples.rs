/// Collection of example GRFs and GRF macros
use crate::grf::Grf;

/// Macro which adds n to an existing function.
/// plus_n_macro(n, f) = \*xs. f(*xs) + n
pub fn plus_n_macro(n: usize, mut f: Grf) -> Grf {
    for _ in 0..n {
        f = Grf::comp(Grf::Succ, vec![f]);
    }
    f
}

/// Constant function that always returns n
pub fn constant(n: usize, arity: usize) -> Grf {
    plus_n_macro(n, Grf::Zero(arity))
}

/// Unary function which adds n to input
pub fn plus_n(n: usize) -> Grf {
    assert!(n >= 1);
    plus_n_macro(n - 1, Grf::Succ)
}

/// Polygonal number functions.
/// Tri = polygonal(1) = \x. x(x+1)/2
/// Square = polygonal(2) = \x. x^2
pub fn polygonal(n: usize) -> Grf {
    // R(Z0, R(S, C(Plus[n], P^3_2)))
    Grf::Rec(
        Box::new(Grf::Zero(0)),
        Box::new(Grf::Rec(
            Box::new(Grf::Succ),
            Box::new(Grf::comp(plus_n(n), vec![Grf::Proj(3, 2)])),
        )),
    )
}

pub fn triangular() -> Grf {
    polygonal(1)
}
pub fn square() -> Grf {
    polygonal(2)
}

/// Iterate application of a function onto a base (incremented).
///     RepSucc[f] := R(S, C(f, P_2)) = \xy. f^x(y+1)
pub fn rep_succ(f: Grf) -> Grf {
    let step = Grf::comp(f, vec![Grf::Proj(3, 2)]);
    Grf::Rec(Box::new(Grf::Succ), Box::new(step))
}

/// Diagonalize 2-ary f -> unary and then repeatedly apply.
///     DiagRep[f] := R(S, C(f, P(3,2), P(3,2))) = \xy. (\z. f(z,z))^x (y+1)
pub fn diag_rep(f: Grf) -> Grf {
    let diag = Grf::comp(f, vec![Grf::Proj(3, 2), Grf::Proj(3, 2)]);
    Grf::Rec(Box::new(Grf::Succ), Box::new(diag))
}

/// Diagonalize 2-ary f -> unary (incrementing input first).
///     DiagS[f] := C(f, S, S) = \x. f(x+1, x+1)
pub fn diag_succ(f: Grf) -> Grf {
    Grf::comp(f, vec![Grf::Succ, Grf::Succ])
}

/// Ackermann of Diagonalized
///     AckDiag[n,f] := DiagS[DiagRep^n[RepSucc[f]]]
pub fn ack_diag(n: usize, mut f: Grf) -> Grf {
    f = rep_succ(f);
    for _ in 0..n {
        f = diag_rep(f);
    }
    diag_succ(f)
}

/// Diagonalization across repeated application of a function
///   RepDiag[f](x) = f^{x+1}(x+2).
///   RepDiag[f] = C(R(S, C(f, P(3,2))), S, S) ∈ GRF_1.
pub fn rep_diag(f: Grf) -> Grf {
    let step = Grf::comp(f, vec![Grf::Proj(3, 2)]);
    let outer = Grf::Rec(Box::new(Grf::Succ), Box::new(step));
    Grf::comp(outer, vec![Grf::Succ, Grf::Succ])
}

/// Ackermann Diagonalized Triangle
/// adt[n] = RepDiag^n[Tri]
pub fn adt(n: usize) -> Grf {
    let mut f = triangular();
    for _ in 0..n {
        f = rep_diag(f);
    }
    f
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::simulate::{simulate, Num};

    fn eval(grf: &Grf, args: &[Num]) -> Option<Num> {
        let (result, _steps) = simulate(grf, args, 1_000_000);
        result.into_value()
    }

    #[test]
    fn test_constant() {
        for n in 0..10 {
            let k = constant(n, 0);
            assert_eq!(k.arity(), 0);
            assert_eq!(k.size(), 2 * n + 1);
            assert_eq!(eval(&k, &[]), Some(n as u64));
        }
    }

    #[test]
    fn test_plus_n() {
        for n in 1..10 {
            let k = plus_n(n);
            assert_eq!(k.arity(), 1);
            assert_eq!(k.size(), 2 * n - 1);
            assert_eq!(eval(&k, &[13]), Some((n + 13) as u64));
        }
    }

    #[test]
    fn test_triangular() {
        let tri = triangular();
        assert_eq!(tri.arity(), 1);
        assert_eq!(tri.size(), 7);
        for n in 0..10 {
            assert_eq!(eval(&tri, &[n]), Some(n * (n + 1) / 2));
        }
    }

    #[test]
    fn test_square() {
        let sq = square();
        assert_eq!(sq.arity(), 1);
        assert_eq!(sq.size(), 9);
        for n in 0..10 {
            assert_eq!(eval(&sq, &[n]), Some(n * n));
        }
    }

    #[test]
    fn test_diag_tri() {
        // RepDiag[Tri](n) = Tri^{n+1}(n+2)
        let dt = adt(1);
        assert_eq!(dt.arity(), 1);
        assert_eq!(dt.size(), 14);

        // RepDiag[Tri](1) = Tri^2(3) = Tri(Tri(3)) = Tri(6) = 21
        assert_eq!(eval(&dt, &[1]), Some(21));
        // RepDiag[Tri](2) = Tri^3(4) = Tri(Tri(10)) = Tri(55) = 1540
        assert_eq!(eval(&dt, &[2]), Some(1540));
    }

    #[test]
    #[ignore = "Too slow for standard testing"]
    fn test_diag_tri_big() {
        let dt = adt(1);
        // RepDiag[Tri](3) = Tri^4(5) = Tri(Tri(Tri(15))) = Tri(Tri(120)) = Tri(7260) = 26,357,430
        let (result, _) = simulate(&dt, &[3], 200_000_000);
        assert_eq!(
            result.into_value(),
            Some(26_357_430)
        );
    }

    #[test]
    fn test_champions() {
        // 13: K[6]
        let c13 = constant(6, 0);
        assert_eq!(c13.size(), 13);
        assert_eq!(eval(&c13, &[]), Some(6));

        // 14: C(RepDiag[S], K[2])
        let c14 = Grf::comp(rep_diag(Grf::Succ), vec![constant(2, 0)]);
        assert_eq!(c14.size(), 14);
        assert_eq!(eval(&c14, &[]), Some(7));

        // 16: C(RepDiag[Plus[2]], K[2])
        let c16 = Grf::comp(rep_diag(plus_n(2)), vec![constant(2, 0)]);
        assert_eq!(c16.size(), 16);
        assert_eq!(eval(&c16, &[]), Some(10));

        // 17: C(AckDiag[1,S], K[1])
        let c17 = Grf::comp(ack_diag(1, Grf::Succ), vec![constant(1, 0)]);
        assert_eq!(c17.size(), 17);
        assert_eq!(eval(&c17, &[]), Some(15));

        // 18: C(RepDiag[Tri], K[1])
        let c18 = Grf::comp(rep_diag(triangular()), vec![constant(1, 0)]);
        assert_eq!(c18.size(), 18);
        assert_eq!(eval(&c18, &[]), Some(21));

        // 19: C(AckDiag[1,S], K[2])
        let c19 = Grf::comp(ack_diag(1, Grf::Succ), vec![constant(2, 0)]);
        assert_eq!(c19.size(), 19);
        assert_eq!(eval(&c19, &[]), Some(39));

        // 20: C(RepDiag[Tri], K[2])
        let c20 = Grf::comp(rep_diag(triangular()), vec![constant(2, 0)]);
        assert_eq!(c20.size(), 20);
        assert_eq!(eval(&c20, &[]), Some(1540));
    }
}
