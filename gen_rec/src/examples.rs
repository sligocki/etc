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
    use crate::simulate::simulate;

    // TODO: use version from simulate::tests
    fn eval(grf: &Grf, args: &[u64]) -> Option<u64> {
        let (result, _steps) = simulate(grf, args, 1_000_000);
        result.into_value().map(|v| u64::try_from(v).unwrap())
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
            result.into_value().map(|v| u64::try_from(v).unwrap()),
            Some(26_357_430)
        );
    }
}
