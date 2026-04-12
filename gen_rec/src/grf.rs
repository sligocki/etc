use std::fmt;

/// A General Recursive Function (GRF).
///
/// Each GRF has a well-defined arity (number of inputs) derivable from its structure.
///
/// Size measure: atoms have size 1; combinators have size 1 + sum of sub-expression sizes.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Grf {
    // --- Atoms (size 1) ---

    /// Z_k: k-arity constant-zero. Z_k(x1,...,xk) = 0.
    Zero(usize),

    /// S: 1-arity successor. S(x) = x+1.
    Succ,

    /// P^k_i: k-arity projection (i is 1-based). P^k_i(x1,...,xk) = xi.
    Proj(usize, usize),

    // --- Combinators (size = 1 + sum of parts) ---

    /// C(h, g1..gm): h ∈ GRF_m, each gi ∈ GRF_k, result ∈ GRF_k.  m >= 1.
    /// C(h,g1,...,gm)(x1,...,xk) = h(g1(x1,...,xk), ..., gm(x1,...,xk))
    ///
    /// The third field stores k (the shared arity of all gi and of the result).
    /// Storing it here avoids the O(depth) traversal and prevents panics on
    /// empty-arg edge cases.
    Comp(Box<Grf>, Vec<Grf>, usize),

    /// R(g, h): g ∈ GRF_k, h ∈ GRF_{k+2}, result ∈ GRF_{k+1}.
    /// R(g,h)(0, rest) = g(rest)
    /// R(g,h)(n+1, rest) = h(n, R(g,h)(n, rest), rest)
    Rec(Box<Grf>, Box<Grf>),

    /// M(f): f ∈ GRF_{k+1}, result ∈ GRF_k.
    /// M(f)(x1,...,xk) = min{i ∈ ℕ : f(i,x1,...,xk) = 0}
    Min(Box<Grf>),
}

impl Grf {
    /// Convenience constructor for Comp: derives and stores the arity of the args.
    ///
    /// Panics if `args` is empty (Comp requires at least 1 argument function).
    pub fn comp(h: Self, args: Vec<Self>) -> Self {
        assert!(!args.is_empty(), "Comp requires at least 1 argument function");
        let arity = args[0].arity();
        Grf::Comp(Box::new(h), args, arity)
    }

    /// Returns the arity (number of inputs) of this function.
    pub fn arity(&self) -> usize {
        match self {
            Grf::Zero(k) => *k,
            Grf::Succ => 1,
            Grf::Proj(k, _) => *k,
            // Arity is stored directly; O(1) and no panic on empty args.
            Grf::Comp(_, _, k) => *k,
            // g ∈ GRF_k → R(g,h) ∈ GRF_{k+1}
            Grf::Rec(g, _) => g.arity() + 1,
            // f ∈ GRF_{k+1} → M(f) ∈ GRF_k
            Grf::Min(f) => {
                let a = f.arity();
                debug_assert!(a >= 1, "M(f) requires arity(f) >= 1");
                a - 1
            }
        }
    }

    /// Returns the structural size of this function.
    pub fn size(&self) -> usize {
        match self {
            Grf::Zero(_) | Grf::Succ | Grf::Proj(_, _) => 1,
            Grf::Comp(h, gs, _) => 1 + h.size() + gs.iter().map(Grf::size).sum::<usize>(),
            Grf::Rec(g, h) => 1 + g.size() + h.size(),
            Grf::Min(f) => 1 + f.size(),
        }
    }

    /// Returns true if this is a Primitive Recursive Function (no Min anywhere).
    pub fn is_prf(&self) -> bool {
        match self {
            Grf::Zero(_) | Grf::Succ | Grf::Proj(_, _) => true,
            Grf::Comp(h, gs, _) => h.is_prf() && gs.iter().all(Grf::is_prf),
            Grf::Rec(g, h) => g.is_prf() && h.is_prf(),
            Grf::Min(_) => false,
        }
    }
}

impl fmt::Display for Grf {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Grf::Zero(k) => write!(f, "Z{k}"),
            Grf::Succ => write!(f, "S"),
            Grf::Proj(k, i) => write!(f, "P({k},{i})"),
            Grf::Comp(h, gs, _) => {
                write!(f, "C({h}")?;
                for g in gs {
                    write!(f, ", {g}")?;
                }
                write!(f, ")")
            }
            Grf::Rec(g, h) => write!(f, "R({g}, {h})"),
            Grf::Min(func) => write!(f, "M({func})"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_atom_arities() {
        assert_eq!(Grf::Zero(0).arity(), 0);
        assert_eq!(Grf::Zero(3).arity(), 3);
        assert_eq!(Grf::Succ.arity(), 1);
        assert_eq!(Grf::Proj(1, 1).arity(), 1);
        assert_eq!(Grf::Proj(3, 2).arity(), 3);
    }

    #[test]
    fn test_atom_sizes() {
        assert_eq!(Grf::Zero(0).size(), 1);
        assert_eq!(Grf::Zero(5).size(), 1);
        assert_eq!(Grf::Succ.size(), 1);
        assert_eq!(Grf::Proj(2, 1).size(), 1);
    }

    #[test]
    fn test_comp_arity_and_size() {
        // C(S, Z0): arity=0, size=3
        let f = Grf::comp(Grf::Succ, vec![Grf::Zero(0)]);
        assert_eq!(f.arity(), 0);
        assert_eq!(f.size(), 3);
    }

    #[test]
    fn test_comp_multi_arg_arity() {
        // C(P(2,1), S, Z1): takes 1 arg (each gi has arity 1), arity = 1
        let f = Grf::comp(Grf::Proj(2, 1), vec![Grf::Succ, Grf::Zero(1)]);
        assert_eq!(f.arity(), 1);
        assert_eq!(f.size(), 1 + 1 + 1 + 1); // C + P + S + Z = 4
    }

    #[test]
    fn test_rec_arity_and_size() {
        // R(Z0, C(S, P(3,2))): g=Z0 (arity 0), so result has arity 1
        // h = C(S, P(3,2)) has arity 3
        // size = 1 + 1 + (1 + 1 + 1) = 5
        let g = Grf::Zero(0);
        let h = Grf::comp(Grf::Succ, vec![Grf::Proj(3, 2)]);
        let r = Grf::Rec(Box::new(g), Box::new(h));
        assert_eq!(r.arity(), 1);
        assert_eq!(r.size(), 5);
    }

    #[test]
    fn test_min_arity_and_size() {
        // M(S): f=S arity 1 → M(S) arity 0, size 2
        let m = Grf::Min(Box::new(Grf::Succ));
        assert_eq!(m.arity(), 0);
        assert_eq!(m.size(), 2);
    }

    #[test]
    fn test_k0_1_size() {
        // K_0[1] = C(S, Z0): size = 3
        let k01 = Grf::comp(Grf::Succ, vec![Grf::Zero(0)]);
        assert_eq!(k01.size(), 3);
    }

    #[test]
    fn test_k0_2_size() {
        // K_0[2] = C(S, C(S, Z0)): size = 5
        let k01 = Grf::comp(Grf::Succ, vec![Grf::Zero(0)]);
        let k02 = Grf::comp(Grf::Succ, vec![k01]);
        assert_eq!(k02.size(), 5);
    }

    #[test]
    fn test_plus_size() {
        // Plus = R(P(1,1), C(S, P(3,2))): size = 1 + 1 + (1+1+1) = 5
        let g = Grf::Proj(1, 1);
        let h = Grf::comp(Grf::Succ, vec![Grf::Proj(3, 2)]);
        let plus = Grf::Rec(Box::new(g), Box::new(h));
        assert_eq!(plus.size(), 5);
    }

    #[test]
    fn test_display() {
        let f = Grf::comp(Grf::Succ, vec![Grf::Zero(0)]);
        assert_eq!(f.to_string(), "C(S, Z0)");

        let g = Grf::Min(Box::new(Grf::Succ));
        assert_eq!(g.to_string(), "M(S)");

        let h = Grf::Rec(Box::new(Grf::Zero(0)), Box::new(Grf::Proj(2, 1)));
        assert_eq!(h.to_string(), "R(Z0, P(2,1))");
    }

    #[test]
    fn test_is_prf() {
        assert!(Grf::Succ.is_prf());
        let prf = Grf::comp(Grf::Succ, vec![Grf::Zero(0)]);
        assert!(prf.is_prf());
        let not_prf = Grf::Min(Box::new(Grf::Proj(1, 1)));
        assert!(!not_prf.is_prf());
    }

    /// Tri = R(Z0, R(S, C(S, P(3,2)))): size should be 7
    /// Z0: size 1
    /// P(3,2): size 1
    /// C(S, P(3,2)): size 3
    /// R(S, C(S, P(3,2))): size 1+1+3 = 5
    /// R(Z0, R(S, C(S,P(3,2)))): size 1+1+5 = 7
    #[test]
    fn test_tri_size_and_arity() {
        let tri = make_tri();
        assert_eq!(tri.arity(), 1);
        assert_eq!(tri.size(), 7);
    }

    /// RepDiag[f] = C(R(S, C(f, P(3,2))), S, S): size depends on f.
    /// For f = Tri (size 7):
    ///   P(3,2): 1, C(Tri, P(3,2)): 1+7+1=9, R(S, C(Tri,P(3,2))): 1+1+9=11
    ///   C(R(...), S, S): 1+11+1+1=14
    /// Arity: R(S, ...) ∈ GRF_2 (since g=S ∈ GRF_1 → arity+1=2).
    /// C(R(...), S, S): args are S,S ∈ GRF_1 → result ∈ GRF_1.
    #[test]
    fn test_rep_diag_tri_size_and_arity() {
        let rd_tri = make_rep_diag(make_tri());
        assert_eq!(rd_tri.arity(), 1);
        assert_eq!(rd_tri.size(), 14);
    }

    // -------------------------------------------------------------------------
    // Helpers shared with simulate tests
    // -------------------------------------------------------------------------

    /// Tri(n) = n(n+1)/2  (triangular numbers)
    /// Structure: R(Z0, R(S, C(S, P(3,2))))
    pub(crate) fn make_tri() -> Grf {
        // inner_h = R(S, C(S, P(3,2))): takes args (i, acc, rest...) but here arity 3 total
        // But let's be precise:
        // Tri ∈ GRF_1: R(g, h) with g ∈ GRF_0, h ∈ GRF_2
        //   g = Z0 (arity 0)
        //   h ∈ GRF_2: R(S, C(S, P(3,2))) ... wait, that's arity 3
        //
        // Actually the standard Tri construction:
        //   Tri = R(Z0, h) where h(n, acc) = acc + n + 1
        //   h(n, acc) = add(acc, succ(n))
        //   But with only primitive combinators: h = R(S, C(S, P(3,2))) doesn't work here.
        //
        // Correct construction: Tri = R(Z0, inner) where inner ∈ GRF_2
        //   inner(n, acc) = acc + n + 1
        //   We need add(acc, S(n)) = R(P(1,1), C(S, P(3,2)))(n+1, acc)
        //   That's too big.
        //
        // User's definition: Tri = R(Z, R(S, C(S, P_2)))
        //   Here P_2 means P(?,2) — the 2nd projection.
        //   R(S, C(S, P_2)) as the step function h ∈ GRF_2:
        //     h(i, acc) = R(S, C(S, P(?,2)))(i, acc)
        //     This is itself a Rec! Let's unpack:
        //     R(S, C(S, P(3,2)))(i, acc) where S ∈ GRF_1, C(S,P(3,2)) ∈ GRF_3
        //     Base: S(acc ... wait, base for R(g,h) takes arity(g) args.
        //     g = S, arity(S)=1 → R(S, C(S,P(3,2))) ∈ GRF_2
        //     R(S, C(S,P(3,2)))(0, x) = S(x) = x+1
        //     R(S, C(S,P(3,2)))(n+1, x): h'(n, acc, x) = C(S,P(3,2))(n,acc,x) = S(P(3,2)(n,acc,x)) = acc+1
        //     So R(S, C(S,P(3,2)))(n, x) = x + n + 1
        //
        // So Tri = R(Z0, R(S, C(S, P(3,2)))) where:
        //   outer g = Z0 ∈ GRF_0
        //   outer h = R(S, C(S,P(3,2))) ∈ GRF_2
        //   Tri ∈ GRF_1
        //   Tri(0) = Z0() = 0
        //   Tri(n+1) = R(S, C(S,P(3,2)))(n, Tri(n)) = Tri(n) + n + 1
        //   Tri(n) = 0 + 1 + 2 + ... + n = n(n+1)/2  ✓
        let inner_h = Grf::Rec(
            Box::new(Grf::Succ),
            Box::new(Grf::comp(Grf::Succ, vec![Grf::Proj(3, 2)])),
        );
        Grf::Rec(Box::new(Grf::Zero(0)), Box::new(inner_h))
    }

    /// RepDiag[f] = C(R(S, C(f, P(3,2))), S, S)  ∈ GRF_0
    /// RepDiag[f]() = R(S, C(f, P(3,2)))(S(), S()) = R(S, C(f, P(3,2)))(1, 1)
    ///              = f^{?}(?) ...
    pub(crate) fn make_rep_diag(f: Grf) -> Grf {
        // step(i, acc) = C(f, P(3,2))(i, acc, ...) = f(P(3,2)(i,acc,...)) = f(acc)
        // So R(S, C(f, P(3,2)))(n, x):
        //   Base: S(x) = x+1
        //   Step: step(i, acc) = f(acc)
        //   R(...)(0, x) = x+1
        //   R(...)(1, x) = f(x+1)
        //   R(...)(2, x) = f(f(x+1))
        //   R(...)(n, x) = f^n(x+1)
        //
        // RepDiag[f]() = R(S, C(f,P(3,2)))(S(), S()) = R(S, C(f,P(3,2)))(1, 1) = f^1(1+1) = f(2)
        //   Wait, but we apply it to () so S gives 1 for both.
        //   RepDiag[f]() = R(S, C(f,P(3,2)))(1, 1) = f^1(1+1) = f(2)
        //   RepDiag[Tri]() = Tri(2) = 3?  That seems too small.
        //
        // Let me re-examine. User said C(RepDiag[Tri], K[n]) for n=1..4.
        // C(RepDiag[Tri], K[1])() = RepDiag[Tri](K[1]()) = RepDiag[Tri](1)
        //   So RepDiag takes an argument here! So RepDiag[f] ∈ GRF_1, not GRF_0.
        //
        // Let me re-examine the structure: RepDiag[f] = C(R(S, C(f, P_2)), S, S)
        //   This is C(outer, S, S) where outer = R(S, C(f, P_2))
        //   outer ∈ GRF_2 (as computed above)
        //   C(outer, S, S): each arg (S,S) has arity 1, result arity 1
        //   C(outer, S, S)(x) = outer(S(x), S(x)) = R(S, C(f,P(3,2)))(x+1, x+1)
        //                      = f^{x+1}(x+2)
        //   RepDiag[Tri](1) = Tri^2(3) = Tri(Tri(3)) = Tri(6) = 21
        //   RepDiag[Tri](2) = Tri^3(4) = Tri(Tri(Tri(4))) = Tri(Tri(10)) = Tri(55) = 1540
        //   RepDiag[Tri](3) = Tri^4(5) = Tri(Tri(Tri(Tri(5)))) = Tri(Tri(Tri(15))) = Tri(Tri(120)) = Tri(7260) = 26,357,430  ✓
        // Great!
        //
        // So C(RepDiag[Tri], K[n])() = RepDiag[Tri](K[n]()) = RepDiag[Tri](n) = Tri^{n+1}(n+2)
        //
        // RepDiag[f] ∈ GRF_1:
        //   C(R(S, C(f, P(3,2))), S, S) where args are (S, S) each of arity 1 → result arity 1
        let step = Grf::comp(f, vec![Grf::Proj(3, 2)]);
        let outer = Grf::Rec(Box::new(Grf::Succ), Box::new(step));
        Grf::comp(outer, vec![Grf::Succ, Grf::Succ])
    }
}
