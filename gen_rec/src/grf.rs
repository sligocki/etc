use std::collections::BTreeSet;
use std::fmt;
use std::iter::Peekable;
use std::str::{Chars, FromStr};

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
    /// Convenience constructor for Rec: boxes both sub-functions.
    pub fn rec(g: Self, h: Self) -> Self {
        Grf::Rec(Box::new(g), Box::new(h))
    }

    /// Convenience constructor for Min: boxes the inner function.
    pub fn min(f: Self) -> Self {
        Grf::Min(Box::new(f))
    }

    /// Convenience constructor for Comp: derives and stores the arity of the args.
    ///
    /// Panics if `args` is empty (Comp requires at least 1 argument function).
    pub fn comp(h: Self, args: Vec<Self>) -> Self {
        assert!(
            !args.is_empty(),
            "Comp requires at least 1 argument function"
        );
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

    /// Returns the set of argument positions (1-indexed) this GRF syntactically reads.
    ///
    /// This is a conservative over-approximation: if `j` is absent from the result,
    /// the GRF provably ignores argument `j`. If `j` is present, it may or may not
    /// actually depend on it (e.g. `Rec` always conservatively includes arg 1).
    ///
    /// Used by the simulator to detect when a `Rec` step function ignores its
    /// accumulator (arg 2), enabling the fast-forward optimization.
    pub fn used_args(&self) -> BTreeSet<usize> {
        match self {
            Grf::Zero(_) => BTreeSet::new(),
            Grf::Succ => [1].into_iter().collect(),
            Grf::Proj(_, i) => [*i].into_iter().collect(),
            Grf::Comp(h, gs, _) => {
                // C(h, g1..gm)(args) = h(g1(args), ..., gm(args)).
                // Comp reads arg j iff h reads some position i where gi reads arg j.
                let h_used = h.used_args();
                let mut result = BTreeSet::new();
                for (idx, g) in gs.iter().enumerate() {
                    if h_used.contains(&(idx + 1)) {
                        result.extend(g.used_args());
                    }
                }
                result
            }
            Grf::Rec(g, h) => {
                // R(g,h)(n, r1..r_{k-1}): base g(r1..r_{k-1}), step h(i, acc, r1..r_{k-1}).
                // g's arg j  →  Rec's arg j+1  (rest starts at position 2 of Rec).
                // h's arg j (j≥3)  →  Rec's arg j-1  (h's positions 1,2 are i and acc).
                // Rec always conservatively includes arg 1 (the counter n).
                let g_used = g.used_args();
                let h_used = h.used_args();
                let mut result = BTreeSet::new();
                result.insert(1);
                for j in g_used {
                    result.insert(j + 1);
                }
                for j in h_used {
                    if j >= 3 {
                        result.insert(j - 1);
                    }
                    // j=1 (loop counter i) already covered by arg 1 above.
                    // j=2 (accumulator) is internal — doesn't add a new Rec input.
                }
                result
            }
            Grf::Min(f) => {
                // M(f)(r1..r_k): f(i, r1..r_k). f's arg j (j≥2) → Min's arg j-1.
                let f_used = f.used_args();
                let mut result = BTreeSet::new();
                for j in f_used {
                    if j >= 2 {
                        result.insert(j - 1);
                    }
                }
                result
            }
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

    /// Recursively parses a single GRF expression from the character stream.
    fn parse_expr(chars: &mut Peekable<Chars>) -> Result<Self, String> {
        let c = chars
            .next()
            .ok_or_else(|| "Unexpected end of input".to_string())?;
        match c {
            'Z' => {
                let k = Self::parse_num(chars)?;
                Ok(Grf::Zero(k))
            }
            'S' => Ok(Grf::Succ),
            'P' => {
                Self::consume(chars, '(')?;
                let k = Self::parse_num(chars)?;
                Self::consume(chars, ',')?;
                let i = Self::parse_num(chars)?;
                Self::consume(chars, ')')?;
                Ok(Grf::Proj(k, i))
            }
            'C' => {
                Self::consume(chars, '(')?;
                let h = Self::parse_expr(chars)?;
                Self::consume(chars, ',')?;

                // Comp requires at least one argument `g`
                let mut gs = vec![Self::parse_expr(chars)?];
                while Self::consume(chars, ',').is_ok() {
                    gs.push(Self::parse_expr(chars)?);
                }
                Self::consume(chars, ')')?;
                Ok(Grf::comp(h, gs))
            }
            'R' => {
                Self::consume(chars, '(')?;
                let g = Self::parse_expr(chars)?;
                Self::consume(chars, ',')?;
                let h = Self::parse_expr(chars)?;
                Self::consume(chars, ')')?;
                Ok(Grf::Rec(Box::new(g), Box::new(h)))
            }
            'M' => {
                Self::consume(chars, '(')?;
                let f = Self::parse_expr(chars)?;
                Self::consume(chars, ')')?;
                Ok(Grf::Min(Box::new(f)))
            }
            _ => Err(format!("Unexpected character: {}", c)),
        }
    }

    /// Consumes the expected character or returns an error.
    fn consume(chars: &mut Peekable<Chars>, expected: char) -> Result<(), String> {
        if let Some(&c) = chars.peek() {
            if c == expected {
                chars.next(); // Consume
                return Ok(());
            }
            return Err(format!("Expected '{}', found '{}'", expected, c));
        }
        Err(format!("Expected '{}', found end of input", expected))
    }

    /// Parses an integer from the character stream.
    fn parse_num(chars: &mut Peekable<Chars>) -> Result<usize, String> {
        let mut num_str = String::new();
        while let Some(&c) = chars.peek() {
            if c.is_ascii_digit() {
                num_str.push(c);
                chars.next(); // Consume
            } else {
                break;
            }
        }
        if num_str.is_empty() {
            return Err("Expected a number".to_string());
        }
        num_str.parse::<usize>().map_err(|e| e.to_string())
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

impl FromStr for Grf {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // Strip out all whitespace to simplify parsing rules
        let s: String = s.chars().filter(|c| !c.is_whitespace()).collect();
        let mut chars = s.chars().peekable();

        let result = Self::parse_expr(&mut chars)?;

        if chars.peek().is_some() {
            return Err("Trailing characters found after valid GRF expression".to_string());
        }
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! grf {
        ($($arg:tt)*) => {
            format!($($arg)*).parse::<Grf>().unwrap()
        };
    }

    #[test]
    fn test_atom_arities() {
        assert_eq!(grf!("Z0").arity(), 0);
        assert_eq!(grf!("Z3").arity(), 3);
        assert_eq!(grf!("S").arity(), 1);
        assert_eq!(grf!("P(1,1)").arity(), 1);
        assert_eq!(grf!("P(3,2)").arity(), 3);
    }

    #[test]
    fn test_atom_sizes() {
        assert_eq!(grf!("Z0").size(), 1);
        assert_eq!(grf!("Z5").size(), 1);
        assert_eq!(grf!("S").size(), 1);
        assert_eq!(grf!("P(2,1)").size(), 1);
    }

    #[test]
    fn test_comp_arity_and_size() {
        let f = grf!("C(S, Z0)");
        assert_eq!(f.arity(), 0);
        assert_eq!(f.size(), 3);
    }

    #[test]
    fn test_comp_multi_arg_arity() {
        let f = grf!("C(P(2,1), S, Z1)");
        assert_eq!(f.arity(), 1);
        assert_eq!(f.size(), 4);
    }

    #[test]
    fn test_rec_arity_and_size() {
        let r = grf!("R(Z0, C(S, P(3,2)))");
        assert_eq!(r.arity(), 1);
        assert_eq!(r.size(), 5);
    }

    #[test]
    fn test_min_arity_and_size() {
        let m = grf!("M(S)");
        assert_eq!(m.arity(), 0);
        assert_eq!(m.size(), 2);
    }

    #[test]
    fn test_plus_size() {
        let plus = grf!("R(P(1,1), C(S, P(3,2)))");
        assert_eq!(plus.size(), 5);
    }

    #[test]
    fn test_display() {
        let f = grf!("C(S, Z0)");
        assert_eq!(f.to_string(), "C(S, Z0)");

        let g = grf!("M(S)");
        assert_eq!(g.to_string(), "M(S)");

        let h = grf!("R(Z0, P(2,1))");
        assert_eq!(h.to_string(), "R(Z0, P(2,1))");
    }

    #[test]
    fn test_is_prf() {
        // PRFs
        assert!(grf!("S").is_prf());
        assert!(grf!("C(S, Z0)").is_prf());
        // Not PRFs
        assert!(!grf!("M(P(1,1))").is_prf());
        assert!(!grf!("C(S, M(S))").is_prf());
    }

    fn ua(s: &str) -> BTreeSet<usize> {
        s.parse::<Grf>().unwrap().used_args()
    }

    fn set(xs: &[usize]) -> BTreeSet<usize> {
        xs.iter().cloned().collect()
    }

    #[test]
    fn test_used_args_atoms() {
        assert_eq!(ua("Z0"), set(&[]));
        assert_eq!(ua("Z3"), set(&[]));
        assert_eq!(ua("S"), set(&[1]));
        assert_eq!(ua("P(1,1)"), set(&[1]));
        assert_eq!(ua("P(3,2)"), set(&[2]));
    }

    #[test]
    fn test_used_args_comp() {
        // C(S, Z1): S uses arg 1 of its input = g1's output. g1=Z1 uses nothing.
        assert_eq!(ua("C(S,Z1)"), set(&[]));
        // C(S, P(2,1)): S uses arg 1 = P(2,1)'s output. P(2,1) uses arg 1.
        assert_eq!(ua("C(S,P(2,1))"), set(&[1]));
        // C(P(2,1), S, Z1): P(2,1) uses position 1 = S's output. S uses arg 1.
        assert_eq!(ua("C(P(2,1),S,Z1)"), set(&[1]));
        // C(P(2,2), S, Z1): P(2,2) uses position 2 = Z1's output. Z1 uses nothing.
        assert_eq!(ua("C(P(2,2),S,Z1)"), set(&[]));
    }

    #[test]
    fn test_used_args_rec() {
        // R(Z0, P(2,2)): g=Z0 uses {}, h=P(2,2) uses {2} (acc, internal). Rec uses {1}.
        assert_eq!(ua("R(Z0,P(2,2))"), set(&[1]));
        // R(P(1,1), C(S,P(3,2))): add(n, m). g=P(1,1) uses {1}→Rec arg 2.
        // h=C(S,P(3,2)) uses {2} (acc, internal). Rec uses {1,2}.
        assert_eq!(ua("R(P(1,1),C(S,P(3,2)))"), set(&[1, 2]));
        // R(Z1, P(3,1)): predecessor. g=Z1 uses {}, h=P(3,1) uses {1} (counter, internal).
        // h uses nothing with j>=3. Rec uses {1}.
        assert_eq!(ua("R(Z1,P(3,1))"), set(&[1]));
    }

    #[test]
    fn test_used_args_rec_acc_ignored() {
        // Key invariant for the fast-forward optimisation:
        // R(Z1, P(3,1)) has used_args = {1}, so arg 2 (acc) is absent.
        let inner = grf!("R(Z1,P(3,1))");
        assert!(!inner.used_args().contains(&2));
        // Outer R(Z0, inner): inner.used_args = {1}, so inner ignores acc.
        let outer = Grf::rec(Grf::Zero(0), inner);
        assert!(!outer.used_args().contains(&2));
    }

    #[test]
    fn test_used_args_min() {
        // M(P(1,1)): f(i)=i, f uses {1} (i, internal). Min's args: f's j>=2 → none.
        assert_eq!(ua("M(P(1,1))"), set(&[]));
        // M(P(2,2)): f(i,x)=x, f uses {2} → Min's arg 1.
        assert_eq!(ua("M(P(2,2))"), set(&[1]));
    }
}
