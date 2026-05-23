use std::collections::BTreeSet;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::iter::Peekable;
use std::str::{Chars, FromStr};
use std::sync::OnceLock;

use crate::closed_form::{closed_form_of, ClosedForm};
use crate::sim_nat::SmallNat;

/// Parse a GRF from a format string, panicking on error.
///
/// Accepts the same format arguments as `format!`, passes the result through
/// `str::parse::<Grf>()`, and unwraps. Useful in tests and examples.
///
/// ```ignore
/// let f = grf!("R(Z0, P(2,1))");
/// let g = grf!("C(S, P({k},{i})", k = 3, i = 2);
/// ```
#[macro_export]
macro_rules! grf {
    ($($arg:tt)*) => {
        format!($($arg)*).parse::<$crate::grf::Grf>().unwrap()
    };
}

/// Flexibility of a GRF when its arguments are rewired.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Rewirability {
    /// Fully flexible. Can map outer arguments to any indices freely.
    Full,
    /// Locked to argument 1 as the counter. (e.g. Rec)
    CounterLocked,
    /// Locked to arity 1 and argument 1. (e.g. Succ)
    SuccLocked,
}

/// The structural variant of a GRF node (renamed from `Grf` to allow the wrapper struct).
///
/// Each combinator stores child `Grf` nodes (which carry the lazy ClosedForm cache).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum GrfKind {
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
    Comp(Box<Grf>, Vec<Grf>, usize),

    /// R(g, h): g ∈ GRF_k, h ∈ GRF_{k+2}, result ∈ GRF_{k+1}.
    Rec(Box<Grf>, Box<Grf>),

    /// M(f): f ∈ GRF_{k+1}, result ∈ GRF_k.
    Min(Box<Grf>),
}

/// A General Recursive Function (GRF) with a lazily-computed ClosedForm cache.
///
/// The `kind` field holds the structural variant; `cf` caches the result of
/// `closed_form_of` on first access via `closed_form()`.
///
/// `PartialEq`, `Eq`, and `Hash` are based on `kind` only — `cf` is a
/// transparent cache and does not affect identity.
pub struct Grf {
    pub kind: GrfKind,
    /// Lazily computed once; `None` means no closed form exists for this node.
    pub(crate) cf: OnceLock<Option<ClosedForm>>,
}

impl Clone for Grf {
    fn clone(&self) -> Self {
        let cf = OnceLock::new();
        if let Some(v) = self.cf.get() {
            let _ = cf.set(v.clone());
        }
        Grf {
            kind: self.kind.clone(),
            cf,
        }
    }
}

impl fmt::Debug for Grf {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.kind.fmt(f)
    }
}

impl PartialEq for Grf {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
    }
}

impl Eq for Grf {}

impl Hash for Grf {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.kind.hash(state);
    }
}

impl Grf {
    pub(crate) fn new(kind: GrfKind) -> Self {
        Grf {
            kind,
            cf: OnceLock::new(),
        }
    }

    // --- Atom constructors ---

    /// Z_k: k-arity constant-zero.
    pub fn zero_atom(k: usize) -> Self {
        Self::new(GrfKind::Zero(k))
    }

    /// S: 1-arity successor.
    pub fn succ_atom() -> Self {
        Self::new(GrfKind::Succ)
    }

    /// P^k_i: k-arity projection (i is 1-based).
    pub fn proj_atom(k: usize, i: usize) -> Self {
        Self::new(GrfKind::Proj(k, i))
    }

    // --- Combinator constructors ---

    /// Convenience constructor for Rec: boxes both sub-functions.
    pub fn rec(g: Self, h: Self) -> Self {
        Self::new(GrfKind::Rec(Box::new(g), Box::new(h)))
    }

    /// Convenience constructor for Min: boxes the inner function.
    pub fn min(f: Self) -> Self {
        Self::new(GrfKind::Min(Box::new(f)))
    }

    /// Convenience constructor for Comp: derives and stores the arity of the args.
    ///
    /// Panics if `args` is empty (use `comp0` for 0-arg Comp).
    pub fn comp(h: Self, args: Vec<Self>) -> Self {
        assert!(
            !args.is_empty(),
            "Comp requires at least 1 argument function; use comp0 for 0-arg Comp"
        );
        let arity = args[0].arity();
        Self::new(GrfKind::Comp(Box::new(h), args, arity))
    }

    /// Convenience constructor for 0-arg Comp: `Ck(h)` lifts a 0-arity `h` to
    /// a constant function of `outer_arity` inputs.
    pub fn comp0(h: Self, outer_arity: usize) -> Self {
        Self::new(GrfKind::Comp(Box::new(h), vec![], outer_arity))
    }

    // --- ClosedForm access ---

    /// Returns the closed-form semantic representation, computing and caching it on
    /// first call. Returns `None` for `Min`-containing GRFs or unsupported patterns.
    pub fn closed_form(&self) -> Option<&ClosedForm> {
        self.cf.get_or_init(|| closed_form_of(self)).as_ref()
    }

    // --- Structural queries ---

    /// Returns the arity (number of inputs) of this function.
    pub fn arity(&self) -> usize {
        match &self.kind {
            GrfKind::Zero(k) => *k,
            GrfKind::Succ => 1,
            GrfKind::Proj(k, _) => *k,
            // Arity is stored directly; O(1) and no panic on empty args.
            GrfKind::Comp(_, _, k) => *k,
            // g ∈ GRF_k → R(g,h) ∈ GRF_{k+1}
            GrfKind::Rec(g, _) => g.arity() + 1,
            // f ∈ GRF_{k+1} → M(f) ∈ GRF_k
            GrfKind::Min(f) => {
                let a = f.arity();
                debug_assert!(a >= 1, "M(f) requires arity(f) >= 1");
                a - 1
            }
        }
    }

    /// Returns the structural size of this function.
    pub fn size(&self) -> usize {
        match &self.kind {
            GrfKind::Zero(_) | GrfKind::Succ | GrfKind::Proj(_, _) => 1,
            GrfKind::Comp(h, gs, _) => 1 + h.size() + gs.iter().map(Grf::size).sum::<usize>(),
            GrfKind::Rec(g, h) => 1 + g.size() + h.size(),
            GrfKind::Min(f) => 1 + f.size(),
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
    /// Returns true if this GRF can provably never return 0.
    ///
    /// Conservative: returns false when unsure. Used by the enumerator to
    /// prune `M(f)` when `f` is always positive (M(f) always diverges).
    pub fn is_never_zero(&self) -> bool {
        match &self.kind {
            GrfKind::Succ => {
                return true;
            }
            GrfKind::Rec(g, h) => {
                // R(g, h)(n, rest): base g(rest), then h applies n times accumulating.
                // Positive for all n iff: g never zero AND h positive when accumulator positive.
                if g.is_never_zero() && h.is_positive_for_pos_arg(2) {
                    return true;
                }
            }
            GrfKind::Comp(h, gs, _) => {
                // C(+, ...) -> +
                if h.is_never_zero() {
                    return true;
                }

                // If any inner argument is strictly positive and the outer function
                // preserves positivity for that argument, the result is strictly positive.
                for (i, gi) in gs.iter().enumerate() {
                    if gi.is_never_zero() && h.is_positive_for_pos_arg(i + 1) {
                        return true;
                    }
                }

                // C(R(_, +), +, _, ...) -> +
                // C(R(_, h_step), gs) -> + when h_step and all gs are always positive:
                // gs[0] is never zero so the counter n >= 1, meaning R always steps at
                // least once; since h_step is never zero the result is always positive.
                if let GrfKind::Rec(_, h_step) = &h.kind {
                    if h_step.is_never_zero() && gs.first().map_or(false, |g| g.is_never_zero()) {
                        return true;
                    }
                }
            }
            _ => {}
        }
        return false;
    }

    /// Returns true if `f(args…) > 0` whenever arg `j` > 0, regardless of other args.
    ///
    /// Conservative: returns false when unsure. For the Min fast-forward (j=1, the search
    /// counter): if this holds and f(0, args) > 0, then Min diverges since no later i
    /// can produce 0.
    pub fn is_positive_for_pos_arg(&self, j: usize) -> bool {
        if self.is_never_zero() {
            return true;
        }
        match &self.kind {
            GrfKind::Proj(_, i) => *i == j,
            GrfKind::Rec(g, h) => {
                if j == 1 {
                    // Counter positive (n ≥ 1): h fires at least once. If h always
                    // returns positive, done. The g.is_never_zero() + h.is_positive_for_pos_arg(2)
                    // case is already covered by is_never_zero() above (which was extended
                    // to include that pattern), so here we only need h.is_never_zero().
                    h.is_never_zero()
                } else {
                    // Rec's outer arg j (j ≥ 2) maps to g's arg (j-1).
                    // Base (n=0): g positive when g's arg (j-1) positive.
                    // Steps: h positive when accumulator (arg 2) positive (or when j -> j+1 pos)
                    let h_pos = h.is_positive_for_pos_arg(2) || h.is_positive_for_pos_arg(j+1);
                    g.is_positive_for_pos_arg(j - 1) && h_pos
                }
            }
            GrfKind::Comp(h, gs, _) => {
                // h positive when h's arg 1 positive, gs[0] positive when comp's arg j positive
                if h.is_positive_for_pos_arg(1)
                    && gs.first().map_or(false, |g| g.is_positive_for_pos_arg(j))
                {
                    return true;
                }
                // h = Proj to position p: output = gs[p-1], delegate
                if let GrfKind::Proj(_, p) = &h.kind {
                    if let Some(gp) = gs.get(p - 1) {
                        return gp.is_positive_for_pos_arg(j);
                    }
                }
                false
            }
            _ => false,
        }
    }

    pub fn used_args(&self) -> BTreeSet<usize> {
        match &self.kind {
            GrfKind::Zero(_) => BTreeSet::new(),
            GrfKind::Succ => [1].into_iter().collect(),
            GrfKind::Proj(_, i) => [*i].into_iter().collect(),
            GrfKind::Comp(h, gs, _) => {
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
            GrfKind::Rec(g, h) => {
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
            GrfKind::Min(f) => {
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

    /// Returns the outer argument indices in DFS first-occurrence order.
    ///
    /// A pre-order walk of the tree records each `Proj` index the first time it
    /// is encountered, accounting for the argument remappings introduced by
    /// `Rec` (counter fixed at slot 1, accumulator synthetic) and `Min`
    /// (search variable synthetic).
    ///
    /// `self` is in canonical argument order iff the result equals
    /// `[1, 2, ..., self.arity()]`.  Combined with the all-args-used check
    /// (`self.used_args().len() == self.arity()`), this forms the full RNF
    /// criterion used by the `comp_rnf` pruning flag.
    pub fn canonical_arg_order(&self) -> Vec<usize> {
        let identity: Vec<usize> = (1..=self.arity()).collect();
        let mut seen = vec![false; self.arity() + 1];
        let mut order = Vec::new();
        grf_outer_arg_dfs(self, &identity, &mut seen, &mut order);
        order
    }

    /// Checks if this GRF is strictly in Rewire Normal Form (RNF).
    /// That is, it uses all arguments, and their first occurrences appear in canonical order `[1..n]`.
    pub fn is_rnf(&self) -> bool {
        self.used_args().len() == self.arity()
            && self.canonical_arg_order() == (1..=self.arity()).collect::<Vec<_>>()
    }

    /// Returns the rewiring flexibility of this GRF.
    pub fn rewirability(&self) -> Rewirability {
        match &self.kind {
            GrfKind::Zero(_) | GrfKind::Proj(_, _) | GrfKind::Comp(_, _, _) | GrfKind::Min(_) => {
                Rewirability::Full
            }
            GrfKind::Rec(_, _) => Rewirability::CounterLocked,
            GrfKind::Succ => Rewirability::SuccLocked,
        }
    }

    /// Returns true if this is a Primitive Recursive Function (no Min anywhere).
    pub fn is_prf(&self) -> bool {
        match &self.kind {
            GrfKind::Zero(_) | GrfKind::Succ | GrfKind::Proj(_, _) => true,
            GrfKind::Comp(h, gs, _) => h.is_prf() && gs.iter().all(Grf::is_prf),
            GrfKind::Rec(g, h) => g.is_prf() && h.is_prf(),
            GrfKind::Min(_) => false,
        }
    }

    /// Returns `Some(k)` if this function is structurally equivalent to
    /// `λ(args). args[2] + k`, i.e. a chain of k Succs applied to P2.
    /// Used to accelerate R(g, h) when h is an affine step on the accumulator.
    pub fn acc_plus_k(&self) -> Option<SmallNat> {
        match &self.kind {
            GrfKind::Proj(_, 2) => Some(0),
            GrfKind::Comp(outer, inners, _) => {
                if let GrfKind::Succ = &outer.kind {
                    if inners.len() == 1 {
                        return inners[0].acc_plus_k().map(|k| k + 1);
                    }
                }
                None
            }
            _ => None,
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
                Ok(Grf::zero_atom(k))
            }
            'S' => Ok(Grf::succ_atom()),
            'P' => {
                Self::consume(chars, '(')?;
                let k = Self::parse_num(chars)?;
                Self::consume(chars, ',')?;
                let i = Self::parse_num(chars)?;
                Self::consume(chars, ')')?;
                Ok(Grf::proj_atom(k, i))
            }
            'C' => {
                // 0-arg form: Ck(h) where k is the outer arity encoded as a decimal integer.
                if chars.peek().map_or(false, |c| c.is_ascii_digit()) {
                    let k = Self::parse_num(chars)?;
                    Self::consume(chars, '(')?;
                    let h = Self::parse_expr(chars)?;
                    Self::consume(chars, ')')?;
                    return Ok(Grf::comp0(h, k));
                }
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
                Ok(Grf::rec(g, h))
            }
            'M' => {
                Self::consume(chars, '(')?;
                let f = Self::parse_expr(chars)?;
                Self::consume(chars, ')')?;
                Ok(Grf::min(f))
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

/// Recursively collects outer-arg indices in DFS first-occurrence order.
///
/// `map[i-1]` is the outer-arg index for inner arg `i`; 0 means synthetic
/// (not an outer arg, e.g. Rec's accumulator or Min's search variable).
fn grf_outer_arg_dfs(g: &Grf, map: &[usize], seen: &mut Vec<bool>, order: &mut Vec<usize>) {
    match &g.kind {
        GrfKind::Proj(_, i) => {
            let outer = map[i - 1];
            if outer > 0 && !seen[outer] {
                seen[outer] = true;
                order.push(outer);
            }
        }
        GrfKind::Zero(_) => {}
        GrfKind::Succ => {
            // Succ uses its single inner arg directly (no Proj node).
            debug_assert_eq!(map.len(), 1);
            let outer = map[0];
            if outer > 0 && !seen[outer] {
                seen[outer] = true;
                order.push(outer);
            }
        }
        GrfKind::Comp(_, gs, _) => {
            // Outer args flow into gs; head h only sees abstract inner positions.
            for gi in gs {
                grf_outer_arg_dfs(gi, map, seen, order);
            }
        }
        GrfKind::Rec(base, step) => {
            let k = base.arity() + 1; // outer arity of this Rec
                                      // Counter = outer map[0]; always encountered first for Rec.
            let outer_counter = map[0];
            if outer_counter > 0 && !seen[outer_counter] {
                seen[outer_counter] = true;
                order.push(outer_counter);
            }
            // base's arg j (1-indexed) → outer map[j]  (j = 1..k-1)
            let map_base: Vec<usize> = (1..k).map(|j| map[j]).collect();
            grf_outer_arg_dfs(base, &map_base, seen, order);
            // step: arg 1 → map[0] (counter), arg 2 → 0 (acc), arg j≥3 → map[j-2]
            let mut map_step = vec![map[0], 0usize];
            for j in 3..=(k + 1) {
                map_step.push(map[j - 2]);
            }
            grf_outer_arg_dfs(step, &map_step, seen, order);
        }
        GrfKind::Min(inner) => {
            let k = g.arity();
            // inner: arg 1 → 0 (search var), arg j≥2 → map[j-2]
            let mut map_inner = vec![0usize];
            for i in 0..k {
                map_inner.push(map[i]);
            }
            grf_outer_arg_dfs(inner, &map_inner, seen, order);
        }
    }
}

impl fmt::Display for Grf {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            GrfKind::Zero(k) => write!(f, "Z{k}"),
            GrfKind::Succ => write!(f, "S"),
            GrfKind::Proj(k, i) => write!(f, "P({k},{i})"),
            GrfKind::Comp(h, gs, k) => {
                if gs.is_empty() {
                    // 0-arg Comp: Ck(h) format encodes the outer arity for round-tripping.
                    write!(f, "C{k}({h})")
                } else {
                    write!(f, "C({h}")?;
                    for g in gs {
                        write!(f, ", {g}")?;
                    }
                    write!(f, ")")
                }
            }
            GrfKind::Rec(g, h) => write!(f, "R({g}, {h})"),
            GrfKind::Min(func) => write!(f, "M({func})"),
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
    fn test_is_positive_for_pos_arg() {
        // Atoms
        assert!(grf!("S").is_positive_for_pos_arg(1)); // Succ always positive
        assert!(grf!("P(1,1)").is_positive_for_pos_arg(1)); // Proj to arg1
        assert!(grf!("P(2,2)").is_positive_for_pos_arg(2)); // Proj to arg2
        assert!(!grf!("Z0").is_positive_for_pos_arg(1)); // always 0
        assert!(!grf!("P(2,2)").is_positive_for_pos_arg(1)); // returns arg2, not arg1

        // Rec j=1: true iff step is never_zero (counter > 0 → h fires once)
        assert!(grf!("R(Z0, S)").is_positive_for_pos_arg(1)); // step=S never_zero
        assert!(grf!("R(P(1,1), C(S,P(3,2)))").is_positive_for_pos_arg(1)); // step C(S,...) never_zero
        assert!(!grf!("R(P(1,1), P(3,2))").is_positive_for_pos_arg(1)); // step P(3,2) not never_zero, g not never_zero
                                                                        // R(S, P(3,2)): is_never_zero (P2 echoes acc which started at S(x)≥1), so positive for any j
        assert!(grf!("R(S, P(3,2))").is_positive_for_pos_arg(1));
        // R(S, P(3,3)): step returns outer arg (not acc), so NOT always positive even for n≥1
        assert!(!grf!("R(S, P(3,3))").is_positive_for_pos_arg(1));

        // Rec j=2: g positive for arg1, h positive for arg2 (acc)
        // R(P(2,1), C(S,P(4,1))): g=P(2,1) pos for arg1, h=C(S,...) never_zero → pos for arg2
        assert!(grf!("R(P(2,1), C(S,P(4,1)))").is_positive_for_pos_arg(2));
        // g=Z(1) not pos for arg1 → false
        assert!(!grf!("R(Z1, C(S,P(3,2)))").is_positive_for_pos_arg(2));

        // is_never_zero implies is_positive_for_pos_arg for any j
        assert!(grf!("S").is_positive_for_pos_arg(99));
        assert!(grf!("C(S, Z0)").is_positive_for_pos_arg(1));

        // The motivating example: R(S, R(P(2,1), C(S,P(4,1)))) is now never_zero,
        // which implies is_positive_for_pos_arg for any j.
        assert!(grf!("R(S, R(P(2,1), C(S,P(4,1))))").is_never_zero());
        assert!(grf!("R(S, R(P(2,1), C(S,P(4,1))))").is_positive_for_pos_arg(1));

        // Comp: h positive for arg1, gs[0] positive for arg j
        assert!(grf!("C(R(Z0,S), P(1,1))").is_positive_for_pos_arg(1));
        assert!(!grf!("C(R(Z0,S), P(2,2))").is_positive_for_pos_arg(1));

        // Comp: h = Proj to position p, delegate to gs[p-1]
        assert!(grf!("C(P(2,1), R(Z0,S), Z0)").is_positive_for_pos_arg(1));
        assert!(!grf!("C(P(2,2), R(Z0,S), Z0)").is_positive_for_pos_arg(1));
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
        let outer = Grf::rec(Grf::zero_atom(0), inner);
        assert!(!outer.used_args().contains(&2));
    }

    #[test]
    fn test_used_args_min() {
        // M(P(1,1)): f(i)=i, f uses {1} (i, internal). Min's args: f's j>=2 → none.
        assert_eq!(ua("M(P(1,1))"), set(&[]));
        // M(P(2,2)): f(i,x)=x, f uses {2} → Min's arg 1.
        assert_eq!(ua("M(P(2,2))"), set(&[1]));
    }

    fn cao(s: &str) -> Vec<usize> {
        s.parse::<Grf>().unwrap().canonical_arg_order()
    }

    #[test]
    fn test_canonical_arg_order_atoms() {
        assert_eq!(cao("Z0"), vec![] as Vec<usize>);
        assert_eq!(cao("S"), vec![1]);
        assert_eq!(cao("P(1,1)"), vec![1]);
        // P(2,1) uses only arg 1 — args appear as [1].
        assert_eq!(cao("P(2,1)"), vec![1]);
        // P(2,2) uses only arg 2 — first (and only) outer arg seen is 2, not 1.
        assert_eq!(cao("P(2,2)"), vec![2]);
    }

    #[test]
    fn test_canonical_arg_order_comp() {
        // C(S, P(2,1)): gs=[P(2,1)], first outer arg = 1. Canonical.
        assert_eq!(cao("C(S,P(2,1))"), vec![1]);
        // C(S, P(2,2)): gs=[P(2,2)], first outer arg = 2. Non-canonical.
        assert_eq!(cao("C(S,P(2,2))"), vec![2]);
        // C(P(2,1), P(3,2), P(3,1)): gs traversed in order: P(3,2) sees 2 first,
        // P(3,1) sees 1 second. Order = [2, 1]. Non-canonical.
        assert_eq!(cao("C(P(2,1),P(3,2),P(3,1))"), vec![2, 1]);
        // C(P(2,1), P(3,1), P(3,2)): gs = [P(3,1), P(3,2)]. Order = [1, 2]. Canonical.
        assert_eq!(cao("C(P(2,1),P(3,1),P(3,2))"), vec![1, 2]);
    }

    #[test]
    fn test_canonical_arg_order_rec() {
        // add = R(P(1,1), C(S,P(3,2))): arity 2.
        // Counter (outer 1) seen first. base=P(1,1): base arg 1 → outer 2.
        // Order = [1, 2]. Canonical.
        assert_eq!(cao("R(P(1,1),C(S,P(3,2)))"), vec![1, 2]);

        // R(P(2,2), C(P(2,1),P(4,3),P(4,1))): arity 3.
        // Counter (outer 1) first. base=P(2,2): base arg 2 → outer 3. Second = 3.
        // step gs=[P(4,3),P(4,1)]: P(4,3) sees step arg 3 → outer 2. Third = 2.
        // Order = [1, 3, 2]. Non-canonical.
        assert_eq!(cao("R(P(2,2),C(P(2,1),P(4,3),P(4,1)))"), vec![1, 3, 2]);
    }

    #[test]
    fn test_canonical_arg_order_min() {
        // M(P(2,2)): inner=P(2,2) uses inner arg 2 → outer arg 1. Order = [1]. Canonical.
        assert_eq!(cao("M(P(2,2))"), vec![1]);
        // M(P(2,1)): inner=P(2,1) uses inner arg 1 (search var, synthetic). Order = [].
        assert_eq!(cao("M(P(2,1))"), vec![] as Vec<usize>);
    }

    #[test]
    fn test_acc_plus_k() {
        assert_eq!(Grf::proj_atom(3, 2).acc_plus_k(), Some(0));
        assert_eq!(Grf::proj_atom(3, 1).acc_plus_k(), None);
        assert_eq!(Grf::zero_atom(2).acc_plus_k(), None);
        // C(S, P(3,2)) → Some(1)
        let cs_p2 = Grf::comp(Grf::succ_atom(), vec![Grf::proj_atom(3, 2)]);
        assert_eq!(cs_p2.acc_plus_k(), Some(1));
        // C(S, C(S, P(3,2))) → Some(2)
        let cs_cs_p2 = Grf::comp(Grf::succ_atom(), vec![cs_p2]);
        assert_eq!(cs_cs_p2.acc_plus_k(), Some(2));
        assert_eq!(grf!("C(S, C(S, C(S, S)))").acc_plus_k(), None);
        assert_eq!(grf!("C(S, C(S, C(S, Z0)))").acc_plus_k(), None);
        assert_eq!(grf!("C(S, C(S, C(S, P(1, 1))))").acc_plus_k(), None);
        assert_eq!(grf!("C(S, C(S, C(S, P(3, 3))))").acc_plus_k(), None);
    }

    #[test]
    fn test_is_never_zero_preservation() {
        // C(b, P(1,1), S) is never zero where b = R(P(1,1), R(P(2,1), C(S, P(4,2))))
        let b = grf!("R(P(1,1), R(P(2,1), C(S, P(4,2))))");
        let inner1 = grf!("P(1,1)");
        let inner2 = grf!("S");
        let comp = Grf::comp(b.clone(), vec![inner1, inner2]);
        assert!(comp.is_never_zero());

        // But b itself is not never zero because its base case (P(1,1)) can be zero.
        assert!(!b.is_never_zero());

        // a = R(P(2,1), C(S, P(4,2))) preserves positivity for arg 2
        let a = grf!("R(P(2,1), C(S, P(4,2)))");
        assert!(a.is_positive_for_pos_arg(2));

        // b preserves positivity for arg 2
        assert!(b.is_positive_for_pos_arg(2));
    }

    #[test]
    fn test_always_pos_rec_param() {
        // From min_prf 12 holdout: M(R(C(S, Z0), R(S, R(P(2,2), C(S, P(4,2))))))
        let a = Grf::succ_atom();
        let b = grf!("R(P(2,2), C(S, P(4,2)))");
        let c = Grf::rec(a.clone(), b.clone());

        assert!(a.is_positive_for_pos_arg(1));
        assert!(b.is_positive_for_pos_arg(3));
        assert!(c.is_positive_for_pos_arg(2));

        let d = grf!("R(C(S, Z0), R(S, R(P(2,2), C(S, P(4,2)))))");
        assert!(d.is_never_zero());
    }
}
