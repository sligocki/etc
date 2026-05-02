/// GRF alias catalogue: substitutes known sub-expressions with readable names.
///
/// Usage:
/// ```
/// use gen_rec::alias::AliasDb;
/// let db = AliasDb::default();
/// println!("{}", db.alias(&grf));
/// ```
use std::collections::HashMap;
use std::cmp::Reverse;

use crate::grf::Grf;
use crate::mgrf::{parse_mgrf_with_modules, MgrfFile};

const BASE_MGRF:     &str = include_str!("../mgrf/base.mgrf");
const FUNC_REP_MGRF: &str = include_str!("../mgrf/func_rep.mgrf");
const ACK_WORM_MGRF: &str = include_str!("../mgrf/ack_worm.mgrf");

fn weaken(grf: &Grf) -> Grf {
    match grf {
        Grf::Zero(k) => Grf::Zero(k + 1),
        Grf::Succ => Grf::Succ,
        Grf::Proj(k, i) => Grf::Proj(k + 1, *i),
        Grf::Comp(h, gs, k) => Grf::Comp(
            Box::new(weaken(h)),
            gs.iter().map(|g| weaken(g)).collect(),
            k + 1,
        ),
        Grf::Rec(g, h) => Grf::Rec(Box::new(weaken(g)), Box::new(weaken(h))),
        Grf::Min(f) => Grf::Min(Box::new(weaken(f))),
    }
}

struct Entry {
    alias: String,
    grf: Grf,
}

const ALIAS_COLOR: &str = "\x1b[1;96m"; // bold bright-cyan
const RESET: &str = "\x1b[0m";

/// A compiled catalogue of aliased GRFs for sub-expression lookup.
pub struct AliasDb {
    entries: Vec<Entry>,
    colored: bool,
    base_file: MgrfFile,
    ack_file: MgrfFile,
}

impl AliasDb {
    /// Build the catalogue without color.  `max_param` controls how many levels
    /// of parameterised macros (constant, Plus[n], AckDiag, …) are expanded.
    /// The default is 6.
    pub fn new(max_param: usize) -> Self {
        Self::new_colored(max_param, false)
    }

    /// Like `new`, but wraps each matched alias in ANSI bold-cyan when `colored`
    /// is true.  Pass `std::io::stdout().is_terminal()` to auto-detect.
    pub fn new_colored(max_param: usize, colored: bool) -> Self {
        let mut entries: Vec<Entry> = Vec::new();

        macro_rules! push {
            ($alias:expr, $grf:expr) => {
                entries.push(Entry { alias: $alias.to_string(), grf: $grf });
            };
        }

        // Load GRF definitions from embedded .mgrf files.
        let modules: HashMap<String, String> = [
            ("base".to_string(),     BASE_MGRF.to_string()),
            ("func_rep".to_string(), FUNC_REP_MGRF.to_string()),
        ].into();
        let base_file = parse_mgrf_with_modules(BASE_MGRF, &modules)
            .expect("embedded base.mgrf should always parse");
        let ack_file = parse_mgrf_with_modules(ACK_WORM_MGRF, &modules)
            .expect("embedded ack_worm.mgrf should always parse");

        // ── All named GRFs from base.mgrf (Add, Pred, Div2, Pow2, Tri, …) ───
        for (name, grf) in &base_file.defs {
            push!(name.clone(), grf.clone());
        }

        // ── All named GRFs from ack_worm.mgrf (AckWorm, Graham, …) ──────────
        for (name, grf) in &ack_file.defs {
            push!(name.clone(), grf.clone());
        }

        // ── K[n], Plus[n], Monus[n], Mult[n] num-macro families ────────────────────
        for n in 1..=max_param {
            // Skip K[0] -> Z
            if let Ok(g) = base_file.eval_expr(&format!("K[{n}]")) {
                push!(format!("K[{n}]"), g);
            }
        }
        for n in 2..=max_param {
            // Skip Plus[1] -> S
            if let Ok(g) = base_file.eval_expr(&format!("Plus[{n}]")) {
                push!(format!("Plus[{n}]"), g);
            }
            // Skip Monus[0] -> P1 & Monus[1] -> Pred
            if let Ok(g) = base_file.eval_expr(&format!("Monus[{n}]")) {
                push!(format!("Monus[{n}]"), g);
            }
            // Skip Mult[1] (trivial)
            if let Ok(g) = base_file.eval_expr(&format!("Mult[{n}]")) {
                push!(format!("Mult[{n}]"), g);
            }
        }

        // TODO: GRF-macro aliases (RepSucc[f], DiagRep[f], DiagS[f]) require structural
        // sub-expression matching — not yet supported. Concrete instantiations (AckWorm,
        // Graham, etc.) are already covered by the named defs loaded above.

        // ── Weakened versions: FuncName_k for 1–2 extra unused inputs ──────────
        let base: Vec<(String, Grf)> = entries
            .iter()
            .map(|e| (e.alias.clone(), e.grf.clone()))
            .collect();
        for (alias, grf) in &base {
            let arity = grf.arity();
            let w1 = weaken(grf);
            push!(format!("{alias}^{}", arity + 1), w1.clone());
            push!(format!("{alias}^{}", arity + 2), weaken(&w1));
        }

        // Largest-GRF-first: more specific (larger) aliases win over fragments.
        entries.sort_by_key(|e| Reverse(e.grf.size()));

        Self { entries, colored, base_file, ack_file }
    }

    /// Parse a mgrf expression, resolving alias names and macro families.
    ///
    /// Accepts full mgrf expression syntax: `R(Z, P1)`, `C(Add, S)`, named
    /// GRFs (`Add`, `AckWorm`), num-macros (`Plus[7]`, `Monus[3]`, `K^2[4]`),
    /// and standard raw-GRF atoms (`Z0`, `S`, `P(2,1)`).  Returns `Err` if
    /// the expression cannot be parsed or resolved.
    pub fn resolve(&self, expr: &str) -> Result<Grf, String> {
        let expr = expr.trim();
        self.base_file.eval_expr(expr)
            .or_else(|_| self.ack_file.eval_expr(expr))
            .map_err(|_| {
                // Re-run base_file to surface a useful parse/resolve error.
                self.base_file.eval_expr(expr)
                    .unwrap_err()
            })
    }

    /// Rewrite `grf` bottom-up, substituting every matching sub-expression
    /// with its alias.  Returns the full expression as a string.
    pub fn alias(&self, grf: &Grf) -> String {
        self.alias_node(grf)
    }

    fn alias_node(&self, grf: &Grf) -> String {
        // Exact match wins before we recurse into children.
        for entry in &self.entries {
            if *grf == entry.grf {
                return if self.colored {
                    format!("{ALIAS_COLOR}{}{RESET}", entry.alias)
                } else {
                    entry.alias.clone()
                };
            }
        }
        match grf {
            Grf::Zero(k) => format!("Z{k}"),
            Grf::Succ => "S".to_string(),
            Grf::Proj(k, i) => format!("P({k},{i})"),
            Grf::Comp(h, gs, _) => {
                let head = self.alias_node(h);
                let args: Vec<String> = gs.iter().map(|g| self.alias_node(g)).collect();
                format!("C({}, {})", head, args.join(", "))
            }
            Grf::Rec(g, h) => {
                format!("R({}, {})", self.alias_node(g), self.alias_node(h))
            }
            Grf::Min(f) => format!("M({})", self.alias_node(f)),
        }
    }
}

impl Default for AliasDb {
    fn default() -> Self {
        Self::new(10)
    }
}

/// Convenience: build an `AliasDb` with color auto-detected from stdout.
pub fn alias_db_for_stdout(max_param: usize, no_alias: bool) -> Option<AliasDb> {
    if no_alias {
        return None;
    }
    use std::io::IsTerminal;
    Some(AliasDb::new_colored(max_param, std::io::stdout().is_terminal()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::example_ack::{pred, add, plus2};
    use crate::examples::{shift_succ, constant};
    use crate::grf::Grf;

    #[test]
    fn test_exact_atoms() {
        let db = AliasDb::default();
        assert_eq!(db.alias(&pred()), "Pred");
        assert_eq!(db.alias(&add()), "Add");
        // AckWorm from the mgrf file (Rust's ack_worm() is structurally different).
        assert_eq!(db.alias(&db.resolve("AckWorm").unwrap()), "AckWorm");
    }

    #[test]
    fn test_succ_not_aliased() {
        let db = AliasDb::default();
        // S stays as S, not Plus[1]
        assert_eq!(db.alias(&Grf::Succ), "S");
    }

    #[test]
    fn test_plus2_aliased() {
        let db = AliasDb::default();
        assert_eq!(db.alias(&plus2()), "Plus[2]");
    }

    #[test]
    fn test_resolve_embedded_alias() {
        let db = AliasDb::default();
        let direct = db.resolve("C(ShiftS, S, S)").unwrap();
        let raw = db.resolve(&format!("C({}, S, S)", shift_succ())).unwrap();
        assert_eq!(direct, raw);
    }

    #[test]
    fn test_sub_expression() {
        let db = AliasDb::default();
        let grf = Grf::comp(add(), vec![plus2()]);
        assert_eq!(db.alias(&grf), "C(Add, Plus[2])");
    }

    #[test]
    fn test_constant() {
        let db = AliasDb::default();
        assert_eq!(db.alias(&constant(3, 0)), "K[3]");
        assert_eq!(db.alias(&constant(1, 2)), "K[1]^2");
        assert_eq!(db.alias(&constant(0, 2)), "Z2");
    }
}
