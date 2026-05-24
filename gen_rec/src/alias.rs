use std::cmp::Reverse;
/// GRF alias catalogue: substitutes known sub-expressions with readable names.
use std::collections::{HashMap, HashSet};

use crate::grf::{Grf, GrfKind};
use crate::mgrf::{lift_grf, parse_mgrf_with_modules, MgrfFile};

// Ordered list of embedded mgrf files. Earlier files take precedence for
// deduplication: a macro name present in both base.mgrf and bool_zero.mgrf
// (via `use base:{K}`) is only emitted from base.mgrf.
const MGRF_FILES: &[(&str, &str)] = &[
    ("base", include_str!("../mgrf/base.mgrf")),
    ("bool_zero", include_str!("../mgrf/bool_zero.mgrf")),
    ("func_rep", include_str!("../mgrf/func_rep.mgrf")),
];

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
    files: Vec<MgrfFile>,
    merged: MgrfFile,
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
        let mut seen_defs: HashSet<String> = HashSet::new();
        let mut seen_macros: HashSet<String> = HashSet::new();

        macro_rules! push {
            ($alias:expr, $grf:expr) => {
                entries.push(Entry {
                    alias: $alias.to_string(),
                    grf: $grf,
                });
            };
        }

        // All embedded files are available as modules so cross-file `use` resolves.
        let modules: HashMap<String, String> = MGRF_FILES
            .iter()
            .map(|(name, content)| (name.to_string(), content.to_string()))
            .collect();

        let mut files: Vec<MgrfFile> = Vec::new();
        for (_, content) in MGRF_FILES {
            let file = parse_mgrf_with_modules(content, &modules)
                .expect("embedded .mgrf should always parse");

            // Named GRFs — first file wins (no duplicates across files).
            // Skip atoms: S, Z_k, P^k_i are always rendered directly in alias_node
            // and must not be overridden (e.g. bool_zero defines True := Z and False1 := S).
            for (name, grf) in &file.defs {
                if seen_defs.insert(name.clone())
                    && !matches!(
                        &grf.kind,
                        GrfKind::Succ | GrfKind::Zero(_) | GrfKind::Proj(_, _)
                    )
                {
                    push!(name.clone(), grf.clone());
                }
            }

            // Num-macro families — first file wins.
            // num_macro_defs includes imported macros (e.g. ack_worm inherits K from
            // base via `use base:{K}`), so the seen_macros guard prevents double-emit.
            // Named GRFs (pushed above) take precedence for equal-size entries via
            // stable sort; atoms (Succ, Zero, Proj) are rendered directly in
            // alias_node and must never be overridden by a macro entry.
            for (macro_name, _) in &file.num_macro_defs {
                if seen_macros.insert(macro_name.clone()) {
                    for n in 0..=max_param {
                        if let Ok(g) = file.eval_expr(&format!("{macro_name}[{n}]")) {
                            if !matches!(
                                &g.kind,
                                GrfKind::Succ | GrfKind::Zero(_) | GrfKind::Proj(_, _)
                            ) {
                                push!(format!("{macro_name}[{n}]"), g);
                            }
                        }
                    }
                }
            }

            files.push(file);
        }

        // TODO: GRF-macro aliases (RepSucc[f], DiagRep[f], DiagS[f]) require structural
        // sub-expression matching — not yet supported. Concrete instantiations (AckWorm,
        // Graham, etc.) are already covered by the named defs loaded above.

        // ── Lifted versions: FuncName^k for 1–4 extra unused inputs ────────────
        // lift_grf fails for GRFs that cannot be lifted (e.g. S); those are skipped.
        let base: Vec<(String, Grf)> = entries
            .iter()
            .map(|e| (e.alias.clone(), e.grf.clone()))
            .collect();
        for (alias, grf) in &base {
            let ar = grf.arity();
            for ar_inc in 1..=4 {
                let new_ar = ar + ar_inc;
                if let Ok(w) = lift_grf(grf, new_ar) {
                    push!(format!("{alias}^{}", new_ar), w);
                }
            }
        }

        // Largest-GRF-first: more specific (larger) aliases win over fragments.
        entries.sort_by_key(|e| Reverse(e.grf.size()));

        let merged = MgrfFile::merge(&files.iter().collect::<Vec<_>>());
        Self {
            entries,
            colored,
            files,
            merged,
        }
    }

    /// Parse a mgrf expression, resolving alias names and macro families.
    ///
    /// Accepts full mgrf expression syntax: `R(Z, P1)`, `C(Add, S)`, named
    /// GRFs (`Add`, `AckWorm`), num-macros (`Plus[7]`, `Monus[3]`, `K^2[4]`),
    /// and standard raw-GRF atoms (`Z0`, `S`, `P(2,1)`).  Returns `Err` if
    /// the expression cannot be parsed or resolved.
    pub fn resolve(&self, expr: &str) -> Result<Grf, String> {
        let expr = expr.trim();
        // Try the merged context first so expressions that span multiple files
        // (e.g. DiagS[RepSucc[Tri]] — macros from func_rep, names from base) work.
        if let Ok(g) = self.merged.eval_expr(expr) {
            return Ok(g);
        }
        for file in &self.files {
            if let Ok(g) = file.eval_expr(expr) {
                return Ok(g);
            }
        }
        // Re-run merged to surface a useful error.
        Err(self.merged.eval_expr(expr).unwrap_err())
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
        match &grf.kind {
            GrfKind::Zero(k) => format!("Z{k}"),
            GrfKind::Succ => "S".to_string(),
            GrfKind::Proj(k, i) => format!("P({k},{i})"),
            GrfKind::Comp(h, gs, _) => {
                let head = self.alias_node(h);
                let args: Vec<String> = gs.iter().map(|g| self.alias_node(g)).collect();
                format!("C({}, {})", head, args.join(", "))
            }
            GrfKind::Rec(g, h) => {
                format!("R({}, {})", self.alias_node(g), self.alias_node(h))
            }
            GrfKind::Min(f) => format!("M({})", self.alias_node(f)),
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
    Some(AliasDb::new_colored(
        max_param,
        std::io::stdout().is_terminal(),
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::grf::Grf;

    fn pred() -> Grf {
        Grf::rec(Grf::zero_atom(0), Grf::proj_atom(2, 1))
    }
    fn plus2() -> Grf {
        Grf::comp(Grf::succ_atom(), vec![Grf::succ_atom()])
    }
    fn add() -> Grf {
        Grf::rec(
            Grf::proj_atom(1, 1),
            Grf::comp(Grf::succ_atom(), vec![Grf::proj_atom(3, 2)]),
        )
    }
    fn shift() -> Grf {
        Grf::rec(
            Grf::proj_atom(1, 1),
            Grf::comp(add(), vec![Grf::proj_atom(3, 2), Grf::proj_atom(3, 2)]),
        )
    }
    fn constant(n: usize, arity: usize) -> Grf {
        let mut f = Grf::zero_atom(arity);
        for _ in 0..n {
            f = Grf::comp(Grf::succ_atom(), vec![f]);
        }
        f
    }

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
        assert_eq!(db.alias(&Grf::succ_atom()), "S");
    }

    #[test]
    fn test_succ_lift_skipped() {
        use crate::mgrf::lift_grf;
        // lift_grf correctly rejects lifting S to arity 2.
        // The old weaken() returned S unchanged, which would have added a spurious
        // "Plus[1]^2" -> S (arity 1) entry if Plus[1]=S entered the catalog.
        assert!(lift_grf(&Grf::succ_atom(), 2).is_err());
        // Confirm S still aliases correctly and no spurious "S^k" entry overrides it.
        let db = AliasDb::default();
        assert_eq!(db.alias(&Grf::succ_atom()), "S");
    }

    #[test]
    fn test_plus2_aliased() {
        let db = AliasDb::default();
        assert_eq!(db.alias(&plus2()), "Plus[2]");
    }

    #[test]
    fn test_resolve_embedded_alias() {
        let db = AliasDb::default();
        let direct = db.resolve("C(Shift, S, S)").unwrap();
        let raw = db.resolve(&format!("C({}, S, S)", shift())).unwrap();
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
