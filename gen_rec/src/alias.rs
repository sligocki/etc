/// GRF alias catalogue: substitutes known sub-expressions with readable names.
///
/// Usage:
/// ```
/// use gen_rec::alias::AliasDb;
/// let db = AliasDb::default();
/// println!("{}", db.alias(&grf));
/// ```
use std::cmp::Reverse;

use crate::example_ack::{
    ack, ack_loop, ack_step, ack_worm, add, bit, dec_append, dec_append_n, div2, div2k, graham,
    init_list, mod2, not, omega, plus2, pop_k, pred, rmonus, rmonus_odd, sgn, shift,
};
use crate::examples::{ack_diag, constant, diag_rep, diag_succ, plus_n, polygonal, rep_succ};
use crate::grf::Grf;

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

        // ── example_ack named functions ──────────────────────────────────────
        push!("Pred",        pred());
        push!("Not",         not());
        push!("Sgn",         sgn());
        push!("Add",         add());
        push!("RMonus",      rmonus());
        push!("Mod2",        mod2());
        push!("Shift",       shift());
        push!("RMonusOdd",   rmonus_odd());
        push!("Div2",        div2());
        push!("Div2k",       div2k());
        push!("DecAppend",   dec_append());
        push!("DecAppendN",  dec_append_n());
        push!("Bit",         bit());
        push!("PopK",        pop_k());
        push!("AckStep",     ack_step());
        push!("AckLoop",     ack_loop());
        push!("AckWorm",     ack_worm());
        push!("InitList",    init_list());
        push!("Ack",         ack());
        push!("Omega",       omega());
        push!("Graham",      graham());

        // ── examples: fixed functions ────────────────────────────────────────
        push!("Tri",    crate::examples::triangular());
        push!("Square", crate::examples::square());

        // ── Plus[n]: skip n=1 (that's just S, left as-is) ───────────────────
        // plus2() from example_ack equals plus_n(2) from examples; one entry covers both.
        for n in 2..=max_param {
            push!(format!("Plus[{n}]"), plus_n(n));
        }

        // ── Polygonal[n] ─────────────────────────────────────────────────────
        for n in 1..=max_param {
            push!(format!("Polygonal[{n}]"), polygonal(n));
        }

        // ── K[n] constants ───────────────────────────────────────────────────
        for n in 0..=max_param {
            push!(format!("K[{n}]"), constant(n, 0));
            for k in 1..=3usize {
                push!(format!("K[{n}]_{k}"), constant(n, k));
            }
        }

        // ── RepSucc / DiagRep / DiagSucc applied to small bases ──────────────
        let bases: &[(&str, Grf)] = &[
            ("S",       Grf::Succ),
            ("Plus[2]", plus2()),
            ("Tri",     crate::examples::triangular()),
        ];
        for (bname, base) in bases {
            push!(format!("RepSucc[{bname}]"),  rep_succ(base.clone()));
            push!(format!("DiagRep[{bname}]"),  diag_rep(base.clone()));
            push!(format!("DiagSucc[{bname}]"), diag_succ(base.clone()));
        }

        // ── AckDiag[n, base] ─────────────────────────────────────────────────
        for n in 0..=max_param {
            for (bname, base) in bases {
                push!(format!("AckDiag[{n},{bname}]"), ack_diag(n, base.clone()));
            }
        }

        // Largest-GRF-first: more specific (larger) aliases win over fragments.
        entries.sort_by_key(|e| Reverse(e.grf.size()));

        Self { entries, colored }
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
        Self::new(6)
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
    use crate::grf::Grf;

    #[test]
    fn test_exact_atoms() {
        let db = AliasDb::default();
        assert_eq!(db.alias(&pred()), "Pred");
        assert_eq!(db.alias(&add()), "Add");
        assert_eq!(db.alias(&ack_worm()), "AckWorm");
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
    fn test_sub_expression() {
        let db = AliasDb::default();
        let grf = Grf::comp(add(), vec![plus2()]);
        assert_eq!(db.alias(&grf), "C(Add, Plus[2])");
    }

    #[test]
    fn test_ack_diag_1_s() {
        let db = AliasDb::new(2);
        let grf = ack_diag(1, Grf::Succ);
        assert_eq!(db.alias(&grf), "AckDiag[1,S]");
    }

    #[test]
    fn test_constant() {
        let db = AliasDb::default();
        assert_eq!(db.alias(&constant(3, 0)), "K[3]");
        assert_eq!(db.alias(&constant(0, 2)), "K[0]_2");
    }
}
