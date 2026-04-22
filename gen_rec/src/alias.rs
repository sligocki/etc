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

/// A compiled catalogue of aliased GRFs for sub-expression lookup.
pub struct AliasDb {
    entries: Vec<Entry>,
}

impl AliasDb {
    /// Build the catalogue.  `max_param` controls how many levels of
    /// parameterised macros (constant, plus_n, AckDiag, …) are expanded.
    /// The default is 6.
    pub fn new(max_param: usize) -> Self {
        let mut entries: Vec<Entry> = Vec::new();

        macro_rules! push {
            ($alias:expr, $grf:expr) => {
                entries.push(Entry { alias: $alias.to_string(), grf: $grf });
            };
        }

        // ── example_ack named functions ──────────────────────────────────────
        push!("pred",         pred());
        push!("not",          not());
        push!("sgn",          sgn());
        push!("plus2",        plus2());
        push!("add",          add());
        push!("rmonus",       rmonus());
        push!("mod2",         mod2());
        push!("shift",        shift());
        push!("rmonus_odd",   rmonus_odd());
        push!("div2",         div2());
        push!("div2k",        div2k());
        push!("dec_append",   dec_append());
        push!("dec_append_n", dec_append_n());
        push!("bit",          bit());
        push!("pop_k",        pop_k());
        push!("ack_step",     ack_step());
        push!("ack_loop",     ack_loop());
        push!("ack_worm",     ack_worm());
        push!("init_list",    init_list());
        push!("ack",          ack());
        push!("omega",        omega());
        push!("graham",       graham());

        // ── examples: fixed functions ────────────────────────────────────────
        push!("tri",    crate::examples::triangular());
        push!("square", crate::examples::square());

        // ── examples: parameterised ──────────────────────────────────────────
        for n in 1..=max_param {
            push!(format!("plus_{n}"),       plus_n(n));
            push!(format!("polygonal({n})"), polygonal(n));
        }
        for n in 0..=max_param {
            push!(format!("K[{n}]"), constant(n, 0));
            for k in 1..=3usize {
                push!(format!("K[{n}]_{k}"), constant(n, k));
            }
        }

        // ── rep_succ / diag_rep / diag_succ applied to small bases ───────────
        let bases: &[(&str, Grf)] = &[
            ("S",     Grf::Succ),
            ("plus2", plus2()),
            ("tri",   crate::examples::triangular()),
        ];
        for (bname, base) in bases {
            push!(format!("rep_succ({bname})"),  rep_succ(base.clone()));
            push!(format!("diag_rep({bname})"),  diag_rep(base.clone()));
            push!(format!("diag_succ({bname})"), diag_succ(base.clone()));
        }

        // ── AckDiag[n, base] ─────────────────────────────────────────────────
        for n in 0..=max_param {
            for (bname, base) in bases {
                push!(format!("AckDiag[{n},{bname}]"), ack_diag(n, base.clone()));
            }
        }

        // Largest-GRF-first: more specific (larger) aliases win over fragments.
        entries.sort_by_key(|e| Reverse(e.grf.size()));

        Self { entries }
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
                return entry.alias.clone();
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::grf::Grf;

    #[test]
    fn test_exact_atoms() {
        let db = AliasDb::default();
        assert_eq!(db.alias(&pred()), "pred");
        assert_eq!(db.alias(&add()), "add");
        assert_eq!(db.alias(&ack_worm()), "ack_worm");
    }

    #[test]
    fn test_sub_expression() {
        let db = AliasDb::default();
        let grf = Grf::comp(add(), vec![plus2()]);
        assert_eq!(db.alias(&grf), "C(add, plus2)");
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
