/// Break down a GRF expression into its named R/M sub-expressions and show I/O tables.
///
/// Usage examples:
///   explore 'M(C(R(P1,1), R(R(S, P(2,1)), R(R(P(2,1), P(1,1)), P(2,1)))))'
///   explore 'R(Z0, P(2,1))' --grid 4
///   explore ack_worm --no-sim
use std::collections::BTreeMap;

use clap::Parser;
use gen_rec::alias::AliasDb;
use gen_rec::grf::Grf;
use gen_rec::io_table::print_io_table;
use gen_rec::sem::{sem_ignores_arg, sem_of, AffineFn, Sem};

#[derive(Parser, Debug)]
#[command(about = "Explore a GRF by naming its R/M sub-expressions and showing I/O tables")]
struct Args {
    /// GRF expression or alias name.
    expr: String,

    /// Simulation step budget per evaluation (0 = unlimited).
    #[arg(long, default_value_t = 100_000)]
    max_steps: u64,

    /// Inclusive maximum input value for I/O tables.
    #[arg(long, default_value_t = 10)]
    grid: u64,

    /// Skip I/O tables; show structural info only.
    #[arg(long)]
    no_sim: bool,
}

/// Collect unique R/M nodes in post-order, recording their string keys in `order`.
fn collect_subexprs(grf: &Grf, seen: &mut BTreeMap<String, Grf>, order: &mut Vec<String>) {
    match grf {
        Grf::Comp(h, gs, _) => {
            collect_subexprs(h, seen, order);
            for g in gs {
                collect_subexprs(g, seen, order);
            }
        }
        Grf::Rec(g, h) => {
            collect_subexprs(g, seen, order);
            collect_subexprs(h, seen, order);
        }
        Grf::Min(f) => {
            collect_subexprs(f, seen, order);
        }
        _ => return,
    }
    if matches!(grf, Grf::Rec(..) | Grf::Min(..)) {
        let key = grf.to_string();
        if !seen.contains_key(&key) {
            seen.insert(key.clone(), grf.clone());
            order.push(key);
        }
    }
}

/// Map index to name: 0→"a", 1→"b", …, 25→"z", 26→"aa", 27→"ab", …
fn idx_to_name(i: usize) -> String {
    if i < 26 {
        ((b'a' + i as u8) as char).to_string()
    } else {
        let outer = (i / 26) - 1;
        let inner = i % 26;
        format!(
            "{}{}",
            (b'a' + outer as u8) as char,
            (b'a' + inner as u8) as char
        )
    }
}

/// Format `grf`, substituting any sub-expression whose string key is in `names`.
/// Mirrors the Display impl in grf.rs but replaces named sub-trees with their names.
fn fmt_subst(grf: &Grf, names: &BTreeMap<String, String>) -> String {
    let key = grf.to_string();
    if let Some(name) = names.get(&key) {
        return name.clone();
    }
    match grf {
        Grf::Zero(k) => format!("Z{}", k),
        Grf::Succ => "S".to_string(),
        Grf::Proj(k, i) => format!("P({},{})", k, i),
        Grf::Comp(h, gs, k) => {
            let h_str = fmt_subst(h, names);
            if gs.is_empty() {
                format!("C{}({})", k, h_str)
            } else {
                let gs_str: Vec<String> = gs.iter().map(|g| fmt_subst(g, names)).collect();
                format!("C({}, {})", h_str, gs_str.join(", "))
            }
        }
        Grf::Rec(g, h) => format!("R({}, {})", fmt_subst(g, names), fmt_subst(h, names)),
        Grf::Min(f) => format!("M({})", fmt_subst(f, names)),
    }
}

// ---------------------------------------------------------------------------
// Semantic formula display
// ---------------------------------------------------------------------------

static ARG_NAMES: &[&str] = &["x", "y", "z", "w", "v", "u", "t", "s", "r", "q", "p"];

fn arg_name(pos: usize) -> &'static str {
    ARG_NAMES.get(pos).copied().unwrap_or("x")
}

fn decrement_n(v: &str, n: usize) -> String {
    match n {
        0 => v.to_string(),
        1 => format!("{}-1", v),
        n => format!("{}-{}", v, n),
    }
}

fn term_str(c: i64, v: &str) -> String {
    let vp = if c.abs() != 1 && v.chars().any(|ch| ch == '-' || ch == '+') {
        format!("({})", v)
    } else {
        v.to_string()
    };
    match c {
        1 => vp,
        -1 => format!("-{}", vp),
        _ => format!("{}*{}", c, vp),
    }
}

fn fmt_affine_expr(af: &AffineFn, vars: &[String]) -> String {
    let mut parts: Vec<String> = Vec::new();
    for (i, &c) in af.coeffs[1..].iter().enumerate() {
        if c != 0 {
            parts.push(term_str(c, &vars[i]));
        }
    }
    if af.coeffs[0] != 0 {
        parts.push(af.coeffs[0].to_string());
    }
    if parts.is_empty() {
        return "0".to_string();
    }
    let mut result = parts[0].clone();
    for p in &parts[1..] {
        if p.starts_with('-') {
            result.push_str(&format!(" - {}", &p[1..]));
        } else {
            result.push_str(&format!(" + {}", p));
        }
    }
    result
}

/// Format a rule's RHS. For Affine: formula. For Piecewise (rare zero_branch): inline ternary.
fn fmt_rule_rhs(sem: &Sem, vars: &[String]) -> String {
    match sem {
        Sem::Affine(af) => fmt_affine_expr(af, vars),
        Sem::Piecewise(pw) => {
            let x = vars[0].as_str();
            let zero_rhs = fmt_rule_rhs(&pw.zero_branch, &vars[1..]);
            let pos_var0 = decrement_n(x, 1);
            let pos_vars: Vec<String> =
                std::iter::once(pos_var0).chain(vars[1..].iter().cloned()).collect();
            let pos_rhs = fmt_rule_rhs(&pw.pos_branch, &pos_vars);
            format!("({x}=0 ? {zero_rhs} : {pos_rhs})")
        }
    }
}

/// Print multi-line pattern-matching rules for a Sem, prefixed with fn_name.
fn print_sem_rules(fn_name: &str, sem: &Sem) {
    let args: Vec<String> = (0..sem.arity()).map(|i| arg_name(i).to_string()).collect();
    emit_rules(fn_name, sem, &args, 0);
}

fn emit_rules(fn_name: &str, sem: &Sem, args: &[String], depth: usize) {
    match sem {
        Sem::Affine(af) => {
            let formula_args: Vec<String> = if args.is_empty() {
                vec![]
            } else {
                let first = decrement_n(&args[0], depth);
                std::iter::once(first).chain(args[1..].iter().cloned()).collect()
            };
            let lhs: Vec<String> = args
                .iter()
                .enumerate()
                .map(|(j, name)| {
                    if sem_ignores_arg(sem, j + 1) { "_".to_string() } else { name.clone() }
                })
                .collect();
            println!("  {}({}) = {}", fn_name, lhs.join(", "), fmt_affine_expr(af, &formula_args));
        }
        Sem::Piecewise(pw) => {
            let zero_lhs: Vec<String> = std::iter::once(depth.to_string())
                .chain(args[1..].iter().enumerate().map(|(j, name)| {
                    if sem_ignores_arg(&pw.zero_branch, j + 1) { "_".to_string() } else { name.clone() }
                }))
                .collect();
            println!("  {}({}) = {}", fn_name, zero_lhs.join(", "),
                     fmt_rule_rhs(&pw.zero_branch, &args[1..]));
            emit_rules(fn_name, &pw.pos_branch, args, depth + 1);
        }
    }
}

fn main() {
    let args = Args::parse();

    let grf = match AliasDb::default().resolve(&args.expr) {
        Ok(g) => g,
        Err(e) => {
            eprintln!("error: {e}");
            std::process::exit(1);
        }
    };

    let prf_tag = if grf.is_prf() { "PRF" } else { "GRF" };
    println!("Expression: {}", grf);
    println!("Arity: {} | Size: {} | {}", grf.arity(), grf.size(), prf_tag);

    // Collect R/M sub-expressions in post-order.
    let mut seen: BTreeMap<String, Grf> = BTreeMap::new();
    let mut order: Vec<String> = Vec::new();
    collect_subexprs(&grf, &mut seen, &mut order);

    // Remove the root from the sub-expression list so it is always shown expanded.
    let root_key = grf.to_string();
    if order.last() == Some(&root_key) {
        order.pop();
    }

    // Build name map: grf-string → name letter(s).
    let mut names: BTreeMap<String, String> = BTreeMap::new();
    for (i, key) in order.iter().enumerate() {
        names.insert(key.clone(), idx_to_name(i));
    }

    // Print each named sub-expression.
    if order.is_empty() {
        println!();
        println!("(No nested R/M sub-expressions)");
    } else {
        println!();
        println!("=== Sub-expressions ===");

        for (i, key) in order.iter().enumerate() {
            let sub = &seen[key];
            let name = idx_to_name(i);
            // Use only previously-assigned names so each sub-expression is shown
            // in terms of earlier ones (but never its own name).
            let partial_names: BTreeMap<String, String> = order[..i]
                .iter()
                .enumerate()
                .map(|(j, k)| (k.clone(), idx_to_name(j)))
                .collect();
            let subst = fmt_subst(sub, &partial_names);
            let prf = if sub.is_prf() { ", PRF" } else { "" };
            let used = sub.used_args();
            let used_str: String = used.iter().map(|j| j.to_string()).collect::<Vec<_>>().join(",");
            let used_tag = if used.is_empty() {
                String::new()
            } else {
                format!(", used={{{}}}", used_str)
            };

            println!();
            println!(
                "{} := {}    [arity {}, size {}{}{}]",
                name,
                subst,
                sub.arity(),
                sub.size(),
                prf,
                used_tag,
            );

            if let Some(sem) = sem_of(sub) {
                print_sem_rules(&name, &sem);
            } else if !args.no_sim {
                print_io_table(sub, args.grid, args.max_steps);
            }
        }
    }

    // Root summary.
    println!();
    println!("=== Root ===");
    let root_subst = fmt_subst(&grf, &names);
    println!(
        "{}    [arity {}, size {}]",
        root_subst,
        grf.arity(),
        grf.size()
    );
    let root_name = idx_to_name(order.len());
    if let Some(sem) = sem_of(&grf) {
        print_sem_rules(&root_name, &sem);
    } else if !args.no_sim {
        print_io_table(&grf, args.grid, args.max_steps);
    }
}
