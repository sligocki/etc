/// Break down a GRF expression into its named R/M sub-expressions and show I/O tables.
///
/// Usage examples:
///   explore 'M(C(R(P1,1), R(R(S, P(2,1)), R(R(P(2,1), P(1,1)), P(2,1)))))'
///   explore 'R(Z0, P(2,1))' --grid 4
///   explore ack_worm --no-sim
use std::collections::BTreeMap;

use clap::Parser;
use gen_rec::alias::AliasDb;
use gen_rec::grf::{Grf, GrfKind};
use gen_rec::io_table::print_io_table;

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
    match &grf.kind {
        GrfKind::Comp(h, gs, _) => {
            collect_subexprs(h, seen, order);
            for g in gs {
                collect_subexprs(g, seen, order);
            }
        }
        GrfKind::Rec(g, h) => {
            collect_subexprs(g, seen, order);
            collect_subexprs(h, seen, order);
        }
        GrfKind::Min(f) => {
            collect_subexprs(f, seen, order);
        }
        _ => return,
    }
    if matches!(&grf.kind, GrfKind::Rec(..) | GrfKind::Min(..)) {
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
    match &grf.kind {
        GrfKind::Zero(k) => format!("Z{}", k),
        GrfKind::Succ => "S".to_string(),
        GrfKind::Proj(k, i) => format!("P({},{})", k, i),
        GrfKind::Comp(h, gs, k) => {
            let h_str = fmt_subst(h, names);
            if gs.is_empty() {
                format!("C{}({})", k, h_str)
            } else {
                let gs_str: Vec<String> = gs.iter().map(|g| fmt_subst(g, names)).collect();
                format!("C({}, {})", h_str, gs_str.join(", "))
            }
        }
        GrfKind::Rec(g, h) => format!("R({}, {})", fmt_subst(g, names), fmt_subst(h, names)),
        GrfKind::Min(f) => format!("M({})", fmt_subst(f, names)),
    }
}

fn main() {
    let args = Args::parse();

    let expr_str = if let Some((file_path, idx_str)) = args.expr.rsplit_once(':') {
        if let Ok(idx) = idx_str.parse::<usize>() {
            if std::path::Path::new(file_path).exists() {
                let content = std::fs::read_to_string(file_path).expect("Failed to read file");
                let entries = gen_rec::io_grl::parse_grf_entries(&content);
                if idx >= entries.len() {
                    eprintln!(
                        "error: index {} out of bounds for file {} ({} entries)",
                        idx,
                        file_path,
                        entries.len()
                    );
                    std::process::exit(1);
                }
                entries[idx].expr.clone()
            } else {
                args.expr.clone()
            }
        } else {
            args.expr.clone()
        }
    } else {
        args.expr.clone()
    };

    let grf = match AliasDb::default().resolve(&expr_str) {
        Ok(g) => g,
        Err(e) => {
            eprintln!("error: {e}");
            std::process::exit(1);
        }
    };

    let prf_tag = if grf.is_prf() { "PRF" } else { "GRF" };
    println!("Expression: {}", grf);
    println!(
        "Arity: {} | Size: {} | {}",
        grf.arity(),
        grf.size(),
        prf_tag
    );

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
            let used_str: String = used
                .iter()
                .map(|j| j.to_string())
                .collect::<Vec<_>>()
                .join(",");
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

            if let Some(sem) = sub.closed_form() {
                sem.print_rules(&name);
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
    if let Some(sem) = grf.closed_form() {
        sem.print_rules(&root_name);
    } else if !args.no_sim {
        print_io_table(&grf, args.grid, args.max_steps);
    }
}
