/// Show GRF optimizations applied node-by-node.
///
/// Usage examples:
///   show_opt ack_worm
///   show_opt "C(S, Z1)"
///   show_opt ack_worm --no-fingerprint
///   show_opt pred --db-max-size 10
///
/// Named functions: pred, not, sgn, plus2, double, rmonus, mod2, shift,
///   rmonus_odd, div2, div2k, dec_append, dec_append_n, bit, pop_k,
///   ack_step, ack_loop, ack_worm, init_list, ack, omega, graham
use clap::Parser;
use gen_rec::example_ack::{
    ack, ack_loop, ack_step, ack_worm, add, bit, dec_append, dec_append_n, div2, div2k,
    graham, init_list, mod2, not, omega, plus2, pop_k, pred, rmonus, rmonus_odd, sgn, shift,
};
use gen_rec::fingerprint::FingerprintDb;
use gen_rec::grf::Grf;
use gen_rec::novel_db::{fingerprint_db_from_dir, fingerprint_db_from_file};
use gen_rec::optimize::{opt_fingerprint, opt_inline_proj};
use std::path::PathBuf;

const WRAP: usize = 72;

#[derive(Parser, Debug)]
#[command(
    about = "Show GRF optimizations with per-node diffs",
    long_about = "Applies optimization passes to a GRF and prints each substitution\n\
                  made, showing where in the AST it occurred and the before/after\n\
                  expression. EXPR may be a raw GRF string like \"C(S,Z1)\" or a\n\
                  named function like \"ack_worm\"."
)]
struct Args {
    /// GRF expression or named function (pred, ack_worm, ...).
    expr: String,

    /// Skip the opt_inline_proj pass.
    #[arg(long)]
    no_inline_proj: bool,

    /// Skip the opt_fingerprint pass.
    #[arg(long)]
    no_fingerprint: bool,

    /// Load fingerprint DB from a single novel DB file.
    /// Mutually exclusive with --db-dir and --db-max-size / --db-max-arity.
    #[arg(long, value_name = "PATH")]
    db_path: Option<PathBuf>,

    /// Load fingerprint DB from all .db files in this directory.
    /// Mutually exclusive with --db-path.
    #[arg(long, value_name = "DIR")]
    db_dir: Option<PathBuf>,

    /// Max GRF size included in the fingerprint DB (ignored if --db-path/--db-dir is set).
    #[arg(long, default_value_t = 8)]
    db_max_size: usize,

    /// Max arity included in the fingerprint DB (ignored if --db-path/--db-dir is set).
    #[arg(long, default_value_t = 3)]
    db_max_arity: usize,

    /// Include Minimization in the fingerprint DB (ignored if --db-path/--db-dir is set).
    #[arg(long)]
    db_allow_min: bool,

    /// Simulation step budget used when fingerprinting (0 = unlimited).
    #[arg(long, default_value_t = 10_000)]
    max_steps: u64,
}

// ── AST diff ─────────────────────────────────────────────────────────────────

struct Change {
    path: String,
    before: Grf,
    after: Grf,
}

/// Recursively walk `before` and `after` in parallel.  When they diverge and
/// the divergence cannot be explained by a child change (i.e. the top-level
/// variants or arg counts differ), record the whole node as a substitution.
fn collect_diff(before: &Grf, after: &Grf, path: &str, out: &mut Vec<Change>) {
    if before == after {
        return;
    }
    match (before, after) {
        (Grf::Comp(h1, gs1, _), Grf::Comp(h2, gs2, _)) if gs1.len() == gs2.len() => {
            collect_diff(h1, h2, &format!("{path}.head"), out);
            for (i, (g1, g2)) in gs1.iter().zip(gs2.iter()).enumerate() {
                collect_diff(g1, g2, &format!("{path}.arg{i}"), out);
            }
        }
        (Grf::Rec(g1, h1), Grf::Rec(g2, h2)) => {
            collect_diff(g1, g2, &format!("{path}.base"), out);
            collect_diff(h1, h2, &format!("{path}.step"), out);
        }
        (Grf::Min(f1), Grf::Min(f2)) => {
            collect_diff(f1, f2, &format!("{path}.inner"), out);
        }
        // Variants differ or arg counts differ — the whole node was replaced.
        _ => out.push(Change {
            path: path.to_string(),
            before: before.clone(),
            after: after.clone(),
        }),
    }
}

fn diff(before: &Grf, after: &Grf) -> Vec<Change> {
    let mut changes = Vec::new();
    collect_diff(before, after, "root", &mut changes);
    changes
}

// ── display ──────────────────────────────────────────────────────────────────

fn trunc(s: &str) -> String {
    // GRF strings are ASCII, so byte indexing is safe.
    if s.len() <= WRAP {
        s.to_string()
    } else {
        format!("{}...", &s[..WRAP])
    }
}

fn rule(label: &str) -> String {
    let dashes = WRAP + 4;
    let used = label.len() + 4; // "── <label> "
    let trail = dashes.saturating_sub(used);
    format!("── {} {}", label, "─".repeat(trail))
}

fn print_pass(title: &str, before: &Grf, after: &Grf) {
    println!();
    println!("{}", rule(title));

    let changes = diff(before, after);
    if changes.is_empty() {
        println!("  No changes.");
        return;
    }

    let saved = before.size() as i64 - after.size() as i64;
    println!(
        "  {} substitution(s)  [{} → {} nodes, −{}]",
        changes.len(),
        before.size(),
        after.size(),
        saved,
    );
    for (i, ch) in changes.iter().enumerate() {
        println!();
        println!(
            "  {}. {}  [size {} → {}]",
            i + 1,
            ch.path,
            ch.before.size(),
            ch.after.size(),
        );
        println!("     was: {}", trunc(&ch.before.to_string()));
        println!("     now: {}", trunc(&ch.after.to_string()));
    }
}

// ── named function lookup ─────────────────────────────────────────────────────

fn resolve(expr: &str) -> Result<Grf, String> {
    let grf = match expr {
        "pred" => pred(),
        "not" => not(),
        "sgn" => sgn(),
        "plus2" => plus2(),
        "add" => add(),
        "rmonus" => rmonus(),
        "mod2" => mod2(),
        "shift" => shift(),
        "rmonus_odd" => rmonus_odd(),
        "div2" => div2(),
        "div2k" => div2k(),
        "dec_append" => dec_append(),
        "dec_append_n" => dec_append_n(),
        "bit" => bit(),
        "pop_k" => pop_k(),
        "ack_step" => ack_step(),
        "ack_loop" => ack_loop(),
        "ack_worm" => ack_worm(),
        "init_list" => init_list(),
        "ack" => ack(),
        "omega" => omega(),
        "graham" => graham(),
        _ => return expr.parse::<Grf>().map_err(|e| format!("parse error: {e}")),
    };
    Ok(grf)
}

// ── main ─────────────────────────────────────────────────────────────────────

fn main() {
    let args = Args::parse();

    let original = match resolve(&args.expr) {
        Ok(g) => g,
        Err(e) => {
            eprintln!("error: {e}");
            std::process::exit(1);
        }
    };

    println!(
        "Input [arity={}, size={}]:",
        original.arity(),
        original.size()
    );
    println!("  {}", original.to_string());

    let mut current = original.clone();

    // Pass 1: opt_inline_proj
    if !args.no_inline_proj {
        let after = opt_inline_proj(current.clone());
        print_pass("opt_inline_proj", &current, &after);
        current = after;
    }

    // Pass 2: opt_fingerprint
    if !args.no_fingerprint {
        let db = if let Some(ref path) = args.db_path {
            eprint!("Loading fingerprint DB from {}... ", path.display());
            match fingerprint_db_from_file(path, args.max_steps) {
                Ok(db) => { eprintln!("done."); db }
                Err(e) => { eprintln!(); eprintln!("error: {e}"); std::process::exit(1); }
            }
        } else if let Some(ref dir) = args.db_dir {
            eprint!("Loading fingerprint DB from {}/ ... ", dir.display());
            match fingerprint_db_from_dir(dir, args.max_steps) {
                Ok(db) => { eprintln!("done."); db }
                Err(e) => { eprintln!(); eprintln!("error: {e}"); std::process::exit(1); }
            }
        } else {
            eprint!(
                "Building fingerprint DB (size≤{}, arity≤{})... ",
                args.db_max_size, args.db_max_arity
            );
            let db = FingerprintDb::build(
                args.db_max_size,
                args.db_max_arity,
                args.db_allow_min,
                args.max_steps,
            );
            eprintln!("done.");
            db
        };

        let title = format!(
            "opt_fingerprint  DB: size≤{}, arity≤{}",
            args.db_max_size, args.db_max_arity
        );
        let after = opt_fingerprint(current.clone(), &db);
        print_pass(&title, &current, &after);
        current = after;
    }

    // Summary
    let total_saved = original.size() as i64 - current.size() as i64;
    println!();
    println!("{}", rule("summary"));
    if total_saved == 0 {
        println!("  No changes.  [size={}]", current.size());
    } else {
        println!(
            "  {} → {}  (−{} nodes, {:.1}%)",
            original.size(),
            current.size(),
            total_saved,
            100.0 * total_saved as f64 / original.size() as f64,
        );
        println!();
        println!("  {}", current.to_string());
    }
}
