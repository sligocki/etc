/// Display GRF structure, aliases, static properties, and LaTeX form.
///
/// Prints the fully-unaliased and fully-aliased forms, static properties
/// useful for understanding pruning decisions, and a LaTeX rendering.
///
/// Usage:
///   cargo run --bin info -- 'R(Z0, P(2,1))'
///   cargo run --bin info -- Add
use clap::Parser;
use gen_rec::alias::AliasDb;
use gen_rec::grf::{Grf, GrfKind};
use std::io::IsTerminal;

#[derive(Parser, Debug)]
#[command(
    about = "Display GRF structure, aliases, static properties, and LaTeX",
    long_about = "Prints raw and aliased forms, static properties, and LaTeX notation.\n\
                  For M(f) expressions the inner function is also analysed.\n\
                  EXPR may be a raw GRF string or an alias name like \"Add\"."
)]
struct Args {
    /// GRF expression or alias name (Pred, Add, Plus[2], ...).
    expr: String,

    /// Maximum n for parameterised macros (constant, plus_n, AckDiag, ...).
    #[arg(long, default_value_t = 10)]
    max_param: usize,
}

// ---------------------------------------------------------------------------
// LaTeX rendering
// ---------------------------------------------------------------------------

fn latex_num(n: usize) -> String {
    if n < 10 {
        format!("{n}")
    } else {
        format!("{{{n}}}")
    }
}

fn to_latex(grf: &Grf) -> String {
    match &grf.kind {
        GrfKind::Zero(k) => format!("Z^{}", latex_num(*k)),
        GrfKind::Succ => "S".to_string(),
        GrfKind::Proj(k, i) => format!("P^{}_{}", latex_num(*k), latex_num(*i)),
        GrfKind::Comp(h, gs, _) => {
            let mut args = vec![to_latex(h)];
            args.extend(gs.iter().map(to_latex));
            format!("C^{}({})", latex_num(grf.arity()), args.join(", "))
        }
        GrfKind::Rec(g, h) => {
            format!(
                "R^{}({}, {})",
                latex_num(grf.arity()),
                to_latex(g),
                to_latex(h)
            )
        }
        GrfKind::Min(f) => {
            format!("M^{}({})", latex_num(grf.arity()), to_latex(f))
        }
    }
}

// ---------------------------------------------------------------------------
// Static property display
// ---------------------------------------------------------------------------

fn print_static_props(grf: &Grf) {
    let arity = grf.arity();
    let used = grf.analysis.used_args.clone();
    let used_str: Vec<String> = used.iter().map(|i| i.to_string()).collect();
    println!("  is_never_zero            : {}", grf.is_never_zero());
    for j in 1..=arity.max(1) {
        println!(
            "  is_positive_for_pos_arg({}) : {}",
            j,
            grf.is_positive_for_pos_arg(j)
        );
    }
    println!("  used_args                : {{{}}}", used_str.join(", "));
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

fn main() {
    let args = Args::parse();
    let db = AliasDb::new_colored(args.max_param, std::io::stdout().is_terminal());

    let grf = match db.resolve(&args.expr) {
        Ok(g) => g,
        Err(e) => {
            eprintln!("error: {e}");
            std::process::exit(1);
        }
    };

    println!("raw   [arity={}, size={}]:", grf.arity(), grf.size());
    println!("  {}", grf);
    println!();
    println!("alias:");
    println!("  {}", db.alias(&grf));
    println!();
    println!("latex:");
    println!("  {}", to_latex(&grf));
    println!();
    println!("static properties:");
    print_static_props(&grf);

    if let GrfKind::Min(inner) = &grf.kind {
        println!();
        println!("inner [arity={}, size={}]:", inner.arity(), inner.size());
        println!("  {}", inner);
        println!();
        println!("inner static properties:");
        print_static_props(inner);
        println!();
        // TODO: check all enumeration pruning rules (comp_proj, comp_zero,
        // rec_zero_base, rec_proj_base, comp_assoc, comp_rnf, inline_proj,
        // rec_step_p2, min_trivial, min_dom, ...).
        // The stream-based approach (enumerate at this size/arity and check
        // membership) is logically clean but too slow for large GRFs.
        // The alternative is a per-flag predicate that mirrors for_each_grf's
        // conditions, but that duplicates logic and needs to be kept in sync.
        println!("pruning (min_dom subset):");
        let uses_search_var = inner.analysis.used_args.contains(&1);
        let never_zero = inner.is_never_zero();
        println!("  uses search var (arg 1) : {uses_search_var}");
        println!("  is_never_zero           : {never_zero}");
        if !uses_search_var {
            println!("  -> min_dom would prune (ignores search var)");
        } else if never_zero {
            println!("  -> min_dom would prune (never zero)");
        } else {
            println!("  -> not pruned by min_dom");
        }
    }
}
