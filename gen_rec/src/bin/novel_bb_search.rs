/// BBµ search using novel-sub-expression enumeration.
///
/// Instead of exhaustively enumerating all GRFs, this binary uses `NovelEnumerator`
/// to restrict candidates to those whose sub-expressions are all canonical
/// (minimal representatives of their equivalence class).  The correctness argument:
/// any GRF_0 computing value v has a rewritten form with canonical sub-expressions
/// that also computes v and is no larger — so BBµ(n) is attained by some canonical
/// GRF of size n.  This dramatically shrinks the search space at large sizes.
use clap::Parser;
use gen_rec::grf::Grf;
use gen_rec::alias::AliasDb;
use gen_rec::novel_enum::NovelEnumerator;
use gen_rec::simulate::{simulate, Num};
use rayon::prelude::*;
use std::time::Instant;

#[derive(Parser, Debug)]
#[command(
    about = "Search for BBµ champions using novel-sub-expression enumeration",
    long_about = None
)]
struct Args {
    /// Maximum size to enumerate up to.
    max_size: usize,

    /// Maximum steps per simulation before giving up (0 = unlimited).
    #[arg(long, default_value_t = 100_000_000)]
    max_steps: u64,

    /// Number of canonical fingerprint inputs (larger = fewer false-positive equivalences).
    #[arg(long, default_value_t = 64)]
    fp_inputs: usize,

    /// Max steps for fingerprint computation (should be << max_steps).
    #[arg(long, default_value_t = 100_000)]
    fp_steps: u64,

    /// Include Minimization combinator (default: PRF only).
    #[arg(long)]
    allow_min: bool,

    /// Print per-(arity,size) memo stats after each size.
    #[arg(long)]
    verbose: bool,
}

struct SizeResult {
    size: usize,
    raw_count: usize,
    novel_count: usize,
    timed_out: usize,
    best_value: Option<Num>,
    best_exprs: Vec<String>,
    #[allow(dead_code)]
    elapsed_enum: f64,
    #[allow(dead_code)]
    elapsed_sim: f64,
}

fn main() {
    let args = Args::parse();

    println!(
        "Novel BBµ search: 0-arity {}, max_size={}, max_steps={}, fp_inputs={}, fp_steps={}, threads={}",
        if args.allow_min { "GRF" } else { "PRF" },
        args.max_size,
        args.max_steps,
        args.fp_inputs,
        args.fp_steps,
        rayon::current_num_threads(),
    );
    println!("{}", "=".repeat(90));

    let alias_db = AliasDb::default();
    let mut en = NovelEnumerator::new(args.fp_inputs, args.fp_steps, args.allow_min);
    let mut results: Vec<SizeResult> = Vec::new();
    let total_start = Instant::now();

    for size in 1..=args.max_size {
        // Build the memo for arity 0 at this size (and all dependencies).
        let enum_start = Instant::now();
        en.compute_size(0, size);
        let novel_count = en.candidates(0, size).len();

        // Get ALL size-n GRF_0 with canonical sub-expressions (no outer functional dedup).
        let raw: Vec<Grf> = en.raw_candidates_at_size(0, size);
        let raw_count = raw.len();
        let elapsed_enum = enum_start.elapsed().as_secs_f64();

        // Simulate in parallel.
        let sim_start = Instant::now();
        let outcomes: Vec<(Option<Num>, String)> = raw
            .par_iter()
            .map(|grf| {
                let (result, _) = simulate(grf, &[], args.max_steps);
                (result.into_value(), grf.to_string())
            })
            .collect();
        let elapsed_sim = sim_start.elapsed().as_secs_f64();

        let mut best_val: Option<Num> = None;
        let mut best_exprs: Vec<String> = Vec::new();
        let mut timed_out = 0usize;

        for (value, display) in outcomes {
            match value {
                None => timed_out += 1,
                Some(v) => {
                    let cmp = best_val
                        .as_ref()
                        .map_or(std::cmp::Ordering::Greater, |cur| v.cmp(cur));
                    match cmp {
                        std::cmp::Ordering::Greater => {
                            best_val = Some(v);
                            best_exprs = vec![display];
                        }
                        std::cmp::Ordering::Equal => best_exprs.push(display),
                        std::cmp::Ordering::Less => {}
                    }
                }
            }
        }

        let best_str = match &best_val {
            Some(v) => v.to_string(),
            None => "-".to_string(),
        };

        println!(
            "n={:>3}: best={:<8} raw={:<8} novel={:<8} holdouts={:<6} [{:.2}s enum={:.2}s sim={:.2}s]",
            size,
            best_str,
            raw_count,
            novel_count,
            timed_out,
            elapsed_enum + elapsed_sim,
            elapsed_enum,
            elapsed_sim,
        );
        const MAX_VIA: usize = 5;
        for expr in best_exprs.iter().take(MAX_VIA) {
            let grf: Grf = expr.parse().unwrap();
            println!("       via {}  [{}]", expr, alias_db.alias(&grf));
        }
        if best_exprs.len() > MAX_VIA {
            println!("       ... (+{} more tied expressions)", best_exprs.len() - MAX_VIA);
        }

        if args.verbose {
            let stats = en.memo_stats();
            // Count totals.
            let total_pairs = stats.len();
            let total_novel: usize = stats.iter().map(|&(_, _, n)| n).sum();
            eprintln!(
                "       memo: {} (arity,size) pairs, {} total novel GRFs",
                total_pairs, total_novel
            );
            // Print per-arity summary: arity → (max_size, total novel across sizes).
            let mut by_arity: std::collections::BTreeMap<usize, (usize, usize)> =
                std::collections::BTreeMap::new();
            for &(a, s, n) in &stats {
                let e = by_arity.entry(a).or_insert((0, 0));
                e.0 = e.0.max(s);
                e.1 += n;
            }
            let arity_lines: Vec<String> = by_arity
                .iter()
                .map(|(&a, &(max_s, total))| format!("a{}:s1..{}({})", a, max_s, total))
                .collect();
            eprintln!("       {}", arity_lines.join("  "));
        }

        results.push(SizeResult {
            size,
            raw_count,
            novel_count,
            timed_out,
            best_value: best_val,
            best_exprs,
            elapsed_enum,
            elapsed_sim,
        });
    }

    let total_elapsed = total_start.elapsed().as_secs_f64();

    println!();
    println!("{}", "=".repeat(90));
    println!(
        "Novel BBµ_{} summary  (fp_inputs={}, fp_steps={}, max_steps={})",
        if args.allow_min { "GRF" } else { "PRF" },
        args.fp_inputs,
        args.fp_steps,
        args.max_steps,
    );
    println!("{}", "=".repeat(90));
    println!(
        "{:>4}  {:>8}  {:>8}  {:>8}  {:>8}  {}",
        "n", "BBµ(n)≥", "raw", "novel", "holdouts", "Champion"
    );
    println!("{}", "-".repeat(90));
    for r in &results {
        let max_val_str = match &r.best_value {
            Some(v) => v.to_string(),
            None => "-".to_string(),
        };
        let expr_str = if r.best_exprs.is_empty() {
            "-".to_string()
        } else {
            let raw = &r.best_exprs[0];
            let named = raw.parse::<Grf>().map(|g| alias_db.alias(&g))
                .unwrap_or_else(|_| raw.clone());
            if r.best_exprs.len() > 1 {
                format!("{named}  (+{} ties)", r.best_exprs.len() - 1)
            } else {
                named
            }
        };
        println!(
            "{:>4}  {:>8}  {:>8}  {:>8}  {:>8}  {}",
            r.size, max_val_str, r.raw_count, r.novel_count, r.timed_out, expr_str,
        );
    }
    println!("{}", "-".repeat(90));
    println!("Total time: {:.2}s", total_elapsed);
}
