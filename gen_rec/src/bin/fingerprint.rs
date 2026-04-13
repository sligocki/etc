/// Fingerprint GRFs to discover equivalence classes and guide pruning decisions.
///
/// Strategy: evaluate each GRF on a canonical set of inputs and group by
/// (arity, output-tuple).  Any GRF whose (arity, fingerprint) matches a
/// strictly smaller GRF is "cross-redundant" — a candidate for pruning in
/// the generator.
///
/// Outputs:
///   1. Summary table: total / novel / redundant counts per (size, arity)
///   2. Redundancy by structural category (what does the redundant GRF look like?)
///   3. Redundancy by canonical target (what smaller GRF is it equivalent to?)
use clap::Parser;
use gen_rec::enumerate::{count_grf, stream_grf};
use gen_rec::grf::Grf;
use gen_rec::pruning::PruningOpts;
use gen_rec::simulate::simulate;
use std::collections::HashMap;

#[derive(Parser, Debug)]
#[command(about = "Fingerprint GRFs to discover equivalence classes for pruning")]
struct Args {
    /// Maximum size to analyze.
    #[arg(default_value_t = 10)]
    max_size: usize,

    /// Minimum arity to analyze (default 1: 0-arity GRFs are constants, not true functions).
    #[arg(long, default_value_t = 1)]
    min_arity: usize,

    /// Maximum arity to analyze.
    #[arg(long, default_value_t = 3)]
    max_arity: usize,

    /// Max steps per simulation (keep small for fast fingerprinting).
    #[arg(long, default_value_t = 10_000)]
    max_steps: u64,

    /// Include Minimization combinator.
    #[arg(long)]
    allow_min: bool,

    /// Include trivial compositions C(Z,...) and C(P,...).
    #[arg(long)]
    include_trivial: bool,

    /// Disable composition canonicalisation (on by default).
    #[arg(long)]
    no_comp_assoc: bool,

    /// Disable R(Z(k), Z(k+2)) and R(Z(k), P(k+2,2)) pruning (on by default).
    #[arg(long)]
    no_rec_zero_base: bool,

    /// Disable C(R(g,h), Z(p), …) pruning (on by default).
    #[arg(long)]
    no_rec_zero_arg: bool,

    /// Max redundant examples to show per structural category.
    #[arg(long, default_value_t = 5)]
    samples: usize,

    /// How many canonical targets to show in the by-target breakdown (0 = all).
    #[arg(long, default_value_t = 20)]
    top_targets: usize,
}

// A fingerprint is one entry per canonical input: None = diverged, Some(s) = output.
type Fingerprint = Vec<Option<String>>;

fn compute_fp(grf: &Grf, inputs: &[Vec<u64>], max_steps: u64) -> Fingerprint {
    inputs
        .iter()
        .map(|inp| {
            let (result, _) = simulate(grf, inp, max_steps);
            result.into_value().map(|v| v.to_string())
        })
        .collect()
}

/// Generate the canonical input set for a given arity.
/// For arity k, produce all k-tuples drawn from {0 .. per_dim-1}
/// where per_dim is chosen so the total stays ≤ ~32 test cases.
fn canonical_inputs(arity: usize) -> Vec<Vec<u64>> {
    if arity == 0 {
        return vec![vec![]];
    }
    let per_dim: u64 = match arity {
        1 => 8,  // 8 inputs
        2 => 4,  // 16 inputs
        3 => 3,  // 27 inputs
        _ => 2,  // 2^arity inputs
    };
    let mut result: Vec<Vec<u64>> = vec![vec![]];
    for _ in 0..arity {
        let mut next = Vec::new();
        for prefix in &result {
            for v in 0..per_dim {
                let mut row = prefix.clone();
                row.push(v);
                next.push(row);
            }
        }
        result = next;
    }
    result
}

/// Coarse structural label for a GRF — used to group redundancy examples.
fn grf_category(grf: &Grf) -> &'static str {
    match grf {
        Grf::Rec(_, h) => match h.as_ref() {
            // Step function returns the accumulator unchanged → R always == base case extended
            Grf::Proj(_, 2) => "R(_,P(·,2))      [step=acc, result independent of n]",
            // Step function returns the step counter
            Grf::Proj(_, 1) => "R(_,P(·,1))      [step=counter]",
            // Step function returns one of the "rest" args (ignores acc and counter)
            Grf::Proj(k, i) if *i >= 3 && *i <= *k => {
                "R(_,P(·,≥3))     [step=rest_arg, ignores acc]"
            }
            // Step always returns 0
            Grf::Zero(_) => "R(_,Z)           [step=zero]",
            Grf::Comp(ih, _, _) if matches!(ih.as_ref(), Grf::Zero(_)) => {
                "R(_,C(Z,…))      [step=zero via comp]"
            }
            // Step is itself a Rec
            Grf::Rec(_, _) => "R(_,R(…))        [nested rec]",
            // Step is a Comp
            Grf::Comp(_, _, _) => "R(_,C(…))        [step=comp]",
            _ => "R(_,other)",
        },
        Grf::Comp(h, gs, _) => {
            let repeated = gs.len() > 1 && gs.iter().all(|g| g == &gs[0]);
            match h.as_ref() {
                // C(C(f,…), g,…) can sometimes be rewritten as C(f, C(…, g,…), …)
                Grf::Comp(_, _, _) => "C(C(·),·)        [nested comp in head]",
                Grf::Rec(_, _) if repeated => "C(R(·),g,g,…)    [rec head, repeated args]",
                Grf::Rec(_, _) => "C(R(·),·)        [rec in head]",
                Grf::Succ if gs.len() == 1 => "C(S,·)           [succ of single arg]",
                _ => "C(other)",
            }
        }
        Grf::Min(_) => "M(·)",
        _ => "atom",
    }
}

fn main() {
    let args = Args::parse();
    let opts = PruningOpts {
        skip_trivial: !args.include_trivial,
        comp_assoc: !args.no_comp_assoc,
        skip_rec_zero_base: !args.no_rec_zero_base,
        skip_rec_zero_arg: !args.no_rec_zero_arg,
    };

    println!(
        "Fingerprinting: max_size={}, arity={}..={}, allow_min={}, opts={:?}",
        args.max_size, args.min_arity, args.max_arity, args.allow_min, opts
    );
    println!("{}", "=".repeat(78));

    // (arity, fingerprint) → (min_size_seen, canonical_expr)
    let mut fp_db: HashMap<(usize, Fingerprint), (usize, String)> = HashMap::new();

    // Grouping 1: by structural category of the redundant GRF.
    // category → (total_cross_redundant, sample_examples)
    let mut by_cat: HashMap<&'static str, (usize, Vec<(usize, String, usize, String)>)> =
        HashMap::new();

    // Grouping 2: by canonical target (the smaller GRF it is equivalent to).
    // canonical_expr → (total_cross_redundant, sample_redundant_exprs)
    let mut by_target: HashMap<String, (usize, Vec<(usize, String)>)> = HashMap::new();

    // Per (size, arity): (total, novel, cross_redundant)
    let mut summary: Vec<(usize, usize, usize, usize, usize)> = Vec::new();

    for arity in args.min_arity..=args.max_arity {
        let inputs = canonical_inputs(arity);
        let n_inputs = inputs.len();

        // Print a header row for this arity so the user can see progress.
        let total_expected: usize = (1..=args.max_size)
            .map(|s| count_grf(s, arity, args.allow_min, opts))
            .sum();
        eprintln!(
            "arity={}: {} canonical inputs, ~{} GRFs total to process",
            arity, n_inputs, total_expected
        );

        for size in 1..=args.max_size {
            let mut total = 0usize;
            let mut novel = 0usize;
            let mut cross_redundant = 0usize;

            stream_grf(size, arity, args.allow_min, opts, &mut |grf: &Grf| {
                total += 1;
                let fp = compute_fp(grf, &inputs, args.max_steps);
                let key = (arity, fp);
                let expr = grf.to_string();

                match fp_db.get(&key) {
                    None => {
                        fp_db.insert(key, (size, expr));
                        novel += 1;
                    }
                    Some((min_size, min_expr)) => {
                        if *min_size < size {
                            cross_redundant += 1;

                            // Grouping 1: structural category of the redundant GRF.
                            let cat = grf_category(grf);
                            let entry = by_cat.entry(cat).or_default();
                            entry.0 += 1;
                            if entry.1.len() < args.samples {
                                entry.1.push((size, expr.clone(), *min_size, min_expr.clone()));
                            }

                            // Grouping 2: canonical target it is equivalent to.
                            let tgt = by_target.entry(min_expr.clone()).or_default();
                            tgt.0 += 1;
                            if tgt.1.len() < args.samples {
                                tgt.1.push((size, expr));
                            }
                        }
                        // same-size duplicates (two size-k GRFs with identical fingerprint)
                        // are not counted separately here
                    }
                }
            });

            summary.push((size, arity, total, novel, cross_redundant));
        }
    }

    // -----------------------------------------------------------------------
    // Print summary table
    // -----------------------------------------------------------------------
    println!(
        "{:>4}  {:>5}  {:>10}  {:>8}  {:>9}  {:>7}",
        "size", "arity", "total", "novel", "redundant", "novel%"
    );
    println!("{}", "-".repeat(58));
    let mut prev_arity = 999usize;
    for (size, arity, total, novel, redund) in &summary {
        if *arity != prev_arity {
            if prev_arity != 999 {
                println!();
            }
            prev_arity = *arity;
        }
        let pct = if *total > 0 {
            100.0 * *novel as f64 / *total as f64
        } else {
            0.0
        };
        println!(
            "{:>4}  {:>5}  {:>10}  {:>8}  {:>9}  {:>6.1}%",
            size, arity, total, novel, redund, pct
        );
    }

    // -----------------------------------------------------------------------
    // Redundancy breakdown by structural category
    // -----------------------------------------------------------------------
    println!();
    println!("{}", "=".repeat(78));
    println!("Cross-size redundancy by structural category of the redundant GRF");
    println!(
        "(redundant = fingerprint identical to a strictly smaller GRF of the same arity)"
    );
    println!("{}", "=".repeat(78));

    let mut cats: Vec<_> = by_cat.iter().collect();
    cats.sort_by(|(_, (ca, _)), (_, (cb, _))| cb.cmp(ca));

    for (cat, (count, examples)) in &cats {
        println!("\n[{count:>8}]  {cat}");
        for (size, expr, min_size, min_expr) in examples.iter() {
            println!("           n={}  {}  ≡  n={}  {}", size, expr, min_size, min_expr);
        }
    }

    // -----------------------------------------------------------------------
    // Redundancy breakdown by canonical target
    // -----------------------------------------------------------------------
    println!();
    println!("{}", "=".repeat(78));
    println!("Cross-size redundancy by canonical target (most-impersonated functions)");
    println!("(each entry: the small canonical GRF and the larger GRFs equivalent to it)");
    println!("{}", "=".repeat(78));

    let mut targets: Vec<_> = by_target.iter().collect();
    targets.sort_by(|(_, (ca, _)), (_, (cb, _))| cb.cmp(ca));

    let limit = if args.top_targets == 0 {
        targets.len()
    } else {
        args.top_targets.min(targets.len())
    };

    for (canonical, (count, examples)) in targets.iter().take(limit) {
        println!("\n[{count:>8}] ≡  {canonical}");
        for (size, expr) in examples.iter() {
            println!("           n={}  {}", size, expr);
        }
    }
    if targets.len() > limit {
        println!("\n  ... ({} more canonical targets not shown)", targets.len() - limit);
    }

    // -----------------------------------------------------------------------
    // Grand total
    // -----------------------------------------------------------------------
    println!();
    let total_all: usize = summary.iter().map(|(_, _, t, _, _)| t).sum();
    let total_novel: usize = summary.iter().map(|(_, _, _, n, _)| n).sum();
    let total_redund: usize = summary.iter().map(|(_, _, _, _, r)| r).sum();
    println!("{}", "=".repeat(78));
    println!(
        "Grand total: {} GRFs,  {} novel ({:.1}%),  {} cross-redundant ({:.1}%)",
        total_all,
        total_novel,
        100.0 * total_novel as f64 / total_all as f64,
        total_redund,
        100.0 * total_redund as f64 / total_all as f64,
    );
}
