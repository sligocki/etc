/// Report what fraction of novel GRFs closed_form_of can represent, and list smallest holdouts.
///
/// Uses ClosedFormEnumerator (novel sub-expression enumeration) instead of exhaustive
/// stream_grf.  GRFs are only generated from canonical sub-expressions, so the counts
/// reflect the novel/deduped population rather than all raw GRFs.
///
/// Usage examples:
///   closed_form_coverage                          # arities 0..=2, sizes 1..=8, PRF only
///   closed_form_coverage --max-arity 3            # also include arity 3
///   closed_form_coverage --max-size 10            # enumerate larger sizes
///   closed_form_coverage --allow-min              # include Min combinator
///   closed_form_coverage --holdouts 20            # show more holdouts
///   closed_form_coverage --max-steps 0            # skip value preview
use clap::Parser;
use gen_rec::closed_form::{closed_form_of, ClosedForm};
use gen_rec::closed_form_enum::ClosedFormEnumerator;
use gen_rec::grf::Grf;
use gen_rec::simulate::{simulate, SimResult};

#[derive(Parser, Debug)]
#[command(about = "Report closed_form.rs coverage over enumerated GRFs")]
struct Args {
    /// Maximum arity to enumerate (0..=max_arity inclusive).
    #[arg(long, default_value_t = 2)]
    max_arity: usize,

    /// Maximum size to enumerate (inclusive).
    #[arg(long, default_value_t = 8)]
    max_size: usize,

    /// Include the Minimization combinator.
    #[arg(long)]
    allow_min: bool,

    /// Number of holdout GRFs to display per arity.
    #[arg(long, default_value_t = 10)]
    holdouts: usize,

    /// Max simulation steps when computing value previews (0 = skip preview).
    #[arg(long, default_value_t = 10_000)]
    max_steps: u64,
}

// ---------------------------------------------------------------------------
// Value preview
// ---------------------------------------------------------------------------

/// Evaluate f on a small canonical grid and format as a compact string.
///
/// arity 0 : "f()=V"
/// arity 1 : "f(0..3) = V0 V1 V2 V3"
/// arity 2 : "f(0,0)=A f(1,0)=B f(0,1)=C f(1,1)=D"
/// arity 3+: skip (too many inputs)
fn value_preview(f: &Grf, max_steps: u64) -> String {
    let arity = f.arity();
    if max_steps == 0 || arity > 2 {
        return String::new();
    }

    let eval = |args: &[u64]| -> String {
        let (res, _) = simulate(f, args, max_steps);
        match res {
            SimResult::Value(v) => v.to_string(),
            SimResult::Diverge => "∞".to_string(),
            SimResult::OutOfSteps => "?".to_string(),
            SimResult::ArityMismatch => "!".to_string(),
        }
    };

    match arity {
        0 => format!("f()={}", eval(&[])),
        1 => {
            let vals: Vec<String> = (0..4).map(|i| eval(&[i])).collect();
            format!("f(0..3) = {}", vals.join(" "))
        }
        2 => {
            let pts: &[(&str, &[u64])] = &[
                ("f(0,0)", &[0, 0]),
                ("f(1,0)", &[1, 0]),
                ("f(0,1)", &[0, 1]),
                ("f(1,1)", &[1, 1]),
                ("f(2,2)", &[2, 2]),
            ];
            pts.iter()
                .map(|(label, args)| format!("{}={}", label, eval(args)))
                .collect::<Vec<_>>()
                .join("  ")
        }
        _ => String::new(),
    }
}

// ---------------------------------------------------------------------------
// Holdout classification
// ---------------------------------------------------------------------------

/// Short label explaining why closed_form_of failed for this GRF.
///
/// For `Comp` nodes whose inner components are not representable, the reason
/// recursively describes WHY that sub-node fails rather than just "not sem".
fn holdout_reason(grf: &Grf) -> String {
    match grf {
        Grf::Min(_) => "Min".into(),
        Grf::Rec(g, h) => {
            let uses_acc = h.used_args().contains(&2);
            let acc_k = h.acc_plus_k().is_some();
            let sem_h = closed_form_of(h);

            if acc_k {
                match closed_form_of(g) {
                    None => "Rec[A]: base not sem".into(),
                    Some(ClosedForm::Piecewise(_)) => "Rec[A]: base is piecewise".into(),
                    Some(ClosedForm::Affine(_)) => "Rec[A]: unexpected (should be covered)".into(),
                }
            } else if !uses_acc {
                if closed_form_of(g).is_none() {
                    "Rec[B]: base not sem".into()
                } else {
                    match sem_h {
                        None => "Rec[B]: step not sem".into(),
                        Some(ClosedForm::Affine(ref af)) if af.coeffs.get(2) == Some(&0) => {
                            "Rec[B]: step ok (unexpected)".into()
                        }
                        Some(ClosedForm::Affine(_)) => "Rec[B]: step has nonzero acc coeff".into(),
                        Some(ClosedForm::Piecewise(_)) => "Rec[B]: step is piecewise".into(),
                    }
                }
            } else {
                match sem_h {
                    None => "Rec: step uses acc, not sem".into(),
                    Some(ClosedForm::Affine(_)) => "Rec: step uses acc, affine (not acc+k)".into(),
                    Some(ClosedForm::Piecewise(_)) => "Rec: step uses acc, piecewise".into(),
                }
            }
        }
        Grf::Comp(h, gs, _) => {
            for (i, g) in gs.iter().enumerate() {
                match closed_form_of(g) {
                    None => {
                        return format!("Comp: arg[{}] → {}", i + 1, holdout_reason(g));
                    }
                    Some(ClosedForm::Piecewise(_)) => return "Comp: arg is piecewise".into(),
                    Some(ClosedForm::Affine(_)) => {}
                }
            }
            match closed_form_of(h) {
                None => format!("Comp: head → {}", holdout_reason(h)),
                Some(ClosedForm::Piecewise(_)) => "Comp: head is piecewise".into(),
                Some(ClosedForm::Affine(_)) => "Comp: all affine (unexpected)".into(),
            }
        }
        _ => "atom (unexpected)".into(),
    }
}

fn root_cause(reason: &str) -> &str {
    reason.rsplit(" → ").next().unwrap_or(reason)
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

fn main() {
    let args = Args::parse();

    // Pre-compute all needed (arity, size) entries up front.
    // ClosedFormEnumerator auto-resolves dependency arities beyond max_arity.
    let mut en = ClosedFormEnumerator::with_pruning(true, args.allow_min);
    for arity in 0..=args.max_arity {
        for size in 1..=args.max_size {
            en.compute_size(arity, size);
        }
    }

    let mut grand_total = 0usize;
    let mut grand_covered = 0usize;
    // reason → count, accumulated across all arities
    let mut grand_reason_counts: std::collections::BTreeMap<String, usize> =
        std::collections::BTreeMap::new();

    for arity in 0..=args.max_arity {
        println!("=== Arity {} ===", arity);
        println!("{:>5}  {:>8}  {:>8}  {:>6}", "size", "total", "covered", "%");
        println!("{}", "-".repeat(36));

        let mut arity_total = 0usize;
        let mut arity_covered = 0usize;
        // first `holdouts` uncovered GRFs (for the example list)
        let mut arity_holdouts: Vec<(usize, String)> = Vec::new();
        // reason → count for this arity
        let mut reason_counts: std::collections::BTreeMap<String, usize> =
            std::collections::BTreeMap::new();
        // first example per reason (for the grouped display)
        let mut reason_examples: std::collections::BTreeMap<String, (usize, String)> =
            std::collections::BTreeMap::new();

        for size in 1..=args.max_size {
            let mut size_total = 0usize;
            let mut size_covered = 0usize;

            for grf in en.candidates(arity, size) {
                size_total += 1;
                if closed_form_of(grf).is_some() {
                    size_covered += 1;
                } else {
                    let reason = holdout_reason(grf);
                    let root = root_cause(&reason).to_string();
                    *reason_counts.entry(root.clone()).or_insert(0) += 1;
                    *grand_reason_counts.entry(root.clone()).or_insert(0) += 1;
                    if arity_holdouts.len() < args.holdouts {
                        arity_holdouts.push((size, grf.to_string()));
                    }
                    reason_examples
                        .entry(root)
                        .or_insert_with(|| (size, grf.to_string()));
                }
            };

            let pct = if size_total > 0 {
                100.0 * size_covered as f64 / size_total as f64
            } else {
                100.0
            };
            println!(
                "{:>5}  {:>8}  {:>8}  {:>5.1}%",
                size, size_total, size_covered, pct
            );

            arity_total += size_total;
            arity_covered += size_covered;
        }

        let arity_pct = if arity_total > 0 {
            100.0 * arity_covered as f64 / arity_total as f64
        } else {
            100.0
        };
        println!("{}", "-".repeat(36));
        println!(
            "{:>5}  {:>8}  {:>8}  {:>5.1}%",
            "SUM", arity_total, arity_covered, arity_pct
        );
        println!();

        grand_total += arity_total;
        grand_covered += arity_covered;

        // --- Reason breakdown ---
        if !reason_counts.is_empty() {
            let holdout_total: usize = reason_counts.values().sum();
            println!("  Holdout breakdown for arity {}:", arity);
            // Sort by count descending
            let mut reasons: Vec<_> = reason_counts.iter().collect();
            reasons.sort_by(|a, b| b.1.cmp(a.1));
            for (reason, count) in &reasons {
                let pct = 100.0 * **count as f64 / holdout_total as f64;
                let example = &reason_examples[*reason];
                println!(
                    "    {:>6}  ({:>4.1}%)  {:<36}  e.g. [{}] {}",
                    fmt_count(**count),
                    pct,
                    reason,
                    example.0,
                    example.1
                );
            }
            println!();
        }

        // --- Per-size holdout examples ---
        if !arity_holdouts.is_empty() {
            println!(
                "  Holdout examples for arity {} (first {} shown):",
                arity,
                arity_holdouts.len()
            );
            for (size, grf_str) in &arity_holdouts {
                let grf: Grf = grf_str.parse().unwrap();
                let reason = holdout_reason(&grf);
                let preview = value_preview(&grf, args.max_steps);
                if preview.is_empty() {
                    println!("    [{}]  {:<44}  {}", size, grf_str, reason);
                } else {
                    println!("    [{}]  {:<44}  {}  |  {}", size, grf_str, reason, preview);
                }
            }
            println!();
        }
    }

    // --- Grand summary ---
    let grand_pct = if grand_total > 0 {
        100.0 * grand_covered as f64 / grand_total as f64
    } else {
        100.0
    };
    println!(
        "=== Overall (arities 0..={}, sizes 1..={}) ===",
        args.max_arity, args.max_size
    );
    println!("  total novel GRFs : {}", fmt_count(grand_total));
    println!(
        "  covered          : {}  ({:.1}%)",
        fmt_count(grand_covered),
        grand_pct,
    );
    let grand_holdouts = grand_total.saturating_sub(grand_covered);
    println!("  holdouts         : {}", fmt_count(grand_holdouts));

    if !grand_reason_counts.is_empty() {
        println!();
        println!("  Holdout reasons (all arities combined, by count):");
        let mut reasons: Vec<_> = grand_reason_counts.iter().collect();
        reasons.sort_by(|a, b| b.1.cmp(a.1));
        for (reason, count) in &reasons {
            let pct = 100.0 * **count as f64 / grand_holdouts as f64;
            println!("    {:>7}  ({:>4.1}%)  {}", fmt_count(**count), pct, reason);
        }
    }
}

fn fmt_count(n: usize) -> String {
    if n < 1_000 {
        format!("{}", n)
    } else if n < 1_000_000 {
        format!("{:.1}K", n as f64 / 1_000.0)
    } else {
        format!("{:.2}M", n as f64 / 1_000_000.0)
    }
}
