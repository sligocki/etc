//! ClosedForm analysis tools.
//!
//! Subcommands:
//!   coverage  - report closed_form_of coverage over enumerated GRFs
//!   test      - validate closed_form_of against simulate for all GRFs
//!   list      - list distinct semantic ClosedForms for a given arity
//!   dups      - find structurally distinct ClosedForms with equal semantics
use std::collections::HashMap;
use std::time::Instant;

use clap::{Args, Parser, Subcommand};
use gen_rec::closed_form::{closed_form_of, ClosedForm};
use gen_rec::closed_form_enum::{ClosedFormEnumerator, EnumMode};
use gen_rec::enumerate::stream_grf;
use gen_rec::fingerprint::canonical_inputs;
use gen_rec::grf::Grf;
use gen_rec::pruning::PruningOpts;
use gen_rec::sim_nat::SmallNat;
use gen_rec::simulate::{simulate, SimResult};

// =============================================================================
// CLI
// =============================================================================

#[derive(Parser)]
#[command(name = "closed_form", about = "ClosedForm analysis tools")]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Report closed_form_of coverage over enumerated GRFs.
    Coverage(CoverageArgs),
    /// Validate closed_form_of against simulate for all GRFs.
    Test(TestArgs),
    /// List distinct semantic ClosedForms for a given arity.
    List(ListArgs),
    /// Find structurally distinct ClosedForms with equal semantics.
    Dups(DupsArgs),
}

// =============================================================================
// Coverage args
// =============================================================================

#[derive(Args, Debug)]
struct CoverageArgs {
    /// Maximum arity to enumerate (0..=max_arity inclusive).
    #[arg(long, default_value_t = 2)]
    max_arity: usize,

    /// Maximum size to enumerate (inclusive).
    #[arg(long, default_value_t = 12)]
    max_size: usize,

    /// Include the Minimization combinator.
    #[arg(long)]
    allow_min: bool,

    /// Number of holdout GRFs to display per arity.
    #[arg(long, default_value_t = 10)]
    holdouts: usize,

    /// Max simulation steps when computing value previews (0 = skip preview).
    #[arg(long, default_value_t = 10_000)]
    max_steps: SmallNat,
}

// =============================================================================
// Test args
// =============================================================================

#[derive(Args, Debug)]
struct TestArgs {
    /// Arity to test.
    /// Infinite mode (no --max-size): defaults to 1.
    /// Finite mode (--max-size given): if omitted, tests arities 0..=2.
    #[arg(long)]
    arity: Option<usize>,

    /// Maximum size (inclusive). If omitted, runs forever with increasing sizes.
    #[arg(long)]
    max_size: Option<usize>,

    /// Maximum simulation steps per input.
    #[arg(long, default_value_t = 1_000_000)]
    max_steps: u64,

    /// Test a single GRF expression instead of enumerating.
    /// With no positional args: tests on the standard grid of inputs.
    /// With positional args: tests only those specific argument values.
    #[arg(long)]
    grf: Option<String>,

    /// Argument values for --grf (space-separated u64).
    args: Vec<u64>,
}

// =============================================================================
// List args
// =============================================================================

#[derive(Args, Debug)]
struct ListArgs {
    /// Arity to list.
    arity: usize,

    /// Maximum size to enumerate (inclusive).
    #[arg(long, default_value_t = 8)]
    max_size: usize,

    /// Maximum number of entries to show (0 = unlimited).
    #[arg(long, default_value_t = 0)]
    limit: usize,

    /// Include the Minimization combinator.
    #[arg(long)]
    allow_min: bool,
}

// =============================================================================
// Dups args
// =============================================================================

#[derive(Args, Debug)]
struct DupsArgs {
    /// Arity to search.
    arity: usize,

    /// Maximum size to enumerate (inclusive).
    #[arg(long, default_value_t = 8)]
    max_size: usize,

    /// Maximum number of dup groups to report (0 = unlimited).
    #[arg(long, default_value_t = 0)]
    max_dups: usize,

    /// Include the Minimization combinator.
    #[arg(long)]
    allow_min: bool,
}

// =============================================================================
// Main
// =============================================================================

fn main() {
    let cli = Cli::parse();
    match cli.command {
        Command::Coverage(a) => run_coverage(a),
        Command::Test(a) => run_test(a),
        Command::List(a) => run_list(a),
        Command::Dups(a) => run_dups(a),
    }
}

// =============================================================================
// Shared helpers
// =============================================================================

fn fmt_count(n: usize) -> String {
    if n < 1_000 {
        format!("{}", n)
    } else if n < 1_000_000 {
        format!("{:.1}K", n as f64 / 1_000.0)
    } else {
        format!("{:.2}M", n as f64 / 1_000_000.0)
    }
}

fn elapsed_str(start: Instant) -> String {
    format!("{:.1}s", start.elapsed().as_secs_f64())
}

/// Compact algebraic description of a ClosedForm.
///
/// Affine: "0", "1 + x1", "x1 + 2·x2", etc.
/// Piecewise: "(x2=0 ? <zero> : <pos>@x2-1)"
///
/// Variable names are threaded through the recursion so that zero_branch of a Piecewise
/// branching on x_i is displayed with x_i removed (outer x_{i+1} shows as x_{i+1}, not x_i).
fn format_cf(cf: &ClosedForm) -> String {
    let names: Vec<String> = (1..=cf.arity()).map(|i| format!("x{i}")).collect();
    format_cf_named(cf, &names)
}

fn format_cf_named(cf: &ClosedForm, names: &[String]) -> String {
    match cf {
        ClosedForm::Affine(af) => {
            let mut terms: Vec<String> = Vec::new();
            if af.coeffs[0] != 0 || af.arity == 0 {
                terms.push(af.coeffs[0].to_string());
            }
            for (i, &c) in af.coeffs[1..].iter().enumerate() {
                let xi = &names[i];
                match c {
                    0 => {}
                    1 => terms.push(xi.clone()),
                    -1 => terms.push(format!("-{xi}")),
                    _ => terms.push(format!("{c}·{xi}")),
                }
            }
            if terms.is_empty() {
                "0".to_string()
            } else {
                terms.join(" + ")
            }
        }
        ClosedForm::Piecewise(pw) => {
            let bi = pw.branch_index; // 0-indexed
            let bname = &names[bi];
            // pos_branch: same variable names as outer (bi-th arg is decremented, not removed).
            let pos_str = format_cf_named(&pw.pos_branch, names);
            // zero_branch: remove names[bi] from the list (that arg is absent in the zero case).
            let zero_names: Vec<String> =
                names.iter().enumerate().filter(|&(i, _)| i != bi).map(|(_, n)| n.clone()).collect();
            let zero_str = format_cf_named(&pw.zero_branch, &zero_names);
            format!("({bname}=0 ? {zero_str} : {pos_str}@{bname}-1)")
        }
    }
}

/// Sample output values for a ClosedForm: arity 0-2 get compact strings.
fn cf_preview(cf: &ClosedForm) -> String {
    let show = |v: Option<SmallNat>| v.map_or("?".to_string(), |n| n.to_string());
    match cf.arity() {
        0 => format!("f()={}", show(cf.eval(&[]))),
        1 => (0u64..8).map(|i| show(cf.eval(&[i]))).collect::<Vec<_>>().join(" "),
        2 => {
            // f(n,0) for n=0..3, f(0,n) for n=1..3  (7 compact points)
            let mut parts = Vec::new();
            parts.push(format!(
                "f(·,0)={}",
                (0u64..4).map(|n| show(cf.eval(&[n, 0]))).collect::<Vec<_>>().join("")
            ));
            parts.push(format!(
                "f(0,·)={}",
                (0u64..4).map(|n| show(cf.eval(&[0, n]))).collect::<Vec<_>>().join("")
            ));
            parts.join("  ")
        }
        _ => String::new(),
    }
}

/// Fingerprint a ClosedForm by evaluating on canonical inputs.
fn cf_fingerprint(cf: &ClosedForm) -> Vec<Option<SmallNat>> {
    canonical_inputs(cf.arity())
        .iter()
        .map(|args| cf.eval(args))
        .collect()
}

// =============================================================================
// coverage helpers (ported from closed_form_coverage.rs)
// =============================================================================

fn value_preview(f: &Grf, max_steps: SmallNat) -> String {
    let arity = f.arity();
    if max_steps == 0 || arity > 2 {
        return String::new();
    }
    let eval = |args: &[SmallNat]| -> String {
        let (res, _) = simulate(f, args, max_steps);
        match res {
            SimResult::Value(v) => v.to_string(),
            SimResult::Diverge => "∞".to_string(),
            SimResult::OutOfSteps => "?".to_string(),
            SimResult::ArityMismatch => "!".to_string(),
            SimResult::ValueOverflow => "!overflow".to_string(),
        }
    };
    match arity {
        0 => format!("f()={}", eval(&[])),
        1 => {
            let vals: Vec<String> = (0..4).map(|i| eval(&[i])).collect();
            format!("f(0..3) = {}", vals.join(" "))
        }
        2 => {
            let pts: &[(&str, &[SmallNat])] = &[
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
                    None => return format!("Comp: arg[{}] → {}", i + 1, holdout_reason(g)),
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

fn run_coverage(args: CoverageArgs) {
    let mut en = ClosedFormEnumerator::with_pruning(EnumMode::AllGrf, args.allow_min);
    for arity in 0..=args.max_arity {
        for size in 1..=args.max_size {
            en.compute_size(arity, size);
        }
    }

    let mut grand_total = 0usize;
    let mut grand_covered = 0usize;
    let mut grand_reason_counts: std::collections::BTreeMap<String, usize> =
        std::collections::BTreeMap::new();

    for arity in 0..=args.max_arity {
        println!("=== Arity {} ===", arity);
        println!("{:>5}  {:>8}  {:>8}  {:>6}", "size", "total", "covered", "%");
        println!("{}", "-".repeat(36));

        let mut arity_total = 0usize;
        let mut arity_covered = 0usize;
        let mut arity_holdouts: Vec<(usize, String)> = Vec::new();
        let mut reason_counts: std::collections::BTreeMap<String, usize> =
            std::collections::BTreeMap::new();
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
                    reason_examples.entry(root).or_insert_with(|| (size, grf.to_string()));
                }
            }
            let pct = if size_total > 0 {
                100.0 * size_covered as f64 / size_total as f64
            } else {
                100.0
            };
            println!("{:>5}  {:>8}  {:>8}  {:>5.1}%", size, size_total, size_covered, pct);
            arity_total += size_total;
            arity_covered += size_covered;
        }

        let arity_pct = if arity_total > 0 {
            100.0 * arity_covered as f64 / arity_total as f64
        } else {
            100.0
        };
        println!("{}", "-".repeat(36));
        println!("{:>5}  {:>8}  {:>8}  {:>5.1}%", "SUM", arity_total, arity_covered, arity_pct);
        println!();
        grand_total += arity_total;
        grand_covered += arity_covered;

        if !reason_counts.is_empty() {
            let holdout_total: usize = reason_counts.values().sum();
            println!("  Holdout breakdown for arity {}:", arity);
            let mut reasons: Vec<_> = reason_counts.iter().collect();
            reasons.sort_by(|a, b| b.1.cmp(a.1));
            for (reason, count) in &reasons {
                let pct = 100.0 * **count as f64 / holdout_total as f64;
                let example = &reason_examples[*reason];
                println!(
                    "    {:>6}  ({:>4.1}%)  {:<36}  e.g. [{}] {}",
                    fmt_count(**count), pct, reason, example.0, example.1
                );
            }
            println!();
        }

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
        grand_pct
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

// =============================================================================
// test helpers (ported from test_closed_form.rs)
// =============================================================================

fn test_inputs(arity: usize) -> Vec<Vec<u64>> {
    if arity == 0 {
        return vec![vec![]];
    }
    let vals: &[u64] = &[0, 1, 2, 3, 5, 8];
    let mut result: Vec<Vec<u64>> = vec![vec![]];
    for _ in 0..arity {
        let mut next = Vec::new();
        for prefix in &result {
            for &v in vals {
                let mut row = prefix.clone();
                row.push(v);
                next.push(row);
            }
        }
        result = next;
    }
    result
}

fn check_size(arity: usize, size: usize, max_steps: u64) -> (usize, usize) {
    let inputs = test_inputs(arity);
    let opts = PruningOpts::default();
    let mut grfs_checked = 0usize;
    let mut grfs_bad = 0usize;
    stream_grf(size, arity, false, opts, &mut |grf| {
        let cf = match closed_form_of(grf) {
            Some(cf) => cf,
            None => return,
        };
        grfs_checked += 1;
        let mut first_bad: Option<(Vec<u64>, Option<u64>, Option<u64>)> = None;
        let mut bad_count = 0usize;
        for args in &inputs {
            let (sim_result, _) = simulate(grf, args, max_steps);
            let sim_val = match sim_result {
                SimResult::Value(v) => Some(v),
                SimResult::Diverge | SimResult::OutOfSteps => None,
                SimResult::ArityMismatch => panic!("arity mismatch for {} on {:?}", grf, args),
                SimResult::ValueOverflow => None,
            };
            let cf_val = cf.eval(args);
            if cf_val != sim_val {
                bad_count += 1;
                if first_bad.is_none() {
                    first_bad = Some((args.clone(), cf_val, sim_val));
                }
            }
        }
        if bad_count > 0 {
            grfs_bad += 1;
            let (bad_args, cf_val, sim_val) = first_bad.unwrap();
            eprintln!(
                "MISMATCH: {}  args={:?}  cf={:?}  sim={:?}  ({}/{} inputs bad)",
                grf, bad_args, cf_val, sim_val, bad_count, inputs.len()
            );
        }
    });
    (grfs_checked, grfs_bad)
}

fn check_one_grf(grf_str: &str, explicit_args: &[u64], max_steps: u64) {
    let grf: Grf = match grf_str.parse() {
        Ok(g) => g,
        Err(e) => {
            eprintln!("parse error: {e}");
            std::process::exit(1);
        }
    };
    let arity = grf.arity();
    let cf = match closed_form_of(&grf) {
        Some(cf) => cf,
        None => {
            println!("{grf_str}: closed_form_of returned None");
            return;
        }
    };
    let inputs: Vec<Vec<u64>> = if explicit_args.is_empty() {
        test_inputs(arity)
    } else {
        if explicit_args.len() != arity {
            eprintln!(
                "arity mismatch: GRF has arity {arity} but {} args given",
                explicit_args.len()
            );
            std::process::exit(1);
        }
        vec![explicit_args.to_vec()]
    };
    let mut bad_count = 0usize;
    let mut first_bad: Option<(Vec<u64>, Option<u64>, Option<u64>)> = None;
    for input in &inputs {
        let (sim_result, _) = simulate(&grf, input, max_steps);
        let sim_val = match sim_result {
            SimResult::Value(v) => Some(v),
            SimResult::Diverge | SimResult::OutOfSteps => None,
            SimResult::ArityMismatch => panic!("arity mismatch for {grf_str} on {input:?}"),
            SimResult::ValueOverflow => None,
        };
        let cf_val = cf.eval(input);
        if cf_val != sim_val {
            bad_count += 1;
            if first_bad.is_none() {
                first_bad = Some((input.clone(), cf_val, sim_val));
            }
        } else {
            println!("ok: {grf_str} args={input:?}  cf={cf_val:?}");
        }
    }
    if bad_count > 0 {
        let (bad_args, cf_val, sim_val) = first_bad.unwrap();
        eprintln!(
            "MISMATCH: {grf_str}  args={bad_args:?}  cf={cf_val:?}  sim={sim_val:?}  ({bad_count}/{} inputs bad)",
            inputs.len()
        );
        std::process::exit(1);
    }
}

fn run_test(args: TestArgs) {
    if let Some(grf_str) = &args.grf {
        check_one_grf(grf_str, &args.args, args.max_steps);
        return;
    }
    let start = Instant::now();
    match args.max_size {
        None => {
            let arity = args.arity.unwrap_or(1);
            let mut grand_grfs = 0usize;
            println!("Infinite mode: arity {}, sizes 1, 2, 3, ...", arity);
            for size in 1.. {
                let (grfs_checked, grfs_bad) = check_size(arity, size, args.max_steps);
                grand_grfs += grfs_checked;
                if grfs_bad > 0 {
                    eprintln!(
                        "  size {:3}: {} bad GRFs  [{}]",
                        size, grfs_bad, elapsed_str(start)
                    );
                    std::process::exit(1);
                } else {
                    println!(
                        "  size {:3}: {:8} GRFs ok  (total: {})  [{}]",
                        size, grfs_checked, grand_grfs, elapsed_str(start)
                    );
                }
            }
        }
        Some(max_size) => {
            let (arity_lo, arity_hi) = match args.arity {
                Some(a) => (a, a),
                None => (0, 2),
            };
            let mut grand_grfs = 0usize;
            let mut grand_bad = 0usize;
            for arity in arity_lo..=arity_hi {
                println!("arity {}:", arity);
                for size in 1..=max_size {
                    let (grfs_checked, grfs_bad) = check_size(arity, size, args.max_steps);
                    grand_grfs += grfs_checked;
                    grand_bad += grfs_bad;
                    if grfs_bad > 0 {
                        println!(
                            "  size {:3}: {:8} GRFs, {} bad  [{}]",
                            size, grfs_checked, grfs_bad, elapsed_str(start)
                        );
                    } else {
                        println!(
                            "  size {:3}: {:8} GRFs ok  [{}]",
                            size, grfs_checked, elapsed_str(start)
                        );
                    }
                }
            }
            if grand_bad > 0 {
                eprintln!(
                    "{} bad GRFs out of {} checked (arities {}..={}, sizes 1..={})  [{}]",
                    grand_bad, grand_grfs, arity_lo, arity_hi, max_size, elapsed_str(start)
                );
                std::process::exit(1);
            } else {
                println!(
                    "All {} GRFs matched (arities {}..={}, sizes 1..={})  [{}]",
                    grand_grfs, arity_lo, arity_hi, max_size, elapsed_str(start)
                );
            }
        }
    }
}

// =============================================================================
// list
// =============================================================================

fn run_list(args: ListArgs) {
    let mut en = ClosedFormEnumerator::with_pruning(EnumMode::ClosedFormOnly, args.allow_min);
    for size in 1..=args.max_size {
        en.compute_size(args.arity, size);
    }

    // Count total so we can print it in the header.
    let total: usize = (1..=args.max_size)
        .map(|s| en.candidates(args.arity, s).len())
        .sum();

    println!(
        "=== Arity {} (up to size {}) — {} distinct semantic forms ===",
        args.arity, args.max_size, total
    );

    let limit = if args.limit > 0 { args.limit } else { usize::MAX };

    // Collect all rows first so we can compute column widths.
    let mut rows: Vec<(usize, String, String, String)> = Vec::new();
    'outer: for size in 1..=args.max_size {
        for grf in en.candidates(args.arity, size) {
            let cf = match closed_form_of(grf) {
                Some(cf) => cf,
                None => continue,
            };
            rows.push((size, grf.to_string(), format_cf(&cf), cf_preview(&cf)));
            if rows.len() >= limit {
                break 'outer;
            }
        }
    }

    let grf_w = rows.iter().map(|(_, g, _, _)| g.len()).max().unwrap_or(0);
    let formula_w = rows.iter().map(|(_, _, f, _)| f.len()).max().unwrap_or(0);

    for (size, grf_str, formula, preview) in &rows {
        println!("[{:2}]  {:<grf_w$}  {:<formula_w$}  {}", size, grf_str, formula, preview);
    }
    if rows.len() >= limit {
        println!("... ({} total, limit {} reached)", total, args.limit);
    }
}

// =============================================================================
// dups
// =============================================================================

fn run_dups(args: DupsArgs) {
    let mut en = ClosedFormEnumerator::with_pruning(EnumMode::ClosedFormOnly, args.allow_min);
    for size in 1..=args.max_size {
        en.compute_size(args.arity, size);
    }

    // Group (size, grf_str, ClosedForm) by semantic fingerprint.
    let mut groups: HashMap<Vec<Option<SmallNat>>, Vec<(usize, String, ClosedForm)>> =
        HashMap::new();
    for size in 1..=args.max_size {
        for grf in en.candidates(args.arity, size) {
            if let Some(cf) = closed_form_of(grf) {
                let fp = cf_fingerprint(&cf);
                groups
                    .entry(fp)
                    .or_default()
                    .push((size, grf.to_string(), cf));
            }
        }
    }

    // Collect groups with > 1 structural form.
    let mut dup_groups: Vec<Vec<(usize, String, ClosedForm)>> =
        groups.into_values().filter(|g| g.len() > 1).collect();

    // Sort each group by size, then sort groups by their smallest member.
    for g in &mut dup_groups {
        g.sort_by_key(|(size, _, _)| *size);
    }
    dup_groups.sort_by_key(|g| g[0].0);

    if dup_groups.is_empty() {
        println!(
            "No semantic duplicates found (arity {}, sizes 1..={}).",
            args.arity, args.max_size
        );
        return;
    }

    let n_canonical = args.arity.max(1); // canonical_inputs count hint for display
    let input_pts = if args.arity == 0 { 1 } else if args.arity == 1 { 8 } else { 32 };
    println!(
        "=== Semantic duplicates: arity {}, sizes 1..={} ===",
        args.arity, args.max_size
    );
    println!(
        "Comparison by ClosedForm eval on {} canonical input(s) — not proven exact.",
        input_pts
    );
    let limit = if args.max_dups > 0 { args.max_dups } else { usize::MAX };
    let shown = dup_groups.len().min(limit);
    println!(
        "{} dup group(s){}:\n",
        dup_groups.len(),
        if dup_groups.len() > shown {
            format!(", showing {}", shown)
        } else {
            String::new()
        }
    );

    for group in dup_groups.iter().take(limit) {
        // Show sample values from the first (smallest) entry.
        let preview = cf_preview(&group[0].2);
        println!("  values: {}", preview);
        for (size, grf_str, cf) in group {
            println!("    [{:2}]  {:<50}  {}", size, grf_str, format_cf(cf));
        }
        println!();
    }

    let _ = n_canonical; // silence unused warning
}
