/// Heuristic scan of M(PRF) holdouts: flag inner PRFs that are non-monotone.
///
/// If the inner PRF f(n) never decreases, M(f) is unlikely to halt (it must
/// reach 0).  If f(n+1) < f(n) for some n, there is at least a structural
/// path toward zero.  A does additional checks for f(n+k) < f(n) for a
/// range of sizes to rule out alternating (and larger cycle) functions.
///
/// Usage:
///   monotone_heuristic results/min_prf/14_10M/holdout.txt
///   monotone_heuristic --max-val 20 --max-steps 100000 holdout.txt
use clap::Parser;
use gen_rec::grf::{Grf, GrfKind};
use gen_rec::io_grl::{self, GrfEntry};
use gen_rec::mgrf::parse_mgrf_to_grfs;
use gen_rec::simulate::{simulate};
use std::fs;
use std::io::BufWriter;
use std::path::PathBuf;

#[derive(Parser, Debug)]
#[command(about = "Heuristic: flag M(PRF) holdouts whose inner PRF is non-monotone")]
struct Args {
    /// Holdout files to scan.
    files: Vec<PathBuf>,

    /// Evaluate inner PRF on inputs min_val..max_val.
    #[arg(long, default_value_t = 12)]
    min_val: u64,

    /// Evaluate inner PRF on inputs min_val..max_val.
    #[arg(long, default_value_t = 42)]
    max_val: u64,

    /// Step budget per individual inner-PRF call (0 = unlimited).
    #[arg(long, default_value_t = 100_000)]
    max_steps: u64,

    /// Max stride for the alternating filter (checks strides 2..=max_stride).
    #[arg(long, default_value_t = 6)]
    max_stride: usize,

    /// Print all entries, not just candidates.
    #[arg(long)]
    verbose: bool,

    /// Include timeout entries in output (deferred to end of file).
    #[arg(long)]
    timeout: bool,

    /// Probe a single GRF expression and show detailed stride analysis.
    #[arg(long)]
    probe: Option<String>,

    /// Write candidate (decreasing / hits-zero) GRFs to this file in .grl format.
    #[arg(long)]
    output: Option<PathBuf>,
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum Class {
    /// f(n) == 0 for some n in range — M(f) would halt if it reached that n.
    HitsZero,
    /// f(n+1) < f(n) AND f(n+2) < f(n) for some n — genuine decrease.
    Decreasing,
    /// f(n+1) < f(n) for some n, but each parity class is non-decreasing.
    Alternating,
    /// At least one simulation timed out; sequence is partially unknown.
    Timeout,
    /// f is non-decreasing and always > 0 across the tested range.
    Monotone,
}

impl std::fmt::Display for Class {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Class::HitsZero    => write!(f, "hits-zero  "),
            Class::Decreasing  => write!(f, "decreasing "),
            Class::Alternating => write!(f, "alternating"),
            Class::Timeout     => write!(f, "timeout    "),
            Class::Monotone    => write!(f, "monotone   "),
        }
    }
}

fn classify(vals: &[Option<u64>]) -> Class {
    let mut prev: Option<u64> = None;
    let mut any_timeout = false;

    for &v in vals {
        match v {
            None => any_timeout = true,
            Some(0) => return Class::HitsZero,
            Some(cur) => {
                if prev.map_or(false, |p| cur < p) {
                    return Class::Decreasing;
                }
                prev = Some(cur);
            }
        }
    }

    if any_timeout { Class::Timeout } else { Class::Monotone }
}

// Returns true iff every stride in 2..=max_stride has at least one decrease.
// If any stride has no decrease, the function is periodic at that stride period.
fn all_strides_have_decrease(vals: &[Option<u64>], max_stride: usize) -> bool {
    for stride in 2..=max_stride {
        let found = (0..vals.len().saturating_sub(stride))
            .any(|i| matches!((vals[i], vals[i + stride]), (Some(a), Some(b)) if b < a));
        if !found {
            return false;
        }
    }
    true
}

fn fmt_vals(vals: &[Option<u64>]) -> String {
    vals.iter()
        .map(|v| match v { Some(n) => n.to_string(), None => "?".to_string() })
        .collect::<Vec<_>>()
        .join(" ")
}

fn process_file(path: &PathBuf, args: &Args) {
    let content = match fs::read_to_string(path) {
        Ok(c) => c,
        Err(e) => { eprintln!("error reading {}: {}", path.display(), e); return; }
    };

    let budget = if args.max_steps == 0 { u64::MAX } else { args.max_steps };

    let mut out_writer: Option<BufWriter<fs::File>> = args.output.as_ref().map(|p| {
        let f = fs::File::create(p).unwrap_or_else(|e| {
            eprintln!("error creating output {}: {}", p.display(), e);
            std::process::exit(1);
        });
        let mut w = BufWriter::new(f);
        io_grl::write_grl_header(&mut w,
            &format!("monotone_heuristic candidates from {}", path.display())).ok();
        w
    });

    let mut total        = 0usize;
    let mut n_hits_zero   = 0usize;
    let mut n_decreasing  = 0usize;
    let mut n_alternating = 0usize;
    let mut n_timeout     = 0usize;
    let mut n_monotone    = 0usize;
    let mut timeout_lines: Vec<String> = Vec::new();

    println!("=== {} ===", path.display());

    for entry in io_grl::parse_grf_entries(&content) {
        let expr = &entry.expr;

        let grf: Grf = match expr.parse() {
            Ok(g) => g,
            Err(e) => { eprintln!("parse error ({}): {}", e, expr); continue; }
        };

        let inner = match &grf.kind {
            GrfKind::Min(f) => f.as_ref().clone(),
            _ => { eprintln!("expected M(...), got: {}", expr); continue; }
        };

        if inner.arity() != 1 {
            eprintln!("inner arity {} != 1, skipping: {}", inner.arity(), expr);
            continue;
        }

        // Skip if provably always positive: is_never_zero covers all inputs;
        // is_positive_for_pos_arg(1) covers n >= 1 (the entire min_val..max_val range
        // when min_val >= 1, which is the default 12).
        if inner.is_never_zero() || inner.is_positive_for_pos_arg(1) { continue; }

        let vals: Vec<Option<u64>> = (args.min_val..args.max_val)
            .map(|n| simulate(&inner, &[n], budget).0.into_value())
            .collect();

        let class = classify(&vals);
        let has_timeouts = vals.iter().any(|v| v.is_none());
        let class = if class == Class::Decreasing && !has_timeouts && !all_strides_have_decrease(&vals, args.max_stride) {
            Class::Alternating
        } else {
            class
        };
        total += 1;

        match class {
            Class::HitsZero    => n_hits_zero   += 1,
            Class::Decreasing  => n_decreasing  += 1,
            Class::Alternating => n_alternating += 1,
            Class::Timeout     => n_timeout     += 1,
            Class::Monotone    => n_monotone    += 1,
        }

        let is_candidate = matches!(class, Class::HitsZero | Class::Decreasing)
            || (args.timeout && matches!(class, Class::Timeout));
        if is_candidate || args.verbose {
            let formatted = format!("[{}] {}  [{}]", class, expr, fmt_vals(&vals));
            if matches!(class, Class::Timeout) {
                timeout_lines.push(formatted);
            } else {
                println!("{}", formatted);
            }
        }
        if matches!(class, Class::HitsZero | Class::Decreasing) {
            if let Some(ref mut w) = out_writer {
                io_grl::write_grf_entry(w, &GrfEntry {
                    expr: expr.to_string(),
                    status: None,
                    steps: entry.steps,
                    base_steps: None,
                    score: None,
                    unknown_reason: None,
                }).ok();
            }
        }
    }

    println!(
        "--- total: {}  hits-zero: {}  decreasing: {}  alternating: {}  timeout: {}  monotone: {}",
        total, n_hits_zero, n_decreasing, n_alternating, n_timeout, n_monotone
    );

    if args.timeout && !timeout_lines.is_empty() {
        println!("--- timeouts ({}):", timeout_lines.len());
        for line in &timeout_lines {
            println!("{}", line);
        }
    }

    println!();
}

fn parse_mgrf_expr(expr: &str) -> Result<Grf, String> {
    let content = format!("Probe := {}", expr);
    parse_mgrf_to_grfs(&content)?
        .into_iter()
        .next()
        .map(|(_, g)| g)
        .ok_or_else(|| "no definition produced".to_string())
}

fn probe_grf(expr: &str, args: &Args) {
    let grf: Grf = match parse_mgrf_expr(expr) {
        Ok(g) => g,
        Err(e) => { eprintln!("parse error: {}", e); return; }
    };

    let inner = match &grf.kind {
        GrfKind::Min(f) => f.as_ref().clone(),
        _ => grf.clone(),
    };

    println!("probe : {}", expr);
    if matches!(&grf.kind, GrfKind::Min(_)) {
        println!("inner : {}", inner);
    }
    println!("arity : {}", inner.arity());

    if inner.arity() != 1 {
        eprintln!("inner arity {} != 1, cannot probe", inner.arity());
        return;
    }

    let budget = if args.max_steps == 0 { u64::MAX } else { args.max_steps };
    let vals: Vec<Option<u64>> = (args.min_val..args.max_val)
        .map(|n| simulate(&inner, &[n], budget).0.into_value())
        .collect();

    println!("range : {}..{}", args.min_val, args.max_val);
    println!("values: [{}]", fmt_vals(&vals));

    let has_timeouts = vals.iter().any(|v| v.is_none());
    let base_class = classify(&vals);
    println!("stride 1 (classify): {}{}", base_class,
        if has_timeouts { "  [has timeouts — stride filter skipped]" } else { "" });

    if base_class == Class::Decreasing && !has_timeouts {
        println!();
        let mut all_pass = true;
        for stride in 2..=args.max_stride {
            let witness = (0..vals.len().saturating_sub(stride))
                .find(|&i| matches!((vals[i], vals[i + stride]), (Some(a), Some(b)) if b < a));
            if let Some(i) = witness {
                let n = args.min_val + i as u64;
                println!("  stride {:2}: decrease at f({})={} > f({})={}",
                    stride, n, vals[i].unwrap(), n + stride as u64, vals[i + stride].unwrap());
            } else {
                all_pass = false;
                println!("  stride {:2}: NO decrease — residue classes mod {}:", stride, stride);
                for r in 0..stride {
                    let class_vals: Vec<String> = (r..vals.len())
                        .step_by(stride)
                        .map(|i| match vals[i] { Some(v) => v.to_string(), None => "?".to_string() })
                        .collect();
                    println!("    [mod {} = {}]: {}", stride, r, class_vals.join(" "));
                }
            }
        }
        let final_class = if all_pass { Class::Decreasing } else { Class::Alternating };
        println!();
        println!("final : {}", final_class);
    } else {
        println!("final : {}", base_class);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sv(ns: &[u64]) -> Vec<Option<u64>> {
        ns.iter().map(|&n| Some(n)).collect()
    }

    fn classify_full(vals: &[Option<u64>], max_stride: usize) -> Class {
        let class = classify(vals);
        let has_timeouts = vals.iter().any(|v| v.is_none());
        if class == Class::Decreasing && !has_timeouts && !all_strides_have_decrease(vals, max_stride) {
            Class::Alternating
        } else {
            class
        }
    }

    // --- all_strides_have_decrease unit tests ---

    #[test]
    fn stride_period2_no_decrease() {
        // stride-2 pairs are equal: (1,1), (2,2), ...
        assert!(!all_strides_have_decrease(&sv(&[1,2,1,2,1,2,1,2,1,2]), 5));
    }

    #[test]
    fn stride_period3_no_stride3_decrease() {
        // stride-3 pairs are equal; stride-2 does have a decrease so OR would pass this
        assert!(!all_strides_have_decrease(&sv(&[1,2,3,1,2,3,1,2,3,1,2,3]), 5));
    }

    #[test]
    fn stride_period4_no_stride4_decrease() {
        assert!(!all_strides_have_decrease(&sv(&[1,2,3,4,1,2,3,4,1,2,3,4]), 5));
    }

    #[test]
    fn stride_period5_no_stride5_decrease() {
        assert!(!all_strides_have_decrease(&sv(&[1,2,3,4,5,1,2,3,4,5,1,2,3,4,5]), 5));
    }

    #[test]
    fn stride_genuine_decrease_passes_all() {
        // strictly decreasing: every stride shows a decrease
        assert!(all_strides_have_decrease(&sv(&[100,90,80,70,60,50,40,30,20,10,9,8]), 5));
    }

    // --- full classify + stride-filter tests ---

    #[test]
    fn classify_period2_alternating() {
        assert_eq!(classify_full(&sv(&[1,2,1,2,1,2,1,2,1,2,1,2]), 5), Class::Alternating);
    }

    #[test]
    fn classify_period2_starting_high_alternating() {
        assert_eq!(classify_full(&sv(&[2,1,2,1,2,1,2,1,2,1,2,1]), 5), Class::Alternating);
    }

    #[test]
    fn classify_big_small_alternating() {
        // [10 5 12 6 14 7 16 8 18 9]: stride-2 subsequences are increasing
        assert_eq!(classify_full(&sv(&[10,5,12,6,14,7,16,8,18,9]), 5), Class::Alternating);
    }

    #[test]
    fn classify_period3_alternating() {
        // stride-2 has a decrease (3→2), but stride-3 does not
        assert_eq!(classify_full(&sv(&[3,1,2,3,1,2,3,1,2,3,1,2]), 5), Class::Alternating);
    }

    #[test]
    fn classify_period5_alternating() {
        assert_eq!(classify_full(&sv(&[1,2,3,4,5,1,2,3,4,5,1,2,3,4,5]), 5), Class::Alternating);
    }

    #[test]
    fn classify_genuine_decrease_is_decreasing() {
        assert_eq!(classify_full(&sv(&[100,90,80,70,60,50,40,30,20,10,9,8]), 5), Class::Decreasing);
    }

    #[test]
    fn classify_decrease_with_timeouts_not_filtered() {
        // Stride filter must be skipped when data is incomplete: the missing values
        // could be the ones that would show the stride-k decrease.
        let vals: Vec<Option<u64>> = vec![Some(10), None, Some(5), None, Some(8), None, Some(3)];
        assert_eq!(classify_full(&vals, 5), Class::Decreasing);
    }
}

fn main() {
    let args = Args::parse();

    if let Some(expr) = &args.probe {
        probe_grf(expr, &args);
        if args.files.is_empty() {
            return;
        }
        println!();
    }

    if args.files.is_empty() {
        eprintln!("error: no holdout files given (use --probe EXPR or pass a holdout file)");
        std::process::exit(1);
    }

    for path in &args.files {
        process_file(path, &args);
    }
}
