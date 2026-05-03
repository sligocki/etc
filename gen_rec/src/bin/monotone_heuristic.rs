/// Heuristic scan of M(PRF) holdouts: flag inner PRFs that are non-monotone.
///
/// If the inner PRF f(n) never decreases, M(f) is unlikely to halt (it must
/// reach 0).  If f(n+1) < f(n) for some n, there is at least a structural
/// path toward zero.
///
/// Usage:
///   monotone_heuristic results/min_prf/14_10M/holdout.txt
///   monotone_heuristic --max-val 20 --max-steps 100000 holdout.txt
use clap::Parser;
use gen_rec::grf::Grf;
use gen_rec::simulate::simulate;
use std::fs;
use std::path::PathBuf;

#[derive(Parser, Debug)]
#[command(about = "Heuristic: flag M(PRF) holdouts whose inner PRF is non-monotone")]
struct Args {
    /// Holdout files to scan.
    files: Vec<PathBuf>,

    /// Evaluate inner PRF on inputs min_val..max_val.
    #[arg(long, default_value_t = 10)]
    min_val: u64,

    /// Evaluate inner PRF on inputs min_val..max_val.
    #[arg(long, default_value_t = 30)]
    max_val: u64,

    /// Step budget per individual inner-PRF call (0 = unlimited).
    #[arg(long, default_value_t = 100_000)]
    max_steps: u64,

    /// Print all entries, not just candidates.
    #[arg(long)]
    verbose: bool,
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum Class {
    /// f(n) == 0 for some n in range — M(f) would halt if it reached that n.
    HitsZero,
    /// f(n+1) < f(n) for some n — non-monotone, candidate to halt.
    Decreasing,
    /// At least one simulation timed out; sequence is partially unknown.
    Timeout,
    /// f is non-decreasing and always > 0 across the tested range.
    Monotone,
}

impl std::fmt::Display for Class {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Class::HitsZero   => write!(f, "hits-zero "),
            Class::Decreasing => write!(f, "decreasing"),
            Class::Timeout    => write!(f, "timeout   "),
            Class::Monotone   => write!(f, "monotone  "),
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

    let mut total = 0usize;
    let mut n_hits_zero  = 0usize;
    let mut n_decreasing = 0usize;
    let mut n_timeout    = 0usize;
    let mut n_monotone   = 0usize;

    println!("=== {} ===", path.display());

    for line in content.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }

        // Line format: "STEPS  EXPR"
        let mut parts = line.splitn(2, |c: char| c.is_whitespace());
        let _steps = parts.next().unwrap_or("").trim();
        let expr = match parts.next() {
            Some(e) => e.trim(),
            None => continue,
        };

        let grf: Grf = match expr.parse() {
            Ok(g) => g,
            Err(e) => { eprintln!("parse error ({}): {}", e, expr); continue; }
        };

        let inner = match &grf {
            Grf::Min(f) => f.as_ref().clone(),
            _ => { eprintln!("expected M(...), got: {}", expr); continue; }
        };

        if inner.arity() != 1 {
            eprintln!("inner arity {} != 1, skipping: {}", inner.arity(), expr);
            continue;
        }

        // Skip trivial stuff
        if inner.is_never_zero() { continue; }

        let vals: Vec<Option<u64>> = (args.min_val..args.max_val)
            .map(|n| simulate(&inner, &[n], budget).0.into_value())
            .collect();

        let class = classify(&vals);
        total += 1;

        match class {
            Class::HitsZero   => n_hits_zero  += 1,
            Class::Decreasing => n_decreasing += 1,
            Class::Timeout    => n_timeout    += 1,
            Class::Monotone   => n_monotone   += 1,
        }

        let is_candidate = matches!(class, Class::HitsZero | Class::Decreasing | Class::Timeout);
        if is_candidate || args.verbose {
            println!("[{}] {}  [{}]", class, expr, fmt_vals(&vals));
        }
    }

    println!(
        "--- total: {}  hits-zero: {}  decreasing: {}  timeout: {}  monotone: {}",
        total, n_hits_zero, n_decreasing, n_timeout, n_monotone
    );
    println!();
}

fn main() {
    let args = Args::parse();

    if args.files.is_empty() {
        eprintln!("error: no holdout files given");
        std::process::exit(1);
    }

    for path in &args.files {
        process_file(path, &args);
    }
}
