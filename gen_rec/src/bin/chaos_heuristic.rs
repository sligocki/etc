/// Chaos-score heuristic for M(f) holdouts.
///
/// For each M(f) in a holdout file, evaluates the inner function f(0..max_val)
/// and computes a "chaos score": how many terms were needed before any simple
/// predictor (Berlekamp-Massey linear recurrence, or direct period-k check)
/// stayed correct for `stability` consecutive steps.  Never-locked sequences
/// (score = ∞) are the most interesting — they resist all pattern detection.
///
/// Output is sorted by chaos score descending (∞ first).
///
/// Usage:
///   cargo run --bin chaos_heuristic -- results/min_prf/16_100k/holdout.txt
///   cargo run --bin chaos_heuristic -- --probe 'M(C(R(Z0,P(2,1)),C(S,S)))' --max-val 40
use clap::Parser;
use gen_rec::chaos_score::chaos_score;
use gen_rec::grf::Grf;
use gen_rec::io_grl;
use gen_rec::mgrf::parse_mgrf_to_grfs;
use gen_rec::simulate::simulate;
use std::fs;
use std::path::PathBuf;

#[derive(Parser, Debug)]
#[command(about = "Chaos-score heuristic: rank M(f) holdouts by sequence unpredictability")]
struct Args {
    /// Holdout files to scan.
    files: Vec<PathBuf>,

    /// Evaluate inner PRF on f(0)..f(max_val).
    #[arg(long, default_value_t = 100)]
    max_val: u64,

    /// Step budget per individual simulation call (0 = unlimited).
    #[arg(long, default_value_t = 100_000)]
    max_steps: u64,

    /// Consecutive correct predictions needed to declare pattern found.
    #[arg(long, default_value_t = 12)]
    stability: usize,

    /// Max period for direct period-k predictors (complements BM for short histories).
    #[arg(long, default_value_t = 8)]
    max_period: usize,

    /// Reject Berlekamp-Massey recurrences longer than this (avoids overfitting).
    #[arg(long, default_value_t = 16)]
    max_recurrence: usize,

    /// Also run BM predictors that skip the first k terms (k=1..max_transient).
    /// Detects sequences with a transient prefix that doesn't fit the eventual
    /// linear recurrence (e.g. a[0]=1 followed by a[n]=2*a[n-1]+1 for n>=1).
    #[arg(long, default_value_t = 3)]
    max_transient: usize,

    /// Allow lock-on this many steps before stability threshold at end of sequence.
    /// Prevents missing obvious patterns in short sequences (e.g. exponential growth
    /// that times out after ~15 terms).  Set to 0 for strict mode.
    #[arg(long, default_value_t = 2)]
    end_slack: usize,

    /// Show all entries, not just the top N.
    #[arg(long)]
    verbose: bool,

    /// Show at most N entries (0 = all).
    #[arg(long, default_value_t = 20)]
    top: usize,

    /// Probe a single expression: show values and chaos score detail.
    #[arg(long)]
    probe: Option<String>,
}

struct Entry {
    expr: String,
    vals: Vec<u64>,
    score: Option<usize>, // None = never locked
}

fn fmt_vals(vals: &[u64], limit: usize) -> String {
    let shown: Vec<String> = vals.iter().take(limit).map(|v| v.to_string()).collect();
    if vals.len() > limit {
        format!("[{} ...]", shown.join(" "))
    } else {
        format!("[{}]", shown.join(" "))
    }
}

fn score_display(score: Option<usize>) -> String {
    match score {
        None => "  ∞".to_string(),
        Some(s) => format!("{:3}", s),
    }
}

fn evaluate_inner(inner: &Grf, max_val: u64, budget: u64) -> Vec<u64> {
    let mut vals = Vec::with_capacity(max_val as usize);
    for n in 0..max_val {
        match simulate(inner, &[n], budget).0.into_value() {
            Some(v) => vals.push(v),
            None => break, // stop on first timeout/diverge to keep sequence contiguous
        }
    }
    vals
}

fn parse_mgrf_expr(expr: &str) -> Result<Grf, String> {
    let content = format!("Probe := {}", expr);
    parse_mgrf_to_grfs(&content)?
        .into_iter()
        .next()
        .map(|(_, g)| g)
        .ok_or_else(|| "no definition produced".to_string())
}

fn probe_entry(expr: &str, args: &Args) {
    let grf: Grf = match parse_mgrf_expr(expr) {
        Ok(g) => g,
        Err(e) => { eprintln!("parse error: {}", e); return; }
    };
    let inner = match &grf {
        Grf::Min(f) => f.as_ref().clone(),
        _ => grf.clone(),
    };
    if inner.arity() != 1 {
        eprintln!("inner arity {} != 1, cannot probe", inner.arity());
        return;
    }
    let budget = if args.max_steps == 0 { u64::MAX } else { args.max_steps };
    let vals = evaluate_inner(&inner, args.max_val, budget);
    let score = chaos_score(&vals, args.stability, args.max_recurrence, args.max_period, args.max_transient, args.end_slack);

    println!("expr    : {}", expr);
    println!("values  : {}", fmt_vals(&vals, 40));
    println!("n_terms : {}", vals.len());
    match score {
        Some(t) => println!("lock-on : step {} (after seeing {} terms)", t, t + 2),
        None     => println!("lock-on : ∞  (no predictor stabilised; stability={}, max_period={}, max_recurrence={})",
            args.stability, args.max_period, args.max_recurrence),
    }
}

fn process_file(path: &PathBuf, args: &Args) {
    let content = match fs::read_to_string(path) {
        Ok(c) => c,
        Err(e) => { eprintln!("error reading {}: {}", path.display(), e); return; }
    };

    let budget = if args.max_steps == 0 { u64::MAX } else { args.max_steps };
    let mut entries: Vec<Entry> = Vec::new();
    let mut skipped = 0usize;

    for entry in io_grl::parse_grf_entries(&content) {
        let expr = &entry.expr;

        let grf: Grf = match expr.parse() {
            Ok(g) => g,
            Err(e) => { eprintln!("parse error ({}): {}", e, expr); continue; }
        };
        let inner = match &grf {
            Grf::Min(f) => f.as_ref().clone(),
            _ => { eprintln!("expected M(...), got: {}", expr); continue; }
        };
        if inner.arity() != 1 {
            skipped += 1;
            continue;
        }
        if inner.is_never_zero() || inner.is_positive_for_pos_arg(1) {
            skipped += 1;
            continue;
        }

        let vals = evaluate_inner(&inner, args.max_val, budget);
        let score = chaos_score(&vals, args.stability, args.max_recurrence, args.max_period, args.max_transient, args.end_slack);
        entries.push(Entry { expr: expr.to_string(), vals, score });
    }

    // Sort: None (∞) first, then descending by score.
    entries.sort_by(|a, b| match (a.score, b.score) {
        (None, None) => std::cmp::Ordering::Equal,
        (None, Some(_)) => std::cmp::Ordering::Less,
        (Some(_), None) => std::cmp::Ordering::Greater,
        (Some(x), Some(y)) => y.cmp(&x),
    });

    let total = entries.len();
    let never_locked = entries.iter().filter(|e| e.score.is_none()).count();
    let locked_scores: Vec<usize> = entries.iter().filter_map(|e| e.score).collect();
    let mean_locked = if locked_scores.is_empty() {
        None
    } else {
        Some(locked_scores.iter().sum::<usize>() as f64 / locked_scores.len() as f64)
    };

    println!("=== {} ===", path.display());

    let show_limit = if args.verbose || args.top == 0 { entries.len() } else { args.top };
    for entry in entries.iter().take(show_limit) {
        println!("lock={} {}  {}", score_display(entry.score), entry.expr, fmt_vals(&entry.vals, 20));
    }
    if !args.verbose && args.top > 0 && entries.len() > args.top {
        println!("  ... ({} more entries)", entries.len() - args.top);
    }

    print!("--- total: {}  skipped: {}  undetected: {}", total, skipped, never_locked);
    if let Some(mean) = mean_locked {
        print!("  mean-lock: {:.1}", mean);
    }
    println!();
    println!();
}

fn main() {
    let args = Args::parse();

    if let Some(expr) = &args.probe {
        probe_entry(expr, &args);
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
