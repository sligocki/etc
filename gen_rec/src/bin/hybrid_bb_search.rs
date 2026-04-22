/// Hybrid BBµ search: novel memo for sub-expressions ≤ threshold, exhaustive
/// streaming above.
///
/// Small sub-expressions (size ≤ threshold) are deduplicated by the
/// NovelEnumerator with generous fp_inputs — correctness is controlled by
/// how many fingerprint inputs you provide, not by a size-dependent compromise.
/// Sub-expressions above threshold are streamed exhaustively from canonical
/// small pieces, with no fingerprinting and therefore no false-positive risk.
///
/// This separates the two concerns: spend fingerprint budget on small GRFs
/// where it is cheap and effective; enumerate large GRFs completely.
use clap::Parser;
use gen_rec::grf::Grf;
use gen_rec::alias::AliasDb;
use gen_rec::novel_enum::NovelEnumerator;
use gen_rec::simulate::{simulate, Num};
use rayon::prelude::*;
use std::cell::Cell;
use std::time::{Duration, Instant};

#[derive(Parser, Debug)]
#[command(
    about = "BBµ search: novel memo for sub-expressions ≤ threshold, streaming above",
    long_about = None,
)]
struct Args {
    /// Maximum size to enumerate up to.
    max_size: usize,

    /// Sub-expressions of size ≤ threshold are replaced by canonical
    /// representatives from the novel memo.  Above threshold everything is
    /// enumerated exhaustively.  Default 12 keeps memo-building cheap while
    /// covering all interesting sub-expression structure.
    #[arg(long, default_value_t = 12)]
    threshold: usize,

    /// Maximum steps per simulation before giving up (0 = unlimited).
    #[arg(long, default_value_t = 100_000_000)]
    max_steps: u64,

    /// Fingerprint inputs used when building the novel memo.  More inputs →
    /// fewer false-positive equivalences → safer pruning.
    #[arg(long, default_value_t = 128)]
    fp_inputs: usize,

    /// Step budget per fingerprint evaluation (should be << max_steps).
    #[arg(long, default_value_t = 100_000)]
    fp_steps: u64,

    /// Include Minimization combinator (default: PRF only).
    #[arg(long)]
    allow_min: bool,

    /// Batch size for parallel simulation.
    #[arg(long, default_value_t = 2000)]
    batch_size: usize,

    /// Print per-arity memo stats after each size.
    #[arg(long)]
    verbose: bool,

    /// Show raw GRF strings instead of aliases.
    #[arg(long)]
    no_alias: bool,
}

struct BatchResult {
    best_value: Option<Num>,
    best_exprs: Vec<String>,
    timed_out: usize,
    total_steps: u64,
    max_steps_single: u64,
}

fn process_batch(batch: &[Grf], max_steps: u64) -> BatchResult {
    let outcomes: Vec<(Option<Num>, u64, String)> = batch
        .par_iter()
        .map(|grf| {
            let (result, steps) = simulate(grf, &[], max_steps);
            (result.into_value(), steps, grf.to_string())
        })
        .collect();

    let mut best_val: Option<Num> = None;
    let mut best_exprs: Vec<String> = Vec::new();
    let mut timed_out = 0usize;
    let mut total_steps = 0u64;
    let mut max_steps_single = 0u64;

    for (value, steps, display) in outcomes {
        total_steps += steps;
        if steps > max_steps_single {
            max_steps_single = steps;
        }
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
    BatchResult { best_value: best_val, best_exprs, timed_out, total_steps, max_steps_single }
}

fn merge_batch(
    br: BatchResult,
    best_val: &mut Option<Num>,
    best_exprs: &mut Vec<String>,
    timed_out: &mut usize,
    total_steps: &mut u64,
    max_steps: &mut u64,
) {
    *timed_out += br.timed_out;
    *total_steps += br.total_steps;
    if br.max_steps_single > *max_steps {
        *max_steps = br.max_steps_single;
    }
    if let Some(v) = br.best_value {
        let cmp = best_val
            .as_ref()
            .map_or(std::cmp::Ordering::Greater, |cur| v.cmp(cur));
        match cmp {
            std::cmp::Ordering::Greater => {
                *best_val = Some(v);
                *best_exprs = br.best_exprs;
            }
            std::cmp::Ordering::Equal => best_exprs.extend(br.best_exprs),
            std::cmp::Ordering::Less => {}
        }
    }
}

fn fmt_si(n: u64) -> String {
    if n < 1_000 {
        format!("{}", n)
    } else if n < 1_000_000 {
        format!("{:.1}k", n as f64 / 1_000.0)
    } else if n < 1_000_000_000 {
        format!("{:.1}M", n as f64 / 1_000_000.0)
    } else if n < 1_000_000_000_000 {
        format!("{:.1}B", n as f64 / 1_000_000_000.0)
    } else {
        format!("{:.1}T", n as f64 / 1_000_000_000_000.0)
    }
}

fn main() {
    let args = Args::parse();

    println!(
        "Hybrid BBµ search: 0-arity {}, max_size={}, threshold={}, fp_inputs={}, \
         max_steps={}, threads={}, batch={}",
        if args.allow_min { "GRF" } else { "PRF" },
        args.max_size,
        args.threshold,
        args.fp_inputs,
        args.max_steps,
        rayon::current_num_threads(),
        args.batch_size,
    );

    let alias_db = if args.no_alias { None } else { Some(AliasDb::default()) };
    let fmt = |expr: &str| -> String {
        match &alias_db {
            Some(db) => expr.parse::<Grf>().map(|g| db.alias(&g)).unwrap_or_else(|_| expr.to_string()),
            None => expr.to_string(),
        }
    };
    let mut en = NovelEnumerator::new(args.fp_inputs, args.fp_steps, args.allow_min);

    // Pre-build the novel memo up to the threshold.  This is the only place
    // where fingerprinting happens; everything above threshold is streamed
    // without any fingerprint computation.
    println!("Building novel memo for sizes 1..={} ...", args.threshold);
    let warmup_start = Instant::now();
    for size in 1..=args.threshold.min(args.max_size) {
        en.compute_size(0, size);
    }
    let warmup_elapsed = warmup_start.elapsed().as_secs_f64();
    {
        let stats = en.memo_stats();
        let total_novel: usize = stats.iter().map(|&(_, _, n)| n).sum();
        println!(
            "Memo ready: {} (arity,size) pairs, {} novel GRFs [{:.2}s]",
            stats.len(),
            total_novel,
            warmup_elapsed,
        );
        if args.verbose {
            let mut by_arity: std::collections::BTreeMap<usize, (usize, usize)> =
                std::collections::BTreeMap::new();
            for &(a, s, n) in &stats {
                let e = by_arity.entry(a).or_insert((0, 0));
                e.0 = e.0.max(s);
                e.1 += n;
            }
            let lines: Vec<String> = by_arity
                .iter()
                .map(|(&a, &(max_s, total))| format!("a{}:s1..{}({})", a, max_s, total))
                .collect();
            println!("       {}", lines.join("  "));
        }
    }
    println!("{}", "=".repeat(90));

    struct SizeResult {
        size: usize,
        total: usize,
        timed_out: usize,
        best_value: Option<Num>,
        best_exprs: Vec<String>,
        total_steps: u64,
        max_steps_single: u64,
    }

    let mut results: Vec<SizeResult> = Vec::new();
    let total_start = Instant::now();

    for size in 1..=args.max_size {
        let size_start = Instant::now();

        let mut total = 0usize;
        let mut size_best_val: Option<Num> = None;
        let mut size_best_exprs: Vec<String> = Vec::new();
        let mut size_timed_out = 0usize;
        let mut size_total_steps: u64 = 0;
        let mut size_max_steps: u64 = 0;
        let mut batch: Vec<Grf> = Vec::with_capacity(args.batch_size);

        let sim_time_cell = Cell::new(Duration::ZERO);
        let batch_size = args.batch_size;
        let max_steps_sim = args.max_steps;

        let flush = |batch: &mut Vec<Grf>,
                     best_val: &mut Option<Num>,
                     best_exprs: &mut Vec<String>,
                     timed_out: &mut usize,
                     total_steps: &mut u64,
                     max_steps: &mut u64| {
            if batch.is_empty() {
                return;
            }
            let sim_start = Instant::now();
            let br = process_batch(batch, max_steps_sim);
            sim_time_cell.set(sim_time_cell.get() + sim_start.elapsed());
            merge_batch(br, best_val, best_exprs, timed_out, total_steps, max_steps);
            batch.clear();
        };

        if size > args.threshold {
            en.pre_warm_for_size(size, args.threshold);
        }
        en.stream_from_novel_db(0, size, args.threshold, &mut |grf: &Grf| {
            total += 1;
            batch.push(grf.clone());
            if batch.len() >= batch_size {
                flush(
                    &mut batch,
                    &mut size_best_val,
                    &mut size_best_exprs,
                    &mut size_timed_out,
                    &mut size_total_steps,
                    &mut size_max_steps,
                );
            }
        });
        flush(
            &mut batch,
            &mut size_best_val,
            &mut size_best_exprs,
            &mut size_timed_out,
            &mut size_total_steps,
            &mut size_max_steps,
        );

        let elapsed = size_start.elapsed().as_secs_f64();
        let sim_secs = sim_time_cell.get().as_secs_f64();
        let enum_secs = elapsed - sim_secs;

        let best_str = match &size_best_val {
            Some(v) => v.to_string(),
            None => "-".to_string(),
        };

        println!(
            "n={:>3}: best={:<12} {:>8} candidates  {} holdouts  \
             [{:.2}s enum={:.2}s sim={:.2}s  {} steps]",
            size,
            best_str,
            total,
            size_timed_out,
            elapsed,
            enum_secs,
            sim_secs,
            fmt_si(size_total_steps),
        );
        const MAX_VIA: usize = 5;
        for expr in size_best_exprs.iter().take(MAX_VIA) {
            println!("       via {}", fmt(expr));
        }
        if size_best_exprs.len() > MAX_VIA {
            println!("       ... (+{} more tied)", size_best_exprs.len() - MAX_VIA);
        }
        if size_timed_out > 0 {
            println!(
                "       max_single={} total_steps={}",
                fmt_si(size_max_steps),
                fmt_si(size_total_steps),
            );
        }

        if args.verbose {
            let stats = en.memo_stats();
            let total_pairs = stats.len();
            let total_novel: usize = stats.iter().map(|&(_, _, n)| n).sum();
            eprintln!(
                "       memo: {} (arity,size) pairs, {} total novel GRFs",
                total_pairs, total_novel
            );
            let mut by_arity: std::collections::BTreeMap<usize, (usize, usize)> =
                std::collections::BTreeMap::new();
            for &(a, s, n) in &stats {
                let e = by_arity.entry(a).or_insert((0, 0));
                e.0 = e.0.max(s);
                e.1 += n;
            }
            let lines: Vec<String> = by_arity
                .iter()
                .map(|(&a, &(max_s, total))| format!("a{}:s1..{}({})", a, max_s, total))
                .collect();
            eprintln!("       {}", lines.join("  "));
        }

        results.push(SizeResult {
            size,
            total,
            timed_out: size_timed_out,
            best_value: size_best_val,
            best_exprs: size_best_exprs,
            total_steps: size_total_steps,
            max_steps_single: size_max_steps,
        });
    }

    let total_elapsed = total_start.elapsed().as_secs_f64();

    println!();
    println!("{}", "=".repeat(90));
    println!(
        "Hybrid BBµ_{} summary  (threshold={}, fp_inputs={}, max_steps={})",
        if args.allow_min { "GRF" } else { "PRF" },
        args.threshold,
        args.fp_inputs,
        args.max_steps,
    );
    println!("{}", "=".repeat(90));
    println!(
        "{:>4}  {:>12}  {:>10}  {:>8}  {:>10}  {}",
        "n", "BBµ(n)≥", "candidates", "holdouts", "tot_steps", "Champion"
    );
    println!("{}", "-".repeat(90));
    for r in &results {
        let val_str = match &r.best_value {
            Some(v) => v.to_string(),
            None => "-".to_string(),
        };
        let expr_str = if r.best_exprs.is_empty() {
            "-".to_string()
        } else {
            let s = fmt(&r.best_exprs[0]);
            if r.best_exprs.len() > 1 {
                format!("{s}  (+{} ties)", r.best_exprs.len() - 1)
            } else {
                s
            }
        };
        println!(
            "{:>4}  {:>12}  {:>10}  {:>8}  {:>10}  {}",
            r.size, val_str, r.total, r.timed_out, fmt_si(r.total_steps), expr_str,
        );
    }
    println!("{}", "-".repeat(90));
    println!("Total time: {:.2}s", total_elapsed);
}
