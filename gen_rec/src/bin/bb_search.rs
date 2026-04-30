/// Enumerate all 0-arity GRFs of increasing size and track BBµ champions.
///
/// Enumeration is single-threaded using a fully-streaming algorithm: GRF trees
/// are generated one at a time without materialising any Vec<Grf>, keeping peak
/// memory at ~20 MB regardless of size.  Simulation is parallelised with Rayon.
use clap::Parser;
use gen_rec::enumerate::{count_grf, stream_grf};
use gen_rec::grf::Grf;
use gen_rec::alias::alias_db_for_stdout;
use gen_rec::pruning::PruningOpts;
use gen_rec::simulate::{simulate, Num, SimResult};
use rayon::prelude::*;
use std::cell::Cell;
use std::time::{Duration, Instant};

#[derive(Parser, Debug)]
#[command(
    about = "Search for BBµ champions by exhaustive enumeration of 0-arity GRFs",
    long_about = None
)]
struct Args {
    /// Maximum size to enumerate up to.
    max_size: usize,

    /// Maximum steps per simulation before giving up (0 = unlimited).
    #[arg(long, default_value_t = 100_000_000)]
    max_steps: u64,

    /// Include Minimization combinator (default: PRF only).
    #[arg(long)]
    allow_min: bool,

    /// Only search M(f) where f is a PRF (arity-1, no nested Min).
    /// Mutually exclusive with --allow-min.
    #[arg(long, conflicts_with = "allow_min")]
    min_prf: bool,

    /// Batch size for parallel simulation (tune for your CPU count).
    #[arg(long, default_value_t = 2000)]
    batch_size: usize,

    /// How many future sizes to show time estimates for.
    #[arg(long, default_value_t = 3)]
    lookahead: usize,

    /// Show raw GRF strings instead of aliases.
    #[arg(long)]
    no_alias: bool,

    /// Enable inline-proj pruning (prune C(h, P/Z...) that inline to smaller form).
    #[arg(long)]
    inline_proj: bool,

    /// Number of distinct top scores to track and display per size.
    #[arg(long, default_value_t = 10)]
    top_k: usize,
}

// ---------------------------------------------------------------------------
// Top-K tracker
// ---------------------------------------------------------------------------

/// Track the top-K distinct scoring GRFs, retaining all exprs per score.
struct TopK {
    k: usize,
    /// Ascending by score; at most `k` entries.
    entries: Vec<(Num, Vec<String>)>,
}

impl TopK {
    fn new(k: usize) -> Self {
        TopK { k, entries: Vec::new() }
    }

    fn best(&self) -> Option<Num> {
        self.entries.last().map(|(v, _)| *v)
    }

    fn insert(&mut self, score: Num, expr: String) {
        match self.entries.binary_search_by_key(&score, |(s, _)| *s) {
            Ok(idx) => self.entries[idx].1.push(expr),
            Err(idx) => {
                self.entries.insert(idx, (score, vec![expr]));
                if self.entries.len() > self.k {
                    self.entries.remove(0); // drop lowest score
                }
            }
        }
    }

    fn merge_from(&mut self, other: TopK) {
        for (score, exprs) in other.entries {
            for expr in exprs {
                self.insert(score, expr);
            }
        }
    }

    /// Iterate entries from highest to lowest score.
    fn iter_desc(&self) -> impl Iterator<Item = &(Num, Vec<String>)> {
        self.entries.iter().rev()
    }
}

// ---------------------------------------------------------------------------
// Batch processing
// ---------------------------------------------------------------------------

struct BatchResult {
    top_k: TopK,
    timed_out: usize,
    diverged: usize,
    total_steps: u64,
    max_steps_single: u64,
}

struct SizeResult {
    size: usize,
    total: usize,
    timed_out: usize,
    diverged: usize,
    top_k: TopK,
    total_steps: u64,
    max_steps_single: u64,
}

fn process_batch(batch: &[Grf], max_steps: u64, k: usize) -> BatchResult {
    let outcomes: Vec<(SimResult, u64, String)> = batch
        .par_iter()
        .map(|grf| {
            let (result, steps) = simulate(grf, &[], max_steps);
            (result, steps, grf.to_string())
        })
        .collect();

    let mut top_k = TopK::new(k);
    let mut timed_out = 0usize;
    let mut diverged = 0usize;
    let mut total_steps = 0u64;
    let mut max_steps_single = 0u64;

    for (result, steps, display) in outcomes {
        total_steps += steps;
        match result {
            SimResult::OutOfSteps => timed_out += 1,
            SimResult::Diverge => diverged += 1,
            SimResult::Value(v) => {
                if steps > max_steps_single {
                    max_steps_single = steps;
                }
                top_k.insert(v, display);
            }
        }
    }
    BatchResult { top_k, timed_out, diverged, total_steps, max_steps_single }
}

fn merge_batch(
    br: BatchResult,
    size_top_k: &mut TopK,
    size_timed_out: &mut usize,
    size_diverged: &mut usize,
    size_total_steps: &mut u64,
    size_max_steps: &mut u64,
) {
    *size_timed_out += br.timed_out;
    *size_diverged += br.diverged;
    *size_total_steps += br.total_steps;
    if br.max_steps_single > *size_max_steps {
        *size_max_steps = br.max_steps_single;
    }
    size_top_k.merge_from(br.top_k);
}

// ---------------------------------------------------------------------------
// Time estimation helpers
// ---------------------------------------------------------------------------

fn estimate_time(
    future_size: usize,
    allow_min: bool,
    min_prf: bool,
    count_opts: PruningOpts,
    secs_per_fn: f64,
) -> Option<f64> {
    let count = count_at_size(future_size, allow_min, min_prf, count_opts);
    if count == 0 || secs_per_fn <= 0.0 {
        return None;
    }
    Some(count as f64 * secs_per_fn)
}

fn count_at_size(size: usize, allow_min: bool, min_prf: bool, count_opts: PruningOpts) -> usize {
    if min_prf {
        if size < 2 { 0 } else { count_grf(size - 1, 1, false, count_opts) }
    } else {
        count_grf(size, 0, allow_min, count_opts)
    }
}

fn fmt_duration(secs: f64) -> String {
    if secs < 60.0 {
        format!("{:.1}s", secs)
    } else if secs < 3600.0 {
        format!("{:.1}m", secs / 60.0)
    } else if secs < 86400.0 {
        format!("{:.1}h", secs / 3600.0)
    } else {
        format!("{:.1}d", secs / 86400.0)
    }
}

fn fmt_si(n: u64) -> String {
    if n < 1_000 {
        format!("{}", n)
    } else {
        fmt_si_f64(n as f64)
    }
}
fn fmt_si_f64(n: f64) -> String {
    if n < 1_000.0 {
        format!("{:.1}", n)
    } else if n < 1_000_000.0 {
        format!("{:.1}k", n / 1_000.0)
    } else if n < 1_000_000_000.0 {
        format!("{:.1}M", n / 1_000_000.0)
    } else if n < 1_000_000_000_000.0 {
        format!("{:.1}B", n / 1_000_000_000.0)
    } else {
        format!("{:.1}T", n / 1_000_000_000_000.0)
    }
}

fn main() {
    let args = Args::parse();
    let count_opts = PruningOpts::default(); // count_grf doesn't support skip_inline_proj
    let opts = PruningOpts {
        skip_inline_proj: args.inline_proj,
        skip_min_dominated: true,
        ..PruningOpts::default()
    };

    let mode_str = if args.min_prf {
        "M(PRF)"
    } else if args.allow_min {
        "GRF"
    } else {
        "PRF"
    };

    println!(
        "BBµ search: 0-arity {}, max_size={}, max_steps={}, opts={:?}, threads={}, batch={}",
        mode_str,
        args.max_size,
        args.max_steps,
        opts,
        rayon::current_num_threads(),
        args.batch_size,
    );
    println!("{}", "=".repeat(90));

    let alias_db = alias_db_for_stdout(6, args.no_alias);
    let fmt = |expr: &str| -> String {
        match &alias_db {
            Some(db) => expr.parse::<Grf>().map(|g| db.alias(&g)).unwrap_or_else(|_| expr.to_string()),
            None => expr.to_string(),
        }
    };
    let mut results: Vec<SizeResult> = Vec::new();
    let mut smoothed_secs_per_fn: Option<f64> = None;
    let total_start = Instant::now();

    for size in 1..=args.max_size {
        let size_start = Instant::now();

        let mut total = 0usize;
        let mut size_timed_out = 0usize;
        let mut size_diverged = 0usize;
        let mut size_top_k = TopK::new(args.top_k);
        let mut size_total_steps: u64 = 0;
        let mut size_max_steps: u64 = 0;
        let mut batch: Vec<Grf> = Vec::with_capacity(args.batch_size);

        let sim_time_cell = Cell::new(Duration::ZERO);

        let flush = |batch: &mut Vec<Grf>,
                     top_k: &mut TopK,
                     timed_out: &mut usize,
                     diverged: &mut usize,
                     total_steps: &mut u64,
                     max_steps: &mut u64| {
            if batch.is_empty() {
                return;
            }
            let sim_start = Instant::now();
            let br = process_batch(batch, args.max_steps, args.top_k);
            sim_time_cell.set(sim_time_cell.get() + sim_start.elapsed());
            merge_batch(br, top_k, timed_out, diverged, total_steps, max_steps);
            batch.clear();
        };

        if args.min_prf && size >= 2 {
            // Enumerate M(f) where f is a PRF of arity 1 and size (size-1).
            stream_grf(size - 1, 1, false, opts, &mut |f: &Grf| {
                // Apply skip_min_dominated checks (stream-only, not in count_grf).
                if opts.skip_min_dominated {
                    if !f.used_args().contains(&1) { return; }
                    if f.is_never_zero() { return; }
                }
                total += 1;
                batch.push(Grf::min(f.clone()));
                if batch.len() >= args.batch_size {
                    flush(
                        &mut batch,
                        &mut size_top_k,
                        &mut size_timed_out,
                        &mut size_diverged,
                        &mut size_total_steps,
                        &mut size_max_steps,
                    );
                }
            });
        } else if !args.min_prf {
            stream_grf(size, 0, args.allow_min, opts, &mut |grf: &Grf| {
                total += 1;
                batch.push(grf.clone());
                if batch.len() >= args.batch_size {
                    flush(
                        &mut batch,
                        &mut size_top_k,
                        &mut size_timed_out,
                        &mut size_diverged,
                        &mut size_total_steps,
                        &mut size_max_steps,
                    );
                }
            });
        }
        flush(
            &mut batch,
            &mut size_top_k,
            &mut size_timed_out,
            &mut size_diverged,
            &mut size_total_steps,
            &mut size_max_steps,
        );

        let elapsed = size_start.elapsed().as_secs_f64();
        let sim_secs = sim_time_cell.get().as_secs_f64();
        let enum_secs = elapsed - sim_secs;

        if total > 0 {
            let cur_rate = elapsed / total as f64;
            smoothed_secs_per_fn = Some(match smoothed_secs_per_fn {
                None => cur_rate,
                Some(prev) => 0.3 * cur_rate + 0.7 * prev,
            });
        }

        let best_str = match size_top_k.best() {
            Some(v) => v.to_string(),
            None => "-".to_string(),
        };

        println!(
            "n={}: best={}, {} holdouts, {} fns  [{:.2}s sim={:.2}s enum={:.2}s, {} steps, {} steps/s]",
            size,
            best_str,
            size_timed_out,
            total,
            elapsed,
            sim_secs,
            enum_secs,
            fmt_si(size_total_steps),
            fmt_si_f64(size_total_steps as f64 / elapsed.max(1e-9)),
        );

        // Print top-k scores.
        const MAX_EXPRS_PER_SCORE: usize = 5;
        for (rank, (score, exprs)) in size_top_k.iter_desc().enumerate() {
            let shown = exprs.len().min(MAX_EXPRS_PER_SCORE);
            let overflow = exprs.len().saturating_sub(MAX_EXPRS_PER_SCORE);
            print!("  #{}: score={}", rank + 1, score);
            if exprs.len() > 1 {
                print!(" ({} tied)", exprs.len());
            }
            println!();
            for expr in exprs.iter().take(shown) {
                println!("       via {}", fmt(expr));
            }
            if overflow > 0 {
                println!("       ... (+{} more)", overflow);
            }
        }
        if size_timed_out > 0 {
            println!(
                "       max_single={}, total_steps={}",
                fmt_si(size_max_steps),
                fmt_si(size_total_steps),
            );
        }

        if size < args.max_size && args.lookahead > 0 {
            if let Some(rate) = smoothed_secs_per_fn {
                let estimates: Vec<String> = (1..=args.lookahead)
                    .filter_map(|ds| {
                        let future = size + ds;
                        let est = estimate_time(future, args.allow_min, args.min_prf, count_opts, rate)?;
                        let count = count_at_size(future, args.allow_min, args.min_prf, count_opts);
                        Some(format!(
                            "n={}: ~{} ({} fns)",
                            future,
                            fmt_duration(est),
                            count
                        ))
                    })
                    .collect();
                if !estimates.is_empty() {
                    println!("       est: {}", estimates.join("  |  "));
                }
            }
        }

        results.push(SizeResult {
            size,
            total,
            timed_out: size_timed_out,
            diverged: size_diverged,
            top_k: size_top_k,
            total_steps: size_total_steps,
            max_steps_single: size_max_steps,
        });
    }

    let total_elapsed = total_start.elapsed().as_secs_f64();

    let has_min = args.allow_min || args.min_prf;
    let sep_width = if has_min { 101 } else { 90 };

    println!();
    println!("{}", "=".repeat(sep_width));
    println!(
        "BBµ_{} summary  (opts={:?}, max_steps={})",
        mode_str,
        opts,
        args.max_steps
    );
    println!("{}", "=".repeat(sep_width));
    if has_min {
        println!(
            "{:>4}  {:>10}  {:>10}  {:>10}  {:>10}  {:>10}  {:>10}  {}",
            "n", "BBµ(n) ≥", "max_steps", "holdouts", "#diverge", "#fns", "tot_steps", "Champion"
        );
    } else {
        println!(
            "{:>4}  {:>10}  {:>10}  {:>10}  {:>10}  {:>10}  {}",
            "n", "BBµ(n) ≥", "max_steps", "holdouts", "#fns", "tot_steps", "Champion"
        );
    }
    println!("{}", "-".repeat(sep_width));
    for r in &results {
        let best = r.top_k.best();
        let max_val_str = match best {
            Some(v) => v.to_string(),
            None => "-".to_string(),
        };
        let expr_str = match r.top_k.iter_desc().next() {
            None => "-".to_string(),
            Some((_, exprs)) => {
                let s = fmt(&exprs[0]);
                if exprs.len() > 1 {
                    format!("{s}  (+{} ties)", exprs.len() - 1)
                } else {
                    s
                }
            }
        };
        if has_min {
            println!(
                "{:>4}  {:>10}  {:>10}  {:>10}  {:>10}  {:>10}  {:>10}  {}",
                r.size,
                max_val_str,
                fmt_si(r.max_steps_single),
                r.timed_out,
                r.diverged,
                r.total,
                fmt_si(r.total_steps),
                expr_str,
            );
        } else {
            println!(
                "{:>4}  {:>10}  {:>10}  {:>10}  {:>10}  {:>10}  {}",
                r.size,
                max_val_str,
                fmt_si(r.max_steps_single),
                r.timed_out,
                r.total,
                fmt_si(r.total_steps),
                expr_str,
            );
        }
    }
    println!("{}", "-".repeat(sep_width));
    println!("Total time: {:.2}s", total_elapsed);
}
