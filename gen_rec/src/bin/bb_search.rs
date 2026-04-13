/// Enumerate all 0-arity PRF of increasing size and track BBµ champions.
///
/// Enumeration is single-threaded using a fully-streaming algorithm: GRF trees
/// are generated one at a time without materialising any Vec<Grf>, keeping peak
/// memory at ~20 MB regardless of size.  Simulation is parallelised with Rayon.
use clap::Parser;
use gen_rec::enumerate::{count_grf, stream_grf};
use gen_rec::grf::Grf;
use gen_rec::pruning::PruningOpts;
use gen_rec::simulate::simulate;
use rayon::prelude::*;
use rug::Integer;
use std::cell::Cell;
use std::time::{Duration, Instant};

#[derive(Parser, Debug)]
#[command(
    about = "Search for BBµ champions by exhaustive enumeration of 0-arity PRFs",
    long_about = None
)]
struct Args {
    /// Maximum size to enumerate up to.
    max_size: usize,

    /// Maximum steps per simulation before giving up.
    #[arg(long, default_value_t = 100_000_000)]
    max_steps: u64,

    /// Include trivial compositions: C(Z_m,...) and C(P^m_i,...).
    /// These are always equivalent to simpler expressions (Z_k or g_i)
    /// and so can be pruned without missing any champion values.
    #[arg(long)]
    include_trivial: bool,

    /// Disable composition canonicalisation (on by default).
    /// By default C(C(f,g), k) is skipped in favour of the equivalent C(f, C(g,k)).
    #[arg(long)]
    no_comp_assoc: bool,

    /// Disable R(Z(k), Z(k+2)) and R(Z(k), P(k+2,2)) pruning (on by default).
    /// Both are always ≡ Z(k+1): the zero-base starts at 0 and the step either
    /// returns 0 or returns the accumulator (which stays 0).
    #[arg(long)]
    no_rec_zero_base: bool,

    /// Disable C(R(g,h), Z(p), …) pruning (on by default).
    /// By default these are skipped: the first arg forces n=0, so the result
    /// equals C(g, …) which is strictly smaller and generated independently.
    #[arg(long)]
    no_rec_zero_arg: bool,

    /// Include Minimization combinator (default: PRF only).
    #[arg(long)]
    allow_min: bool,

    /// Batch size for parallel simulation (tune for your CPU count).
    #[arg(long, default_value_t = 2000)]
    batch_size: usize,

    /// How many future sizes to show time estimates for.
    #[arg(long, default_value_t = 3)]
    lookahead: usize,
}

/// Aggregate result for one batch.
struct BatchResult {
    best_value: Option<Integer>,
    best_exprs: Vec<String>,
    timed_out: usize,
    total_steps: u64,
    max_steps_single: u64,
}

/// Aggregate result for one size level.
struct SizeResult {
    size: usize,
    total: usize,
    timed_out: usize,
    best_value: Option<Integer>,
    best_exprs: Vec<String>,
    total_steps: u64,
    max_steps_single: u64,
}

fn fmt_integer(v: &Integer) -> String {
    let s = v.to_string();
    if s.len() <= 22 {
        s
    } else {
        let log10 = v.significant_bits() as f64 * std::f64::consts::LOG10_2;
        format!("~10^{:.2} ({} digits)", log10, s.len())
    }
}

/// Simulate a batch of GRFs in parallel and return aggregate results.
fn process_batch(batch: &[Grf], max_steps: u64) -> BatchResult {
    let mut best_val: Option<Integer> = None;
    let mut best_exprs: Vec<String> = Vec::new();
    let mut timed_out = 0usize;
    let mut total_steps = 0u64;
    let mut max_steps_single = 0u64;

    let outcomes: Vec<(Option<Integer>, u64, String)> = batch
        .par_iter()
        .map(|grf| {
            let (result, steps) = simulate(grf, &[], max_steps);
            (result.into_value(), steps, grf.to_string())
        })
        .collect();

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
    BatchResult {
        best_value: best_val,
        best_exprs,
        timed_out,
        total_steps,
        max_steps_single,
    }
}

/// Merge a BatchResult into per-size accumulators.
fn merge_batch(
    br: BatchResult,
    size_best_val: &mut Option<Integer>,
    size_best_exprs: &mut Vec<String>,
    size_timed_out: &mut usize,
    size_total_steps: &mut u64,
    size_max_steps: &mut u64,
) {
    *size_timed_out += br.timed_out;
    *size_total_steps += br.total_steps;
    if br.max_steps_single > *size_max_steps {
        *size_max_steps = br.max_steps_single;
    }
    if let Some(v) = br.best_value {
        let cmp = size_best_val
            .as_ref()
            .map_or(std::cmp::Ordering::Greater, |cur| v.cmp(cur));
        match cmp {
            std::cmp::Ordering::Greater => {
                *size_best_val = Some(v);
                *size_best_exprs = br.best_exprs;
            }
            std::cmp::Ordering::Equal => size_best_exprs.extend(br.best_exprs),
            std::cmp::Ordering::Less => {}
        }
    }
}

fn estimate_time(
    future_size: usize,
    allow_min: bool,
    opts: PruningOpts,
    secs_per_fn: f64,
) -> Option<f64> {
    let count = count_grf(future_size, 0, allow_min, opts);
    if count == 0 || secs_per_fn <= 0.0 {
        return None;
    }
    Some(count as f64 * secs_per_fn)
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
    let opts = PruningOpts {
        skip_trivial: !args.include_trivial,
        comp_assoc: !args.no_comp_assoc,
        skip_rec_zero_base: !args.no_rec_zero_base,
        skip_rec_zero_arg: !args.no_rec_zero_arg,
    };

    println!(
        "BBµ search: 0-arity {}, max_size={}, max_steps={}, opts={:?}, threads={}, batch={}",
        if args.allow_min { "GRF" } else { "PRF" },
        args.max_size,
        args.max_steps,
        opts,
        rayon::current_num_threads(),
        args.batch_size,
    );
    println!("{}", "=".repeat(90));

    let mut results: Vec<SizeResult> = Vec::new();
    let mut smoothed_secs_per_fn: Option<f64> = None;
    let total_start = Instant::now();

    for size in 1..=args.max_size {
        let size_start = Instant::now();

        let mut total = 0usize;
        let mut size_timed_out = 0usize;
        let mut size_best_val: Option<Integer> = None;
        let mut size_best_exprs: Vec<String> = Vec::new();
        let mut size_total_steps: u64 = 0;
        let mut size_max_steps: u64 = 0;
        let mut batch: Vec<Grf> = Vec::with_capacity(args.batch_size);

        // Cell<Duration> gives interior mutability so the flush closure can
        // accumulate simulation time without changing its signature.
        let sim_time_cell = Cell::new(Duration::ZERO);

        let flush = |batch: &mut Vec<Grf>,
                     best_val: &mut Option<Integer>,
                     best_exprs: &mut Vec<String>,
                     timed_out: &mut usize,
                     total_steps: &mut u64,
                     max_steps: &mut u64| {
            if batch.is_empty() {
                return;
            }
            let sim_start = Instant::now();
            let br = process_batch(batch, args.max_steps);
            sim_time_cell.set(sim_time_cell.get() + sim_start.elapsed());
            merge_batch(br, best_val, best_exprs, timed_out, total_steps, max_steps);
            batch.clear();
        };

        stream_grf(
            size,
            0,
            args.allow_min,
            opts,
            &mut |grf: &Grf| {
                total += 1;
                batch.push(grf.clone());
                if batch.len() >= args.batch_size {
                    flush(
                        &mut batch,
                        &mut size_best_val,
                        &mut size_best_exprs,
                        &mut size_timed_out,
                        &mut size_total_steps,
                        &mut size_max_steps,
                    );
                }
            },
        );
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

        if total > 0 {
            let cur_rate = elapsed / total as f64;
            smoothed_secs_per_fn = Some(match smoothed_secs_per_fn {
                None => cur_rate,
                Some(prev) => 0.3 * cur_rate + 0.7 * prev,
            });
        }

        let best_str = match &size_best_val {
            Some(v) => fmt_integer(v),
            None => "-".to_string(),
        };

        println!(
            "n={:3}: best={}, {:6} holdouts, {:9} fns  [{:.2}s sim={:.2}s enum={:.2}s, {} steps, {} steps/s]",
            size,
            total,
            size_timed_out,
            best_str,
            elapsed,
            sim_secs,
            enum_secs,
            fmt_si(size_total_steps),
            fmt_si_f64(size_total_steps as f64 / elapsed),
        );
        const MAX_VIA: usize = 20;
        if !size_best_exprs.is_empty() {
            for expr in size_best_exprs.iter().take(MAX_VIA) {
                println!("       via {}", expr);
            }
            if size_best_exprs.len() > MAX_VIA {
                println!(
                    "       ... (+{} more tied expressions)",
                    size_best_exprs.len() - MAX_VIA
                );
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
                        let est = estimate_time(future, args.allow_min, opts, rate)?;
                        let count = count_grf(future, 0, args.allow_min, opts);
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
        "BBµ_{} summary  (opts={:?}, max_steps={})",
        if args.allow_min { "GRF" } else { "PRF" },
        opts,
        args.max_steps
    );
    println!("{}", "=".repeat(90));
    println!(
        "{:>4}  {:>12}  {:>10}  {:>10}  {:>12}  {:>10}  {}",
        "n", "#fns", "over_steps", "BBµ(n)", "total_steps", "max_steps", "Champion"
    );
    println!("{}", "-".repeat(90));
    for r in &results {
        let val_str = match &r.best_value {
            Some(v) => fmt_integer(v),
            None => "-".to_string(),
        };
        let expr_str = if r.best_exprs.is_empty() {
            "-".to_string()
        } else if r.best_exprs.len() == 1 {
            r.best_exprs[0].clone()
        } else {
            format!("{} (+{} ties)", r.best_exprs[0], r.best_exprs.len() - 1)
        };
        println!(
            "{:>4}  {:>12}  {:>10}  {:>10}  {:>12}  {:>10}  {}",
            r.size,
            r.total,
            r.timed_out,
            val_str,
            fmt_si(r.total_steps),
            fmt_si(r.max_steps_single),
            expr_str,
        );
    }
    println!("{}", "-".repeat(90));
    println!("Total time: {:.2}s", total_elapsed);
}
