/// Enumerate 0-arity GRFs of a given size and track BBµ champions.
use clap::Parser;
use gen_rec::alias::alias_db_for_stdout;
use gen_rec::closed_form_enum::{ClosedFormEnumerator, EnumMode};
use gen_rec::enumerate::stream_grf;
use gen_rec::grf::Grf;
use gen_rec::io_grl::{self, GrfEntry, Status};
use gen_rec::pruning::PruningOpts;
use gen_rec::sim_nat::{BigNat, SimNat, SmallNat};
use gen_rec::simulate::{SimResult, SimSteps};
use rayon::prelude::*;
use std::fs;
use std::io::{BufWriter, Write};
use std::path::PathBuf;
use std::time::{Duration, Instant};

// ---------------------------------------------------------------------------
// CLI args
// ---------------------------------------------------------------------------

#[derive(Parser, Debug)]
#[command(
    about = "Search for BBµ champions by exhaustive enumeration of 0-arity GRFs",
    long_about = None
)]
struct Args {
    /// Size of GRFs to enumerate.
    size: usize,

    /// Directory for result files
    results_dir: Option<PathBuf>,

    /// Maximum steps per simulation before giving up (0 = unlimited).
    #[arg(long, default_value_t = 100_000_000)]
    max_steps: u64,

    /// Include Minimization combinator (default: PRF only).
    #[arg(long)]
    allow_min: bool,

    /// Only search M(f) where f is a PRF (arity-1, no nested Min).
    #[arg(long, conflicts_with = "allow_min")]
    min_prf: bool,

    /// Batch size for parallel simulation.
    #[arg(long, default_value_t = 2000)]
    batch_size: usize,

    /// Show raw GRF strings instead of aliases in terminal output.
    #[arg(long)]
    no_alias: bool,

    /// Adjust pruning flags from the recommended set.
    /// Use +flag to enable, -flag to disable, or bare flag to enable.
    /// Example: --opts -comp_null,+comp_rnf
    #[arg(long, value_name = "OPTS")]
    opts: Option<String>,

    /// Number of top halting GRFs to track and write to halt file.
    #[arg(long, default_value_t = 100)]
    top_k: usize,

    /// Seconds between progress lines (0 = disable).
    #[arg(long, default_value_t = 30)]
    progress_secs: u64,

    /// Restrict enumeration to a range: --seek START COUNT.
    #[arg(long, num_args = 2, value_names = ["START", "COUNT"])]
    seek: Option<Vec<usize>>,

    /// Use ClosedFormEnumerator instead of stream_grf.
    /// Reduces candidates by deduplicating sub-expressions on ClosedForm structural
    /// equality, while remaining complete: every semantically distinct GRF is reachable.
    #[arg(long)]
    cf: bool,

    /// Cap CF caching to domains where arity+size <= LIMIT; larger domains stream
    /// without caching. Reduces memory at large sizes at the cost of some dedup
    /// Optional limit for ClosedForm caching (size + arity <= cf_limit).
    /// Defaults to `size`, reducing memory significantly for BBµ(n) when n >= 7.
    #[arg(long)]
    cf_limit: Option<usize>,

    /// Enable dynamic RNF regeneration for massively reduced memory usage.
    #[arg(long)]
    dynamic_rnf: bool,

    #[arg(long)]
    bignat: bool,
}

// ---------------------------------------------------------------------------
// TopK: flat ranked list of best individual halting GRFs
// ---------------------------------------------------------------------------

/// Tracks the top-K individual halting GRFs by score.
/// Entries are (score, steps, base_steps, raw_expr) sorted ascending; best at end.
struct TopK<N: SimNat> {
    k: usize,
    entries: Vec<(N, u64, N, String)>,
}

impl<N: SimNat> TopK<N> {
    fn new(k: usize) -> Self {
        TopK {
            k,
            entries: Vec::new(),
        }
    }

    fn best_score(&self) -> Option<N> {
        self.entries.last().map(|(s, _, _, _)| s.clone())
    }

    fn insert(&mut self, score: N, steps: u64, base_steps: N, expr: String) {
        if self.entries.len() >= self.k && score < self.entries[0].0 {
            return;
        }
        let pos = self.entries.partition_point(|(s, _, _, _)| *s < score);
        self.entries.insert(pos, (score, steps, base_steps, expr));
        if self.entries.len() > self.k {
            self.entries.remove(0);
        }
    }

    fn merge_from(&mut self, other: TopK<N>) {
        for (score, steps, base_steps, expr) in other.entries {
            self.insert(score, steps, base_steps, expr);
        }
    }

    fn iter_desc(&self) -> impl Iterator<Item = &(N, u64, N, String)> {
        self.entries.iter().rev()
    }
}

// ---------------------------------------------------------------------------
// Accumulator: mutable run state
// ---------------------------------------------------------------------------

struct Accumulator<N: SimNat> {
    top_k: TopK<N>,
    total: usize,
    holdouts: usize,
    diverged: usize,
    total_steps: SmallNat,
    max_steps_single: SmallNat,
    sim_nanos: u64,
}

impl<N: SimNat> Accumulator<N> {
    fn new(k: usize) -> Self {
        Accumulator {
            top_k: TopK::<N>::new(k),
            total: 0,
            holdouts: 0,
            diverged: 0,
            total_steps: 0,
            max_steps_single: 0,
            sim_nanos: 0,
        }
    }
}

// ---------------------------------------------------------------------------
// Batch processing
// ---------------------------------------------------------------------------

struct BatchResult<N: SimNat> {
    top_k: TopK<N>,
    holdouts: Vec<(u64, String, Option<&'static str>)>,
    diverged: usize,
    total_steps: SmallNat,
}

fn process_batch<N: SimNat + Send + Sync>(
    batch: &[Grf],
    max_steps: u64,
    k: usize,
) -> BatchResult<N> {
    // Strings not allocated in worker threads — avoids macOS nano-zone
    // cross-thread free errors ("pointer being freed was not allocated").
    let outcomes: Vec<(SimResult<N>, SimSteps<N>)> = batch
        .par_iter()
        .map(|grf| {
            gen_rec::simulate::simulate_opts::<N>(
                grf,
                &[],
                if max_steps == 0 {
                    None
                } else {
                    Some(max_steps)
                },
                gen_rec::simulate::SimOpts::default(),
            )
        })
        .collect();

    let mut top_k = TopK::new(k);
    let mut holdouts = Vec::new();
    let mut diverged = 0usize;
    let mut total_steps: SmallNat = 0;

    for (idx, (result, sim_steps)) in outcomes.into_iter().enumerate() {
        let steps = sim_steps.sim;
        total_steps += steps;
        match result {
            SimResult::OutOfSteps => {
                holdouts.push((steps, batch[idx].to_string(), Some("OutOfSteps")))
            }
            SimResult::Diverge => diverged += 1,
            SimResult::Value(v) => {
                top_k.insert(v, steps, sim_steps.base_approx, batch[idx].to_string())
            }
            SimResult::ArityMismatch => panic!("arity mismatch in bb_search for {}", batch[idx]),
            SimResult::ValueOverflow => {
                holdouts.push((steps, batch[idx].to_string(), Some("Overflow")))
            }
        }
    }
    BatchResult {
        top_k,
        holdouts,
        diverged,
        total_steps,
    }
}

fn flush_batch<W: Write, N: SimNat + Send + Sync>(
    batch: &mut Vec<Grf>,
    acc: &mut Accumulator<N>,
    holdout_w: &mut W,
    max_steps: u64,
    k: usize,
) {
    if batch.is_empty() {
        return;
    }
    let t0 = Instant::now();
    let br = process_batch(batch, max_steps, k);
    acc.sim_nanos += t0.elapsed().as_nanos() as u64;
    acc.holdouts += br.holdouts.len();
    acc.diverged += br.diverged;
    acc.total_steps += br.total_steps;
    for (s, _, _) in &br.holdouts {
        if *s > acc.max_steps_single {
            acc.max_steps_single = *s;
        }
    }
    for (steps, expr, reason) in br.holdouts {
        io_grl::write_grf_entry(
            holdout_w,
            &GrfEntry {
                expr,
                status: Some(Status::Unknown),
                steps: Some(steps),
                base_steps: None,
                score: None,
                unknown_reason: reason.map(|r| r.to_string()),
            },
        )
        .unwrap();
    }
    acc.top_k.merge_from(br.top_k);
    batch.clear();
}

// ---------------------------------------------------------------------------
// Formatting helpers
// ---------------------------------------------------------------------------

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

// ---------------------------------------------------------------------------
// main
// ---------------------------------------------------------------------------

fn main() {
    let args = Args::parse();
    if args.bignat {
        run_search::<BigNat>(&args);
    } else {
        run_search::<SmallNat>(&args);
    }
}

fn run_search<N: SimNat + Send + Sync>(args: &Args) {
    let mut opts = PruningOpts::recommended();
    opts.min_dom = true;
    if let Some(ref s) = args.opts {
        opts = opts.apply_flag_adjustments(s).unwrap_or_else(|e| {
            eprintln!("error: {e}");
            std::process::exit(1);
        });
    }
    let mode_str = {
        let base = if args.min_prf {
            "min_prf"
        } else if args.allow_min {
            "grf"
        } else {
            "prf"
        };
        if args.cf {
            format!("{base}+cf")
        } else {
            base.to_string()
        }
    };
    let has_min = args.allow_min || args.min_prf;
    let size = args.size;

    // Results directory.
    if let Some(ref dir) = args.results_dir {
        fs::create_dir_all(dir).expect("failed to create results directory");
    }

    // Open holdout file for streaming writes.
    let mut holdout_writer: Box<dyn std::io::Write> = if let Some(ref dir) = args.results_dir {
        let holdout_path = dir.join("holdout.grl");
        let holdout_file = fs::File::create(&holdout_path).expect("failed to create holdout.grl");
        Box::new(BufWriter::new(holdout_file))
    } else {
        Box::new(std::io::sink())
    };
    if args.results_dir.is_some() {
        io_grl::write_grl_header(
            &mut holdout_writer,
            &format!(
                "BBµ holdouts: mode={mode_str}, size={size}, budget={}",
                args.max_steps
            ),
        )
        .unwrap();
    }

    // Alias formatter for terminal output.
    let alias_db = alias_db_for_stdout(6, args.no_alias);
    let fmt_alias = |expr: &str| -> String {
        match &alias_db {
            Some(db) => expr
                .parse::<Grf>()
                .map(|g| db.alias(&g))
                .unwrap_or_else(|_| expr.to_string()),
            None => expr.to_string(),
        }
    };

    let (seek_start, seek_count) = match args.seek {
        Some(ref v) => (v[0], v[1]),
        None => (0, usize::MAX),
    };

    println!(
        "BBµ search: 0-arity {}, size={}, max_steps={}, opts={:?}",
        mode_str, size, args.max_steps, opts,
    );
    println!(
        "  threads={}, batch={}, top_k={}",
        rayon::current_num_threads(),
        args.batch_size,
        args.top_k
    );
    if let Some(ref dir) = args.results_dir {
        println!("  results: {}/", dir.display());
    } else {
        println!("  results: none");
    }
    println!("{}", "=".repeat(90));

    let start = Instant::now();
    let progress_interval = Duration::from_secs(args.progress_secs);
    let mut last_progress = start;

    let mut acc = Accumulator::<N>::new(args.top_k);
    let mut batch: Vec<Grf> = Vec::with_capacity(args.batch_size);

    // Macro-like helper to flush and maybe print progress.
    // We can't use a real closure because flush_batch already borrows acc/batch/holdout_writer.
    // Instead, inline the progress check after each flush call site.
    macro_rules! maybe_progress {
        () => {
            if args.progress_secs > 0 && last_progress.elapsed() >= progress_interval {
                let t = start.elapsed().as_secs_f64();
                let best_s = acc.top_k.best_score().map_or("-".to_string(), |v| v.to_string());
                let steps_s = fmt_si(acc.total_steps);
                let rate_s = fmt_si_f64(acc.total_steps as f64 / t.max(1e-9));
                if has_min {
                    println!(
                        "[t={:.1}s] best={}  fns={}  holdouts={}  diverged={}  steps={}  ({} steps/s)",
                        t, best_s, fmt_si(acc.total as u64), fmt_si(acc.holdouts as u64),
                        fmt_si(acc.diverged as u64), steps_s, rate_s,
                    );
                } else {
                    println!(
                        "[t={:.1}s] best={}  fns={}  holdouts={}  steps={}  ({} steps/s)",
                        t, best_s, fmt_si(acc.total as u64), fmt_si(acc.holdouts as u64),
                        steps_s, rate_s,
                    );
                }
                last_progress = Instant::now();
            }
        };
    }

    let mut idx = 0usize;

    if args.cf && !(args.min_prf && size < 2) {
        let cf_arity = if args.min_prf { 1 } else { 0 };
        let cf_size = if args.min_prf && size >= 2 {
            size - 1
        } else {
            size
        };
        let cf_allow_min = !args.min_prf && args.allow_min;
        let mut en = ClosedFormEnumerator::with_pruning(EnumMode::AllGrf, cf_allow_min)
            .with_dynamic_rnf(args.dynamic_rnf);
        if let Some(limit) = args.cf_limit {
            en = en.with_cf_limit(limit);
        }
        en.prepare(cf_arity, cf_size);
        en.for_each_raw_candidate(cf_arity, cf_size, &mut |grf| {
            if args.min_prf {
                if opts.min_dom {
                    if !grf.used_args().contains(&1) {
                        return;
                    }
                    if grf.is_never_zero() {
                        return;
                    }
                }
            }
            let g = if args.min_prf {
                Grf::min(grf.clone())
            } else {
                grf.clone()
            };
            let cur = idx;
            idx += 1;
            if cur < seek_start || cur >= seek_start + seek_count {
                return;
            }
            acc.total += 1;
            batch.push(g);
            if batch.len() >= args.batch_size {
                flush_batch(
                    &mut batch,
                    &mut acc,
                    &mut holdout_writer,
                    args.max_steps,
                    args.top_k,
                );
                maybe_progress!();
            }
        });
    } else if args.min_prf && size >= 2 {
        stream_grf(size - 1, 1, false, opts, &mut |f: &Grf| {
            if opts.min_dom {
                if !f.used_args().contains(&1) {
                    return;
                }
                if f.is_never_zero() {
                    return;
                }
            }
            let cur = idx;
            idx += 1;
            if cur < seek_start || cur >= seek_start + seek_count {
                return;
            }
            acc.total += 1;
            batch.push(Grf::min(f.clone()));
            if batch.len() >= args.batch_size {
                flush_batch(
                    &mut batch,
                    &mut acc,
                    &mut holdout_writer,
                    args.max_steps,
                    args.top_k,
                );
                maybe_progress!();
            }
        });
    } else if !args.min_prf {
        stream_grf(size, 0, args.allow_min, opts, &mut |grf: &Grf| {
            let cur = idx;
            idx += 1;
            if cur < seek_start || cur >= seek_start + seek_count {
                return;
            }
            acc.total += 1;
            batch.push(grf.clone());
            if batch.len() >= args.batch_size {
                flush_batch(
                    &mut batch,
                    &mut acc,
                    &mut holdout_writer,
                    args.max_steps,
                    args.top_k,
                );
                maybe_progress!();
            }
        });
    }
    flush_batch(
        &mut batch,
        &mut acc,
        &mut holdout_writer,
        args.max_steps,
        args.top_k,
    );
    holdout_writer.flush().unwrap();

    let elapsed = start.elapsed().as_secs_f64();
    eprintln!("=== ClosedForm Debug Diagnostics ===");
    eprintln!(
        "COMPOSE_CALLS: {}",
        gen_rec::closed_form::COMPOSE_CALLS.load(std::sync::atomic::Ordering::Relaxed)
    );
    eprintln!(
        "REC_INTERNAL_CALLS: {}",
        gen_rec::closed_form::REC_INTERNAL_CALLS.load(std::sync::atomic::Ordering::Relaxed)
    );
    eprintln!(
        "REC_INTERNAL_STEPS: {}",
        gen_rec::closed_form::REC_INTERNAL_STEPS.load(std::sync::atomic::Ordering::Relaxed)
    );
    eprintln!(
        "PERIODIC_PERIOD: {}",
        gen_rec::closed_form::PERIODIC_PERIOD.load(std::sync::atomic::Ordering::Relaxed)
    );

    let sim_secs = acc.sim_nanos as f64 / 1e9;
    let enum_secs = elapsed - sim_secs;

    // Terminal summary.
    let best_str = acc
        .top_k
        .best_score()
        .map_or("-".to_string(), |v| v.to_string());
    if has_min {
        println!(
            "n={}: best={}, {} holdouts, {} diverged, {} fns  [{:.2}s sim={:.2}s enum={:.2}s, {} steps, {} steps/s]",
            size, best_str, acc.holdouts, acc.diverged, acc.total,
            elapsed, sim_secs, enum_secs,
            fmt_si(acc.total_steps),
            fmt_si_f64(acc.total_steps as f64 / elapsed.max(1e-9)),
        );
    } else {
        println!(
            "n={}: best={}, {} holdouts, {} fns  [{:.2}s sim={:.2}s enum={:.2}s, {} steps, {} steps/s]",
            size, best_str, acc.holdouts, acc.total,
            elapsed, sim_secs, enum_secs,
            fmt_si(acc.total_steps),
            fmt_si_f64(acc.total_steps as f64 / elapsed.max(1e-9)),
        );
    }
    if acc.holdouts > 0 {
        println!("  max single: {}", fmt_si(acc.max_steps_single));
    }

    const TERMINAL_DISPLAY: usize = 10;
    for (rank, (score, steps, _base_steps, expr)) in acc.top_k.iter_desc().enumerate() {
        if rank >= TERMINAL_DISPLAY {
            break;
        }
        println!(
            "  #{}: score={}  steps={}  {}",
            rank + 1,
            score,
            fmt_si(*steps),
            fmt_alias(expr)
        );
    }

    if let Some(ref dir) = args.results_dir {
        // Write halt file.
        let halt_path = dir.join("halt.max.grl");
        let mut halt_w =
            BufWriter::new(fs::File::create(&halt_path).expect("failed to create halt.max.grl"));
        io_grl::write_grl_header(
            &mut halt_w,
            &format!(
                "BBµ search: mode={mode_str}, size={size}, budget={}, top-k={}",
                args.max_steps, args.top_k
            ),
        )
        .unwrap();
        for (score, steps, base_steps, expr) in acc.top_k.iter_desc() {
            io_grl::write_grf_entry(
                &mut halt_w,
                &GrfEntry {
                    expr: expr.clone(),
                    status: Some(Status::Halt),
                    steps: Some(*steps),
                    base_steps: Some(base_steps.to_u64_sat()),
                    score: Some(score.to_u64_sat()),
                    unknown_reason: None,
                },
            )
            .unwrap();
        }
        halt_w.flush().unwrap();

        // Write config file.
        let config_path = dir.join("config.json");
        let mut cfg_w =
            BufWriter::new(fs::File::create(&config_path).expect("failed to create config.json"));
        let best_json = acc
            .top_k
            .best_score()
            .map_or("null".to_string(), |v| v.to_string());
        writeln!(cfg_w, "{{").unwrap();
        writeln!(cfg_w, "  \"size\": {},", size).unwrap();
        writeln!(cfg_w, "  \"mode\": \"{mode_str}\",").unwrap();
        writeln!(cfg_w, "  \"max_steps\": {},", args.max_steps).unwrap();
        writeln!(cfg_w, "  \"batch_size\": {},", args.batch_size).unwrap();
        writeln!(cfg_w, "  \"top_k\": {},", args.top_k).unwrap();
        writeln!(cfg_w, "  \"allow_min\": {},", args.allow_min).unwrap();
        writeln!(cfg_w, "  \"min_prf\": {},", args.min_prf).unwrap();
        writeln!(cfg_w, "  \"cf\": {},", args.cf).unwrap();
        match args.cf_limit {
            Some(limit) => writeln!(cfg_w, "  \"cf_limit\": {},", limit).unwrap(),
            None => writeln!(cfg_w, "  \"cf_limit\": null,").unwrap(),
        }
        writeln!(
            cfg_w,
            "  \"opts\": \"{}\",",
            opts.stream_opt_names().join(",")
        )
        .unwrap();
        writeln!(cfg_w, "  \"threads\": {},", rayon::current_num_threads()).unwrap();
        writeln!(cfg_w, "  \"total_fns\": {},", acc.total).unwrap();
        writeln!(cfg_w, "  \"total_holdouts\": {},", acc.holdouts).unwrap();
        writeln!(cfg_w, "  \"total_diverged\": {},", acc.diverged).unwrap();
        writeln!(cfg_w, "  \"elapsed_secs\": {:.3},", elapsed).unwrap();
        writeln!(cfg_w, "  \"best_score\": {}", best_json).unwrap();
        writeln!(cfg_w, "}}").unwrap();
        cfg_w.flush().unwrap();

        println!();
        println!("Results written to {}/", dir.display());
        println!("  halt.max.grl: {} entries", acc.top_k.entries.len());
        println!("  holdout.grl:  {} entries", acc.holdouts);
        println!("  config.json");
    }
}
