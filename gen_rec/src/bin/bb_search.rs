/// Enumerate 0-arity GRFs of a given size and track BBµ champions.
use clap::Parser;
use gen_rec::alias::alias_db_for_stdout;
use gen_rec::closed_form_enum::{ClosedFormEnumerator, EnumMode};
use gen_rec::enumerate::{EnumScope, stream_grf};
use gen_rec::grf::Grf;
use gen_rec::io_grl::{self, GrfEntry, Status};
use gen_rec::pruning::PruningOpts;
use gen_rec::search_util::{Accumulator, flush_batch, fmt_si, fmt_si_f64};
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
    /// The search scope: prf, min_prf, or grf.
    #[arg(value_enum)]
    enum_scope: EnumScope,

    /// Size of GRFs to enumerate.
    size: usize,

    /// Directory for result files
    results_dir: Option<PathBuf>,

    /// Maximum steps per simulation before giving up (0 = unlimited).
    #[arg(long, default_value_t = 100_000)]
    max_steps: u64,

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

    /// Enable ClosedFormEnumerator deduplication (default for min_prf/grf).
    #[arg(long, overrides_with = "no_cf")]
    cf: bool,

    /// Disable ClosedFormEnumerator deduplication (default for prf).
    #[arg(long, overrides_with = "cf")]
    no_cf: bool,

    /// Enable dynamic RNF regeneration for massively reduced memory usage.
    #[arg(long)]
    dynamic_rnf: bool,
}

// ---------------------------------------------------------------------------
// main
// ---------------------------------------------------------------------------

fn main() {
    let args = Args::parse();
    run_search(&args);
}

fn run_search(args: &Args) {
    let mut opts = PruningOpts::recommended();
    opts.min_dom = true;
    if let Some(ref s) = args.opts {
        opts = opts.apply_flag_adjustments(s).unwrap_or_else(|e| {
            eprintln!("error: {e}");
            std::process::exit(1);
        });
    }
    let min_prf = args.enum_scope.min_prf();
    let allow_min = args.enum_scope.allow_min();

    // We default `cf` (ClosedForm deduplication) to true for min_prf and grf.
    // For these modes, simulation steps an input variable (or can diverge), so deduplication
    // saves immense amounts of time.
    // For pure `prf`, 0-arity functions are fast and guaranteed to halt, so the heavy
    // algebraic deduplication overhead of `cf` is not worth it.
    let cf = if args.cf {
        true
    } else if args.no_cf {
        false
    } else {
        !matches!(args.enum_scope, EnumScope::Prf | EnumScope::PrfDiag)
    };

    if cf && args.enum_scope == EnumScope::PrfDiag {
        panic!(
            "ClosedForm deduplication (+cf) is not supported with prf_diag because prf_diag structural search is strictly 0-arity PRFs."
        );
    }

    let mode_str = {
        let base = args.enum_scope.as_str();
        if cf {
            format!("{base}+cf")
        } else {
            base.to_string()
        }
    };
    let has_min = allow_min || min_prf;
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

    let mut acc = Accumulator::new(args.top_k);
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

    if cf && !(min_prf && size < 2) {
        let cf_arity = if min_prf { 1 } else { 0 };
        let cf_size = if min_prf && size >= 2 { size - 1 } else { size };
        let cf_allow_min = !min_prf && allow_min;
        let mut en = ClosedFormEnumerator::with_pruning(EnumMode::AllGrf, cf_allow_min)
            .with_dynamic_rnf(args.dynamic_rnf);
        en.stream_grfs(cf_arity, cf_size, &mut |grf| {
            if min_prf {
                if opts.min_dom {
                    if !grf.used_args().contains(&1) {
                        return;
                    }
                    if grf.is_never_zero() {
                        return;
                    }
                }
            }
            let g = if min_prf {
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
                    true,
                );
                maybe_progress!();
            }
        });
    } else if min_prf && size >= 2 {
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
                    true,
                );
                maybe_progress!();
            }
        });
    } else if !min_prf {
        let mut handle_grf = |grf: &Grf| {
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
                    true,
                );
                maybe_progress!();
            }
        };

        if args.enum_scope == EnumScope::PrfDiag {
            gen_rec::enumerate::stream_prf_diag(size, opts, &mut handle_grf);
        } else {
            stream_grf(size, 0, allow_min, opts, &mut handle_grf);
        }
    }
    flush_batch(
        &mut batch,
        &mut acc,
        &mut holdout_writer,
        args.max_steps,
        args.top_k,
        true,
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
            size,
            best_str,
            acc.holdouts,
            acc.diverged,
            acc.total,
            elapsed,
            sim_secs,
            enum_secs,
            fmt_si(acc.total_steps),
            fmt_si_f64(acc.total_steps as f64 / elapsed.max(1e-9)),
        );
    } else {
        println!(
            "n={}: best={}, {} holdouts, {} fns  [{:.2}s sim={:.2}s enum={:.2}s, {} steps, {} steps/s]",
            size,
            best_str,
            acc.holdouts,
            acc.total,
            elapsed,
            sim_secs,
            enum_secs,
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
                    base_steps: Some(*base_steps),
                    score: Some(*score),
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
        writeln!(cfg_w, "{{").unwrap();
        writeln!(cfg_w, "  \"size\": {},", size).unwrap();
        writeln!(cfg_w, "  \"mode\": \"{mode_str}\",").unwrap();
        writeln!(cfg_w, "  \"max_steps\": {},", args.max_steps).unwrap();
        writeln!(cfg_w, "  \"batch_size\": {},", args.batch_size).unwrap();
        writeln!(cfg_w, "  \"top_k\": {},", args.top_k).unwrap();
        writeln!(cfg_w, "  \"enum_scope\": \"{}\",", args.enum_scope.as_str()).unwrap();
        writeln!(cfg_w, "  \"cf\": {},", cf).unwrap();
        writeln!(
            cfg_w,
            "  \"opts\": \"{}\",",
            opts.stream_opt_names().join(",")
        )
        .unwrap();
        writeln!(cfg_w, "  \"threads\": {}", rayon::current_num_threads()).unwrap();
        writeln!(cfg_w, "}}").unwrap();
        cfg_w.flush().unwrap();

        // Write stats file.
        let stats_path = dir.join("stats.json");
        let mut stats_w =
            BufWriter::new(fs::File::create(&stats_path).expect("failed to create stats.json"));
        let best_json = acc
            .top_k
            .best_score()
            .map_or("null".to_string(), |v| v.to_string());
        writeln!(stats_w, "{{").unwrap();
        writeln!(stats_w, "  \"num_total\": {},", acc.total).unwrap();
        writeln!(
            stats_w,
            "  \"num_halt\": {},",
            acc.total - acc.holdouts - acc.diverged
        )
        .unwrap();
        writeln!(stats_w, "  \"num_diverged\": {},", acc.diverged).unwrap();
        writeln!(stats_w, "  \"num_holdouts\": {},", acc.holdouts).unwrap();
        writeln!(stats_w).unwrap();
        writeln!(stats_w, "  \"max_score\": {}", best_json).unwrap();
        writeln!(stats_w, "  \"max_halt_steps\": {},", acc.max_steps_single).unwrap();
        writeln!(stats_w).unwrap();
        writeln!(stats_w, "  \"total_runtime_s\": {:.3},", elapsed).unwrap();
        writeln!(stats_w, "}}").unwrap();
        stats_w.flush().unwrap();

        println!();
        println!("Results written to {}/", dir.display());
        println!("  halt.max.grl: {} entries", acc.top_k.entries.len());
        println!("  holdout.grl:  {} entries", acc.holdouts);
        println!("  config.json");
        println!("  stats.json");
    }
}
