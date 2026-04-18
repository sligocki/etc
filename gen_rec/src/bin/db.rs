/// Manage a directory of novel-function DB files.
///
/// Usage examples:
///   db status fp/
///   db build fp/ --max-size 12 --arities 0,1,2,3
///   db build fp/ --max-size 8 --allow-min --arities 0,1,2 --jobs 4
///   db build fp/ --arities 0,1,2,3               # infinite mode: runs until Ctrl+C
///   db build fp/ --max-size 10 --fp-inputs 64    # novel-sub-expression mode
use clap::{Parser, Subcommand};
use gen_rec::novel_db::{
    db_filename, db_paths_in_dir, extend_novel_map, load_novel_file, merge_into, retry_timed_out,
    save_novel_file, NovelMap,
};
use gen_rec::novel_enum::NovelEnumerator;
use rayon::prelude::*;
use std::path::PathBuf;
use std::time::Instant;

#[derive(Parser, Debug)]
#[command(about = "Manage a directory of novel-function DB files")]
struct Args {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand, Debug)]
enum Command {
    /// Show coverage of a DB directory.
    Status {
        /// Directory containing .db files.
        dir: PathBuf,
    },
    /// Build or extend novel DBs for the specified arities.
    Build {
        /// Directory to read from and write to.
        dir: PathBuf,

        /// Target max_size (inclusive). Already-covered sizes are skipped.
        /// If omitted, runs indefinitely (saving after each size) until interrupted.
        #[arg(long)]
        max_size: Option<usize>,

        /// Also compute allow_min variants (in addition to PRF).
        #[arg(long)]
        allow_min: bool,

        /// Arities to enumerate (comma-separated, e.g. 0,1,2,3).
        #[arg(long, value_delimiter = ',', default_values = ["0", "1", "2", "3"])]
        arities: Vec<usize>,

        /// Max simulation steps per input when computing fingerprints.
        #[arg(long, default_value_t = 10_000)]
        max_steps: u64,

        /// Number of parallel jobs (default: number of logical CPUs).
        #[arg(long, default_value_t = 0)]
        jobs: usize,

        /// Use novel-sub-expression enumeration with this many fingerprint inputs.
        /// When set, only canonical (minimal) GRFs are used as sub-expressions,
        /// drastically reducing the search space.  Requires --max-size.
        /// NOTE: always enumerates from size 1 (cannot resume from an existing file).
        #[arg(long, default_value_t = 0)]
        fp_inputs: usize,
    },
}

// ── status ────────────────────────────────────────────────────────────────────

fn cmd_status(dir: &PathBuf) {
    let paths = match db_paths_in_dir(dir) {
        Ok(p) => p,
        Err(e) => { eprintln!("error: {e}"); std::process::exit(1); }
    };

    if paths.is_empty() {
        println!("No .db files found in {}/", dir.display());
        return;
    }

    // Collect (arity, allow_min, max_size, entry_count, timed_out_count) from each file.
    let mut info: Vec<(usize, bool, usize, usize, usize)> = Vec::new();
    for path in &paths {
        // Try to parse arity from filename: a{N}_{prf|min}.db
        let stem = path.file_stem().and_then(|s| s.to_str()).unwrap_or("");
        let (arity, allow_min) = if let Some(rest) = stem.strip_prefix('a') {
            if let Some(idx) = rest.find('_') {
                let arity: usize = rest[..idx].parse().unwrap_or(usize::MAX);
                let allow_min = &rest[idx + 1..] == "min";
                (arity, allow_min)
            } else {
                continue;
            }
        } else {
            continue;
        };

        match load_novel_file(path) {
            Ok((meta, map, timed_out)) => {
                info.push((arity, allow_min, meta.max_size, map.len(), timed_out.len()));
            }
            Err(e) => eprintln!("warning: skipping {}: {e}", path.display()),
        }
    }

    if info.is_empty() {
        println!("No readable DB files found.");
        return;
    }

    // Sort and display.
    info.sort_by_key(|(a, m, _, _, _)| (*a, *m));
    let max_arity = info.iter().map(|(a, _, _, _, _)| *a).max().unwrap_or(0);

    // Show t/o column only if any file has timed-out entries.
    let any_timed_out = info.iter().any(|(_, _, _, _, t)| *t > 0);

    if any_timed_out {
        println!("{:<6}  {:>8}  {:>8}  {:>8}  {:>6}", "arity", "prf", "min", "entries", "t/o");
        println!("{}", "-".repeat(44));
    } else {
        println!("{:<6}  {:>8}  {:>8}  {:>8}", "arity", "prf", "min", "entries");
        println!("{}", "-".repeat(36));
    }

    for arity in 0..=max_arity {
        let prf = info.iter().find(|(a, m, _, _, _)| *a == arity && !m);
        let min = info.iter().find(|(a, m, _, _, _)| *a == arity && *m);

        let prf_str = prf.map_or("–".to_string(), |(_, _, sz, _, _)| sz.to_string());
        let min_str = min.map_or("–".to_string(), |(_, _, sz, _, _)| sz.to_string());
        let entries = prf.map_or(0, |(_, _, _, n, _)| *n) + min.map_or(0, |(_, _, _, n, _)| *n);
        let entries_str = if entries == 0 { "–".to_string() } else { entries.to_string() };

        if any_timed_out {
            let to = prf.map_or(0, |(_, _, _, _, t)| *t) + min.map_or(0, |(_, _, _, _, t)| *t);
            let to_str = if to == 0 { "–".to_string() } else { to.to_string() };
            println!("{:<6}  {:>8}  {:>8}  {:>8}  {:>6}", arity, prf_str, min_str, entries_str, to_str);
        } else {
            println!("{:<6}  {:>8}  {:>8}  {:>8}", arity, prf_str, min_str, entries_str);
        }
    }
    println!();
    let total_entries: usize = info.iter().map(|(_, _, _, n, _)| n).sum();
    let total_to: usize = info.iter().map(|(_, _, _, _, t)| t).sum();
    println!("Total entries: {total_entries}");
    if total_to > 0 {
        println!("Timed-out (pending retry): {total_to}");
    }
}

// ── build ─────────────────────────────────────────────────────────────────────

struct BuildJob {
    dir: PathBuf,
    arity: usize,
    allow_min: bool,
    /// None = infinite mode: enumerate until interrupted.
    max_size: Option<usize>,
    max_steps: u64,
    /// 0 = use standard exhaustive enumeration; >0 = use NovelEnumerator with this
    /// many fingerprint inputs. Requires max_size to be Some.
    fp_inputs: usize,
}

fn run_build_job(job: &BuildJob) {
    let mut map: NovelMap = NovelMap::new();
    let mut start_size = 1usize;
    let mut prev_timed_out: Vec<(usize, String)> = Vec::new();
    let mut prev_max_steps = job.max_steps;

    // For allow_min runs, seed from the prf file to prevent re-discovery.
    if job.allow_min {
        let seed = db_filename(&job.dir, job.arity, false);
        if seed.exists() {
            if let Ok((_, seed_map, _)) = load_novel_file(&seed) {
                merge_into(&mut map, seed_map);
            }
        }
    }

    // Load existing target file to determine start_size and any timed-out entries.
    let target = db_filename(&job.dir, job.arity, job.allow_min);
    if target.exists() {
        match load_novel_file(&target) {
            Ok((meta, file_map, timed_out)) => {
                start_size = meta.max_size + 1;
                prev_max_steps = meta.max_steps;
                prev_timed_out = timed_out;
                merge_into(&mut map, file_map);
            }
            Err(e) => {
                eprintln!(
                    "[arity={} {}] warning: could not load existing file: {e}",
                    job.arity,
                    if job.allow_min { "min" } else { "prf" }
                );
            }
        }
    }

    let label = format!(
        "arity={} {}",
        job.arity,
        if job.allow_min { "min" } else { "prf" }
    );

    // Retry previously-timed-out entries if the step budget has increased.
    let (mut timed_out_list, recovered) =
        if !prev_timed_out.is_empty() && job.max_steps > prev_max_steps {
            eprintln!(
                "[{label}] retrying {} timed-out entries (max_steps: {} → {}) ...",
                prev_timed_out.len(),
                prev_max_steps,
                job.max_steps,
            );
            retry_timed_out(prev_timed_out, &mut map, job.arity, job.max_steps)
        } else {
            (prev_timed_out, 0)
        };

    match job.max_size {
        // ── finite mode ───────────────────────────────────────────────────────
        Some(max_size) => {
            let size_range_done = start_size > max_size;
            let nothing_to_do = size_range_done && recovered == 0 && timed_out_list.is_empty();

            if nothing_to_do {
                println!("[{label}] already at max_size={max_size}, nothing to do");
                return;
            }

            let t0 = Instant::now();
            let mut total_tested = 0usize;
            let mut total_new = 0usize;
            if !size_range_done {
                if job.fp_inputs > 0 {
                    // Novel-sub-expression mode: enumerate from scratch using only
                    // canonical sub-expressions.  Cannot resume from start_size > 1
                    // because the enumerator builds its own seen-set internally.
                    eprintln!(
                        "[{label}] novel-enum sizes 1..={max_size} (fp_inputs={}) ...",
                        job.fp_inputs,
                    );
                    let mut en =
                        NovelEnumerator::new(job.fp_inputs, job.max_steps, job.allow_min);
                    let entries = en.run(job.arity, 1, max_size, false);
                    total_tested = entries.len(); // approximate: counts novel GRFs only
                    for (fp, size, grf_str) in entries {
                        let is_novel = map.get(&fp).map_or(true, |(s, _)| size < *s);
                        if is_novel {
                            map.insert(fp, (size, grf_str));
                            total_new += 1;
                        }
                    }
                } else {
                    eprintln!("[{label}] enumerating sizes {start_size}..={max_size} ...");
                    let stats = extend_novel_map(
                        &mut map,
                        job.arity,
                        start_size,
                        max_size,
                        job.allow_min,
                        job.max_steps,
                        false,
                        false,
                    );
                    total_tested = stats.total_tested;
                    total_new = stats.total_new;
                    timed_out_list.extend(stats.timed_out_entries);
                }
            }

            if let Err(e) = save_novel_file(
                &target, job.allow_min, max_size, job.max_steps, &map, &timed_out_list,
            ) {
                eprintln!("[{label}] error saving: {e}");
                return;
            }

            let mut parts: Vec<String> = Vec::new();
            if total_tested > 0 { parts.push(format!("{total_tested} tested")); }
            if recovered > 0 { parts.push(format!("{recovered} t/o recovered")); }
            if !timed_out_list.is_empty() { parts.push(format!("{} timed-out", timed_out_list.len())); }
            parts.push(format!("+{total_new} novel ({} total)", map.len()));
            println!(
                "[{label}] done in {:.1}s: {}  → {}",
                t0.elapsed().as_secs_f64(),
                parts.join(", "),
                target.display(),
            );
        }

        // ── infinite mode ─────────────────────────────────────────────────────
        None => {
            // Print one summary line per size as we go.
            if recovered > 0 {
                println!("[{label}] retried t/o: {recovered} recovered, {} still pending", timed_out_list.len());
            }
            let mut size = start_size;
            loop {
                let t0 = Instant::now();
                let stats = extend_novel_map(
                    &mut map,
                    job.arity,
                    size,
                    size,
                    job.allow_min,
                    job.max_steps,
                    false,
                    false,
                );
                let n_timed_out_this_size = stats.timed_out_entries.len();
                timed_out_list.extend(stats.timed_out_entries);

                if let Err(e) = save_novel_file(
                    &target, job.allow_min, size, job.max_steps, &map, &timed_out_list,
                ) {
                    eprintln!("[{label}] error saving at size {size}: {e}");
                    return;
                }

                let mut parts: Vec<String> = Vec::new();
                parts.push(format!("{} tested", stats.total_tested));
                if n_timed_out_this_size > 0 {
                    parts.push(format!("{n_timed_out_this_size} timed-out ({} total)", timed_out_list.len()));
                }
                parts.push(format!("+{} novel ({} total)", stats.total_new, map.len()));
                println!(
                    "[{label}] size {:>3}  {:.1}s  {}",
                    size,
                    t0.elapsed().as_secs_f64(),
                    parts.join(", "),
                );

                size += 1;
            }
        }
    }
}

fn cmd_build(
    dir: &PathBuf,
    max_size: Option<usize>,
    allow_min: bool,
    arities: &[usize],
    max_steps: u64,
    jobs: usize,
    fp_inputs: usize,
) {
    if let Err(e) = std::fs::create_dir_all(dir) {
        eprintln!("error: could not create {}: {e}", dir.display());
        std::process::exit(1);
    }

    if fp_inputs > 0 && max_size.is_none() {
        eprintln!("error: --fp-inputs requires --max-size (infinite mode not supported with novel-sub-expression enumeration)");
        std::process::exit(1);
    }

    // Build job list: PRF for all arities, then Min if requested.
    let mut job_list: Vec<BuildJob> = Vec::new();
    for &arity in arities {
        job_list.push(BuildJob { dir: dir.clone(), arity, allow_min: false, max_size, max_steps, fp_inputs });
    }
    if allow_min {
        for &arity in arities {
            job_list.push(BuildJob { dir: dir.clone(), arity, allow_min: true, max_size, max_steps, fp_inputs });
        }
    }

    let n_jobs = if jobs == 0 {
        std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(1)
    } else {
        jobs
    };

    rayon::ThreadPoolBuilder::new()
        .num_threads(n_jobs)
        .build_global()
        .unwrap_or(());

    let size_desc = match max_size {
        Some(s) => format!("max_size={s}"),
        None => "infinite".to_string(),
    };
    println!(
        "Building {} job(s) with {} thread(s), {size_desc}, max_steps={max_steps}",
        job_list.len(),
        n_jobs,
    );

    job_list.par_iter().for_each(run_build_job);

    // Only reached in finite mode (infinite jobs never return).
    println!("All jobs complete.");
}

// ── main ──────────────────────────────────────────────────────────────────────

fn main() {
    let args = Args::parse();
    match args.command {
        Command::Status { dir } => cmd_status(&dir),
        Command::Build {
            dir,
            max_size,
            allow_min,
            arities,
            max_steps,
            jobs,
            fp_inputs,
        } => cmd_build(&dir, max_size, allow_min, &arities, max_steps, jobs, fp_inputs),
    }
}
