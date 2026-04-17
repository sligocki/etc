/// Manage a directory of novel-function DB files.
///
/// Usage examples:
///   db status fp/
///   db build fp/ --max-size 12 --arities 0,1,2,3
///   db build fp/ --max-size 8 --allow-min --arities 0,1,2 --jobs 4
use clap::{Parser, Subcommand};
use gen_rec::novel_db::{
    db_filename, db_paths_in_dir, extend_novel_map, load_novel_file, merge_into, save_novel_file,
    NovelMap,
};
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
        #[arg(long, default_value_t = 10)]
        max_size: usize,

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

    // Collect (arity, allow_min, max_size, entry_count) from each file.
    let mut info: Vec<(usize, bool, usize, usize)> = Vec::new();
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
            Ok((meta, map)) => info.push((arity, allow_min, meta.max_size, map.len())),
            Err(e) => eprintln!("warning: skipping {}: {e}", path.display()),
        }
    }

    if info.is_empty() {
        println!("No readable DB files found.");
        return;
    }

    // Sort and display.
    info.sort_by_key(|(a, m, _, _)| (*a, *m));
    let max_arity = info.iter().map(|(a, _, _, _)| *a).max().unwrap_or(0);

    println!("{:<6}  {:>8}  {:>8}  {:>8}", "arity", "prf", "min", "entries");
    println!("{}", "-".repeat(36));

    for arity in 0..=max_arity {
        let prf = info.iter().find(|(a, m, _, _)| *a == arity && !m);
        let min = info.iter().find(|(a, m, _, _)| *a == arity && *m);

        let prf_str = prf.map_or("–".to_string(), |(_, _, sz, _)| sz.to_string());
        let min_str = min.map_or("–".to_string(), |(_, _, sz, _)| sz.to_string());
        let entries = prf.map_or(0, |(_, _, _, n)| *n) + min.map_or(0, |(_, _, _, n)| *n);
        let entries_str = if entries == 0 {
            "–".to_string()
        } else {
            entries.to_string()
        };

        println!(
            "{:<6}  {:>8}  {:>8}  {:>8}",
            arity, prf_str, min_str, entries_str
        );
    }
    println!();
    println!(
        "Total entries: {}",
        info.iter().map(|(_, _, _, n)| n).sum::<usize>()
    );
}

// ── build ─────────────────────────────────────────────────────────────────────

struct BuildJob {
    dir: PathBuf,
    arity: usize,
    allow_min: bool,
    max_size: usize,
    max_steps: u64,
}

fn run_build_job(job: &BuildJob) {
    let t0 = Instant::now();
    let mut map: NovelMap = NovelMap::new();
    let mut start_size = 1usize;

    // For allow_min runs, seed from the prf file to prevent re-discovery.
    if job.allow_min {
        let seed = db_filename(&job.dir, job.arity, false);
        if seed.exists() {
            if let Ok((_, seed_map)) = load_novel_file(&seed) {
                merge_into(&mut map, seed_map);
            }
        }
    }

    // Load existing target file to determine start_size.
    let target = db_filename(&job.dir, job.arity, job.allow_min);
    if target.exists() {
        match load_novel_file(&target) {
            Ok((meta, file_map)) => {
                start_size = meta.max_size + 1;
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

    if start_size > job.max_size {
        println!("[{label}] already at max_size={}, nothing to do", job.max_size);
        return;
    }

    eprintln!(
        "[{label}] enumerating sizes {}..={} ...",
        start_size, job.max_size
    );

    let new_entries = extend_novel_map(
        &mut map,
        job.arity,
        start_size,
        job.max_size,
        job.allow_min,
        job.max_steps,
        false, // partial=false: total functions only
        false, // progress: suppress per-size lines (parallel output would be garbled)
    );

    if let Err(e) = save_novel_file(
        &target,
        job.allow_min,
        job.max_size,
        job.max_steps,
        &map,
    ) {
        eprintln!("[{label}] error saving: {e}");
        return;
    }

    println!(
        "[{label}] done: {} total entries, +{} new, in {:.1}s  → {}",
        map.len(),
        new_entries,
        t0.elapsed().as_secs_f64(),
        target.display(),
    );
}

fn cmd_build(
    dir: &PathBuf,
    max_size: usize,
    allow_min: bool,
    arities: &[usize],
    max_steps: u64,
    jobs: usize,
) {
    if let Err(e) = std::fs::create_dir_all(dir) {
        eprintln!("error: could not create {}: {e}", dir.display());
        std::process::exit(1);
    }

    // Build job list: PRF for all arities, then Min if requested.
    let mut job_list: Vec<BuildJob> = Vec::new();
    for &arity in arities {
        job_list.push(BuildJob {
            dir: dir.clone(),
            arity,
            allow_min: false,
            max_size,
            max_steps,
        });
    }
    if allow_min {
        for &arity in arities {
            job_list.push(BuildJob {
                dir: dir.clone(),
                arity,
                allow_min: true,
                max_size,
                max_steps,
            });
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

    println!(
        "Building {} job(s) with {} thread(s), max_size={}, max_steps={}",
        job_list.len(),
        n_jobs,
        max_size,
        max_steps,
    );

    job_list.par_iter().for_each(run_build_job);

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
        } => cmd_build(&dir, max_size, allow_min, &arities, max_steps, jobs),
    }
}
