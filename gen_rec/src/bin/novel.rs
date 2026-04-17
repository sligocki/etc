/// List the smallest non-redundant GRF for each distinct total function of a given arity.
///
/// Usage examples:
///   novel                                    # arity 1, sizes 1..=10, total only
///   novel 2 --max-size 12                    # arity 2
///   novel 1 --allow-min                      # include Min combinator
///   novel 1 --partial                        # include partial functions
///   novel 1 --max-size 10 --save prf10.db
///   novel 1 --max-size 12 --load prf10.db --save prf12.db
///   novel 1 --max-size 12 --db-dir fp/       # auto-load/save a1_prf.db in fp/
///   novel 1 --max-size 8 --allow-min --db-dir fp/
use clap::Parser;
use gen_rec::novel_db::{
    db_filename, extend_novel_map, format_fp, load_novel_file, merge_into, save_novel_file,
    NovelMap,
};
use std::path::PathBuf;

#[derive(Parser, Debug)]
#[command(
    about = "List the smallest non-redundant GRF for each distinct function",
    long_about = "Enumerates GRFs in size order and prints each one that computes a\n\
                  function not yet seen among smaller GRFs."
)]
struct Args {
    /// Arity of GRFs to enumerate.
    #[arg(default_value_t = 1)]
    arity: usize,

    /// Enumerate up to this size (inclusive).
    #[arg(long, default_value_t = 10)]
    max_size: usize,

    /// Max simulation steps per input when computing fingerprints.
    #[arg(long, default_value_t = 10_000)]
    max_steps: u64,

    /// Include the Minimization combinator.
    #[arg(long)]
    allow_min: bool,

    /// Include GRFs with timeouts (partial functions); default is total-only.
    #[arg(long)]
    partial: bool,

    /// DB directory: auto-loads a{arity}_{prf|min}.db (and the matching prf file as
    /// a seed for --allow-min runs), then saves back when done.
    /// Mutually exclusive with --load / --save.
    #[arg(long, value_name = "DIR")]
    db_dir: Option<PathBuf>,

    /// Load one or more pre-computed novel DB files (can be repeated).
    #[arg(long, value_name = "PATH")]
    load: Vec<PathBuf>,

    /// Save the computed novel DB to this file when done.
    #[arg(long, value_name = "PATH")]
    save: Option<PathBuf>,

    /// Print progress to stderr after each size.
    #[arg(long)]
    progress: bool,
}

fn main() {
    let args = Args::parse();

    let mut map: NovelMap = NovelMap::new();
    let mut start_size = 1usize;

    // ── db-dir: auto-load ─────────────────────────────────────────────────────
    if let Some(ref dir) = args.db_dir {
        // For allow_min runs, pre-populate from the prf file so PRF functions
        // whose Min version is smaller still show the Min version as "novel".
        if args.allow_min {
            let seed = db_filename(dir, args.arity, false);
            if seed.exists() {
                match load_novel_file(&seed) {
                    Ok((_, seed_map, _)) => merge_into(&mut map, seed_map),
                    Err(e) => {
                        eprintln!("warning: could not load seed {}: {e}", seed.display())
                    }
                }
            }
        }
        // Load the main target file (get start_size from its header).
        let target = db_filename(dir, args.arity, args.allow_min);
        if target.exists() {
            match load_novel_file(&target) {
                Ok((meta, file_map, _)) => {
                    start_size = meta.max_size + 1;
                    merge_into(&mut map, file_map);
                }
                Err(e) => {
                    eprintln!("error: could not load {}: {e}", target.display());
                    std::process::exit(1);
                }
            }
        }
    }

    // ── --load: manual files ──────────────────────────────────────────────────
    for load_path in &args.load {
        match load_novel_file(load_path) {
            Ok((meta, file_map, _)) => {
                // Advance start_size only from files with matching allow_min coverage.
                if meta.allow_min == args.allow_min {
                    start_size = start_size.max(meta.max_size + 1);
                }
                merge_into(&mut map, file_map);
            }
            Err(e) => {
                eprintln!("error: could not load {}: {e}", load_path.display());
                std::process::exit(1);
            }
        }
    }

    // ── enumerate ─────────────────────────────────────────────────────────────
    if start_size <= args.max_size {
        let _ = extend_novel_map(
            &mut map,
            args.arity,
            start_size,
            args.max_size,
            args.allow_min,
            args.max_steps,
            args.partial,
            args.progress,
        );
    }

    // ── print sorted output ───────────────────────────────────────────────────
    let mut output: Vec<(usize, &String, &_)> =
        map.iter().map(|(fp, (s, g))| (*s, g, fp)).collect();
    output.sort_by_key(|(s, g, _)| (*s, g.as_str()));
    for (size, grf, fp) in &output {
        println!("{:>4}  {:<40}  [{}]", size, grf, format_fp(fp));
    }

    eprintln!(
        "Done. {} distinct functions for arity {} up to size {}.",
        map.len(),
        args.arity,
        args.max_size,
    );

    // ── save ──────────────────────────────────────────────────────────────────
    let save_path = args
        .save
        .clone()
        .or_else(|| args.db_dir.as_ref().map(|d| db_filename(d, args.arity, args.allow_min)));

    if let Some(path) = save_path {
        if let Err(e) =
            save_novel_file(&path, args.allow_min, args.max_size, args.max_steps, &map, &[])
        {
            eprintln!("error: could not save to {}: {e}", path.display());
            std::process::exit(1);
        }
        eprintln!("Saved {} entries to {}.", map.len(), path.display());
    }
}
