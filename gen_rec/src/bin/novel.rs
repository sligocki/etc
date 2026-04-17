/// List the smallest non-redundant GRF for each distinct total function of a given arity.
///
/// A GRF is non-redundant if no smaller GRF computes the same function on all inputs.
/// By default only GRFs that converge on every canonical input are shown (total functions).
/// Use --partial to also include GRFs with at least one timeout.
///
/// Usage examples:
///   novel                          # arity 1, sizes 1..=10, total only
///   novel 2                        # arity 2
///   novel 1 --max-size 12 --allow-min
///   novel 1 --partial              # include partial functions
///   novel 1 --max-size 10 --save prf10.db
///   novel 1 --max-size 12 --load prf10.db --save prf12.db
///   novel 1 --max-size 8 --allow-min --load prf10.db --save min8.db
use clap::Parser;
use gen_rec::enumerate::stream_grf;
use gen_rec::fingerprint::{canonical_inputs, compute_fp, fp_is_complete, Fingerprint};
use gen_rec::grf::Grf;
use gen_rec::pruning::PruningOpts;
use std::collections::HashMap;
use std::io::{self, BufRead, Write};
use std::path::{Path, PathBuf};

#[derive(Parser, Debug)]
#[command(
    about = "List the smallest non-redundant GRF for each distinct function",
    long_about = "Enumerates GRFs in size order and prints each one that computes a\n\
                  function not yet seen among smaller GRFs.\n\
                  Progress is printed to stderr."
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

// ── file format ───────────────────────────────────────────────────────────────

struct DbMeta {
    allow_min: bool,
    max_size: usize,
}

fn parse_header(line: &str) -> Option<DbMeta> {
    if !line.starts_with("allow_min=") {
        return None;
    }
    let mut allow_min = false;
    let mut max_size = 0usize;
    for kv in line.split_whitespace() {
        if let Some(v) = kv.strip_prefix("allow_min=") {
            allow_min = v == "true";
        } else if let Some(v) = kv.strip_prefix("max_size=") {
            max_size = v.parse().unwrap_or(0);
        }
    }
    Some(DbMeta { allow_min, max_size })
}

/// Load a novel DB file.  Returns (meta, entries) where entries is a vec of (size, grf_string).
fn load_db_file(path: &Path) -> io::Result<(DbMeta, Vec<(usize, String)>)> {
    let file = std::fs::File::open(path)?;
    let reader = io::BufReader::new(file);
    let mut meta: Option<DbMeta> = None;
    let mut entries: Vec<(usize, String)> = Vec::new();

    for (lineno, line) in reader.lines().enumerate() {
        let line = line?;
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        if meta.is_none() {
            meta = Some(parse_header(line).ok_or_else(|| {
                io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!("{}: line {}: expected header", path.display(), lineno + 1),
                )
            })?);
            continue;
        }
        let mut parts = line.splitn(2, '\t');
        let size: usize = parts
            .next()
            .unwrap_or("")
            .trim()
            .parse()
            .map_err(|_| {
                io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!("{}: line {}: bad size", path.display(), lineno + 1),
                )
            })?;
        let grf_str = parts.next().ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                format!("{}: line {}: missing grf", path.display(), lineno + 1),
            )
        })?;
        entries.push((size, grf_str.to_string()));
    }

    let meta = meta.ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidData,
            format!("{}: file has no header", path.display()),
        )
    })?;
    Ok((meta, entries))
}

fn save_db_file(
    path: &Path,
    allow_min: bool,
    max_size: usize,
    max_steps: u64,
    fp_db: &HashMap<Fingerprint, (usize, String)>,
) -> io::Result<()> {
    let file = std::fs::File::create(path)?;
    let mut w = io::BufWriter::new(file);
    writeln!(
        w,
        "allow_min={allow_min} max_size={max_size} max_steps={max_steps}"
    )?;
    // Sort by size then grf string for deterministic output.
    let mut entries: Vec<(&usize, &String)> = fp_db.values().map(|(s, g)| (s, g)).collect();
    entries.sort_by_key(|(s, g)| (*s, g.as_str()));
    for (size, grf) in entries {
        writeln!(w, "{size}\t{grf}")?;
    }
    Ok(())
}

// ── fingerprint helpers ───────────────────────────────────────────────────────

fn fingerprint_grf(
    grf: &Grf,
    inputs: &[Vec<u64>],
    max_steps: u64,
    partial: bool,
) -> Option<Fingerprint> {
    let fp = compute_fp(grf, inputs, max_steps);
    let is_total = fp_is_complete(&fp);
    if !partial && !is_total {
        None
    } else {
        Some(fp)
    }
}

// ── main ─────────────────────────────────────────────────────────────────────

fn main() {
    let args = Args::parse();
    let opts = PruningOpts::default();
    let inputs = canonical_inputs(args.arity);

    // fp → (size, grf_string)
    let mut fp_db: HashMap<Fingerprint, (usize, String)> = HashMap::new();

    // ── load pre-computed files ───────────────────────────────────────────────
    let mut start_size = 1usize;

    for load_path in &args.load {
        let (meta, entries) = match load_db_file(load_path) {
            Ok(r) => r,
            Err(e) => {
                eprintln!("error: could not load {}: {e}", load_path.display());
                std::process::exit(1);
            }
        };

        // Advance start_size only from files whose allow_min coverage matches ours.
        if meta.allow_min == args.allow_min {
            start_size = start_size.max(meta.max_size + 1);
        }

        for (size, grf_str) in entries {
            let grf: Grf = match grf_str.parse() {
                Ok(g) => g,
                Err(e) => {
                    eprintln!("warning: skipping bad grf '{grf_str}': {e}");
                    continue;
                }
            };
            if grf.arity() != args.arity {
                continue; // different arity — still populates fp_db to prevent re-discovery
            }
            if let Some(fp) = fingerprint_grf(&grf, &inputs, args.max_steps, args.partial) {
                let is_novel = fp_db.get(&fp).map_or(true, |(s, _)| size < *s);
                if is_novel {
                    fp_db.insert(fp, (size, grf_str));
                }
            }
        }
    }

    // ── enumerate new sizes ───────────────────────────────────────────────────
    if start_size <= args.max_size {
        for size in start_size..=args.max_size {
            let mut total = 0usize;
            let mut novel = 0usize;

            stream_grf(size, args.arity, args.allow_min, opts, &mut |grf| {
                total += 1;
                if let Some(fp) = fingerprint_grf(grf, &inputs, args.max_steps, args.partial) {
                    let is_novel = fp_db.get(&fp).map_or(true, |(s, _)| size < *s);
                    if is_novel {
                        let expr = grf.to_string();
                        fp_db.insert(fp, (size, expr));
                        novel += 1;
                    }
                }
            });

            if args.progress {
                eprintln!(
                    "size {:>3}: {:>8} enumerated, {:>6} novel ({} distinct functions total)",
                    size,
                    total,
                    novel,
                    fp_db.len()
                );
            }
        }
    }

    // Print all entries sorted by (size, grf_string).
    let mut output: Vec<(usize, &String, &Fingerprint)> = fp_db
        .iter()
        .map(|(fp, (size, grf))| (*size, grf, fp))
        .collect();
    output.sort_by_key(|(size, grf, _)| (*size, grf.as_str()));
    for (size, grf, fp) in &output {
        println!("{:>4}  {:<40}  [{}]", size, grf, fp_display(fp));
    }

    eprintln!(
        "Done. {} distinct functions found for arity {} up to size {}.",
        fp_db.len(),
        args.arity,
        args.max_size,
    );

    // ── save ──────────────────────────────────────────────────────────────────
    if let Some(save_path) = &args.save {
        if let Err(e) = save_db_file(
            save_path,
            args.allow_min,
            args.max_size,
            args.max_steps,
            &fp_db,
        ) {
            eprintln!("error: could not save to {}: {e}", save_path.display());
            std::process::exit(1);
        }
        eprintln!("Saved {} entries to {}.", fp_db.len(), save_path.display());
    }
}

fn fp_display(fp: &Fingerprint) -> String {
    fp.iter()
        .map(|v| match v {
            Some(n) => n.to_string(),
            None => "?".to_string(),
        })
        .collect::<Vec<_>>()
        .join(", ")
}
