/// Shared library for the novel-functions database.
///
/// File format (one file per arity+allow_min combination):
///   Line 1: `allow_min=<bool> max_size=<usize> max_steps=<u64>`
///   Subsequent lines: `<size>\t<grf>\t<fingerprint>`
///     where fingerprint is comma-separated: integers for Value(n), `?` for Unknown, `!` for Diverge.
///   Timed-out lines: `<size>\t<grf>\t?`  (single `?` = no fingerprint computed)
///     These are GRFs that did not converge within max_steps. On reload with a
///     higher step budget, they are retried and may be recovered into the main map.
///
/// Canonical filenames: `a{arity}_{prf|min}.db`
use crate::enumerate::stream_grf;
use crate::fingerprint::{canonical_inputs, compute_fp, fp_is_complete, Fingerprint, FingerprintDb, FpEntry};
use crate::grf::Grf;
use crate::pruning::PruningOpts;
use std::collections::HashMap;
use std::io::{self, BufRead, Write};
use std::path::{Path, PathBuf};

/// In-memory novel DB: fingerprint → (size, grf_string)
pub type NovelMap = HashMap<Fingerprint, (usize, String)>;

pub struct NovelDbMeta {
    pub allow_min: bool,
    pub max_size: usize,
    pub max_steps: u64,
}

/// Canonical filename for a novel DB of the given arity and allow_min setting.
pub fn db_filename(dir: &Path, arity: usize, allow_min: bool) -> PathBuf {
    let suffix = if allow_min { "min" } else { "prf" };
    dir.join(format!("a{arity}_{suffix}.db"))
}

/// Parse a stored fingerprint string: "0,1,2,?,4,!" → Vec<FpEntry>
///
/// Format: integers for Value(n), "?" for Unknown (OutOfSteps), "!" for Diverge.
fn parse_fp(s: &str) -> Option<Fingerprint> {
    s.split(',')
        .map(|v| {
            let v = v.trim();
            if v == "?" {
                Some(FpEntry::Unknown)
            } else if v == "!" {
                Some(FpEntry::Diverge)
            } else {
                v.parse::<u64>().ok().map(FpEntry::Value)
            }
        })
        .collect()
}

/// Format a fingerprint for writing to a file.
///
/// Format: integers for Value(n), "?" for Unknown, "!" for Diverge.
pub fn format_fp(fp: &Fingerprint) -> String {
    fp.iter()
        .map(|v| match v {
            FpEntry::Value(n) => n.to_string(),
            FpEntry::Unknown => "?".to_string(),
            FpEntry::Diverge => "!".to_string(),
        })
        .collect::<Vec<_>>()
        .join(",")
}

/// Load a novel DB file.
///
/// Returns `(meta, map, timed_out)` where:
/// - `map`: entries with known fingerprints (the normal novel entries)
/// - `timed_out`: `(size, grf_string)` pairs stored with a `?` fingerprint —
///   GRFs that did not converge when the file was written; may be retried with
///   a higher step budget via `retry_timed_out`.
///
/// Lines with a stored fingerprint use it directly. Lines without a fingerprint
/// column (old format) are re-fingerprinted using `meta.max_steps`.
pub fn load_novel_file(path: &Path) -> io::Result<(NovelDbMeta, NovelMap, Vec<(usize, String)>)> {
    let file = std::fs::File::open(path)?;
    let reader = io::BufReader::new(file);
    let mut meta: Option<NovelDbMeta> = None;
    let mut map: NovelMap = HashMap::new();
    let mut timed_out: Vec<(usize, String)> = Vec::new();
    let mut needs_refp: Vec<(usize, Grf)> = Vec::new();

    for (lineno, line) in reader.lines().enumerate() {
        let line = line?;
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }

        if meta.is_none() {
            if !line.starts_with("allow_min=") {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!("{}: line {}: expected header", path.display(), lineno + 1),
                ));
            }
            let mut allow_min = false;
            let mut max_size = 0usize;
            let mut max_steps = 10_000u64;
            for kv in line.split_whitespace() {
                if let Some(v) = kv.strip_prefix("allow_min=") {
                    allow_min = v == "true";
                } else if let Some(v) = kv.strip_prefix("max_size=") {
                    max_size = v.parse().unwrap_or(0);
                } else if let Some(v) = kv.strip_prefix("max_steps=") {
                    max_steps = v.parse().unwrap_or(10_000);
                }
            }
            meta = Some(NovelDbMeta { allow_min, max_size, max_steps });
            continue;
        }

        // Data line: size \t grf [\t fp]
        let mut parts = line.splitn(3, '\t');
        let size_s = parts.next().unwrap_or("").trim();
        let grf_s = parts
            .next()
            .ok_or_else(|| {
                io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!("{}: line {}: missing grf", path.display(), lineno + 1),
                )
            })?
            .trim();
        let fp_s = parts.next().map(str::trim);

        let size: usize = size_s.parse().map_err(|_| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                format!("{}: line {}: bad size '{size_s}'", path.display(), lineno + 1),
            )
        })?;

        // A lone "?" in the fingerprint column means "timed out when written".
        if fp_s == Some("?") {
            timed_out.push((size, grf_s.to_string()));
            continue;
        }

        let grf: Grf = grf_s.parse().map_err(|e| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                format!("{}: line {}: parse error: {e}", path.display(), lineno + 1),
            )
        })?;

        if let Some(fp) = fp_s.and_then(parse_fp) {
            // Use stored fingerprint — no simulation needed.
            let e = map.entry(fp).or_insert((size, grf_s.to_string()));
            if size < e.0 {
                *e = (size, grf_s.to_string());
            }
        } else {
            // Old format (no fp column) — re-fingerprint later.
            needs_refp.push((size, grf));
        }
    }

    let meta = meta.ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidData,
            format!("{}: file has no header", path.display()),
        )
    })?;

    // Re-fingerprint entries that lacked the stored fp column.
    if !needs_refp.is_empty() {
        let max_steps = meta.max_steps;
        let mut by_arity: HashMap<usize, Vec<(usize, Grf)>> = HashMap::new();
        for (sz, g) in needs_refp {
            by_arity.entry(g.arity()).or_default().push((sz, g));
        }
        for (arity, entries) in by_arity {
            let inputs = canonical_inputs(arity);
            for (sz, g) in entries {
                let fp = compute_fp(&g, &inputs, max_steps);
                if fp_is_complete(&fp) {
                    let s = g.to_string();
                    let e = map.entry(fp).or_insert((sz, s.clone()));
                    if sz < e.0 {
                        *e = (sz, s);
                    }
                }
            }
        }
    }

    Ok((meta, map, timed_out))
}

/// Re-fingerprint a list of previously-timed-out `(size, grf_string)` entries
/// using a (presumably larger) step budget.
///
/// Entries that converge are merged into `map` (keeping the smaller GRF per
/// fingerprint). Entries that still time out are returned as the remaining
/// timed-out list.
///
/// Returns `(still_timed_out, recovered_count)`.
pub fn retry_timed_out(
    entries: Vec<(usize, String)>,
    map: &mut NovelMap,
    arity: usize,
    max_steps: u64,
) -> (Vec<(usize, String)>, usize) {
    let inputs = canonical_inputs(arity);
    let mut still_timed_out = Vec::new();
    let mut recovered = 0usize;

    for (size, grf_str) in entries {
        let grf: Grf = match grf_str.parse() {
            Ok(g) => g,
            Err(_) => { still_timed_out.push((size, grf_str)); continue; }
        };
        let fp = compute_fp(&grf, &inputs, max_steps);
        if fp_is_complete(&fp) {
            let is_novel = map.get(&fp).map_or(true, |(s, _)| size < *s);
            if is_novel {
                map.insert(fp, (size, grf_str));
            }
            recovered += 1;
        } else {
            still_timed_out.push((size, grf_str));
        }
    }

    (still_timed_out, recovered)
}

/// Save a NovelMap to a file, including stored fingerprints and timed-out entries.
///
/// Timed-out entries are written with a lone `?` as the fingerprint column so they
/// can be retried on a future run with a higher step budget.
pub fn save_novel_file(
    path: &Path,
    allow_min: bool,
    max_size: usize,
    max_steps: u64,
    map: &NovelMap,
    timed_out: &[(usize, String)],
) -> io::Result<()> {
    if let Some(parent) = path.parent() {
        if !parent.as_os_str().is_empty() {
            std::fs::create_dir_all(parent)?;
        }
    }
    let file = std::fs::File::create(path)?;
    let mut w = io::BufWriter::new(file);
    writeln!(w, "allow_min={allow_min} max_size={max_size} max_steps={max_steps}")?;
    let mut entries: Vec<(&Fingerprint, usize, &str)> =
        map.iter().map(|(fp, (s, g))| (fp, *s, g.as_str())).collect();
    entries.sort_by_key(|(_, s, g)| (*s, *g));
    for (fp, size, grf) in entries {
        writeln!(w, "{size}\t{grf}\t{}", format_fp(fp))?;
    }
    // Write timed-out entries sorted by (size, grf) for determinism.
    let mut to_sorted = timed_out.to_vec();
    to_sorted.sort_by(|(sa, ga), (sb, gb)| sa.cmp(sb).then(ga.cmp(gb)));
    for (size, grf) in &to_sorted {
        writeln!(w, "{size}\t{grf}\t?")?;
    }
    Ok(())
}

/// Merge entries from `src` into `dst`, keeping the smaller GRF for each fingerprint.
pub fn merge_into(dst: &mut NovelMap, src: NovelMap) {
    for (fp, (size, grf)) in src {
        let e = dst.entry(fp).or_insert((size, grf.clone()));
        if size < e.0 {
            *e = (size, grf);
        }
    }
}

/// Statistics returned by `extend_novel_map`.
pub struct EnumStats {
    /// Total GRFs passed to the fingerprinting step.
    pub total_tested: usize,
    /// GRFs that were novel (added or replaced a larger entry in the map).
    pub total_new: usize,
    /// GRFs that did not converge within the step budget (excluded from map when !partial).
    /// Contains `(size, grf_string)` for persistence across runs.
    pub timed_out_entries: Vec<(usize, String)>,
}

pub fn extend_novel_map(
    map: &mut NovelMap,
    arity: usize,
    start_size: usize,
    max_size: usize,
    allow_min: bool,
    max_steps: u64,
    partial: bool,
    progress: bool,
) -> EnumStats {
    let opts = PruningOpts::default();
    let inputs = canonical_inputs(arity);
    let mut stats = EnumStats { total_tested: 0, total_new: 0, timed_out_entries: Vec::new() };

    for size in start_size..=max_size {
        let mut n_enum = 0usize;
        let mut n_new = 0usize;

        stream_grf(size, arity, allow_min, opts, &mut |grf| {
            n_enum += 1;
            let fp = compute_fp(grf, &inputs, max_steps);
            if !fp_is_complete(&fp) {
                if !partial {
                    stats.timed_out_entries.push((size, grf.to_string()));
                    return;
                }
            }
            let is_novel = map.get(&fp).map_or(true, |(s, _)| size < *s);
            if is_novel {
                map.insert(fp, (size, grf.to_string()));
                n_new += 1;
                stats.total_new += 1;
            }
        });

        stats.total_tested += n_enum;

        if progress {
            eprintln!(
                "size {:>3}: {:>8} enumerated, {:>5} novel  ({} total)",
                size, n_enum, n_new, map.len()
            );
        }
    }
    stats
}

// ── FingerprintDb construction from novel files ───────────────────────────────

/// All `.db` file paths in a directory, sorted.
pub fn db_paths_in_dir(dir: &Path) -> io::Result<Vec<PathBuf>> {
    let mut paths = Vec::new();
    for entry in std::fs::read_dir(dir)? {
        let path = entry?.path();
        if path.extension().and_then(|e| e.to_str()) == Some("db") {
            paths.push(path);
        }
    }
    paths.sort();
    Ok(paths)
}

/// Build a `FingerprintDb` from a single novel DB file.
/// Uses stored fingerprints when available (no re-simulation needed).
/// Timed-out entries in the file are ignored (they have no fingerprint to look up).
pub fn fingerprint_db_from_file(path: &Path, max_steps: u64) -> io::Result<FingerprintDb> {
    let (meta, map, _timed_out) = load_novel_file(path)?;
    if meta.max_steps != max_steps {
        eprintln!(
            "warning: {} was built with max_steps={} but loading with max_steps={}; \
             fingerprint mismatches may cause missed optimizations",
            path.display(),
            meta.max_steps,
            max_steps,
        );
    }
    let mut db = FingerprintDb::build_empty(max_steps);
    for (fp, (_, grf_str)) in map {
        if let Ok(grf) = grf_str.parse::<Grf>() {
            db.add_entry(grf.arity(), fp, grf);
        }
    }
    Ok(db)
}

/// Build a `FingerprintDb` from all `.db` files in a directory.
/// Timed-out entries in any file are ignored (they have no fingerprint to look up).
pub fn fingerprint_db_from_dir(dir: &Path, max_steps: u64) -> io::Result<FingerprintDb> {
    let mut db = FingerprintDb::build_empty(max_steps);
    for path in db_paths_in_dir(dir)? {
        let (meta, map, _timed_out) = match load_novel_file(&path) {
            Ok(r) => r,
            Err(e) => {
                eprintln!("warning: skipping {}: {e}", path.display());
                continue;
            }
        };
        if meta.max_steps != max_steps {
            eprintln!(
                "warning: {} was built with max_steps={}",
                path.display(),
                meta.max_steps,
            );
        }
        for (fp, (_, grf_str)) in map {
            if let Ok(grf) = grf_str.parse::<Grf>() {
                db.add_entry(grf.arity(), fp, grf);
            }
        }
    }
    Ok(db)
}
