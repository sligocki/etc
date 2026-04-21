/// Distributed / checkpointed BBµ search task manager.
///
/// Three subcommands:
///   gen    — partition size range into tasks and write a manifest
///   run    — execute one or all pending tasks, writing per-task result files
///   merge  — aggregate result files into a per-size champion summary
use clap::{Args, Parser, Subcommand};
use gen_rec::enumerate::{count_grf, seek_stream_grf};
use gen_rec::grf::Grf;
use gen_rec::pruning::PruningOpts;
use gen_rec::simulate::simulate;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fs;
use std::io::{BufRead, BufReader, BufWriter, Write};
use std::path::{Path, PathBuf};
use std::time::Instant;

// ── CLI ───────────────────────────────────────────────────────────────────────

#[derive(Parser, Debug)]
#[command(
    about = "Distributed BBµ search: generate tasks, run them, merge results",
    long_about = None,
)]
struct Cli {
    #[command(subcommand)]
    cmd: Cmd,
}

#[derive(Subcommand, Debug)]
enum Cmd {
    /// Partition a single size into fixed tasks and write manifest + config.
    Gen(GenArgs),
    /// Execute one task (--task-id) or all pending tasks (--all).
    Run(RunArgs),
    /// Simulate a rank range directly and print one result line per GRF.
    Sim(SimArgs),
    /// Read all result files and print a per-size champion summary.
    Summarize(SummarizeArgs),
}

#[derive(Args, Debug)]
struct GenArgs {
    /// Task workspace directory (created if absent).
    dir: PathBuf,

    /// GRF size to generate tasks for.
    size: usize,

    /// GRFs per task chunk.
    #[arg(long, default_value_t = 100_000_000)]
    chunk_size: usize,

    /// Include Minimization combinator (default: PRF only).
    #[arg(long)]
    allow_min: bool,

    /// Maximum simulation steps before giving up on a GRF.
    #[arg(long, default_value_t = 1_000_000)]
    max_steps: u64,

    /// Include GRFs with score >= this in the notable list.
    #[arg(long, default_value_t = 10)]
    save_min_score: u64,

    /// Include GRFs with steps >= this in the notable list
    /// (captures long-running GRFs even if their score is low).
    #[arg(long, default_value_t = 100)]
    save_min_steps: u64,
}

#[derive(Args, Debug)]
struct RunArgs {
    /// Task workspace directory.
    dir: PathBuf,

    /// Run exactly this task ID (idempotent: skips if result already exists).
    /// Suitable for SLURM array jobs: --task-id $SLURM_ARRAY_TASK_ID
    #[arg(long, conflicts_with = "all")]
    task_id: Option<usize>,

    /// Run all pending tasks (those without a result file) in order.
    #[arg(long, conflicts_with = "task_id")]
    all: bool,

    /// Rayon thread-pool size for parallel batch simulation.
    /// Defaults to the number of logical CPUs.
    #[arg(long)]
    threads: Option<usize>,

    /// Simulation batch size (tune to your CPU count × ~200).
    #[arg(long, default_value_t = 2_000)]
    batch_size: usize,
}

#[derive(Args, Debug)]
struct SimArgs {
    /// Task workspace directory (reads size/opts/allow_min from config.json).
    dir: PathBuf,

    /// 0-based rank of the first GRF to simulate.
    start: usize,

    /// Number of GRFs to simulate.
    count: usize,

    /// Override max_steps from config.
    #[arg(long)]
    max_steps: Option<u64>,
}

#[derive(Args, Debug)]
struct SummarizeArgs {
    /// Task workspace directory.
    dir: PathBuf,

    /// How many top-scoring GRFs to display.
    #[arg(long, default_value_t = 10)]
    top: usize,
}

// ── Serialisable data types ───────────────────────────────────────────────────

/// Generation / run parameters stored in config.json.
#[derive(Debug, Clone, Serialize, Deserialize)]
struct Config {
    allow_min: bool,
    opts: SerOpts,
    max_steps: u64,
    save_min_score: u64,
    save_min_steps: u64,
}

/// Serialisable mirror of PruningOpts (avoids adding serde to the lib).
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
struct SerOpts {
    skip_comp_zero: bool,
    skip_comp_proj: bool,
    comp_assoc: bool,
    skip_rec_zero_base: bool,
    skip_rec_zero_arg: bool,
}

impl From<PruningOpts> for SerOpts {
    fn from(o: PruningOpts) -> Self {
        Self {
            skip_comp_zero: o.skip_comp_zero,
            skip_comp_proj: o.skip_comp_proj,
            comp_assoc: o.comp_assoc,
            skip_rec_zero_base: o.skip_rec_zero_base,
            skip_rec_zero_arg: o.skip_rec_zero_arg,
        }
    }
}
impl From<SerOpts> for PruningOpts {
    fn from(o: SerOpts) -> Self {
        Self {
            skip_comp_zero: o.skip_comp_zero,
            skip_comp_proj: o.skip_comp_proj,
            comp_assoc: o.comp_assoc,
            skip_rec_zero_base: o.skip_rec_zero_base,
            skip_rec_zero_arg: o.skip_rec_zero_arg,
        }
    }
}

/// One line in manifest.jsonl.
#[derive(Debug, Clone, Serialize, Deserialize)]
struct TaskEntry {
    task_id: usize,
    size: usize,
    /// 0-based rank of the first GRF in this task.
    start: usize,
    /// Number of GRFs in this task.
    count: usize,
}

/// One entry in the `notable` list of a result file.
#[derive(Debug, Clone, Serialize, Deserialize)]
struct NotableEntry {
    /// 0-based rank within `stream_grf` order for this size.
    rank: usize,
    /// Human-readable expression string.
    expr: String,
    /// "halted" | "unknown" | "infinite"
    status: String,
    /// Present when status == "unknown".
    #[serde(skip_serializing_if = "Option::is_none")]
    unknown_reason: Option<String>,
    /// Output value when status == "halted"; null otherwise.
    score: Option<u64>,
    /// Actual steps taken (halted) or max_steps (over_steps).
    steps: u64,
}

/// Written as task_{id:06}.json after a task completes.
#[derive(Debug, Clone, Serialize, Deserialize)]
struct TaskResult {
    task_id: usize,
    size: usize,
    start: usize,
    count: usize,
    // Run parameters repeated for self-containment.
    allow_min: bool,
    opts: SerOpts,
    max_steps: u64,
    save_min_score: u64,
    save_min_steps: u64,
    // Aggregate stats.
    total_grfs: usize,
    over_steps_count: usize,
    best_score: Option<u64>,
    /// All ranks tied for best_score within this task.
    best_ranks: Vec<usize>,
    elapsed_secs: f64,
    /// score → count of halted GRFs with that score.
    #[serde(default)]
    score_hist: HashMap<u64, u64>,
    /// steps → count of all GRFs that took that many steps.
    #[serde(default)]
    steps_hist: HashMap<u64, u64>,
    // Per-GRF records for notable entries.
    notable: Vec<NotableEntry>,
}

// ── File-path helpers ─────────────────────────────────────────────────────────

fn result_path(dir: &Path, task_id: usize) -> PathBuf {
    dir.join(format!("task_{task_id:06}.json"))
}
fn config_path(dir: &Path) -> PathBuf {
    dir.join("config.json")
}
fn manifest_path(dir: &Path) -> PathBuf {
    dir.join("manifest.jsonl")
}

fn timestamp() -> String {
    let secs = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs();
    let s = secs % 60;
    let m = (secs / 60) % 60;
    let h = (secs / 3600) % 24;
    format!("{h:02}:{m:02}:{s:02}")
}

fn read_config(dir: &Path) -> Config {
    let txt = fs::read_to_string(config_path(dir))
        .expect("Cannot read config.json — did you run `gen` first?");
    serde_json::from_str(&txt).expect("Malformed config.json")
}

fn read_manifest(dir: &Path) -> Vec<TaskEntry> {
    let f = fs::File::open(manifest_path(dir))
        .expect("Cannot open manifest.jsonl — did you run `gen` first?");
    BufReader::new(f)
        .lines()
        .map(|l| serde_json::from_str(&l.unwrap()).unwrap())
        .collect()
}

// ── gen ───────────────────────────────────────────────────────────────────────

fn cmd_gen(args: GenArgs) {
    let dir = &args.dir;
    fs::create_dir_all(dir).expect("Cannot create task directory");

    let opts = PruningOpts::all();
    let config = Config {
        allow_min: args.allow_min,
        opts: opts.into(),
        max_steps: args.max_steps,
        save_min_score: args.save_min_score,
        save_min_steps: args.save_min_steps,
    };
    fs::write(
        config_path(dir),
        serde_json::to_string_pretty(&config).unwrap(),
    )
    .expect("Cannot write config.json");

    let manifest = fs::File::create(manifest_path(dir)).expect("Cannot create manifest.jsonl");
    let mut manifest = BufWriter::new(manifest);

    let mut task_id = 0usize;
    let mut total_grfs = 0usize;
    let count = count_grf(args.size, 0, args.allow_min, opts);

    let mut start = 0;
    while start < count {
        let chunk = (count - start).min(args.chunk_size);
        let entry = TaskEntry {
            task_id,
            size: args.size,
            start,
            count: chunk,
        };
        writeln!(manifest, "{}", serde_json::to_string(&entry).unwrap()).unwrap();
        task_id += 1;
        total_grfs += chunk;
        start += chunk;
    }
    manifest.flush().unwrap();

    println!(
        "Generated {} tasks covering {} GRFs at size {}",
        task_id, total_grfs, args.size
    );
    println!("  config   → {}", config_path(dir).display());
    println!("  manifest → {}", manifest_path(dir).display());
}

// ── Core task execution ───────────────────────────────────────────────────────

/// Mutable accumulators updated by flush_batch.
struct Acc {
    total_grfs: usize,
    over_steps_count: usize,
    best_score: Option<u64>,
    best_ranks: Vec<usize>,
    /// score → count, for halted GRFs only.
    score_hist: HashMap<u64, u64>,
    /// steps → count, for all GRFs.
    steps_hist: HashMap<u64, u64>,
    notable: Vec<NotableEntry>,
}

impl Acc {
    fn new() -> Self {
        Self {
            total_grfs: 0,
            over_steps_count: 0,
            best_score: None,
            best_ranks: Vec::new(),
            score_hist: HashMap::new(),
            steps_hist: HashMap::new(),
            notable: Vec::new(),
        }
    }
}

/// Simulate one batch serially, fold results into `acc`.
fn flush_batch(batch: &mut Vec<(usize, Grf)>, config: &Config, acc: &mut Acc) {
    for (rank, grf) in batch.drain(..) {
        let expr = grf.to_string();
        let (sim_result, steps) = simulate(&grf, &[], config.max_steps);
        let score = sim_result.into_value();

        acc.total_grfs += 1;
        *acc.steps_hist.entry(steps).or_insert(0) += 1;
        match score {
            None => {
                acc.over_steps_count += 1;
                acc.notable.push(NotableEntry {
                    rank,
                    expr,
                    status: "unknown".to_string(),
                    unknown_reason: Some("over_steps".to_string()),
                    score: None,
                    steps,
                });
            }
            Some(s) => {
                *acc.score_hist.entry(s).or_insert(0) += 1;
                let is_new_best = acc.best_score.map_or(true, |bs| s > bs);
                if is_new_best {
                    acc.best_score = Some(s);
                    acc.best_ranks = if s >= config.save_min_score {
                        vec![rank]
                    } else {
                        vec![]
                    };
                } else if acc.best_score == Some(s) && s >= config.save_min_score {
                    acc.best_ranks.push(rank);
                }
                if s >= config.save_min_score || steps >= config.save_min_steps {
                    acc.notable.push(NotableEntry {
                        rank,
                        expr,
                        status: "halted".to_string(),
                        unknown_reason: None,
                        score: Some(s),
                        steps,
                    });
                }
            }
        }
    }
}

/// Run one task and return the result.  Does NOT write to disk.
fn execute_task(task: &TaskEntry, config: &Config, batch_size: usize) -> TaskResult {
    let opts: PruningOpts = config.opts.into();
    let t0 = Instant::now();
    let mut acc = Acc::new();
    let mut batch: Vec<(usize, Grf)> = Vec::with_capacity(batch_size);
    let mut rank = task.start;

    seek_stream_grf(
        task.size,
        0,
        config.allow_min,
        opts,
        task.start,
        task.count,
        &mut |grf: &Grf| {
            batch.push((rank, grf.clone()));
            rank += 1;
            if batch.len() >= batch_size {
                flush_batch(&mut batch, config, &mut acc);
            }
        },
    );
    flush_batch(&mut batch, config, &mut acc);

    TaskResult {
        task_id: task.task_id,
        size: task.size,
        start: task.start,
        count: task.count,
        allow_min: config.allow_min,
        opts: config.opts,
        max_steps: config.max_steps,
        save_min_score: config.save_min_score,
        save_min_steps: config.save_min_steps,
        total_grfs: acc.total_grfs,
        over_steps_count: acc.over_steps_count,
        best_score: acc.best_score,
        best_ranks: acc.best_ranks,
        elapsed_secs: t0.elapsed().as_secs_f64(),
        score_hist: acc.score_hist,
        steps_hist: acc.steps_hist,
        notable: acc.notable,
    }
}

/// Execute one task: check for existing result, run, write atomically.
fn run_task(task: &TaskEntry, config: &Config, dir: &Path, batch_size: usize) {
    let out = result_path(dir, task.task_id);
    if out.exists() {
        return; // idempotent
    }
    println!(
        "[{}] task {:06}: size={} ranks=[{}, {})",
        timestamp(),
        task.task_id,
        task.size,
        task.start,
        task.start + task.count
    );
    let result = execute_task(task, config, batch_size);
    println!(
        "[{}] task {:06}: done  best={:?}  over_steps={}  notable={}  [{:.2}s]",
        timestamp(),
        task.task_id,
        result.best_score,
        result.over_steps_count,
        result.notable.len(),
        result.elapsed_secs,
    );

    // Atomic write: write to .tmp then rename so partial writes are never visible.
    let tmp = out.with_extension("json.tmp");
    fs::write(&tmp, serde_json::to_string_pretty(&result).unwrap())
        .expect("Cannot write result file");
    fs::rename(&tmp, &out).expect("Cannot rename result file");
}

// ── run ───────────────────────────────────────────────────────────────────────

fn cmd_run(args: RunArgs) {
    let config = read_config(&args.dir);

    match (args.task_id, args.all) {
        (Some(id), _) => {
            // Single task (SLURM / distributed mode).
            let tasks = read_manifest(&args.dir);
            let task = tasks
                .iter()
                .find(|t| t.task_id == id)
                .unwrap_or_else(|| panic!("Task id {id} not found in manifest"));
            run_task(task, &config, &args.dir, args.batch_size);
        }
        (_, true) => {
            // All pending tasks — one task per worker thread.
            let n_threads = args.threads.unwrap_or_else(|| {
                std::thread::available_parallelism()
                    .map(|n| n.get())
                    .unwrap_or(1)
            });

            let tasks = read_manifest(&args.dir);
            let total_tasks = tasks.len();
            let pending: Vec<TaskEntry> = tasks
                .into_iter()
                .filter(|t| !result_path(&args.dir, t.task_id).exists())
                .collect();

            println!(
                "[{}] Pending tasks: {}/{}  [threads={}]",
                timestamp(),
                pending.len(),
                total_tasks,
                n_threads,
            );

            use std::collections::VecDeque;
            use std::sync::{Arc, Mutex};
            let queue = Arc::new(Mutex::new(pending.into_iter().collect::<VecDeque<_>>()));
            let total_start = Instant::now();

            let handles: Vec<_> = (0..n_threads)
                .map(|_| {
                    let queue = Arc::clone(&queue);
                    let config = config.clone();
                    let dir = args.dir.clone();
                    let batch_size = args.batch_size;
                    std::thread::spawn(move || loop {
                        let task = queue.lock().unwrap().pop_front();
                        match task {
                            None => break,
                            Some(t) => run_task(&t, &config, &dir, batch_size),
                        }
                    })
                })
                .collect();

            for h in handles {
                h.join().unwrap();
            }
            println!(
                "[{}] All tasks done  [{:.2}s total]",
                timestamp(),
                total_start.elapsed().as_secs_f64()
            );
        }
        _ => {
            eprintln!("Specify either --task-id N or --all");
            std::process::exit(1);
        }
    }
}

// ── sim ───────────────────────────────────────────────────────────────────────

fn cmd_sim(args: SimArgs) {
    let config = read_config(&args.dir);
    let opts: PruningOpts = config.opts.into();
    let max_steps = args.max_steps.unwrap_or(config.max_steps);

    // Config doesn't store size; read it from the manifest.
    let manifest = read_manifest(&args.dir);
    let size = manifest.first().expect("empty manifest").size;

    println!(
        "size={}  ranks=[{}, {})  max_steps={}",
        size,
        args.start,
        args.start + args.count,
        max_steps,
    );

    let mut rank = args.start;
    seek_stream_grf(
        size,
        0,
        config.allow_min,
        opts,
        args.start,
        args.count,
        &mut |grf: &Grf| {
            let expr = grf.to_string();
            let (sim_result, steps) = simulate(grf, &[], max_steps);
            match sim_result.into_value() {
                None => println!("rank={rank:>12}  unknown(over_steps)  steps={steps}  {expr}"),
                Some(s) => println!("rank={rank:>12}  halted  score={s}  steps={steps}  {expr}"),
            }
            rank += 1;
        },
    );
}

// ── merge ─────────────────────────────────────────────────────────────────────

fn merge_hist(mut combined: HashMap<u64, u64>, other: &HashMap<u64, u64>) -> HashMap<u64, u64> {
    for (key, value) in other {
        combined
            .entry(*key)
            .and_modify(|v| *v += *value)
            .or_insert(*value);
    }
    combined
}

// ── helpers ────────────────────────────────────────────────────────────────────

fn fmt_count(n: u64) -> String {
    if n < 1_000 { return n.to_string(); }
    if n < 1_000_000 { return format!("{:.1}k", n as f64 / 1_000.0); }
    if n < 1_000_000_000 { return format!("{:.1}M", n as f64 / 1_000_000.0); }
    format!("{:.1}B", n as f64 / 1_000_000_000.0)
}

/// Print a bar chart.  Bar length uses log₁₀(count+1) so rare entries stay visible.
fn print_bar_chart_log(rows: &[(&str, u64)], total: u64) {
    const BAR_WIDTH: usize = 40;
    let max_log = rows.iter()
        .map(|r| (r.1 as f64 + 1.0).log10())
        .fold(0.0_f64, f64::max)
        .max(1.0);
    let label_w = rows.iter().map(|r| r.0.len()).max().unwrap_or(1);
    for (label, count) in rows {
        let log_val = (*count as f64 + 1.0).log10();
        let bar_len = ((log_val / max_log) * BAR_WIDTH as f64).round() as usize;
        let bar: String = "█".repeat(bar_len);
        let pct = if total > 0 { *count as f64 / total as f64 * 100.0 } else { 0.0 };
        println!(
            "  {:<lw$}  {:<bw$}  {:>12}  ({:.2}%)",
            label, bar, fmt_count(*count), pct,
            lw = label_w, bw = BAR_WIDTH,
        );
    }
}

/// Print a power-of-2 bucketed histogram with log-scale bars.
/// If the data contains any 0 values, they get their own "=0" row before the ≤1 bucket.
fn print_pow2_hist(title: &str, hist: HashMap<u64, u64>) {
    let total: u64 = hist.values().sum();
    let zero_count = hist.get(&0).copied().unwrap_or(0);
    let separate_zero = zero_count > 0;
    let max_val = hist.keys().copied().max().unwrap_or(0);
    let max_k = (0u32..=63).find(|&k| (1u64 << k) >= max_val).unwrap_or(63);
    let breakpoints: Vec<(u64, String)> = (0u32..=max_k)
        .map(|k| (1u64 << k, format!("≤{}", fmt_count(1u64 << k))))
        .collect();
    let mut buckets: Vec<u64> = vec![0; breakpoints.len() + 1];
    for (&val, &count) in &hist {
        if separate_zero && val == 0 { continue; }
        let idx = breakpoints.iter().position(|(bp, _)| val <= *bp)
            .unwrap_or(breakpoints.len());
        buckets[idx] += count;
    }
    let last_label = format!(">{}", fmt_count(1u64 << max_k));
    let mut rows: Vec<(String, u64)> = Vec::new();
    if separate_zero { rows.push(("=0".to_string(), zero_count)); }
    for (i, (_, label)) in breakpoints.iter().enumerate() {
        if buckets[i] > 0 { rows.push((label.clone(), buckets[i])); }
    }
    if *buckets.last().unwrap() > 0 { rows.push((last_label, *buckets.last().unwrap())); }
    let display: Vec<(&str, u64)> = rows.iter().map(|(l, c)| (l.as_str(), *c)).collect();
    println!("{}  (log scale, total: {})", title, fmt_count(total));
    print_bar_chart_log(&display, total);
}

/// Per-size aggregate built during summarize.
struct SizeSummary {
    tasks_done: usize,
    total_grfs: usize,
    over_steps_count: usize,
    runtime_sec: f64,
    best_score: Option<u64>,
    notable: Vec<NotableEntry>,
}

fn cmd_summarize(args: SummarizeArgs) {
    let dir = &args.dir;

    // Count total tasks per size from the manifest.
    let manifest = read_manifest(dir);
    let tasks_total = manifest.len();

    // Read all task_*.json files.
    let mut results: Vec<TaskResult> = Vec::new();
    let mut entries = fs::read_dir(dir)
        .expect("Cannot read task directory")
        .collect::<Result<Vec<_>, _>>()
        .unwrap();
    entries.sort_by_key(|e| e.file_name());

    for entry in entries {
        let path = entry.path();
        let name = path.file_name().unwrap().to_str().unwrap_or("");
        if name.starts_with("task_") && name.ends_with(".json") {
            let txt = fs::read_to_string(&path)
                .unwrap_or_else(|e| panic!("Cannot read {}: {e}", path.display()));
            match serde_json::from_str::<TaskResult>(&txt) {
                Ok(r) => results.push(r),
                Err(e) => eprintln!("Skipping {}: {e}", path.display()),
            }
        }
    }

    if results.is_empty() {
        println!("No result files found in {}", dir.display());
        return;
    }

    let size = results[0].size;
    let mut s = SizeSummary {
        tasks_done: 0,
        total_grfs: 0,
        over_steps_count: 0,
        runtime_sec: 0.0,
        best_score: None,
        notable: Vec::new(),
    };
    let mut score_hist: HashMap<u64, u64> = HashMap::new();
    let mut steps_hist: HashMap<u64, u64> = HashMap::new();
    for r in &results {
        assert_eq!(r.size, size);
        s.tasks_done += 1;
        s.total_grfs += r.total_grfs;
        s.over_steps_count += r.over_steps_count;
        s.runtime_sec += r.elapsed_secs;

        if let Some(score) = r.best_score {
            if s.best_score.map_or(true, |bs| score > bs) {
                s.best_score = Some(score);
            }
        }
        s.notable.extend_from_slice(&r.notable);
        score_hist = merge_hist(score_hist, &r.score_hist);
        steps_hist = merge_hist(steps_hist, &r.steps_hist);
    }

    // Build top-N list: deduplicate by expr, sort by score desc.
    let mut seen_exprs = std::collections::HashSet::new();
    let mut top_entries: Vec<(u64, String)> = s.notable.iter()
        .filter_map(|n| n.score.map(|sc| (sc, n.expr.clone())))
        .filter(|(_, expr)| seen_exprs.insert(expr.clone()))
        .collect();
    top_entries.sort_by(|a, b| b.0.cmp(&a.0));
    top_entries.truncate(args.top);

    // Check completeness.
    let total_done: usize = s.tasks_done;
    let total_tasks: usize = manifest.len();
    let is_partial = total_done < total_tasks;

    let max_steps = steps_hist.keys().copied().max().unwrap_or(0);
    println!();
    print_pow2_hist("Steps Histogram", steps_hist);
    println!();
    print_pow2_hist("Score Histogram", score_hist);
    println!();

    println!("Top {} GRFs:", args.top);
    for (score, expr) in &top_entries {
        println!("  {:>6}  {}", score, expr);
    }
    println!();

    println!("Size: {}", size);
    let score_str = match s.best_score {
        Some(v) => v.to_string(),
        None => "-".to_string(),
    };
    println!("Max Score: {}", score_str);
    println!("Max Steps: {}", max_steps);
    println!("# Over Steps: {}", s.over_steps_count);
    println!("Total GRFs: {}", s.total_grfs);
    println!("Tasks Complete: {}/{}", s.tasks_done, tasks_total);
    println!();

    println!("Total runtime: {:.1} core-hr", s.runtime_sec / 3600.0);
    println!();

    if is_partial {
        println!(
            "*** PARTIAL RESULTS: {}/{} tasks complete ***",
            total_done, total_tasks
        );
    }
}

// ── main ──────────────────────────────────────────────────────────────────────

fn main() {
    let cli = Cli::parse();
    match cli.cmd {
        Cmd::Gen(a) => cmd_gen(a),
        Cmd::Run(a) => cmd_run(a),
        Cmd::Sim(a) => cmd_sim(a),
        Cmd::Summarize(a) => cmd_summarize(a),
    }
}
