use clap::{Parser, Subcommand};
use gen_rec::enumerate::{stream_grf_visited, EnumScope, EnumVisitor};
use std::sync::atomic::{AtomicUsize, Ordering};
use gen_rec::pruning::PruningOpts;
use gen_rec::search_util::{flush_batch, Accumulator};
use gen_rec::io_grl::{self, GrfEntry, Status};
use gen_rec::alias::alias_db_for_stdout;
use gen_rec::grf::Grf;
use std::io::{BufReader, Write, BufWriter};
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use std::cell::RefCell;
use std::fs::{self, File};
use std::path::PathBuf;
use std::rc::Rc;
use rand::seq::SliceRandom;
use rand::SeedableRng;

#[derive(Parser)]
#[command(name = "bb_search_task", about = "MapReduce-style distributed GRF enumeration")]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Phase 1: Initialize the results directory and generate the manifest
    Init {
        results_dir: PathBuf,
        #[arg(value_enum)]
        enum_scope: EnumScope,
        size: usize,
        #[arg(long, default_value_t = 8)]
        task_size: usize,
        #[arg(long, default_value_t = 1000)]
        num_tasks: usize,
        #[arg(long)]
        allow_min: bool,
    },
    /// Phase 2: Run a subtask
    Worker {
        results_dir: PathBuf,
        #[arg(long)]
        task_id: Option<usize>,
        #[arg(long)]
        all_tasks: bool,
        #[arg(long, default_value_t = 100_000)]
        max_steps: u64,
        #[arg(long, default_value_t = 2000)]
        batch_size: usize,
        #[arg(long, default_value_t = 100)]
        top_k: usize,
    },
    /// Phase 3: Combine all results
    Summary {
        results_dir: PathBuf,
        #[arg(long, default_value_t = 100)]
        top_k: usize,
    },
}

#[derive(Serialize, Deserialize)]
struct Manifest {
    enum_scope: String,
    size: usize,
    task_size: usize,
    allow_min: bool,
    #[serde(default)]
    prefixes: Option<Vec<Vec<usize>>>, // Legacy format
    #[serde(default)]
    tasks: Option<Vec<Vec<Vec<usize>>>>, // New grouped format
}

impl Manifest {
    fn num_tasks(&self) -> usize {
        if let Some(ref t) = self.tasks {
            t.len()
        } else if let Some(ref p) = self.prefixes {
            p.len()
        } else {
            0
        }
    }

    fn task_prefixes(&self, task_id: usize) -> Vec<Vec<usize>> {
        if let Some(ref t) = self.tasks {
            t[task_id].clone()
        } else if let Some(ref p) = self.prefixes {
            vec![p[task_id].clone()]
        } else {
            vec![]
        }
    }
}

#[derive(Serialize, Deserialize)]
struct WorkerResult {
    task_id: usize,
    total: usize,
    holdouts: usize,
    diverged: usize,
    total_steps: u64,
    max_steps_single: u64,
    sim_nanos: u64,
    top_k: Vec<(u64, u64, u64, String)>,
    holdout_entries: Vec<HoldoutEntry>,
    #[serde(default)]
    processing_time_secs: f64,
}

#[derive(Serialize, Deserialize)]
struct HoldoutEntry {
    expr: String,
    steps: u64,
    reason: Option<String>,
}

struct ManifestVisitor {
    current_path: Rc<RefCell<Vec<usize>>>,
    prefixes: Rc<RefCell<Vec<Vec<usize>>>>,
    task_size: usize,
}

impl EnumVisitor for ManifestVisitor {
    fn enter_branch(&mut self, branch_id: usize, remaining_size: usize) -> bool {
        let mut path = self.current_path.borrow_mut();
        path.push(branch_id);
        if remaining_size <= self.task_size {
            self.prefixes.borrow_mut().push(path.clone());
            return false; // prune
        }
        true
    }
    fn exit_branch(&mut self) {
        self.current_path.borrow_mut().pop();
    }
}

struct WorkerVisitor {
    current_path: Vec<usize>,
    assigned_prefix: Vec<usize>,
}

impl EnumVisitor for WorkerVisitor {
    fn enter_branch(&mut self, branch_id: usize, _remaining_size: usize) -> bool {
        self.current_path.push(branch_id);
        let depth = self.current_path.len();
        if depth <= self.assigned_prefix.len() {
            if self.current_path[depth - 1] != self.assigned_prefix[depth - 1] {
                return false;
            }
        }
        true
    }
    fn exit_branch(&mut self) {
        self.current_path.pop();
    }
}

fn main() {
    let cli = Cli::parse();

    match cli.command {
        Commands::Init {
            results_dir,
            enum_scope,
            size,
            task_size,
            num_tasks,
            allow_min,
        } => {
            if !results_dir.exists() {
                fs::create_dir_all(&results_dir).unwrap();
            }

            let opts = PruningOpts::recommended();
            let arity = 0;

            let path_ref = Rc::new(RefCell::new(Vec::new()));
            let prefixes_ref = Rc::new(RefCell::new(Vec::new()));

            let mut visitor = ManifestVisitor {
                current_path: path_ref.clone(),
                prefixes: prefixes_ref.clone(),
                task_size,
            };

            stream_grf_visited(size, arity, allow_min, opts, &mut visitor, &mut |_grf| {
                let path = path_ref.borrow();
                prefixes_ref.borrow_mut().push(path.clone());
            });

            drop(visitor);
            let mut prefixes = Rc::try_unwrap(prefixes_ref).unwrap().into_inner();
            
            let raw_len = prefixes.len();
            let mut rng = rand::rngs::StdRng::seed_from_u64(42);
            prefixes.shuffle(&mut rng);

            let mut tasks = Vec::new();
            if num_tasks > 0 && prefixes.len() > 0 {
                let actual_tasks = std::cmp::min(num_tasks, prefixes.len());
                tasks.resize(actual_tasks, Vec::new());
                for (i, prefix) in prefixes.into_iter().enumerate() {
                    tasks[i % actual_tasks].push(prefix);
                }
            } else {
                // If num_tasks is 0, just put them all in one task?
                tasks.push(prefixes);
            }

            let manifest = Manifest {
                enum_scope: match enum_scope {
                    EnumScope::Prf => "prf".to_string(),
                    EnumScope::MinPrf => "min_prf".to_string(),
                    EnumScope::Grf => "grf".to_string(),
                },
                size,
                task_size,
                allow_min,
                prefixes: None,
                tasks: Some(tasks),
            };

            let out = results_dir.join("manifest.json");
            let f = File::create(&out).unwrap();
            serde_json::to_writer_pretty(f, &manifest).unwrap();
            println!("Wrote manifest to {:?} with {} tasks (from {} raw prefixes)", out, manifest.num_tasks(), raw_len);
        }

        Commands::Worker {
            results_dir,
            task_id,
            all_tasks,
            max_steps,
            batch_size,
            top_k,
        } => {
            let manifest_path = results_dir.join("manifest.json");
            let f = File::open(&manifest_path).expect("Failed to open manifest.json in results dir");
            let m: Manifest = serde_json::from_reader(BufReader::new(f)).unwrap();

            let tasks_to_run: Vec<(usize, PathBuf)> = match task_id {
                Some(id) => {
                    if id >= m.num_tasks() {
                        eprintln!("Task ID {} out of bounds", id);
                        std::process::exit(1);
                    }
                    vec![(id, results_dir.join(format!("task_{}.json", id)))]
                }
                None => {
                    if !all_tasks {
                        eprintln!("Must specify either --task-id or --all-tasks");
                        std::process::exit(1);
                    }
                    let mut tasks = Vec::new();
                    for i in 0..m.num_tasks() {
                        let out_path = results_dir.join(format!("task_{}.json", i));
                        if !out_path.exists() {
                            tasks.push((i, out_path));
                        }
                    }
                    tasks
                }
            };

            let total_tasks = m.num_tasks();
            let mut already_completed = 0;
            for i in 0..total_tasks {
                let out_path = results_dir.join(format!("task_{}.json", i));
                if out_path.exists() {
                    already_completed += 1;
                }
            }

            let completed_tasks = AtomicUsize::new(already_completed);

            if tasks_to_run.is_empty() {
                println!("All {} tasks are already completed.", total_tasks);
                return;
            }
            
            if all_tasks {
                if already_completed > 0 {
                    println!("Resuming: {} tasks already completed, {} remaining.", already_completed, tasks_to_run.len());
                } else {
                    println!("Starting all {} tasks...", total_tasks);
                }
            } else {
                println!("Running single task {}...", tasks_to_run[0].0);
            }

            tasks_to_run.into_par_iter().for_each(|(tid, out_path)| {
                let task_start = std::time::Instant::now();
                let task_prefixes = m.task_prefixes(tid);
                let opts = PruningOpts::recommended();

                let mut acc = Accumulator::new(top_k);
                let mut holdouts_buffer: Vec<u8> = Vec::new();

                for prefix in task_prefixes {
                    let mut visitor = WorkerVisitor {
                        current_path: Vec::new(),
                        assigned_prefix: prefix,
                    };

                    let mut batch = Vec::with_capacity(batch_size);

                    stream_grf_visited(m.size, 0, m.allow_min, opts, &mut visitor, &mut |grf| {
                        batch.push(grf.clone());
                        acc.total += 1;
                        if batch.len() >= batch_size {
                            flush_batch(&mut batch, &mut acc, &mut holdouts_buffer, max_steps, top_k, false);
                        }
                    });
                    if !batch.is_empty() {
                        flush_batch(&mut batch, &mut acc, &mut holdouts_buffer, max_steps, top_k, false);
                    }
                }

                // Parse holdouts back from buffer to struct form
                let mut holdout_entries = Vec::new();
                if !holdouts_buffer.is_empty() {
                    for line in String::from_utf8(holdouts_buffer).unwrap().lines() {
                        let fields: Vec<&str> = line.split('\t').collect();
                        if fields.len() >= 3 {
                            holdout_entries.push(HoldoutEntry {
                                expr: fields[1].to_string(),
                                steps: fields[2].parse().unwrap_or(0),
                                reason: if fields.len() > 5 { Some(fields[5].to_string()) } else { None },
                            });
                        }
                    }
                }

                let result = WorkerResult {
                    task_id: tid,
                    total: acc.total,
                    holdouts: acc.holdouts,
                    diverged: acc.diverged,
                    total_steps: acc.total_steps,
                    max_steps_single: acc.max_steps_single,
                    sim_nanos: acc.sim_nanos,
                    top_k: acc.top_k.entries,
                    holdout_entries,
                    processing_time_secs: task_start.elapsed().as_secs_f64(),
                };

                let out_file = File::create(&out_path).unwrap();
                serde_json::to_writer_pretty(out_file, &result).unwrap();
                
                let completed = completed_tasks.fetch_add(1, Ordering::SeqCst) + 1;
                if acc.total > 0 {
                    println!("Task #{} completed ({}/{}): {} GRFs", tid, completed, total_tasks, acc.total);
                }
            });
        }

        Commands::Summary {
            results_dir,
            top_k,
        } => {
            let manifest_path = results_dir.join("manifest.json");
            let f = File::open(&manifest_path).expect("Failed to open manifest.json in results dir");
            let m: Manifest = serde_json::from_reader(BufReader::new(f)).unwrap();

            let mut combined_acc = Accumulator::new(top_k);
            let mut all_holdouts = Vec::new();
            let mut total_processing_time = 0.0;
            let mut empty_tasks = 0;
            let mut max_task_grfs = 0;
            let mut max_task_time = 0.0f64;

            let mut completed_tasks = 0;

            for i in 0..m.num_tasks() {
                let res_path = results_dir.join(format!("task_{}.json", i));
                if !res_path.exists() {
                    continue;
                }
                completed_tasks += 1;
                let res_file = File::open(res_path).unwrap();
                let res: WorkerResult = serde_json::from_reader(BufReader::new(res_file)).unwrap();

                combined_acc.total += res.total;
                combined_acc.holdouts += res.holdouts;
                combined_acc.diverged += res.diverged;
                combined_acc.total_steps += res.total_steps;
                combined_acc.sim_nanos += res.sim_nanos;
                combined_acc.max_steps_single = combined_acc.max_steps_single.max(res.max_steps_single);
                total_processing_time += res.processing_time_secs;
                
                if res.total == 0 {
                    empty_tasks += 1;
                }
                max_task_grfs = max_task_grfs.max(res.total);
                max_task_time = max_task_time.max(res.processing_time_secs);
                
                for entry in res.top_k {
                    combined_acc.top_k.insert(entry.0, entry.1, entry.2, entry.3);
                }
                all_holdouts.extend(res.holdout_entries);
            }

            let total_tasks = m.num_tasks();
            let non_empty_tasks = completed_tasks - empty_tasks;
            let pct_non_empty = if completed_tasks > 0 {
                (non_empty_tasks as f64 / completed_tasks as f64) * 100.0
            } else {
                0.0
            };

            println!("Summary for manifest {:?}", manifest_path);
            if completed_tasks < total_tasks {
                println!("*** WARNING: PARTIAL RESULTS ({} / {} tasks completed) ***", completed_tasks, total_tasks);
            }
            println!("Total Tasks: {}", completed_tasks);
            println!("  - Non-empty tasks: {} ({:.1}%)", non_empty_tasks, pct_non_empty);
            println!("  - Max GRFs/task: {}", format_num(max_task_grfs as u64));
            println!("  - Max Time/task: {:.0}s", max_task_time);
            println!("Total GRFs generated: {}", format_num(combined_acc.total as u64));
            println!("Total processing time: {:.2} core-hours", total_processing_time / 3600.0);
            println!("Holdouts: {}", format_num(combined_acc.holdouts as u64));
            println!("Diverged: {}", format_num(combined_acc.diverged as u64));
            println!("Total steps: {}", format_num(combined_acc.total_steps));
            println!("Max steps (single): {}", format_num(combined_acc.max_steps_single));

            let alias_db = alias_db_for_stdout(6, false);
            let fmt_alias = |expr: &str| -> String {
                match &alias_db {
                    Some(db) => expr
                        .parse::<Grf>()
                        .map(|g| db.alias(&g))
                        .unwrap_or_else(|_| expr.to_string()),
                    None => expr.to_string(),
                }
            };

            println!("\nTop 10 (out of {} tracked)", combined_acc.top_k.entries.len());
            println!("{:>26}  {:>14}  {}", "Score", "Sim Steps", "Expression");
            for (rank, (score, steps, _base_steps, expr)) in combined_acc.top_k.iter_desc().enumerate() {
                if rank >= 10 {
                    break;
                }
                println!("{:>26}  {:>14}  {}", format_num(*score), format_num(*steps), fmt_alias(expr));
            }

            if completed_tasks == total_tasks {
                let halt_path = results_dir.join("halt.max.grl");
                let mut halt_w = BufWriter::new(std::fs::File::create(&halt_path).expect("failed to create halt.max.grl"));
                io_grl::write_grl_header(&mut halt_w, &format!("BBµ search task: size={}", m.size)).unwrap();
                for (score, steps, base_steps, expr) in combined_acc.top_k.iter_desc() {
                    io_grl::write_grf_entry(&mut halt_w, &GrfEntry {
                        expr: expr.clone(),
                        status: Some(Status::Halt),
                        steps: Some(*steps),
                        base_steps: Some(*base_steps),
                        score: Some(*score),
                        unknown_reason: None,
                    }).unwrap();
                }
                halt_w.flush().unwrap();

                let holdout_path = results_dir.join("holdout.grl");
                let mut holdout_w = BufWriter::new(std::fs::File::create(&holdout_path).expect("failed to create holdout.grl"));
                io_grl::write_grl_header(&mut holdout_w, &format!("BBµ search task holdouts: size={}", m.size)).unwrap();
                for h in all_holdouts {
                    io_grl::write_grf_entry(&mut holdout_w, &GrfEntry {
                        expr: h.expr,
                        status: Some(Status::Unknown),
                        steps: Some(h.steps),
                        base_steps: None,
                        score: None,
                        unknown_reason: h.reason,
                    }).unwrap();
                }
                holdout_w.flush().unwrap();

                let stats_path = results_dir.join("stats.json");
                let mut stats_w = BufWriter::new(std::fs::File::create(&stats_path).expect("failed to create stats.json"));
                let best_json = combined_acc.top_k.best_score().map_or("null".to_string(), |v| v.to_string());
                writeln!(stats_w, "{{").unwrap();
                writeln!(stats_w, "  \"num_total\": {},", combined_acc.total).unwrap();
                writeln!(stats_w, "  \"num_halt\": {},", combined_acc.total - combined_acc.holdouts - combined_acc.diverged).unwrap();
                writeln!(stats_w, "  \"num_diverged\": {},", combined_acc.diverged).unwrap();
                writeln!(stats_w, "  \"num_holdouts\": {},", combined_acc.holdouts).unwrap();
                writeln!(stats_w).unwrap();
                writeln!(stats_w, "  \"max_score\": {},", best_json).unwrap();
                writeln!(stats_w, "  \"max_halt_steps\": {},", combined_acc.max_steps_single).unwrap();
                writeln!(stats_w).unwrap();
                writeln!(stats_w, "  \"total_runtime_s\": {:.3},", total_processing_time).unwrap();
                writeln!(stats_w).unwrap();
                writeln!(stats_w, "  \"num_non_empty_tasks\": {},", non_empty_tasks).unwrap();
                writeln!(stats_w, "  \"max_task_size\": {},", max_task_grfs).unwrap();
                writeln!(stats_w, "  \"max_task_time_s\": {:.3}", max_task_time).unwrap();
                writeln!(stats_w, "}}").unwrap();
                stats_w.flush().unwrap();

                println!("\nFinal files generated:");
                println!("  halt.max.grl: {} entries", combined_acc.top_k.entries.len());
                println!("  holdout.grl:  {} entries", combined_acc.holdouts);
                println!("  stats.json");
            }
        }
    }
}

fn format_num(mut n: u64) -> String {
    if n == 0 {
        return "0".to_string();
    }
    let mut s = String::new();
    let mut count = 0;
    while n > 0 {
        if count == 3 {
            s.insert(0, ',');
            count = 0;
        }
        s.insert(0, (b'0' + (n % 10) as u8) as char);
        n /= 10;
        count += 1;
    }
    s
}
