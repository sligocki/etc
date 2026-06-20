use clap::{Parser, Subcommand};
use gen_rec::enumerate::{stream_grf_visited, EnumScope, EnumVisitor};
use gen_rec::pruning::PruningOpts;
use gen_rec::search_util::{flush_batch, Accumulator, fmt_si};
use serde::{Deserialize, Serialize};
use std::cell::RefCell;
use std::fs::{self, File};
use std::io::BufReader;
use std::path::PathBuf;
use std::rc::Rc;

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
        #[arg(long, default_value_t = 6)]
        task_size: usize,
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
    prefixes: Vec<Vec<usize>>,
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
            let prefixes = Rc::try_unwrap(prefixes_ref).unwrap().into_inner();
            let manifest = Manifest {
                enum_scope: match enum_scope {
                    EnumScope::Prf => "prf".to_string(),
                    EnumScope::MinPrf => "min_prf".to_string(),
                    EnumScope::Grf => "grf".to_string(),
                },
                size,
                task_size,
                allow_min,
                prefixes,
            };

            let out = results_dir.join("manifest.json");
            let f = File::create(&out).unwrap();
            serde_json::to_writer_pretty(f, &manifest).unwrap();
            println!("Wrote manifest to {:?} with {} tasks", out, manifest.prefixes.len());
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
                    if id >= m.prefixes.len() {
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
                    for i in 0..m.prefixes.len() {
                        let out_path = results_dir.join(format!("task_{}.json", i));
                        if !out_path.exists() {
                            tasks.push((i, out_path));
                        }
                    }
                    tasks
                }
            };

            for (tid, out_path) in tasks_to_run {
                println!("Running task {}/{}...", tid, m.prefixes.len());
                let task_start = std::time::Instant::now();
                let prefix = m.prefixes[tid].clone();
                let opts = PruningOpts::recommended();
                let mut visitor = WorkerVisitor {
                    current_path: Vec::new(),
                    assigned_prefix: prefix,
                };

                let mut acc = Accumulator::new(top_k);
                let mut batch = Vec::with_capacity(batch_size);

                // In worker, holdouts are temporarily kept in memory or a scratch file.
                // To keep it simple and independent, we'll collect them in memory,
                // then write them into the WorkerResult struct.
                let mut holdouts_buffer: Vec<u8> = Vec::new();

                stream_grf_visited(m.size, 0, m.allow_min, opts, &mut visitor, &mut |grf| {
                    batch.push(grf.clone());
                    acc.total += 1;
                    if batch.len() >= batch_size {
                        flush_batch(&mut batch, &mut acc, &mut holdouts_buffer, max_steps, top_k);
                    }
                });
                if !batch.is_empty() {
                    flush_batch(&mut batch, &mut acc, &mut holdouts_buffer, max_steps, top_k);
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
                println!("Task {} completed. Generated {} GRFs.", tid, acc.total);
            }
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

            for i in 0..m.prefixes.len() {
                let res_path = results_dir.join(format!("task_{}.json", i));
                if !res_path.exists() {
                    eprintln!("Missing result for task {} at {:?}", i, res_path);
                    std::process::exit(1);
                }
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

            let total_tasks = m.prefixes.len();
            let pct_empty = if total_tasks > 0 {
                (empty_tasks as f64 / total_tasks as f64) * 100.0
            } else {
                0.0
            };

            println!("Summary for manifest {:?}", manifest_path);
            println!("Total Tasks: {}", total_tasks);
            println!("  - Empty Tasks: {} ({:.1}%)", empty_tasks, pct_empty);
            println!("  - Max GRFs/task: {}", max_task_grfs);
            println!("  - Max Time/task: {:.2}s", max_task_time);
            println!("Total GRFs generated: {}", combined_acc.total);
            println!("Total processing time: {:.2}s", total_processing_time);
            println!("Holdouts: {}", combined_acc.holdouts);
            println!("Diverged: {}", combined_acc.diverged);
            println!("Total steps: {}", combined_acc.total_steps);
            println!("Max steps (single): {}", combined_acc.max_steps_single);

            println!("\nTop {}", top_k);
            for (score, steps, base_steps, expr) in combined_acc.top_k.iter_desc() {
                println!("{:>10} {:>10} {:>10} {}", score, steps, base_steps, expr);
            }
        }
    }
}
