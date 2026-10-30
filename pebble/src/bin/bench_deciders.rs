use pebble::deciders::{
    decide_bouncer, decide_ctl, decide_cycler, decide_edge_glider, decide_multi_bouncer,
    decide_separated_components, decide_static_backtrack,
};
use pebble::enumeration::TnfEnumerator;
use pebble::io::read_records_from_file;
use pebble::program::Program;
use pebble::simulation::{simulate_with_edge_glider, Simulator};
use rayon::prelude::*;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::path::PathBuf;
use std::process;
use std::time::{Duration, Instant};

use clap::Parser;

#[derive(Parser, Debug)]
#[command(
    name = "bench_deciders",
    about = "Benchmark individual deciders on a list of programs to evaluate runtime, deciding rate, cost efficiency, and optimal pipeline ordering.",
    version
)]
struct Cli {
    /// Optional path to file containing program records or short codes
    #[arg(value_name = "INFILE")]
    infile: Option<PathBuf>,

    /// Path to input file of programs (overrides positional)
    #[arg(short = 'i', long, visible_alias = "infile")]
    input: Option<PathBuf>,

    /// Base max_steps for deciders and simulation
    #[arg(short = 's', long = "steps", default_value_t = 100)]
    steps: u64,

    /// Limit benchmark to first <LIMIT> programs from file
    #[arg(short = 'n', long = "limit")]
    limit: Option<usize>,

    /// Generate a sample of [COUNT] TNF programs of <SIZE> if no file (e.g. --sample 5 or --sample 5 1000)
    #[arg(long = "sample", num_args = 1..=2, value_names = ["SIZE", "COUNT"])]
    sample: Option<Vec<usize>>,

    /// Number of worker threads (default: all cores)
    #[arg(short = 'j', long = "threads")]
    threads: Option<usize>,

    /// Include extended parameter variants (e.g. 200 steps)
    #[arg(long = "extended")]
    extended: bool,
}

fn run_simulation(p: &Program, steps: u64) -> bool {
    let mut sim = Simulator::new(p.size());
    sim.run(p, steps).is_halted()
}

fn run_sim_with_edge_glider(p: &Program, steps: u64) -> bool {
    let outcome = simulate_with_edge_glider(p, steps);
    outcome.is_halted() || outcome.is_decided_non_halting()
}

fn run_static_backtrack(p: &Program, _steps: u64) -> bool {
    decide_static_backtrack(p).is_some()
}

fn run_edge_glider(p: &Program, steps: u64) -> bool {
    decide_edge_glider(p, steps).is_some()
}

fn run_cycler(p: &Program, steps: u64) -> bool {
    decide_cycler(p, steps).is_some()
}

fn run_separated_components(p: &Program, steps: u64) -> bool {
    decide_separated_components(p, steps).is_some()
}

fn run_bouncer(p: &Program, steps: u64) -> bool {
    decide_bouncer(p, steps).is_some()
}

fn run_multi_bouncer(p: &Program, steps: u64) -> bool {
    decide_multi_bouncer(p, steps).is_some()
}

fn run_ctl(p: &Program, steps: u64) -> bool {
    decide_ctl(p, steps).is_some()
}

#[derive(Clone)]
struct DeciderDef {
    name: String,
    steps: u64,
    func: fn(&Program, u64) -> bool,
}

#[derive(Clone)]
struct DeciderBenchResult {
    name: String,
    decided_count: usize,
    decided_pct: f64,
    total_time: Duration,
    avg_time_per_prog: Duration,
    avg_time_per_decided: Option<Duration>,
    throughput: f64,
    decided_mask: Vec<bool>,
}

fn format_duration(d: Duration) -> String {
    let nanos = d.as_nanos();
    if nanos < 1_000 {
        format!("{nanos} ns")
    } else if nanos < 1_000_000 {
        format!("{:.2} µs", nanos as f64 / 1_000.0)
    } else if nanos < 1_000_000_000 {
        format!("{:.2} ms", nanos as f64 / 1_000_000.0)
    } else {
        format!("{:.3} s", d.as_secs_f64())
    }
}

fn load_programs_from_file(path: &PathBuf, limit: Option<usize>) -> Result<Vec<Program>, String> {
    if let Ok(records) = read_records_from_file(path) {
        if !records.is_empty() {
            let mut progs: Vec<Program> = records.into_iter().map(|r| r.program).collect();
            if let Some(lim) = limit {
                progs.truncate(lim);
            }
            return Ok(progs);
        }
    }

    let file = File::open(path).map_err(|e| format!("cannot open file '{}': {e}", path.display()))?;
    let reader = BufReader::new(file);
    let mut progs = Vec::new();

    for line_res in reader.lines() {
        let line = line_res.map_err(|e| format!("read error: {e}"))?;
        let s = line.trim();
        if s.is_empty() || s.starts_with('#') {
            continue;
        }
        let code = s.split_whitespace().next().unwrap_or("");
        if let Ok(p) = code.parse::<Program>() {
            progs.push(p);
            if let Some(lim) = limit {
                if progs.len() >= lim {
                    break;
                }
            }
        }
    }

    if progs.is_empty() {
        return Err(format!("no valid programs found in '{}'", path.display()));
    }
    Ok(progs)
}

fn main() {
    let cli = Cli::parse();

    let input_path = cli.input.or(cli.infile);
    let max_steps = cli.steps;
    let limit = cli.limit;
    let (sample_size, sample_count) = match cli.sample {
        Some(s) => {
            let size = s[0];
            let count = if s.len() > 1 { s[1] } else { 1000 };
            (Some(size), count)
        }
        None => (None, 1000),
    };
    let num_threads = cli.threads;
    let extended = cli.extended;

    if let Some(threads) = num_threads {
        if let Err(err) = rayon::ThreadPoolBuilder::new()
            .num_threads(threads)
            .build_global()
        {
            eprintln!("Error configuring Rayon thread pool: {err}");
            process::exit(1);
        }
    }

    let programs = if let Some(ref path) = input_path {
        match load_programs_from_file(path, limit) {
            Ok(p) => p,
            Err(e) => {
                eprintln!("Error: {e}");
                process::exit(1);
            }
        }
    } else if let Some(size) = sample_size {
        println!("Generating sample of {sample_count} programs of size {size}...");
        let mut sample = Vec::with_capacity(sample_count);
        for entry in TnfEnumerator::new(size, max_steps, max_steps) {
            sample.push(entry.program);
            if sample.len() >= sample_count {
                break;
            }
        }
        sample
    } else {
        eprintln!("Error: please provide an input file or use --sample <SIZE> [COUNT]");
        process::exit(1);
    };

    let num_programs = programs.len();
    if num_programs == 0 {
        eprintln!("Error: 0 programs loaded");
        process::exit(1);
    }

    println!("=== Pebble Automaton Decider Benchmarking Suite ===");
    println!("Benchmark dataset:  {} programs", num_programs);
    println!("Base step limit:    {} steps", max_steps);
    println!("Worker threads:     {}", rayon::current_num_threads());
    println!();

    let mut candidate_defs: Vec<DeciderDef> = vec![
        DeciderDef {
            name: "StaticBacktrack".to_string(),
            steps: 0,
            func: run_static_backtrack,
        },
        DeciderDef {
            name: format!("SimWithEdgeGlider({max_steps})"),
            steps: max_steps,
            func: run_sim_with_edge_glider,
        },
        DeciderDef {
            name: format!("Simulation({max_steps})"),
            steps: max_steps,
            func: run_simulation,
        },
        DeciderDef {
            name: format!("EdgeGlider({max_steps})"),
            steps: max_steps,
            func: run_edge_glider,
        },
        DeciderDef {
            name: format!("Cycler({max_steps})"),
            steps: max_steps,
            func: run_cycler,
        },
        DeciderDef {
            name: format!("SeparatedComponents({max_steps})"),
            steps: max_steps,
            func: run_separated_components,
        },
        DeciderDef {
            name: format!("Bouncer({max_steps})"),
            steps: max_steps,
            func: run_bouncer,
        },
        DeciderDef {
            name: format!("MultiBouncer({max_steps})"),
            steps: max_steps,
            func: run_multi_bouncer,
        },
        DeciderDef {
            name: format!("CTL({max_steps})"),
            steps: max_steps,
            func: run_ctl,
        },
    ];

    if extended {
        let ext_steps = max_steps.max(200);
        candidate_defs.push(DeciderDef {
            name: format!("SimWithEdgeGlider({ext_steps})"),
            steps: ext_steps,
            func: run_sim_with_edge_glider,
        });
        candidate_defs.push(DeciderDef {
            name: format!("Simulation({ext_steps})"),
            steps: ext_steps,
            func: run_simulation,
        });
        candidate_defs.push(DeciderDef {
            name: format!("Cycler({ext_steps})"),
            steps: ext_steps,
            func: run_cycler,
        });
        candidate_defs.push(DeciderDef {
            name: format!("SeparatedComponents({ext_steps})"),
            steps: ext_steps,
            func: run_separated_components,
        });
        candidate_defs.push(DeciderDef {
            name: format!("Bouncer({ext_steps})"),
            steps: ext_steps,
            func: run_bouncer,
        });
        candidate_defs.push(DeciderDef {
            name: format!("MultiBouncer({ext_steps})"),
            steps: ext_steps,
            func: run_multi_bouncer,
        });
        candidate_defs.push(DeciderDef {
            name: format!("CTL({ext_steps})"),
            steps: ext_steps,
            func: run_ctl,
        });
    }

    println!("Running isolated benchmarks for each decider across all {num_programs} programs...");
    let mut results: Vec<DeciderBenchResult> = Vec::with_capacity(candidate_defs.len());

    for def in &candidate_defs {
        let start = Instant::now();
        let mask: Vec<bool> = programs
            .par_iter()
            .map(|p| (def.func)(p, def.steps))
            .collect();
        let total_time = start.elapsed();

        let decided_count = mask.iter().filter(|&&b| b).count();
        let decided_pct = (decided_count as f64 / num_programs as f64) * 100.0;
        let avg_time_per_prog = total_time / (num_programs as u32);
        let avg_time_per_decided = if decided_count > 0 {
            Some(total_time / (decided_count as u32))
        } else {
            None
        };
        let throughput = if total_time.as_secs_f64() > 0.0 {
            num_programs as f64 / total_time.as_secs_f64()
        } else {
            num_programs as f64
        };

        results.push(DeciderBenchResult {
            name: def.name.clone(),
            decided_count,
            decided_pct,
            total_time,
            avg_time_per_prog,
            avg_time_per_decided,
            throughput,
            decided_mask: mask,
        });
    }

    println!();
    println!("=== Standalone Decider Performance (Sorted by Avg Time / Decided Program) ===");
    println!(
        "{:<28} | {:>8} ({:>6}) | {:>10} | {:>12} | {:>14} | {:>14}",
        "Decider", "Decided", "Rate", "Total Time", "Avg / Prog", "Avg / Decided", "Throughput"
    );
    println!("{:-<28}-|-{:-<8}---------|-{:-<10}-|-{:-<12}-|-{:-<14}-|-{:-<14}", "", "", "", "", "", "");

    let mut sorted_by_efficiency = results.clone();
    sorted_by_efficiency.sort_by(|a, b| {
        let a_cost = a.avg_time_per_decided.unwrap_or(Duration::from_secs(86400 * 365));
        let b_cost = b.avg_time_per_decided.unwrap_or(Duration::from_secs(86400 * 365));
        a_cost.cmp(&b_cost)
    });

    for r in &sorted_by_efficiency {
        let avg_decided_str = r
            .avg_time_per_decided
            .map(format_duration)
            .unwrap_or_else(|| "N/A (0)".to_string());
        println!(
            "{:<28} | {:>8} ({:>5.1}%) | {:>10} | {:>12} | {:>14} | {:>11.0} p/s",
            r.name,
            r.decided_count,
            r.decided_pct,
            format_duration(r.total_time),
            format_duration(r.avg_time_per_prog),
            avg_decided_str,
            r.throughput
        );
    }

    println!();
    println!("=== Greedy Optimal Pipeline Ordering Simulation ===");
    println!("Iteratively selecting the decider with lowest cost per newly decided program on the remaining set:");
    println!();
    println!(
        "{:<5} | {:<28} | {:>8} | {:>9} | {:>12} | {:>12}",
        "Stage", "Decider", "Decided", "Remaining", "Stage Time", "Cumul Time"
    );
    println!("{:-<5}-|-{:-<28}-|-{:-<8}-|-{:-<9}-|-{:-<12}-|-{:-<12}", "", "", "", "", "", "");

    let mut undecided: Vec<bool> = vec![true; num_programs];
    let mut used_deciders: Vec<bool> = vec![false; results.len()];
    let mut stage_num = 1;
    let mut cumul_time = Duration::ZERO;
    let mut remaining_count = num_programs;

    while remaining_count > 0 {
        let mut best_idx: Option<usize> = None;
        let mut best_cost_per_decision = f64::INFINITY;
        let mut best_newly_decided = 0;

        for (idx, r) in results.iter().enumerate() {
            if used_deciders[idx] {
                continue;
            }
            let newly_decided = (0..num_programs)
                .filter(|&i| undecided[i] && r.decided_mask[i])
                .count();
            if newly_decided == 0 {
                continue;
            }
            let stage_time_secs = r.avg_time_per_prog.as_secs_f64() * remaining_count as f64;
            let cost_per_decision = stage_time_secs / newly_decided as f64;

            if cost_per_decision < best_cost_per_decision {
                best_cost_per_decision = cost_per_decision;
                best_idx = Some(idx);
                best_newly_decided = newly_decided;
            }
        }

        let Some(best) = best_idx else {
            break;
        };

        used_deciders[best] = true;
        let stage_time = Duration::from_secs_f64(
            results[best].avg_time_per_prog.as_secs_f64() * remaining_count as f64,
        );
        cumul_time += stage_time;
        remaining_count -= best_newly_decided;

        for i in 0..num_programs {
            if undecided[i] && results[best].decided_mask[i] {
                undecided[i] = false;
            }
        }

        println!(
            "{:<5} | {:<28} | {:>8} | {:>9} | {:>12} | {:>12}",
            format!("#{stage_num}"),
            results[best].name,
            format!("+{best_newly_decided}"),
            remaining_count,
            format_duration(stage_time),
            format_duration(cumul_time)
        );

        stage_num += 1;
    }

    if remaining_count > 0 {
        println!(
            "{:<5} | {:<28} | {:>8} | {:>9} | {:>12} | {:>12}",
            "End", "(Undecided Holdouts)", "-", remaining_count, "-", format_duration(cumul_time)
        );
    }
}
