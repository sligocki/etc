/// Simulate a single GRF expression given on the command line.
///
/// Usage examples:
///   sim "C(S, Z0)"
///   sim "R(P(1,1), C(S, P(3,2)))" 3 2
///   sim "R(P(1,1), C(S, P(3,2)))"           # sweep all args 0..=10
///   sim "R(P(1,1), C(S, P(3,2)))" --max-val 20
///   sim "R(P(1,1), C(S, P(3,2)))" _ 3       # fix x1=3, sweep x0
///   sim --max-steps 1000 "M(S)"
use std::time::{Duration, Instant};

use chrono::Local;
use clap::Parser;
use gen_rec::alias::AliasDb;
use gen_rec::grf::Grf;
use gen_rec::simulate::{simulate, simulate_opts, SimOpts, SimResult};

#[derive(Parser, Debug)]
#[command(about = "Simulate a single GRF expression")]
struct Args {
    /// GRF expression or alias name (Add, AckWorm, Plus[2], ...).
    expr: String,

    /// Input arguments. Use a number to fix that arg, '_' to sweep it.
    /// Omit all to sweep every dimension.
    inputs: Vec<String>,

    /// Maximum simulation steps before giving up (0 = unlimited).
    #[arg(long, default_value_t = 100_000_000)]
    max_steps: u64,

    /// Upper bound (inclusive) for each argument in sweep mode.
    #[arg(long, default_value_t = 10)]
    max_val: u64,
}

/// Evaluate grf with `template` supplying fixed args and `sweep` overriding the wildcard slots.
fn sim_val(grf: &Grf, template: &[Option<u64>], sweep: &[(usize, u64)], max_steps: u64) -> Option<u64> {
    let mut args: Vec<u64> = template.iter().map(|v| v.unwrap_or(0)).collect();
    for &(idx, val) in sweep {
        args[idx] = val;
    }
    simulate(grf, &args, max_steps).0.into_value()
}

fn fmt_result(v: Option<u64>) -> String {
    match v {
        Some(n) => n.to_string(),
        None => "?".to_string(),
    }
}

fn print_table_1d(grf: &Grf, template: &[Option<u64>], sweep_idx: usize, n: u64, max_steps: u64) {
    let axis = format!("x{}", sweep_idx + 1);
    let f_hdr = format!("f(x{})", sweep_idx + 1);
    let vals: Vec<Option<u64>> = (0..=n)
        .map(|v| sim_val(grf, template, &[(sweep_idx, v)], max_steps))
        .collect();
    let val_w = vals.iter().map(|v| fmt_result(*v).len()).max().unwrap_or(1).max(f_hdr.len());
    let n_w = n.to_string().len().max(axis.len());

    println!("{:>n_w$}  |  {:>val_w$}", axis, f_hdr);
    println!("{}--+--{}", "-".repeat(n_w), "-".repeat(val_w));
    for (a, v) in vals.iter().enumerate() {
        println!("{:>n_w$}  |  {:>val_w$}", a, fmt_result(*v));
    }
}

fn print_table_2d(grf: &Grf, template: &[Option<u64>], row_idx: usize, col_idx: usize, n: u64, max_steps: u64) {
    let vals: Vec<Vec<Option<u64>>> = (0..=n)
        .map(|a| (0..=n)
            .map(|b| sim_val(grf, template, &[(row_idx, a), (col_idx, b)], max_steps))
            .collect())
        .collect();

    let cell_w = vals.iter().flatten()
        .map(|v| fmt_result(*v).len())
        .chain((0..=n).map(|b| b.to_string().len()))
        .max().unwrap_or(1);

    let row_label = format!("x{}↓", row_idx + 1);
    let row_w = n.to_string().len().max(row_label.chars().count());

    let header: String = (0..=n).map(|b| format!("{:>cell_w$}", b)).collect::<Vec<_>>().join("  ");
    let pad = " ".repeat(row_w);
    println!("{}  |  x{} →", pad, col_idx + 1);
    let corner_pad = " ".repeat(row_w - row_label.chars().count());
    println!("{}{}  |  {}", corner_pad, row_label, header);
    println!("{}--+--{}", "-".repeat(row_w), "-".repeat(header.len()));

    for (a, row) in vals.iter().enumerate() {
        let cells: String = row.iter()
            .map(|v| format!("{:>cell_w$}", fmt_result(*v)))
            .collect::<Vec<_>>().join("  ");
        println!("{:>row_w$}  |  {}", a, cells);
    }
}

fn print_table_nd(grf: &Grf, template: &[Option<u64>], sweep_indices: &[usize], n: u64, max_steps: u64) {
    let sc = sweep_indices.len();
    let count = (n + 1).pow(sc as u32);
    let mut all_sweep_vals: Vec<Vec<u64>> = Vec::with_capacity(count as usize);
    let mut tuple = vec![0u64; sc];
    loop {
        all_sweep_vals.push(tuple.clone());
        let mut pos = sc - 1;
        loop {
            tuple[pos] += 1;
            if tuple[pos] <= n { break; }
            tuple[pos] = 0;
            if pos == 0 { break; }
            pos -= 1;
        }
        if tuple.iter().all(|&x| x == 0) { break; }
    }

    let results: Vec<Option<u64>> = all_sweep_vals.iter()
        .map(|sv| {
            let sweep: Vec<(usize, u64)> = sweep_indices.iter().copied().zip(sv.iter().copied()).collect();
            sim_val(grf, template, &sweep, max_steps)
        })
        .collect();

    let arg_w = n.to_string().len().max(2);
    let val_w = results.iter().map(|v| fmt_result(*v).len()).max().unwrap_or(1).max(6);

    let arg_headers: String = sweep_indices.iter()
        .map(|i| format!("{:>arg_w$}", format!("x{}", i + 1)))
        .collect::<Vec<_>>().join("  ");
    println!("{}  |  {:>val_w$}", arg_headers, "result");
    println!("{}--+--{}", "-".repeat(arg_w * sc + 2 * (sc - 1)), "-".repeat(val_w));

    for (sv, v) in all_sweep_vals.iter().zip(results.iter()) {
        let args_str: String = sv.iter().map(|x| format!("{:>arg_w$}", x)).collect::<Vec<_>>().join("  ");
        println!("{}  |  {:>val_w$}", args_str, fmt_result(*v));
    }
}

/// Run `M(f)(outer_args)` with periodic stderr progress lines.
///
/// Mirrors the minimization logic in `simulate_opts` but prints a status line
/// to stderr every `progress_interval` showing the current search index, f's
/// value at that index, the wall-clock time, and elapsed time.
fn run_min_with_progress(
    f: &Grf,
    outer_args: &[u64],
    max_steps: u64,
    progress_interval: Duration,
) -> (SimResult, u64) {
    let step_budget: Option<u64> = if max_steps == 0 { None } else { Some(max_steps) };
    let mut total_steps: u64 = 1; // cost of the Min node itself

    if f.is_never_zero() {
        return (SimResult::Diverge, total_steps);
    }

    // If f ignores its search variable (arg 1), one evaluation decides.
    if !f.used_args().contains(&1) {
        let mut f_args: Vec<u64> = Vec::with_capacity(outer_args.len() + 1);
        f_args.push(0);
        f_args.extend_from_slice(outer_args);
        let (result, s) = simulate_opts(f, &f_args, step_budget, SimOpts::default());
        total_steps += s;
        return match result {
            SimResult::Value(0) => (SimResult::Value(0), total_steps),
            SimResult::Value(_) => (SimResult::Diverge, total_steps),
            other => (other, total_steps),
        };
    }

    let start = Instant::now();
    let mut last_progress = Instant::now();
    let mut i: u64 = 0;

    loop {
        let remaining = step_budget.map(|b| b.saturating_sub(total_steps));
        if remaining == Some(0) {
            return (SimResult::OutOfSteps, total_steps);
        }

        let mut f_args: Vec<u64> = Vec::with_capacity(outer_args.len() + 1);
        f_args.push(i);
        f_args.extend_from_slice(outer_args);

        let (result, s) = simulate_opts(f, &f_args, remaining, SimOpts::default());
        total_steps += s;

        if last_progress.elapsed() >= progress_interval {
            let f_val = match &result {
                SimResult::Value(v) => v.to_string(),
                SimResult::Diverge => "Diverge".to_string(),
                SimResult::OutOfSteps => "?".to_string(),
            };
            eprintln!(
                "[{}] elapsed={:.1}s  n={}  f(n)={}",
                Local::now().format("%H:%M:%S"),
                start.elapsed().as_secs_f64(),
                i,
                f_val,
            );
            last_progress = Instant::now();
        }

        match result {
            SimResult::Value(0) => return (SimResult::Value(i), total_steps),
            SimResult::Value(_) => i += 1,
            other => return (other, total_steps),
        }
    }
}

fn main() {
    let args = Args::parse();

    let grf = match AliasDb::default().resolve(&args.expr) {
        Ok(g) => g,
        Err(e) => {
            eprintln!("error: {e}");
            std::process::exit(1);
        }
    };

    let arity = grf.arity();

    // Parse inputs: numbers or "_" wildcards.
    let parsed: Vec<Option<u64>> = args.inputs.iter().map(|s| {
        if s == "_" {
            None
        } else {
            match s.parse::<u64>() {
                Ok(v) => Some(v),
                Err(_) => {
                    eprintln!("error: invalid input '{}' (expected a number or '_')", s);
                    std::process::exit(1);
                }
            }
        }
    }).collect();

    // No args given with arity > 0 → full sweep.
    let template: Vec<Option<u64>> = if parsed.is_empty() && arity > 0 {
        vec![None; arity]
    } else {
        parsed
    };

    if template.len() != arity {
        eprintln!(
            "Arity mismatch: `{}` expects {} input{}, got {}",
            grf,
            arity,
            if arity == 1 { "" } else { "s" },
            template.len()
        );
        std::process::exit(1);
    }

    let sweep_indices: Vec<usize> = template.iter().enumerate()
        .filter(|(_, v)| v.is_none())
        .map(|(i, _)| i)
        .collect();

    // Single-run mode: arity 0, or all args concrete.
    if sweep_indices.is_empty() {
        let concrete: Vec<u64> = template.iter().map(|v| v.unwrap()).collect();
        println!("expr  : {}", grf);
        println!("arity : {}", arity);
        println!("size  : {}", grf.size());
        if !concrete.is_empty() {
            let input_str: Vec<String> = concrete.iter().map(|x| x.to_string()).collect();
            println!("inputs: {}", input_str.join(", "));
        }
        println!("---");
        let (result, steps) = if let Grf::Min(f) = &grf {
            run_min_with_progress(f, &concrete, args.max_steps, Duration::from_secs(5))
        } else {
            simulate(&grf, &concrete, args.max_steps)
        };
        match result {
            SimResult::Value(v) => println!("result: {}  ({} steps)", v, steps),
            SimResult::Diverge => println!("result: diverges  ({} steps)", steps),
            SimResult::OutOfSteps => {
                let limit = if args.max_steps == 0 { "unlimited".to_string() } else { args.max_steps.to_string() };
                println!("result: timed out after {} steps (limit: {})", steps, limit);
            }
        }
        return;
    }

    // Sweep mode.
    println!("expr  : {}", grf);
    println!("arity : {}", arity);
    println!("size  : {}", grf.size());
    let sweep_str: Vec<String> = sweep_indices.iter()
        .map(|i| format!("x{}=0..={}", i + 1, args.max_val))
        .collect();
    let fixed_str: Vec<String> = template.iter().enumerate()
        .filter(|(_, v)| v.is_some())
        .map(|(i, v)| format!("x{}={}", i + 1, v.unwrap()))
        .collect();
    if fixed_str.is_empty() {
        println!("sweep : {}", sweep_str.join(", "));
    } else {
        println!("sweep : {}  (fixed: {})", sweep_str.join(", "), fixed_str.join(", "));
    }
    println!("---");

    match sweep_indices.len() {
        1 => print_table_1d(&grf, &template, sweep_indices[0], args.max_val, args.max_steps),
        2 => print_table_2d(&grf, &template, sweep_indices[0], sweep_indices[1], args.max_val, args.max_steps),
        _ => print_table_nd(&grf, &template, &sweep_indices, args.max_val, args.max_steps),
    }
}
