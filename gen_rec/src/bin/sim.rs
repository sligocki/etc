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
use gen_rec::io_table::print_sweep_table;
use gen_rec::simulate::{simulate, simulate_min, SimOpts, SimResult};

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
            let step_budget = if args.max_steps == 0 { None } else { Some(args.max_steps) };
            let start = Instant::now();
            let mut last_progress = Instant::now();
            simulate_min(f, &concrete, step_budget, SimOpts::default(), &mut |n, result, total_steps| {
                if last_progress.elapsed() >= Duration::from_secs(5) {
                    let f_val = match result {
                        SimResult::Value(v) => v.to_string(),
                        SimResult::Diverge => "Diverge".to_string(),
                        SimResult::OutOfSteps => "?".to_string(),
                    };
                    eprintln!(
                        "[{}] elapsed={:.1}s  n={}  f(n)={}  steps={}",
                        Local::now().format("%H:%M:%S"),
                        start.elapsed().as_secs_f64(),
                        n,
                        f_val,
                        total_steps,
                    );
                    last_progress = Instant::now();
                }
            })
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

    print_sweep_table(&grf, &template, &sweep_indices, args.max_val, args.max_steps);
}
