/// Validate closed_form_of(grf).eval(args) == simulate(grf, args) for all GRFs.
///
/// Usage examples:
///   test_closed_form                                  # infinite mode: arity 1, sizes 1, 2, 3, ...
///   test_closed_form --arity 2                        # infinite mode: arity 2
///   test_closed_form --max-size 10                    # finite mode: arities 0..=2, sizes 1..=10
///   test_closed_form --arity 3 --max-size 7           # finite mode: arity 3 only, sizes 1..=7
///   test_closed_form --grf 'R(Z0, P(2,1))'           # single GRF on standard test inputs
///   test_closed_form --grf 'R(Z0, P(2,1))' 3 5 8     # single GRF on specific args
use std::time::Instant;

use clap::Parser;
use gen_rec::closed_form::closed_form_of;
use gen_rec::enumerate::stream_grf;
use gen_rec::pruning::PruningOpts;
use gen_rec::simulate::{simulate, SimResult};

#[derive(Parser, Debug)]
#[command(about = "Validate closed_form_of against simulate for all GRFs")]
struct Args {
    /// Arity to test.
    /// In infinite mode (no --max-size): defaults to 1.
    /// In finite mode (--max-size given): if omitted, tests arities 0..=2.
    #[arg(long)]
    arity: Option<usize>,

    /// Maximum size (inclusive). If omitted, runs forever with increasing sizes.
    #[arg(long)]
    max_size: Option<usize>,

    /// Maximum simulation steps per input.
    #[arg(long, default_value_t = 1_000_000)]
    max_steps: u64,

    /// Test a single GRF expression instead of enumerating.
    /// With no positional args: tests the standard grid of inputs.
    /// With positional args: tests only those specific argument values.
    #[arg(long)]
    grf: Option<String>,

    /// Argument values for --grf (space-separated u64).
    args: Vec<u64>,
}

fn test_inputs(arity: usize) -> Vec<Vec<u64>> {
    if arity == 0 {
        return vec![vec![]];
    }
    let vals: &[u64] = &[0, 1, 2, 3, 5, 8];
    let mut result: Vec<Vec<u64>> = vec![vec![]];
    for _ in 0..arity {
        let mut next = Vec::new();
        for prefix in &result {
            for &v in vals {
                let mut row = prefix.clone();
                row.push(v);
                next.push(row);
            }
        }
        result = next;
    }
    result
}

fn elapsed_str(start: Instant) -> String {
    let s = start.elapsed().as_secs_f64();
    format!("{:.1}s", s)
}

/// Check one (arity, size). Prints one MISMATCH line per bad GRF.
/// Returns (grfs_checked, grfs_bad).
fn check_size(arity: usize, size: usize, max_steps: u64) -> (usize, usize) {
    let inputs = test_inputs(arity);
    let opts = PruningOpts::default();
    let mut grfs_checked = 0usize;
    let mut grfs_bad = 0usize;

    stream_grf(size, arity, false, opts, &mut |grf| {
        let cf = match closed_form_of(grf) {
            Some(cf) => cf,
            None => return,
        };
        grfs_checked += 1;
        let mut first_bad: Option<(Vec<u64>, Option<u64>, Option<u64>)> = None;
        let mut bad_count = 0usize;
        for args in &inputs {
            let (sim_result, _) = simulate(grf, args, max_steps);
            let sim_val = match sim_result {
                SimResult::Value(v) => Some(v),
                SimResult::Diverge | SimResult::OutOfSteps => None,
                SimResult::ArityMismatch => panic!("arity mismatch for {} on {:?}", grf, args),
                SimResult::ValueOverflow => None,
            };
            let cf_val = cf.eval(args);
            if cf_val != sim_val {
                bad_count += 1;
                if first_bad.is_none() {
                    first_bad = Some((args.clone(), cf_val, sim_val));
                }
            }
        }
        if bad_count > 0 {
            grfs_bad += 1;
            let (bad_args, cf_val, sim_val) = first_bad.unwrap();
            eprintln!(
                "MISMATCH: {}  args={:?}  cf={:?}  sim={:?}  ({}/{} inputs bad)",
                grf, bad_args, cf_val, sim_val, bad_count, inputs.len()
            );
        }
    });

    (grfs_checked, grfs_bad)
}

fn check_one_grf(grf_str: &str, explicit_args: &[u64], max_steps: u64) {
    let grf: gen_rec::grf::Grf = match grf_str.parse() {
        Ok(g) => g,
        Err(e) => { eprintln!("parse error: {e}"); std::process::exit(1); }
    };
    let arity = grf.arity();
    let cf = match closed_form_of(&grf) {
        Some(cf) => cf,
        None => { println!("{grf_str}: closed_form_of returned None"); return; }
    };

    let inputs: Vec<Vec<u64>> = if explicit_args.is_empty() {
        test_inputs(arity)
    } else {
        if explicit_args.len() != arity {
            eprintln!("arity mismatch: GRF has arity {arity} but {} args given", explicit_args.len());
            std::process::exit(1);
        }
        vec![explicit_args.to_vec()]
    };

    let mut bad_count = 0usize;
    let mut first_bad: Option<(Vec<u64>, Option<u64>, Option<u64>)> = None;
    for input in &inputs {
        let (sim_result, _) = simulate(&grf, input, max_steps);
        let sim_val = match sim_result {
            SimResult::Value(v) => Some(v),
            SimResult::Diverge | SimResult::OutOfSteps => None,
            SimResult::ArityMismatch => panic!("arity mismatch for {grf_str} on {input:?}"),
            SimResult::ValueOverflow => None,
        };
        let cf_val = cf.eval(input);
        if cf_val != sim_val {
            bad_count += 1;
            if first_bad.is_none() {
                first_bad = Some((input.clone(), cf_val, sim_val));
            }
        } else {
            println!("ok: {grf_str} args={input:?}  cf={cf_val:?}");
        }
    }
    if bad_count > 0 {
        let (bad_args, cf_val, sim_val) = first_bad.unwrap();
        eprintln!(
            "MISMATCH: {grf_str}  args={bad_args:?}  cf={cf_val:?}  sim={sim_val:?}  ({bad_count}/{} inputs bad)",
            inputs.len()
        );
        std::process::exit(1);
    }
}

fn main() {
    let args = Args::parse();

    if let Some(grf_str) = &args.grf {
        check_one_grf(grf_str, &args.args, args.max_steps);
        return;
    }

    let start = Instant::now();

    match args.max_size {
        None => {
            // Infinite mode: one arity, increasing sizes.
            let arity = args.arity.unwrap_or(1);
            let mut grand_grfs = 0usize;
            println!("Infinite mode: arity {}, sizes 1, 2, 3, ...", arity);
            for size in 1.. {
                let (grfs_checked, grfs_bad) = check_size(arity, size, args.max_steps);
                grand_grfs += grfs_checked;
                if grfs_bad > 0 {
                    eprintln!("  size {:3}: {} bad GRFs  [{}]", size, grfs_bad, elapsed_str(start));
                    std::process::exit(1);
                } else {
                    println!("  size {:3}: {:8} GRFs ok  (total: {})  [{}]",
                        size, grfs_checked, grand_grfs, elapsed_str(start));
                }
            }
        }
        Some(max_size) => {
            // Finite mode: all arities 0..=max_arity (or one specific arity).
            let (arity_lo, arity_hi) = match args.arity {
                Some(a) => (a, a),
                None => (0, 2),
            };
            let mut grand_grfs = 0usize;
            let mut grand_bad = 0usize;
            for arity in arity_lo..=arity_hi {
                println!("arity {}:", arity);
                for size in 1..=max_size {
                    let (grfs_checked, grfs_bad) = check_size(arity, size, args.max_steps);
                    grand_grfs += grfs_checked;
                    grand_bad += grfs_bad;
                    if grfs_bad > 0 {
                        println!("  size {:3}: {:8} GRFs, {} bad  [{}]",
                            size, grfs_checked, grfs_bad, elapsed_str(start));
                    } else {
                        println!("  size {:3}: {:8} GRFs ok  [{}]",
                            size, grfs_checked, elapsed_str(start));
                    }
                }
            }
            if grand_bad > 0 {
                eprintln!("{} bad GRFs out of {} checked (arities {}..={}, sizes 1..={})  [{}]",
                    grand_bad, grand_grfs, arity_lo, arity_hi, max_size, elapsed_str(start));
                std::process::exit(1);
            } else {
                println!("All {} GRFs matched (arities {}..={}, sizes 1..={})  [{}]",
                    grand_grfs, arity_lo, arity_hi, max_size, elapsed_str(start));
            }
        }
    }
}
