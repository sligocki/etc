/// Validate closed_form_of(grf).eval(args) == simulate(grf, args) for all GRFs.
///
/// Usage examples:
///   test_closed_form                           # infinite mode: arity 1, sizes 1, 2, 3, ...
///   test_closed_form --arity 2                 # infinite mode: arity 2
///   test_closed_form --max-size 10             # finite mode: arities 0..=2, sizes 1..=10
///   test_closed_form --arity 3 --max-size 7    # finite mode: arity 3 only, sizes 1..=7
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

/// Check one (arity, size). Returns (checked, mismatches_found).
fn check_size(arity: usize, size: usize, max_steps: u64) -> (usize, usize) {
    let inputs = test_inputs(arity);
    let opts = PruningOpts::default();
    let mut checked = 0usize;
    let mut mismatches = 0usize;

    stream_grf(size, arity, false, opts, &mut |grf| {
        let cf = match closed_form_of(grf) {
            Some(cf) => cf,
            None => return,
        };
        for args in &inputs {
            let (sim_result, _) = simulate(grf, args, max_steps);
            let sim_val = match sim_result {
                SimResult::Value(v) => Some(v),
                SimResult::Diverge | SimResult::OutOfSteps => None,
                SimResult::ArityMismatch => {
                    panic!("arity mismatch for {} on {:?}", grf, args);
                }
            };
            let cf_val = cf.eval(args);
            checked += 1;
            if cf_val != sim_val {
                mismatches += 1;
                eprintln!(
                    "MISMATCH: {} args={:?}  cf={:?}  sim={:?}",
                    grf, args, cf_val, sim_val
                );
            }
        }
    });

    (checked, mismatches)
}

fn main() {
    let args = Args::parse();

    match args.max_size {
        None => {
            // Infinite mode: one arity, increasing sizes.
            let arity = args.arity.unwrap_or(1);
            let mut grand_checked = 0usize;
            println!("Infinite mode: arity {}, sizes 1, 2, 3, ...", arity);
            for size in 1.. {
                let (checked, mismatches) = check_size(arity, size, args.max_steps);
                grand_checked += checked;
                if mismatches > 0 {
                    eprintln!("  size {}: {} mismatches!", size, mismatches);
                    std::process::exit(1);
                } else {
                    println!("  size {:3}: {:8} pairs ok  (total: {})", size, checked, grand_checked);
                }
            }
        }
        Some(max_size) => {
            // Finite mode: all arities 0..=max_arity (or one specific arity).
            let (arity_lo, arity_hi) = match args.arity {
                Some(a) => (a, a),
                None => (0, 2),
            };
            let mut grand_checked = 0usize;
            let mut grand_mismatches = 0usize;
            for arity in arity_lo..=arity_hi {
                println!("arity {}:", arity);
                for size in 1..=max_size {
                    let (checked, mismatches) = check_size(arity, size, args.max_steps);
                    grand_checked += checked;
                    grand_mismatches += mismatches;
                    if mismatches > 0 {
                        println!("  size {:3}: {} MISMATCHES", size, mismatches);
                    } else {
                        println!("  size {:3}: {:8} pairs ok", size, checked);
                    }
                }
            }
            if grand_mismatches > 0 {
                eprintln!("{} mismatches found ({} pairs checked)", grand_mismatches, grand_checked);
                std::process::exit(1);
            } else {
                println!("All {} pairs matched (arities {}..={}, sizes 1..={}).",
                    grand_checked, arity_lo, arity_hi, max_size);
            }
        }
    }
}
