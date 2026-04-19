/// Measure how fingerprint input-set size affects novel-function counts.
///
/// Enumerates GRFs once per arity per fp_size, fingerprints each GRF on the
/// canonical input set for that fp_size, and counts distinct fingerprints.
/// A count that stabilises as fp_size grows suggests the input set is large
/// enough to distinguish all distinct functions at that arity/max_size.
///
/// Usage examples:
///   check_fp                                      # arity 1, sizes 1..=8
///   check_fp --arities 1,2,3 --max-size 10
///   check_fp --arities 1,2 --max-size 12 --allow-min
///   check_fp --fp-sizes 1,2,4,8,16,32,64,128,256
use clap::Parser;
use gen_rec::enumerate::stream_grf;
use gen_rec::fingerprint::{canonical_inputs_n, compute_fp, fp_is_complete};
use gen_rec::pruning::PruningOpts;
use std::collections::HashSet;

#[derive(Parser, Debug)]
#[command(
    about = "Measure novel-function counts at varying fingerprint input-set sizes",
    long_about = "Enumerates GRFs and counts how many distinct functions are found\n\
                  under fingerprint input sets of different sizes.  As fp_size\n\
                  increases, previously-collapsed distinct functions are separated\n\
                  and the count rises.  Stabilisation indicates the input set is\n\
                  large enough."
)]
struct Args {
    /// Arities to check (comma-separated).
    #[arg(long, value_delimiter = ',', default_values = ["1", "2", "3"])]
    arities: Vec<usize>,

    /// Enumerate GRFs up to this size (inclusive).
    #[arg(long, default_value_t = 8)]
    max_size: usize,

    /// Max simulation steps per input when computing fingerprints (0 = unlimited).
    #[arg(long, default_value_t = 10_000)]
    max_steps: u64,

    /// Include the Minimization combinator.
    #[arg(long)]
    allow_min: bool,

    /// Fingerprint input-set sizes to test (comma-separated).
    #[arg(long, value_delimiter = ',',
          default_values = ["1", "2", "4", "8", "16", "32", "64", "128"])]
    fp_sizes: Vec<usize>,
}

fn main() {
    let args = Args::parse();
    let opts = PruningOpts::default();

    // Current defaults (used to annotate the table).
    let default_fp = |arity: usize| -> usize {
        match arity {
            0 => 1,
            1 => 8,
            _ => 32,
        }
    };

    for &arity in &args.arities {
        // Sort and deduplicate fp_sizes for clean output.
        let mut fp_sizes = args.fp_sizes.clone();
        fp_sizes.sort_unstable();
        fp_sizes.dedup();

        let max_fp = *fp_sizes.last().expect("fp_sizes is non-empty");

        // Generate a single input set at max_fp.  Smaller fp_sizes are prefixes of
        // this set, preserving the monotonicity property: adding more inputs can only
        // split previously-merged equivalence classes, never merge them.
        let inputs = canonical_inputs_n(arity, max_fp);

        // Enumerate once, collect all complete fingerprints at max_fp size.
        let mut all_fps: Vec<Vec<Option<u64>>> = Vec::new();
        let mut n_total = 0usize;
        let mut n_timeout = 0usize;

        for size in 1..=args.max_size {
            stream_grf(size, arity, args.allow_min, opts, &mut |grf| {
                n_total += 1;
                let fp = compute_fp(grf, &inputs, args.max_steps);
                if fp_is_complete(&fp) {
                    all_fps.push(fp);
                } else {
                    n_timeout += 1;
                }
            });
        }

        let steps_label = if args.max_steps == 0 {
            "unlimited".to_string()
        } else {
            args.max_steps.to_string()
        };

        // Collect all (fp_size, count) pairs by slicing each fp to [:fp_size].
        // Because all fp_sizes use prefixes of the same input set, counts are
        // monotonically non-decreasing — a necessary condition for stability detection.
        let counts: Vec<(usize, usize)> = fp_sizes
            .iter()
            .map(|&fp_size| {
                let cap = fp_size.min(inputs.len());
                let distinct: HashSet<&[Option<u64>]> =
                    all_fps.iter().map(|fp| &fp[..cap]).collect();
                (fp_size, distinct.len())
            })
            .collect();

        println!(
            "arity={}  max_size={}  max_steps={}{}  ({} GRFs, {} timed-out)",
            arity,
            args.max_size,
            steps_label,
            if args.allow_min { "  allow_min" } else { "" },
            n_total,
            n_timeout,
        );
        println!(" {:>9}  {:>8}  {:>6}", "fp_inputs", "novel", "Δ");
        println!(" {}", "-".repeat(27));

        let def = default_fp(arity);

        // The count is monotonically non-decreasing (more inputs can only split
        // previously-merged functions).  "Stable" = first row that reaches the
        // maximum count AND all subsequent rows stay at that count.
        // Equivalently: first row whose count equals the last row's count.
        let max_count = counts.last().map(|(_, c)| *c).unwrap_or(0);
        let stable_at: Option<usize> = counts
            .iter()
            .find(|(_, c)| *c == max_count)
            .map(|(fp, _)| *fp);

        let mut prev_count: Option<usize> = None;
        for &(fp_size, count) in &counts {
            let delta_str = match prev_count {
                None => "   ---".to_string(),
                Some(p) if count == p => "     0".to_string(),
                Some(p) => format!(" {:>+5}", count as i64 - p as i64),
            };

            let mut annotations: Vec<&str> = Vec::new();
            if fp_size == def { annotations.push("← default"); }
            if stable_at == Some(fp_size) { annotations.push("✓ stable"); }

            let ann = if annotations.is_empty() {
                String::new()
            } else {
                format!("  {}", annotations.join("  "))
            };

            println!(" {:>9}  {:>8}  {}{}", fp_size, count, delta_str, ann);
            prev_count = Some(count);
        }
        println!();
    }
}
