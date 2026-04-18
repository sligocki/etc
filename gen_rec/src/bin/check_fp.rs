/// Measure how fingerprint input-set size affects novel-function counts.
///
/// Enumerates GRFs once per arity using the largest requested fp_size, then
/// slices each fingerprint to simulate smaller sizes — avoiding redundant
/// re-enumeration.  A count that stabilises as fp_size grows suggests the
/// input set is large enough to distinguish all distinct functions at that
/// arity/max_size.
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

    /// Max simulation steps per input when computing fingerprints.
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

    // Largest fp_size drives the enumeration; smaller sizes are free slices.
    let max_fp = *args.fp_sizes.iter().max().expect("fp_sizes is non-empty");

    // Current defaults (used to annotate the table).
    let default_fp = |arity: usize| -> usize {
        match arity {
            0 => 1,
            1 => 8,
            _ => 32,
        }
    };

    for &arity in &args.arities {
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

        // Sort and deduplicate fp_sizes for clean output.
        let mut fp_sizes = args.fp_sizes.clone();
        fp_sizes.sort_unstable();
        fp_sizes.dedup();

        // Cap fp_sizes at max_fp (no point asking for more than we computed).
        let fp_sizes: Vec<usize> = fp_sizes.into_iter().filter(|&s| s <= max_fp).collect();

        println!(
            "arity={}  max_size={}  max_steps={}{}  ({} GRFs, {} timed-out)",
            arity,
            args.max_size,
            args.max_steps,
            if args.allow_min { "  allow_min" } else { "" },
            n_total,
            n_timeout,
        );
        println!(" {:>9}  {:>8}  {:>6}", "fp_inputs", "novel", "Δ");
        println!(" {}", "-".repeat(27));

        let def = default_fp(arity);

        // Collect all (fp_size, count) pairs first so we can identify the true
        // stable point in a second pass.
        let counts: Vec<(usize, usize)> = fp_sizes
            .iter()
            .map(|&fp_size| {
                let cap = fp_size.min(inputs.len());
                let distinct: HashSet<&[Option<u64>]> =
                    all_fps.iter().map(|fp| &fp[..cap]).collect();
                (fp_size, distinct.len())
            })
            .collect();

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
