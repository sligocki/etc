/// List the smallest non-redundant GRF for each distinct function of a given arity.
///
/// A GRF is non-redundant if no smaller GRF computes the same function on all inputs.
/// Two GRFs are considered equivalent when they agree on a canonical input set (same
/// outputs including divergence).
///
/// Usage examples:
///   non_redundant          # arity 1, sizes 1..=10
///   non_redundant 2        # arity 2
///   non_redundant 1 --max-size 12 --allow-min
use clap::Parser;
use gen_rec::enumerate::stream_grf;
use gen_rec::fingerprint::{canonical_inputs, compute_fp, Fingerprint};
use gen_rec::pruning::PruningOpts;
use std::collections::HashMap;

#[derive(Parser, Debug)]
#[command(
    about = "List the smallest non-redundant GRF for each distinct function",
    long_about = "Enumerates GRFs in size order and prints each one that computes a\n\
                  function not yet seen among smaller GRFs.\n\
                  Progress is printed to stderr."
)]
struct Args {
    /// Arity of GRFs to enumerate.
    #[arg(default_value_t = 1)]
    arity: usize,

    /// Enumerate up to this size (inclusive).
    #[arg(long, default_value_t = 10)]
    max_size: usize,

    /// Max simulation steps per input when computing fingerprints.
    #[arg(long, default_value_t = 10_000)]
    max_steps: u64,

    /// Include the Minimization combinator.
    #[arg(long)]
    allow_min: bool,

    /// Print progress to stderr after each size.
    #[arg(long)]
    progress: bool,
}

fn main() {
    let args = Args::parse();
    let opts = PruningOpts::default();
    let inputs = canonical_inputs(args.arity);

    // fingerprint → canonical (smallest) GRF string
    let mut fp_db: HashMap<Fingerprint, String> = HashMap::new();

    for size in 1..=args.max_size {
        let mut total = 0usize;
        let mut novel = 0usize;

        stream_grf(size, args.arity, args.allow_min, opts, &mut |grf| {
            total += 1;
            let fp = compute_fp(grf, &inputs, args.max_steps);

            if !fp_db.contains_key(&fp) {
                let expr = grf.to_string();
                let fp_str: Vec<String> = fp
                    .iter()
                    .map(|v| match v {
                        Some(n) => n.to_string(),
                        None => "?".to_string(),
                    })
                    .collect();
                fp_db.insert(fp, expr.clone());
                println!("{:>4}  {:<40}  [{}]", size, expr, fp_str.join(", "));
                novel += 1;
            }
        });

        if args.progress {
            eprintln!(
                "size {:>3}: {:>8} enumerated, {:>6} novel ({} distinct functions total)",
                size,
                total,
                novel,
                fp_db.len()
            );
        }
    }

    eprintln!(
        "Done. {} distinct functions found across {} arities up to size {}.",
        fp_db.len(),
        args.arity,
        args.max_size
    );
}
