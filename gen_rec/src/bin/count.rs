/// Count GRFs of each size under each pruning configuration.
///
/// Outputs a table showing how many GRFs exist at each size for each cumulative
/// pruning config, so you can see the marginal benefit of each rule.
///
/// Fast (count_grf) columns cover all sizes up to --max-size.
/// Stream-only columns (skip_inline_proj, skip_min_dominated, skip_unused_comp_args)
/// are counted by exhaustive enumeration and only shown up to --stream-max-size.
use clap::Parser;
use gen_rec::enumerate::{count_grf, stream_grf};
use gen_rec::pruning::PruningOpts;

const NONE: PruningOpts = PruningOpts::none();
const CP: PruningOpts = PruningOpts { skip_comp_proj: true, ..NONE };
const CZ: PruningOpts = PruningOpts { skip_comp_zero: true, ..CP };
const RBASE: PruningOpts = PruningOpts { skip_rec_zero_arg: true, ..CZ };
const ASSOC: PruningOpts = PruningOpts { comp_assoc: true, ..RBASE };
const RZZ: PruningOpts = PruningOpts { skip_rec_zero_base: true, ..ASSOC };

// GRF chain (allow_min=true): +min_triv and +min_dom are meaningful.
const MIN_TRIV: PruningOpts = PruningOpts { skip_min_trivial_zero: true, ..RZZ };
const INLINE_PROJ: PruningOpts = PruningOpts { skip_inline_proj: true, ..MIN_TRIV };
const MIN_DOM: PruningOpts = PruningOpts { skip_min_dominated: true, ..INLINE_PROJ };
const UNUSED_COMP: PruningOpts = PruningOpts { skip_unused_comp_args: true, ..MIN_DOM };
const RNF: PruningOpts = PruningOpts { skip_comp_not_rnf: true, ..UNUSED_COMP };

// PRF chain (allow_min=false): min flags do nothing, so skip them.
const INLINE_PROJ_PRF: PruningOpts = PruningOpts { skip_inline_proj: true, ..RZZ };
const UNUSED_COMP_PRF: PruningOpts = PruningOpts { skip_unused_comp_args: true, ..INLINE_PROJ_PRF };
const RNF_PRF: PruningOpts = PruningOpts { skip_comp_not_rnf: true, ..UNUSED_COMP_PRF };

/// Build the config list for the given mode.
/// Each entry is (label, opts, stream_only).
fn make_configs(allow_min: bool) -> Vec<(&'static str, PruningOpts, bool)> {
    let mut v: Vec<(&'static str, PruningOpts, bool)> = vec![
        ("none",   NONE,  false),
        ("+cp",    CP,    false),
        ("+cz",    CZ,    false),
        ("+rbase", RBASE, false),
        ("+assoc", ASSOC, false),
        ("+rzz",   RZZ,   false),
    ];
    if allow_min {
        v.push(("+min_triv",    MIN_TRIV,    false));
        v.push(("+inline_proj", INLINE_PROJ, true));
        v.push(("+min_dom",     MIN_DOM,     true));
        v.push(("+unused_comp", UNUSED_COMP, true));
        v.push(("+rnf",         RNF,         true));
    } else {
        v.push(("+inline_proj", INLINE_PROJ_PRF, true));
        v.push(("+unused_comp", UNUSED_COMP_PRF, true));
        v.push(("+rnf",         RNF_PRF,         true));
    }
    v
}

#[derive(Parser, Debug)]
#[command(about = "Count GRFs per size under each pruning configuration")]
struct Args {
    /// Maximum size for fast (count_grf) columns.
    #[arg(long, default_value_t = 20)]
    max_size: usize,

    /// Maximum size for stream-only columns (exhaustive enumeration; can be slow).
    #[arg(long, default_value_t = 12)]
    stream_max_size: usize,

    /// Arity to count.  Use 0 for BBµ (0-arity = constant PRFs).
    #[arg(long, default_value_t = 0)]
    arity: usize,

    /// Include Minimization combinator (default: PRF only).
    #[arg(long)]
    allow_min: bool,
}

fn fmt_count(n: usize) -> String {
    if n < 1_000 {
        format!("{}", n)
    } else if n < 1_000_000 {
        format!("{:.1}K", n as f64 / 1_000.0)
    } else if n < 1_000_000_000 {
        format!("{:.2}M", n as f64 / 1_000_000.0)
    } else if n < 1_000_000_000_000usize {
        format!("{:.2}B", n as f64 / 1_000_000_000.0)
    } else {
        format!("{:.2}T", n as f64 / 1_000_000_000_000.0)
    }
}

fn count_by_stream(size: usize, arity: usize, allow_min: bool, opts: PruningOpts) -> usize {
    let mut n = 0usize;
    stream_grf(size, arity, allow_min, opts, &mut |_| n += 1);
    n
}

fn main() {
    let args = Args::parse();
    let configs = make_configs(args.allow_min);
    let configs = configs.as_slice();

    println!(
        "GRF counts: arity={}, allow_min={}  (stream columns shown for size ≤ {})",
        args.arity, args.allow_min, args.stream_max_size,
    );
    println!("{}", "=".repeat(100));

    const W: usize = 10;
    // Header row
    print!("{:>4}  {:>W$}", "size", configs[0].0);
    for (name, _, _) in &configs[1..] {
        print!("  {:>W$}  {:>5}", name, "%red");
    }
    println!();
    let sep_width = 4 + 2 + W + (configs.len() - 1) * (2 + W + 2 + 5);
    println!("{}", "-".repeat(sep_width));

    let max_size = args.max_size.max(args.stream_max_size);
    // totals_full: accumulates all counted sizes (up to max_size for fast, stream_max for stream).
    let mut totals_full: Vec<usize> = vec![0; configs.len()];
    // totals_partial: accumulates only sizes ≤ stream_max_size for every config.
    // Used to compare stream columns to fast columns on equal footing in the SUM row.
    let mut totals_partial: Vec<usize> = vec![0; configs.len()];
    let mut total_has_stream = false;

    for size in 1..=max_size {
        // Compute count for each config.
        let counts: Vec<Option<usize>> = configs
            .iter()
            .map(|(_, opts, stream_only)| {
                if *stream_only {
                    if size <= args.stream_max_size {
                        Some(count_by_stream(size, args.arity, args.allow_min, *opts))
                    } else {
                        None
                    }
                } else if size <= args.max_size {
                    Some(count_grf(size, args.arity, args.allow_min, *opts))
                } else {
                    None
                }
            })
            .collect();

        // Skip rows where all counts are None.
        if counts.iter().all(|c| c.is_none()) {
            continue;
        }

        for (tot, c) in totals_full.iter_mut().zip(counts.iter()) {
            if let Some(v) = c { *tot += v; }
        }
        if size <= args.stream_max_size {
            for (tot, c) in totals_partial.iter_mut().zip(counts.iter()) {
                if let Some(v) = c { *tot += v; }
            }
        }
        if counts.iter().any(|c| c.is_none()) {
            total_has_stream = true;
        }

        // Print row.
        let first = counts[0].map_or("-".to_string(), fmt_count);
        print!("{:>4}  {:>W$}", size, first);
        for i in 1..configs.len() {
            let cur_str = counts[i].map_or("-".to_string(), fmt_count);
            let pct_str = match (counts[i - 1], counts[i]) {
                (Some(prev), Some(cur)) if prev > 0 => {
                    let saved = prev.saturating_sub(cur);
                    format!("{:4.1}%", 100.0 * saved as f64 / prev as f64)
                }
                (Some(prev), None) if prev > 0 => "    ?".to_string(),
                _ => "    -".to_string(),
            };
            print!("  {:>W$}  {:>5}", cur_str, pct_str);
        }
        println!();
    }

    // Totals row: for stream columns compare partial-to-partial so the % is meaningful.
    println!("{}", "-".repeat(sep_width));
    let first_str = fmt_count(totals_full[0]);
    print!("{:>4}  {:>W$}", "SUM", first_str);
    for i in 1..configs.len() {
        let is_stream = configs[i].2;
        let is_prev_stream = i > 0 && configs[i - 1].2;
        // Once we enter stream territory, compare partial sums for both prev and cur.
        let (prev, cur) = if is_stream || is_prev_stream {
            (totals_partial[i - 1], totals_partial[i])
        } else {
            (totals_full[i - 1], totals_full[i])
        };
        let cur_str = if is_stream && total_has_stream {
            format!("{}*", fmt_count(totals_full[i]))
        } else {
            fmt_count(totals_full[i])
        };
        let pct_str = if prev > 0 {
            let saved = prev.saturating_sub(cur);
            format!("{:4.1}%", 100.0 * saved as f64 / prev as f64)
        } else {
            "    -".to_string()
        };
        print!("  {:>W$}  {:>5}", cur_str, pct_str);
    }
    println!();
    println!();
    println!("Rules (cumulative left to right):");
    println!("  +cp          skip_comp_proj       C(P,…) → one of its args");
    println!("  +cz          skip_comp_zero        C(Z,…) → Z");
    println!("  +rbase       skip_rec_zero_arg     C(R(g,h),Z,…) → C(g,…)");
    println!("  +assoc       comp_assoc            prefer right-associated Comp");
    println!("  +rzz         skip_rec_zero_base    R(Z,Z) / R(Z,P2) → Z");
    if args.allow_min {
        println!("  +min_triv    skip_min_trivial_zero M(Z) / M(P) → Z");
    }
    println!("  +inline_proj skip_inline_proj      C(h,P/Z…) → inlined h  [stream-only]");
    if args.allow_min {
        println!("  +min_dom     skip_min_dominated    M(f) where f ignores search var  [stream-only]");
    }
    println!("  +unused_comp skip_unused_comp_args C(h,…) force unused arg slots to Z  [stream-only]");
  println!("  +rnf         skip_comp_not_rnf     C(h,…) require h in RNF (all args used, canonical order)  [stream-only]");
    println!("%red = % reduction vs the immediately preceding column.");
    if total_has_stream {
        println!("* SUM marked with * covers only sizes ≤ {} for stream-only columns.", args.stream_max_size);
    }
}
