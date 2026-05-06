/// Count GRFs of each size under each pruning configuration.
///
/// Outputs a table showing how many GRFs exist at each size for each cumulative
/// pruning config, so you can see the marginal benefit of each rule.
///
/// Fast (count_grf) columns cover all sizes up to --max-size.
/// Stream-only columns are counted by exhaustive enumeration and only shown
/// up to --stream-max-size.
use clap::Parser;
use gen_rec::enumerate::{count_grf, stream_grf};
use gen_rec::pruning::{PruningOpts, FLAGS};

/// Build the cumulative config list from the global FLAGS registry.
/// Each entry is (label, opts, stream_only).
///
/// Count-compat flags are shown first (cumulatively), then stream-only flags on
/// top — regardless of their order in FLAGS. This ensures no count_grf call ever
/// has a stream-only flag set, which would panic.
fn make_configs(allow_min: bool) -> Vec<(&'static str, PruningOpts, bool)> {
    let mut v = vec![("none", PruningOpts::default(), false)];
    let mut acc = PruningOpts::default();
    let applicable: Vec<_> = FLAGS.iter().filter(|m| allow_min || !m.min_only).collect();
    let ordered = applicable.iter().filter(|m| m.count_compat)
        .chain(applicable.iter().filter(|m| !m.count_compat));
    for meta in ordered {
        (meta.set)(&mut acc, true);
        v.push((meta.name, acc, !meta.count_compat));
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
    for meta in FLAGS {
        if args.allow_min || !meta.min_only {
            let note = if meta.count_compat { "" } else { "  [stream-only]" };
            println!("  {:<15} {}{}", meta.name, meta.desc, note);
        }
    }
    println!("%red = % reduction vs the immediately preceding column.");
    if total_has_stream {
        println!("* SUM marked with * covers only sizes ≤ {} for stream-only columns.", args.stream_max_size);
    }
}
