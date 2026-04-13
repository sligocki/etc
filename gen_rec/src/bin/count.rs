/// Count GRFs of each size under each pruning configuration.
///
/// Outputs a table showing how many GRFs exist at each size for each cumulative
/// pruning config, so you can see the marginal benefit of each rule.
use clap::Parser;
use gen_rec::enumerate::count_grf;
use gen_rec::pruning::PruningOpts;

const NONE: PruningOpts = PruningOpts::none();
const CP: PruningOpts = PruningOpts {
    skip_comp_proj: true,
    ..NONE
};
const CZ: PruningOpts = PruningOpts {
    skip_comp_zero: true,
    ..CP
};
const RBASE: PruningOpts = PruningOpts {
    skip_rec_zero_arg: true,
    ..CZ
};
const ASSOC: PruningOpts = PruningOpts {
    comp_assoc: true,
    ..RBASE
};
const RZZ: PruningOpts = PruningOpts {
    skip_rec_zero_base: true,
    ..ASSOC
};
// assert_eq!(RZZ, PruningOpts::all());

/// The configs in cumulative order, highest-impact rules first.
/// Each entry is (label, opts).
const CONFIGS: &[(&str, PruningOpts)] = &[
    ("none", NONE),
    ("+cp", CP),
    ("+cz", CZ),
    ("+rbase", RBASE),
    ("+assoc", ASSOC),
    ("+rzz", RZZ),
];

#[derive(Parser, Debug)]
#[command(about = "Count GRFs per size under each pruning configuration")]
struct Args {
    /// Maximum size to count.
    #[arg(default_value_t = 20)]
    max_size: usize,

    /// Arity to count.  Use 0 for BBµ (0-arity = constant PRFs).
    #[arg(default_value_t = 0)]
    arity: usize,

    /// Include Minimization combinator (default: PRF only).
    #[arg(long)]
    allow_min: bool,
}

fn fmt_count(n: usize) -> String {
    if n == 0 {
        return "-".to_string();
    }
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

fn main() {
    let args = Args::parse();

    // ---- header ----
    println!(
        "GRF counts: arity={}, allow_min={}",
        args.arity, args.allow_min
    );
    println!("{}", "=".repeat(78));

    // Column widths: count column W chars wide, reduction column 6 chars wide.
    const W: usize = 10;
    print!("{:>4}  {:>W$}", "size", CONFIGS[0].0);
    for (name, _) in &CONFIGS[1..] {
        print!("  {:>W$}  {:>5}", name, "%red");
    }
    println!();
    let sep_width = 4 + 2 + W + (CONFIGS.len() - 1) * (2 + W + 2 + 5);
    println!("{}", "-".repeat(sep_width));

    let mut total_by_config = vec![0usize; CONFIGS.len()];

    for size in 1..=args.max_size {
        let counts: Vec<usize> = CONFIGS
            .iter()
            .map(|(_, opts)| count_grf(size, args.arity, args.allow_min, *opts))
            .collect();

        total_by_config
            .iter_mut()
            .zip(counts.iter())
            .for_each(|(tot, &c)| *tot += c);

        print!("{:>4}  {:>W$}", size, fmt_count(counts[0]));
        for i in 1..CONFIGS.len() {
            let prev = counts[i - 1];
            let cur = counts[i];
            let saved = prev.saturating_sub(cur);
            let pct = if prev > 0 {
                format!("{:4.1}%", 100.0 * saved as f64 / prev as f64)
            } else {
                "    -".to_string()
            };
            print!("  {:>W$}  {:>5}", fmt_count(cur), pct);
        }
        println!();
    }

    // ---- totals row ----
    println!("{}", "-".repeat(sep_width));
    print!("{:>4}  {:>W$}", "SUM", fmt_count(total_by_config[0]));
    for i in 1..CONFIGS.len() {
        let prev = total_by_config[i - 1];
        let cur = total_by_config[i];
        let saved = prev.saturating_sub(cur);
        let pct = if prev > 0 {
            format!("{:4.1}%", 100.0 * saved as f64 / prev as f64)
        } else {
            "    -".to_string()
        };
        print!("  {:>W$}  {:>5}", fmt_count(cur), pct);
    }
    println!();
    println!();
    println!(
        "Legend: none=unpruned  +cp=skip_comp_proj  +cz=skip_comp_zero  +rbase=rec_zero_arg  +assoc=comp_assoc  +rzz=rec_zero_base"
    );
    println!("%red = % reduction from the immediately preceding column.");
}
