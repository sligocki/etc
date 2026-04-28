/// Find the smallest GRF satisfying a named spec.
///
/// Usage examples:
///   search --spec pow2
///   search --spec trailing-bits --arity 2 --all-at-min-size
///   search --spec pred --probe "R(Z0, P(2,1))"
///   search --spec add --progress
use clap::Parser;
use gen_rec::fingerprint::{canonical_inputs_n, verification_inputs};
use gen_rec::semantic_search::{
    exact_spec, exhaustive_probe, probe_spec, search_all_at_min, search_smallest, SearchConfig,
};
use gen_rec::simulate::Num;
use std::time::Instant;

// ── Spec registry ────────────────────────────────────────────────────────────

struct SpecInfo {
    name: &'static str,
    default_arity: usize,
    default_confidence_inputs: usize,
    description: &'static str,
}

const SPECS: &[SpecInfo] = &[
    SpecInfo { name: "succ",          default_arity: 1, default_confidence_inputs: 8,  description: "successor: f(x) = x+1" },
    SpecInfo { name: "pred",          default_arity: 1, default_confidence_inputs: 8,  description: "predecessor (saturating): f(x) = max(0, x-1)" },
    SpecInfo { name: "add",           default_arity: 2, default_confidence_inputs: 32, description: "addition: f(x,y) = x+y" },
    SpecInfo { name: "mul",           default_arity: 2, default_confidence_inputs: 32, description: "multiplication: f(x,y) = x*y" },
    SpecInfo { name: "pow2",          default_arity: 1, default_confidence_inputs: 12, description: "power of two: f(x) = 2^x" },
    SpecInfo { name: "trailing-bits", default_arity: 1, default_confidence_inputs: 64, description: "trailing ones: f(n[,x]) has n trailing 1-bits (arity 1 or 2)" },
];

fn list_specs() {
    eprintln!("Available specs:");
    for s in SPECS {
        eprintln!("  {:16}  arity={}  {}", s.name, s.default_arity, s.description);
    }
}

fn spec_info(name: &str) -> Option<&'static SpecInfo> {
    SPECS.iter().find(|s| s.name == name)
}

fn trailing_bits_spec(inputs: &[Num], output: Num) -> bool {
    let n = inputs[0];
    if n >= 64 { return true; }
    let mask = (1u64 << n) - 1;
    (output & mask) == mask
}

fn build_spec(name: &str) -> Box<dyn FnMut(&[Num], Num) -> bool> {
    match name {
        "succ"          => Box::new(exact_spec(|a| Some(a[0] + 1))),
        "pred"          => Box::new(exact_spec(|a| Some(a[0].saturating_sub(1)))),
        "add"           => Box::new(exact_spec(|a| Some(a[0] + a[1]))),
        "mul"           => Box::new(exact_spec(|a| Some(a[0] * a[1]))),
        "pow2"          => Box::new(exact_spec(|a| Some(1u64 << a[0].min(63)))),
        "trailing-bits" => Box::new(trailing_bits_spec),
        _               => unreachable!(),
    }
}

// ── CLI ───────────────────────────────────────────────────────────────────────

#[derive(Parser, Debug)]
#[command(
    about = "Find the smallest GRF satisfying a named spec",
    long_about = "Search for the smallest GRF (by node count) whose input/output behaviour\n\
                  matches the given spec.  Use --probe to test a specific GRF directly.\n\n\
                  Run with no arguments to list available specs."
)]
struct Args {
    /// Spec name (omit to list available specs).
    #[arg(long)]
    spec: Option<String>,

    /// Arity of the target GRF (overrides spec default).
    #[arg(long)]
    arity: Option<usize>,

    /// Stop searching after this size (inclusive).
    #[arg(long, default_value_t = 12)]
    max_size: usize,

    /// Step budget per simulation call (0 = unlimited).
    #[arg(long, default_value_t = 100_000)]
    max_steps: u64,

    /// Number of inputs required to accept a match.
    #[arg(long)]
    confidence_inputs: Option<usize>,

    /// Allow Min (μ) operator in search.
    #[arg(long)]
    allow_min: bool,

    /// After finding the minimum size, collect and print ALL matches at that size.
    #[arg(long)]
    all_at_min_size: bool,

    /// Test a specific GRF expression against the spec (skips search).
    #[arg(long, value_name = "GRF")]
    probe: Option<String>,

    /// Exhaustively probe a GRF on all inputs 0..=MAX (requires --probe).
    #[arg(long, value_name = "MAX")]
    exhaustive_probe: Option<u64>,

    /// Print per-size candidate counts.
    #[arg(long)]
    progress: bool,

    /// Print per-candidate accept/reject trace (very verbose).
    #[arg(long)]
    trace: bool,
}

// ── Main ──────────────────────────────────────────────────────────────────────

fn main() {
    let args = Args::parse();

    // List specs if no --spec given.
    let spec_name = match &args.spec {
        Some(s) => s.clone(),
        None => {
            list_specs();
            std::process::exit(0);
        }
    };

    let info = match spec_info(&spec_name) {
        Some(i) => i,
        None => {
            eprintln!("Unknown spec '{}'. ", spec_name);
            list_specs();
            std::process::exit(1);
        }
    };

    let arity = args.arity.unwrap_or(info.default_arity);
    let confidence_inputs = args.confidence_inputs.unwrap_or(info.default_confidence_inputs);

    let config = SearchConfig {
        arity,
        allow_min: args.allow_min,
        max_size: args.max_size,
        max_steps: args.max_steps,
        confidence_inputs,
        progress: args.progress,
        trace: args.trace,
    };

    // ── --probe mode ──────────────────────────────────────────────────────────
    if let Some(grf_str) = &args.probe {
        let grf: gen_rec::grf::Grf = match grf_str.parse() {
            Ok(g) => g,
            Err(e) => { eprintln!("Parse error: {e}"); std::process::exit(1); }
        };
        if grf.arity() != arity {
            eprintln!(
                "Arity mismatch: GRF has arity {}, spec expects arity {}",
                grf.arity(), arity
            );
            std::process::exit(1);
        }

        println!("[probe] {}  size={} arity={}", grf, grf.size(), arity);
        println!("spec: {}  ({})", spec_name, info.description);
        println!();

        let mut spec = build_spec(&spec_name);
        let verify = verification_inputs(arity);
        let result = probe_spec(&grf, &mut *spec, &verify, args.max_steps);
        println!("verification inputs ({}): {}", verify.len(), result);

        if let Some(max_val) = args.exhaustive_probe {
            let mut spec2 = build_spec(&spec_name);
            let result2 = exhaustive_probe(&grf, &mut *spec2, max_val, args.max_steps);
            println!("exhaustive 0..={max_val}:        {}", result2);
        } else {
            let conf = canonical_inputs_n(arity, confidence_inputs);
            let mut spec2 = build_spec(&spec_name);
            let result2 = probe_spec(&grf, &mut *spec2, &conf, args.max_steps);
            println!("confidence inputs ({}):  {}", conf.len(), result2);
        }

        return;
    }

    // ── Normal search ─────────────────────────────────────────────────────────
    let t0 = Instant::now();

    if args.all_at_min_size {
        let mut spec = build_spec(&spec_name);
        let results = search_all_at_min(&config, &mut *spec);
        let elapsed = t0.elapsed();

        if results.is_empty() {
            println!(
                "[search] No match found for sizes 1..={} (arity={}, {:.1?})",
                config.max_size, arity, elapsed
            );
            eprintln!("Hint: try --max-size {} or --probe GRF to test a specific candidate.", config.max_size + 4);
        } else {
            println!(
                "[search] size={} ({} match{})  [{:.1?}]",
                results[0].size,
                results.len(),
                if results.len() == 1 { "" } else { "es" },
                elapsed
            );
            for r in &results {
                println!("  {}  (verified on {} inputs)", r.grf, r.inputs_tested);
            }
        }
    } else {
        let mut spec = build_spec(&spec_name);
        let result = search_smallest(&config, &mut *spec);
        let elapsed = t0.elapsed();

        match result {
            Some(r) => {
                println!(
                    "[search] size={}: {}  (arity={}, verified on {} inputs, {:.1?})",
                    r.size, r.grf, arity, r.inputs_tested, elapsed
                );
            }
            None => {
                println!(
                    "[search] No match found for sizes 1..={} (arity={}, {:.1?})",
                    config.max_size, arity, elapsed
                );
                eprintln!("Hint: try --max-size {} or --probe GRF to test a specific candidate.", config.max_size + 4);
            }
        }
    }
}
