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
use std::cmp::min;
use std::time::Instant;

// ── Spec registry ────────────────────────────────────────────────────────────
//
// To add a new spec, add ONE entry to SPECS below.  That's it.

struct SpecDef {
    name: &'static str,
    default_arity: usize,
    description: &'static str,
    build: fn() -> Box<dyn FnMut(&[Num], Num) -> bool>,
}

fn trailing_bits(inputs: &[Num], output: Num) -> bool {
    let n = inputs[0];
    if n >= 64 { return true; }
    let mask = (1u64 << n) - 1;
    (output & mask) == mask
}

const SPECS: &[SpecDef] = &[
    SpecDef {
        name: "succ", default_arity: 1,
        description: "successor: f(x) = x+1",
        build: || Box::new(exact_spec(|a| Some(a[0] + 1))),
    },
    SpecDef {
        name: "pred", default_arity: 1,
        description: "predecessor (saturating): f(x) = max(0, x-1)",
        build: || Box::new(exact_spec(|a| Some(a[0].saturating_sub(1)))),
    },
    SpecDef {
        name: "sgn", default_arity: 1,
        description: "f(x) = if x==0 then 0 else 1",
        build: || Box::new(exact_spec(|a| Some(min(a[0], 1)))),
    },
    SpecDef {
        name: "not", default_arity: 1,
        description: "f(x) = if x==0 then 1 else 0",
        build: || Box::new(exact_spec(|a| Some(1_u64.saturating_sub(a[0])))),
    },
    SpecDef {
        name: "monus2", default_arity: 1,
        description: "f(x) = max(0, x-2)",
        build: || Box::new(exact_spec(|a| Some(a[0].saturating_sub(2)))),
    },
    SpecDef {
        name: "monus3", default_arity: 1,
        description: "f(x) = max(0, x-3)",
        build: || Box::new(exact_spec(|a| Some(a[0].saturating_sub(3)))),
    },
    SpecDef {
        name: "add", default_arity: 2,
        description: "addition: f(x,y) = x+y",
        build: || Box::new(exact_spec(|a| Some(a[0] + a[1]))),
    },
    SpecDef {
        name: "monus", default_arity: 2,
        description: "saturated subtraction: f(x,y) = max(0, x-y)",
        build: || Box::new(exact_spec(|a| Some(a[0].saturating_sub(a[1])))),
    },
    SpecDef {
        name: "rmonus", default_arity: 2,
        description: "f(x,y) = max(0, y-x)",
        build: || Box::new(exact_spec(|a| Some(a[1].saturating_sub(a[0])))),
    },
    SpecDef {
        name: "mul", default_arity: 2,
        description: "multiplication: f(x,y) = x*y",
        build: || Box::new(exact_spec(|a| Some(a[0] * a[1]))),
    },
    SpecDef {
        name: "mul2", default_arity: 2,
        description: "f(x) = 2x",
        build: || Box::new(exact_spec(|a| Some(2*a[0]))),
    },
    // Mod2: 8: R(Z0, C(R(S, Z3), P(2,2), Z2))
    SpecDef {
        name: "mod2", default_arity: 1,
        description: "parity: f(x) = x % 2",
        build: || Box::new(exact_spec(|a| Some(a[0] % 2))),
    },
    SpecDef {
        name: "nmod2", default_arity: 1,
        description: "parity: f(x) = (x+1) % 2",
        build: || Box::new(exact_spec(|a| Some((a[0]+1) % 2))),
    },
    // Mod3: 10: R(Z0, C(R(S, R(P(2,1), Z4)), P(2,2), P(2,2)))
    SpecDef {
        name: "mod3", default_arity: 1,
        description: "f(x) = x % 3",
        build: || Box::new(exact_spec(|a| Some(a[0] % 3))),
    },
    SpecDef {
        name: "div2", default_arity: 1,
        description: "f(x) = floor(x / 2)",
        build: || Box::new(exact_spec(|a| Some(a[0] / 2))),
    },
    SpecDef {
        name: "ceildiv2", default_arity: 1,
        description: "f(x) = ceil(x / 2)",
        build: || Box::new(exact_spec(|a| Some(a[0].div_ceil(2)))),
    },
    SpecDef {
        name: "div3", default_arity: 1,
        description: "f(x) = floor(x / 3)",
        build: || Box::new(exact_spec(|a| Some(a[0] / 3))),
    },
    SpecDef {
        name: "pow2", default_arity: 1,
        description: "power of two: f(x) = 2^x",
        build: || Box::new(exact_spec(|a| Some(1u64 << a[0].min(63)))),
    },
    SpecDef {
        name: "pow2m1", default_arity: 1,
        description: "f(x) = 2^x - 1",
        build: || Box::new(exact_spec(|a| Some((1u64 << a[0].min(63)) - 1))),
    },
    SpecDef {
        name: "trailing-bits", default_arity: 1,
        description: "trailing ones: f(n[,x]) has n trailing 1-bits (arity 1 or 2)",
        build: || Box::new(trailing_bits),
    },
];

fn list_specs() {
    eprintln!("Available specs:");
    for s in SPECS {
        eprintln!("  {:16}  arity={}  {}", s.name, s.default_arity, s.description);
    }
}

fn spec_info(name: &str) -> Option<&'static SpecDef> {
    SPECS.iter().find(|s| s.name == name)
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
    #[arg()]
    spec: Option<String>,

    /// Arity of the target GRF (overrides spec default).
    #[arg(long)]
    arity: Option<usize>,

    /// Stop searching after this size (inclusive).
    #[arg(long, default_value_t = 14)]
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

    /// Run all specs (ignores --spec and --arity).
    #[arg(long)]
    all: bool,
}

// ── Search runner ─────────────────────────────────────────────────────────────

fn print_partials(name: &str, partials: &[gen_rec::semantic_search::SearchResult]) {
    if !partials.is_empty() {
        println!("[{}] {} partial match{} (converges on some inputs, diverges on others):",
            name, partials.len(), if partials.len() == 1 { "" } else { "es" });
        for r in partials {
            println!("  size={}  {}  (verified on {}, timed out on {})",
                r.size, r.grf, r.inputs_tested, r.timed_out_inputs);
        }
    }
}

fn run_search(info: &SpecDef, args: &Args) {
    let arity = args.arity.unwrap_or(info.default_arity);
    let confidence_inputs = args.confidence_inputs.unwrap_or(64);

    let config = SearchConfig {
        arity,
        allow_min: args.allow_min,
        max_size: args.max_size,
        max_steps: args.max_steps,
        confidence_inputs,
        progress: args.progress,
        trace: args.trace,
    };

    let t0 = Instant::now();

    if args.all_at_min_size {
        let mut spec = (info.build)();
        let output = search_all_at_min(&config, &mut *spec);
        let elapsed = t0.elapsed();

        if output.guaranteed.is_empty() {
            println!(
                "[{}] No guaranteed match found for sizes 1..={} (arity={}, {:.1?})",
                info.name, config.max_size, arity, elapsed
            );
            print_partials(info.name, &output.partials);
        } else {
            let min_size = output.guaranteed[0].size;
            println!(
                "[{}] size={} ({} guaranteed match{})  [{:.1?}]",
                info.name, min_size, output.guaranteed.len(),
                if output.guaranteed.len() == 1 { "" } else { "es" },
                elapsed
            );
            for r in &output.guaranteed {
                println!("  {}  (verified on {} inputs)", r.grf, r.inputs_tested);
            }
            print_partials(info.name, &output.partials);
        }
    } else {
        let mut spec = (info.build)();
        let output = search_smallest(&config, &mut *spec);
        let elapsed = t0.elapsed();

        if let Some(r) = output.guaranteed.first() {
            println!(
                "[{}] size={}: {}  (arity={}, verified on {} inputs, {:.1?})",
                info.name, r.size, r.grf, arity, r.inputs_tested, elapsed
            );
        } else {
            println!(
                "[{}] No guaranteed match found for sizes 1..={} (arity={}, {:.1?})",
                info.name, config.max_size, arity, elapsed
            );
        }
        print_partials(info.name, &output.partials);
    }
}

// ── Main ──────────────────────────────────────────────────────────────────────

fn main() {
    let args = Args::parse();

    // ── --all mode ────────────────────────────────────────────────────────────
    if args.all {
        for info in SPECS {
            run_search(info, &args);
        }
        return;
    }

    // ── Resolve spec ──────────────────────────────────────────────────────────
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

    // ── --probe mode ──────────────────────────────────────────────────────────
    if let Some(grf_str) = &args.probe {
        let arity = args.arity.unwrap_or(info.default_arity);
        let confidence_inputs = args.confidence_inputs.unwrap_or(64);

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

        let mut spec = (info.build)();
        let verify = verification_inputs(arity);
        let result = probe_spec(&grf, &mut *spec, &verify, args.max_steps);
        println!("verification inputs ({}): {}", verify.len(), result);

        if let Some(max_val) = args.exhaustive_probe {
            let mut spec2 = (info.build)();
            let result2 = exhaustive_probe(&grf, &mut *spec2, max_val, args.max_steps);
            println!("exhaustive 0..={max_val}:        {}", result2);
        } else {
            let conf = canonical_inputs_n(arity, confidence_inputs);
            let mut spec2 = (info.build)();
            let result2 = probe_spec(&grf, &mut *spec2, &conf, args.max_steps);
            println!("confidence inputs ({}):  {}", conf.len(), result2);
        }

        return;
    }

    // ── Normal search ─────────────────────────────────────────────────────────
    run_search(info, &args);
}
