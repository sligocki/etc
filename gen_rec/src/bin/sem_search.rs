/// Find the smallest GRF satisfying a named spec.
///
/// Usage examples:
///   search --spec pow2
///   search --spec trailing-bits --arity 2 --all-at-min-size
///   search --spec pred --probe "R(Z, P1)"
///   search --spec add --progress
use clap::Parser;
use gen_rec::alias::alias_db_for_stdout;
use gen_rec::fingerprint::{canonical_inputs_n, verification_inputs};
use gen_rec::semantic_search::{
    SearchConfig, bool_spec, exact_spec, exhaustive_probe, probe_spec, search_all_at_min,
    search_smallest,
};
use std::cmp::min;
use std::time::Instant;

// ── Spec registry ────────────────────────────────────────────────────────────
//
// To add a new spec, add ONE entry to SPECS below.  That's it.

struct SpecDef {
    name: &'static str,
    default_arity: usize,
    description: &'static str,
    build: fn() -> Box<dyn FnMut(&[u64], u64) -> bool>,
}

fn plus_8p(inputs: &[u64], output: u64) -> bool {
    output >= inputs[0] + 8
}

fn trailing_bits(inputs: &[u64], output: u64) -> bool {
    let n = inputs[0];
    if n >= 64 {
        return true;
    }
    let mask = (1u64 << n) - 1;
    (output & mask) == mask
}

const SPECS: &[SpecDef] = &[
    SpecDef {
        name: "succ",
        default_arity: 1,
        description: "successor: f(x) = x+1",
        build: || Box::new(exact_spec(|a| Some(a[0] + 1))),
    },
    SpecDef {
        name: "pred",
        default_arity: 1,
        description: "predecessor (saturating): f(x) = max(0, x-1)",
        build: || Box::new(exact_spec(|a| Some(a[0].saturating_sub(1)))),
    },
    SpecDef {
        name: "sgn",
        default_arity: 1,
        description: "f(x) = if x==0 then 0 else 1",
        build: || Box::new(exact_spec(|a| Some(min(a[0], 1)))),
    },
    SpecDef {
        name: "not",
        default_arity: 1,
        description: "f(x) = if x==0 then 1 else 0",
        build: || Box::new(exact_spec(|a| Some(1_u64.saturating_sub(a[0])))),
    },
    SpecDef {
        name: "monus2",
        default_arity: 1,
        description: "f(x) = max(0, x-2)",
        build: || Box::new(exact_spec(|a| Some(a[0].saturating_sub(2)))),
    },
    SpecDef {
        name: "monus3",
        default_arity: 1,
        description: "f(x) = max(0, x-3)",
        build: || Box::new(exact_spec(|a| Some(a[0].saturating_sub(3)))),
    },
    SpecDef {
        name: "add",
        default_arity: 2,
        description: "addition: f(x,y) = x+y",
        build: || Box::new(exact_spec(|a| Some(a[0] + a[1]))),
    },
    SpecDef {
        name: "monus",
        default_arity: 2,
        description: "saturated subtraction: f(x,y) = max(0, x-y)",
        build: || Box::new(exact_spec(|a| Some(a[0].saturating_sub(a[1])))),
    },
    SpecDef {
        name: "rmonus",
        default_arity: 2,
        description: "f(x,y) = max(0, y-x)",
        build: || Box::new(exact_spec(|a| Some(a[1].saturating_sub(a[0])))),
    },
    SpecDef {
        name: "mult",
        default_arity: 2,
        description: "multiplication: f(x,y) = x*y",
        build: || Box::new(exact_spec(|a| Some(a[0] * a[1]))),
    },
    SpecDef {
        name: "mult2",
        default_arity: 1,
        description: "f(x) = 2x",
        build: || Box::new(exact_spec(|a| Some(2 * a[0]))),
    },
    SpecDef {
        name: "mult2s",
        default_arity: 1,
        description: "f(x) = 2x+1",
        build: || Box::new(exact_spec(|a| Some(2 * a[0] + 1))),
    },
    // Mod2: 8: R(Z, C(R(S, Z), P2, Z))
    SpecDef {
        name: "mod2",
        default_arity: 1,
        description: "parity: f(x) = x % 2",
        build: || Box::new(exact_spec(|a| Some(a[0] % 2))),
    },
    SpecDef {
        name: "nmod2",
        default_arity: 1,
        description: "parity: f(x) = (x+1) % 2",
        build: || Box::new(exact_spec(|a| Some((a[0] + 1) % 2))),
    },
    // Mod3: 10: R(Z, C(R(S, R(P1, Z)), P2, P2))
    SpecDef {
        name: "mod3",
        default_arity: 1,
        description: "f(x) = x % 3",
        build: || Box::new(exact_spec(|a| Some(a[0] % 3))),
    },
    // Mod3is0: 14: C(R(P1, C(R(Z, R(S, R(Z, P1))), P2)), P1, S)
    SpecDef {
        name: "mod3is0",
        default_arity: 1,
        description: "f(x) = (x % 3) == 0",
        build: || Box::new(exact_spec(|a| Some(((a[0] % 3) == 0) as u64))),
    },
    // Mod3is1: 12: R(Z, R(S, C(R(S, R(P1, Z)), P2, P2)))
    SpecDef {
        name: "mod3is1",
        default_arity: 1,
        description: "f(x) = (x % 3) == 1",
        build: || Box::new(exact_spec(|a| Some(((a[0] % 3) == 1) as u64))),
    },
    // Mod3is2: 12: R(Z, R(P1, C(R(S, R(P1, Z)), P2, P2)))
    SpecDef {
        name: "mod3is2",
        default_arity: 1,
        description: "f(x) = (x % 3) == 2",
        build: || Box::new(exact_spec(|a| Some(((a[0] % 3) == 2) as u64))),
    },
    // Mod : PRF17 : R(Z, C(R(R(S, P2), R(R(R(Z, P1), P1), P2)), P3, P3, P2))
    SpecDef {
        name: "mod",
        default_arity: 2,
        description: "f(x, y) = x % y",
        build: || {
            Box::new(exact_spec(
                |a| if a[1] != 0 { Some(a[0] % a[1]) } else { None },
            ))
        },
    },
    // Mod_S : 12 : M(C(R(P1, R(R(P2, P1), P2)), P2, P1, P3))
    //      PRF13 : R(Z, C(R(P1, R(R(P2, P1), P2)), P3, P2, P3))
    SpecDef {
        name: "mod_s",
        default_arity: 2,
        description: "f(x, y) = x % (y+1)",
        build: || Box::new(exact_spec(|a| Some(a[0] % (a[1] + 1)))),
    },
    SpecDef {
        name: "div2",
        default_arity: 1,
        description: "f(x) = floor(x / 2)",
        build: || Box::new(exact_spec(|a| Some(a[0] / 2))),
    },
    SpecDef {
        name: "ceildiv2",
        default_arity: 1,
        description: "f(x) = ceil(x / 2)",
        build: || Box::new(exact_spec(|a| Some(a[0].div_ceil(2)))),
    },
    SpecDef {
        name: "truediv2",
        default_arity: 1,
        description: "f(2k) = k",
        build: || {
            Box::new(exact_spec(|a| {
                if (a[0] % 2) == 0 {
                    Some(a[0] / 2)
                } else {
                    None
                }
            }))
        },
    },
    SpecDef {
        name: "div3",
        default_arity: 1,
        description: "f(x) = floor(x / 3)",
        build: || Box::new(exact_spec(|a| Some(a[0] / 3))),
    },
    SpecDef {
        name: "ceildiv3",
        default_arity: 1,
        description: "f(x) = ceil(x / 3)",
        build: || Box::new(exact_spec(|a| Some(a[0].div_ceil(3)))),
    },
    // Pow2 : 12 : C(S, Pow2P)
    SpecDef {
        name: "pow2",
        default_arity: 1,
        description: "power of two: f(x) = 2^x",
        build: || Box::new(exact_spec(|a| Some(1u64 << a[0].min(63)))),
    },
    // Pow2P : 10 : R(Z, C(R(S, C(S, P2)), P2, P2))
    SpecDef {
        name: "pow2p",
        default_arity: 1,
        description: "f(x) = 2^x - 1",
        build: || Box::new(exact_spec(|a| Some((1u64 << a[0].min(63)) - 1))),
    },
    // Pow2S : 14 : C(S, Pow2)
    SpecDef {
        name: "pow2s",
        default_arity: 1,
        description: "f(x) = 2^x + 1",
        build: || Box::new(exact_spec(|a| Some((1u64 << a[0].min(63)) + 1))),
    },
    // Pow : PRF15 : R(K[1], R(Mult, P2))
    SpecDef {
        name: "pow",
        default_arity: 2,
        description: "f(k,b) = b^k",
        build: || Box::new(exact_spec(|a| Some(a[1].pow(a[0] as u32)))),
    },
    // PowS : PRF13 : R(P1, R(Mult, P2))
    SpecDef {
        name: "pow_s",
        default_arity: 2,
        description: "f(k,b) = b^{k+1}",
        build: || Box::new(exact_spec(|a| Some(a[1].pow((a[0] + 1) as u32)))),
    },
    // PowSS : PRF13 : R(S, R(MultIS, P2))
    SpecDef {
        name: "pow_ss",
        default_arity: 2,
        description: "f(k,b) = (b+1)^{k+1}",
        build: || Box::new(exact_spec(|a| Some((a[1] + 1).pow((a[0] + 1) as u32)))),
    },
    // SumPowS : C(Add, C(PowS, P1, P2), C(PowS, P1, P3))
    SpecDef {
        name: "sum_pow_s",
        default_arity: 3,
        description: "f(k,a,b) = a^{k+1} + b^{k+1}",
        build: || {
            Box::new(exact_spec(|a| {
                Some(a[1].pow((a[0] + 1) as u32) + a[2].pow((a[0] + 1) as u32))
            }))
        },
    },
    SpecDef {
        name: "square",
        default_arity: 1,
        description: "f(x) = x^2",
        build: || Box::new(exact_spec(|a| Some(a[0].pow(2)))),
    },
    // Equals : GRF:13 : C(R(Z, R(S, Z)), R(S, C(R(Z, P1), P2)))
    SpecDef {
        name: "equals",
        default_arity: 2,
        description: "f(x,y) = if x==y then 1 else 0",
        build: || Box::new(exact_spec(|a| Some((a[0] == a[1]) as u64))),
    },
    // ZEquals : GRF:11 : C(R(P1, R(R(P2, P1), P2)), P1, P2, P1)
    SpecDef {
        name: "z_equals",
        default_arity: 2,
        description: "f(x,y) = if x==y then 0 else (>0)",
        build: || Box::new(bool_spec(|a| a[0] == a[1])),
    },
    // ZOr : GRF:3 : R(Z, P3)
    SpecDef {
        name: "z_or",
        default_arity: 2,
        description: "",
        build: || Box::new(bool_spec(|a| a[0] == 0 || a[1] == 0)),
    },
    // ZAnd : GRF:5 : R(P1, K[1])
    SpecDef {
        name: "z_and",
        default_arity: 2,
        description: "",
        build: || Box::new(bool_spec(|a| a[0] == 0 && a[1] == 0)),
    },
    // ZIff : GRF:7 : R(P1, R(R(S, Z), P3))
    SpecDef {
        name: "z_iff",
        default_arity: 2,
        description: "",
        build: || Box::new(bool_spec(|a| (a[0] == 0) == (a[1] == 0))),
    },
    // ZIsTri : PRF:17 : C(R(P1, C(PredDef, RMonus^3, P2)), P1, P1)
    SpecDef {
        name: "z_is_tri",
        default_arity: 1,
        description: "f(x) = if x == Tri(k) then 0 else (>0)",
        build: || {
            Box::new(bool_spec(|a| {
                let mut n = a[0] as i64;
                for k in 0..n + 1 {
                    n -= k;
                    if n == 0 {
                        return true;
                    } else if n < 0 {
                        return false;
                    }
                }
                panic!()
            }))
        },
    },
    // ZIsSquare : PRF:18 : C(R(P1, R(Pred, C(R(P1, R(P3, P1)), P2, P3, P2))), P1, P1)
    SpecDef {
        name: "z_is_square",
        default_arity: 1,
        description: "f(x) = if x==k^2 then 0 else (>0)",
        build: || {
            Box::new(bool_spec(|a| {
                let n = a[0];
                let root_n = (n as f64).sqrt() as u64;
                n == root_n * root_n
            }))
        },
    },
    // ZGE : 7 : RMonus
    // ZLE : PRF10 : C(RMonus, P2, P1)
    // ZGT : 7 : RMonusS
    // ZGE : 10 : C(RMonusS, P2, P1)
    SpecDef {
        name: "z_le",
        default_arity: 2,
        description: "f(x,y) = if x ≤ y then 0 else (>0)",
        build: || Box::new(bool_spec(|a| a[0] <= a[1])),
    },
    // PRF14 : C(R(P1, Z), R(Z, R(P2, C(R(Z, P1), P2))), P2)
    SpecDef {
        name: "wp1_ord",
        default_arity: 2,
        description: "",
        build: || {
            Box::new(bool_spec(|a| {
                match (a[0], a[1]) {
                    (_, 0) => true,  // n <= 0
                    (0, _) => false, // 0 > n+1
                    (n, m) => n <= m,
                }
            }))
        },
    },
    // PRF14 : C(R(P1, C(R(P1, P1), R(P3, P3), P2)), P1, P1, P2)
    SpecDef {
        name: "wp1_ord_ge",
        default_arity: 2,
        description: "",
        build: || {
            Box::new(bool_spec(|a| match (a[0], a[1]) {
                (0, _) => true,
                (_, 0) => false,
                (n, m) => n >= m,
            }))
        },
    },
    SpecDef {
        name: "w2_ord",
        default_arity: 2,
        description: "",
        build: || Box::new(bool_spec(|a| (a[0] % 2, a[0]) <= (a[1] % 2, a[1]))),
    },
    SpecDef {
        name: "plus_8p",
        default_arity: 1,
        description: "f(x) ≥ x+8",
        build: || Box::new(plus_8p),
    },
    // Size 10
    // Arity 2: R(x, C(R(S, C(S, P2)), P2, P2))
    //      for x in Z, P1, S
    //  x=Z:  f(a,b) = 2^a - 1
    //  x=P1: f(a,b) = (b+1) 2^a - 1
    //  x=S:  f(a,b) = (b+2) 2^a - 1
    SpecDef {
        name: "trailing-bits",
        default_arity: 1,
        description: "trailing ones: f(n[,x]) has n trailing 1-bits (arity 1 or 2)",
        build: || Box::new(trailing_bits),
    },
    SpecDef {
        name: "A002262",
        default_arity: 1,
        description: "https://oeis.org/A002262",
        build: || Box::new(exact_spec(|a| Some(a002262(a[0])))),
    },
    SpecDef {
        name: "RMonus_A002262",
        default_arity: 2,
        description: "C(RMonus, A002262, P2)",
        build: || Box::new(exact_spec(|a| Some(a[1].saturating_sub(a002262(a[0]))))),
    },
    SpecDef {
        name: "tri_diff",
        default_arity: 1,
        description: "",
        build: || Box::new(exact_spec(|a| Some(tri_diff(a[0])))),
    },
    // RMonusTri : PRF11 : R(P1, R(Pred, C(Pred, P2)))
    SpecDef {
        name: "rmonus_tri",
        default_arity: 2,
        description: "f(a, b) = b -. tri(a)",
        build: || Box::new(exact_spec(|a| Some(a[1].saturating_sub(tri(a[0]))))),
    },
    // RMonusTriS : PRF11 : R(S, R(Pred, C(Pred, P2)))
    SpecDef {
        name: "rmonus_tri_s",
        default_arity: 2,
        description: "f(a, b) = b+1 -. tri(a)",
        build: || Box::new(exact_spec(|a| Some(a[1].saturating_sub(tri(a[0]))))),
    },
    // TriLess : Ex: 20: C(TriP, M(RMonusTriS))
    SpecDef {
        name: "tri_less",
        default_arity: 1,
        description: "",
        build: || Box::new(exact_spec(|a| Some(tri_less(a[0])))),
    },
];

pub fn a002262(n: u64) -> u64 {
    // Cast to u128 to prevent overflow when calculating 2n + 1 for large n
    let n_128 = n as u128;
    let k = 2 * n_128 + 1;

    // .isqrt() returns the integer square root (equivalent to floor(sqrt(k)))
    let s = k.isqrt();

    // Mathematical trick: sqrt(k) is closer to s than s+1 if k <= s^2 + s
    let t = if k <= s * s + s { s } else { s + 1 };

    // Grouping as (t + 2n) - t^2 prevents intermediate subtraction underflow
    // since t^2 is always <= t + 2n.
    (((t + 2 * n_128) - t * t) / 2) as u64
}

/// Triangle numbers
pub fn tri(n: u64) -> u64 {
    n * (n + 1) / 2
}
/// (Floor) Inverse of tri()
/// inv_tri(n) = max {k ≥ 0 : tri(k) ≤ n}
pub fn inv_tri(n: u64) -> u64 {
    let mut acc = 0;
    for k in 1.. {
        acc += k;
        if acc > n {
            return k - 1;
        }
    }
    panic!()
}
/// tri_less(n) = max{tri(k) ≤ n}
pub fn tri_less(n: u64) -> u64 {
    tri(inv_tri(n))
}
pub fn tri_diff(n: u64) -> u64 {
    let x = tri_less(n);
    // If k == n, then formula is Tri(k) - Tri(-1), but that would underflow u64, luckily Tri(-1) = Tri(0) = 0
    x - tri(n.saturating_sub(x + 1))
}

fn list_specs() {
    eprintln!("Available specs:");
    for s in SPECS {
        eprintln!(
            "  {:16}  arity={}  {}",
            s.name, s.default_arity, s.description
        );
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

    /// Disable alias resolution for --probe input (accept only raw GRF strings).
    #[arg(long)]
    no_alias: bool,
}

// ── Search runner ─────────────────────────────────────────────────────────────

fn print_partials(name: &str, partials: &[gen_rec::semantic_search::SearchResult]) {
    if !partials.is_empty() {
        println!(
            "[{}] {} partial match{} (converges on some inputs, diverges on others):",
            name,
            partials.len(),
            if partials.len() == 1 { "" } else { "es" }
        );
        for r in partials {
            println!(
                "  size={}  {}  (verified on {}, timed out on {})",
                r.size, r.grf, r.inputs_tested, r.timed_out_inputs
            );
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
                info.name,
                min_size,
                output.guaranteed.len(),
                if output.guaranteed.len() == 1 {
                    ""
                } else {
                    "es"
                },
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

        let alias_db = alias_db_for_stdout(10, args.no_alias);
        let grf: gen_rec::grf::Grf = match alias_db
            .as_ref()
            .map(|db| db.resolve(grf_str))
            .unwrap_or_else(|| grf_str.parse().map_err(|e| format!("parse error: {e}")))
        {
            Ok(g) => g,
            Err(e) => {
                eprintln!("{e}");
                std::process::exit(1);
            }
        };
        if grf.arity() != arity {
            eprintln!(
                "Arity mismatch: GRF has arity {}, spec expects arity {}",
                grf.arity(),
                arity
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
