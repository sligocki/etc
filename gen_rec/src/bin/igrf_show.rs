/// Print sizes (raw, after opt_inline_proj, after opt_fingerprint) for all
/// named GRFs defined in a .igrf file, then run inline spec tests.
///
/// Usage:
///   igrf_show erdos.igrf
///   igrf_show erdos.igrf --fp-max-size 8
use clap::Parser;
use gen_rec::fingerprint::FingerprintDb;
use gen_rec::igrf::parse_igrf_file;
use gen_rec::optimize::{opt_fingerprint, opt_inline_proj};
use gen_rec::simulate::simulate;
use std::collections::HashMap;
use std::path::PathBuf;

#[derive(Parser, Debug)]
#[command(about = "Print sizes for all GRFs defined in a .igrf file before and after optimization")]
struct Args {
    /// Path to the .igrf file.
    file: PathBuf,

    /// Max GRF size included in the fingerprint DB (0 = skip fingerprint pass).
    #[arg(long, default_value_t = 0)]
    fp_max_size: usize,

    /// Max arity included in the fingerprint DB.
    #[arg(long, default_value_t = 3)]
    fp_max_arity: usize,

    /// Include Minimization in the fingerprint DB.
    #[arg(long)]
    fp_allow_min: bool,

    /// Max simulation steps per test case and for fingerprinting.
    #[arg(long, default_value_t = 1_000_000)]
    max_steps: u64,
}

fn main() {
    let args = Args::parse();

    let content = std::fs::read_to_string(&args.file)
        .unwrap_or_else(|e| panic!("Cannot read {:?}: {}", args.file, e));

    let file = parse_igrf_file(&content)
        .unwrap_or_else(|e| panic!("Parse error: {}", e));

    let db = if args.fp_max_size > 0 {
        eprint!(
            "Building fingerprint DB (size≤{}, arity≤{})... ",
            args.fp_max_size, args.fp_max_arity
        );
        let db = FingerprintDb::build(
            args.fp_max_size,
            args.fp_max_arity,
            args.fp_allow_min,
            args.max_steps,
        );
        eprintln!("done.");
        Some(db)
    } else {
        None
    };

    // ── Size table ────────────────────────────────────────────────────────────

    if db.is_some() {
        println!("{:<22}  {:>4}  {:>5}  {:>5}  {:>5}", "name", "ar", "raw", "ip", "fp");
        println!("{}", "-".repeat(45));
    } else {
        println!("{:<22}  {:>4}  {:>5}  {:>5}", "name", "ar", "raw", "ip");
        println!("{}", "-".repeat(38));
    }

    for (name, grf) in &file.defs {
        let ar = grf.arity();
        let raw = grf.size();
        let ip = opt_inline_proj(grf.clone());
        let ip_size = ip.size();

        if let Some(ref db) = db {
            let fp = opt_fingerprint(ip, db);
            println!("{:<22}  {:>4}  {:>5}  {:>5}  {:>5}", name, ar, raw, ip_size, fp.size());
        } else {
            println!("{:<22}  {:>4}  {:>5}  {:>5}", name, ar, raw, ip_size);
        }
    }

    // ── Spec tests ────────────────────────────────────────────────────────────

    if file.tests.is_empty() {
        return;
    }

    println!();
    let grf_map: HashMap<&str, _> = file.defs.iter().map(|(n, g)| (n.as_str(), g)).collect();
    let mut passed = 0usize;
    let mut failed = 0usize;

    for tc in &file.tests {
        let grf = match grf_map.get(tc.name.as_str()) {
            Some(g) => g,
            None => {
                println!("FAIL  {} -- undefined GRF", tc.name);
                failed += 1;
                continue;
            }
        };
        let args_str = tc.args.iter().map(|a| a.to_string()).collect::<Vec<_>>().join(", ");
        let (result, _) = simulate(grf, &tc.args, args.max_steps);
        let ok = match (result.into_value(), tc.expected) {
            (Some(got), Some(exp)) => got == exp,
            (None,      None)      => true,
            _                      => false,
        };
        if ok {
            passed += 1;
        } else {
            let exp_str = tc.expected.map_or("⊥".to_string(), |v| v.to_string());
            println!("FAIL  {}({}) == {}", tc.name, args_str, exp_str);
            failed += 1;
        }
    }

    if failed == 0 {
        println!("{} tests passed.", passed);
    } else {
        println!("{} passed, {} FAILED.", passed, failed);
        std::process::exit(1);
    }
}
