/// Print sizes (raw, after opt_inline_proj, after opt_fingerprint) for all
/// named GRFs defined in a .igrf file.
///
/// Usage:
///   igrf_show erdos.igrf
///   igrf_show erdos.igrf --fp-max-size 8
use clap::Parser;
use gen_rec::fingerprint::FingerprintDb;
use gen_rec::igrf::parse_igrf_to_grfs;
use gen_rec::optimize::{opt_fingerprint, opt_inline_proj};
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

    /// Max simulation steps when fingerprinting.
    #[arg(long, default_value_t = 100_000)]
    max_steps: u64,
}

fn main() {
    let args = Args::parse();

    let content = std::fs::read_to_string(&args.file)
        .unwrap_or_else(|e| panic!("Cannot read {:?}: {}", args.file, e));

    let entries = parse_igrf_to_grfs(&content)
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

    if db.is_some() {
        println!("{:<22}  {:>4}  {:>5}  {:>5}  {:>5}", "name", "ar", "raw", "ip", "fp");
        println!("{}", "-".repeat(45));
    } else {
        println!("{:<22}  {:>4}  {:>5}  {:>5}", "name", "ar", "raw", "ip");
        println!("{}", "-".repeat(38));
    }

    for (name, grf) in &entries {
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
}
