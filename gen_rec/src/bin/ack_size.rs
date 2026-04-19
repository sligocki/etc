/// Print sizes (raw, after opt_inline_proj, after opt_fingerprint) for all
/// named GRFs in example_ack.
///
/// Usage:
///   opt_ack                        # inline_proj only (no fingerprint DB)
///   opt_ack --fp-max-size 8        # enable fingerprint pass too
///
use clap::Parser;
use gen_rec::example_ack::{
    ack, ack_loop, ack_step, ack_worm, bit, dec_append, dec_append_n, div2, div2k, double,
    graham, init_list, mod2, monus2, not, omega, plus2, pop_k, pred, rmonus, rmonus_odd, sgn,
    shift,
};
use gen_rec::fingerprint::FingerprintDb;
use gen_rec::grf::Grf;
use gen_rec::optimize::{opt_fingerprint, opt_inline_proj};

#[derive(Parser, Debug)]
#[command(about = "Print sizes for all example_ack GRFs before and after optimization")]
struct Args {
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

    let entries: &[(&str, Grf)] = &[
        ("pred",         pred()),
        ("not",          not()),
        ("sgn",          sgn()),
        ("plus2",        plus2()),
        ("double",       double()),
        ("rmonus",       rmonus()),
        ("mod2",         mod2()),
        ("shift",        shift()),
        ("monus2",       monus2()),
        ("rmonus_odd",   rmonus_odd()),
        ("div2",         div2()),
        ("div2k",        div2k()),
        ("dec_append",   dec_append()),
        ("dec_append_n", dec_append_n()),
        ("bit",          bit()),
        ("pop_k",        pop_k()),
        ("ack_step",     ack_step()),
        ("ack_loop",     ack_loop()),
        ("ack_worm",     ack_worm()),
        ("init_list",    init_list()),
        ("ack",          ack()),
        ("omega",        omega()),
        ("graham",       graham()),
    ];

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
        println!("{:<14}  {:>5}  {:>5}  {:>5}", "name", "raw", "ip", "fp");
        println!("{}", "-".repeat(35));
    } else {
        println!("{:<14}  {:>5}  {:>5}", "name", "raw", "ip");
        println!("{}", "-".repeat(28));
    }

    for (name, grf) in entries {
        let raw = grf.size();
        let ip = opt_inline_proj(grf.clone());
        let ip_size = ip.size();

        if let Some(ref db) = db {
            let fp = opt_fingerprint(ip, db);
            println!("{:<14}  {:>5}  {:>5}  {:>5}", name, raw, ip_size, fp.size());
        } else {
            println!("{:<14}  {:>5}  {:>5}", name, raw, ip_size);
        }
    }
}
