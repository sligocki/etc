use clap::Parser;
use mbb::enumerate::{enumerate, evaluate_file};

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
#[command(override_usage = "enumerate [OPTIONS] <NUM_STATES> <STEP_LIMIT> <OUT_FILE>\n       enumerate [OPTIONS] -i <INPUT> [NUM_STATES] <STEP_LIMIT> <OUT_FILE>")]
struct Args {
    /// Number of states in the program (or step limit if num_states omitted with -i)
    #[arg(value_name = "NUM_STATES")]
    arg1: String,

    /// Step limit for simulation (or output file if num_states omitted with -i)
    #[arg(value_name = "STEP_LIMIT")]
    arg2: String,

    /// Output file to write the results
    #[arg(value_name = "OUT_FILE")]
    arg3: Option<String>,

    /// Input file containing programs to evaluate (skips TNF enumeration)
    #[arg(short = 'i', long, alias = "in-file", alias = "input-file")]
    input: Option<String>,

    /// Maximum number of registers allowed. Defaults to num_states / 2 + 1
    #[arg(short, long)]
    max_regs: Option<usize>,

    /// Allow NoOp instructions
    #[arg(short = 'n', long)]
    allow_no_ops: bool,

    /// Compute exact start_by step for cycles and TCs
    #[arg(short = 'e', long)]
    exact_start: bool,

    /// Optional limit on the number of programs to enumerate or evaluate
    #[arg(short, long)]
    limit: Option<usize>,

    /// Only output unknown programs (holdouts)
    #[arg(short = 'u', long)]
    only_unknown: bool,

    /// Configure deciders (+name to enable, -name to disable). Defaults: congruence.
    #[arg(short = 'd', long, default_value = "")]
    deciders: String,
}

fn main() {
    let args = Args::parse();
    let decider_config = mbb::deciders::DeciderConfig::parse(&args.deciders);

    let mut input_file = args.input;
    let (num_states, step_limit, out_file) = if let Some(ref out) = args.arg3 {
        let parsed_num_states = args.arg1.parse::<usize>();
        match parsed_num_states {
            Ok(ns) => {
                let step_limit = args
                    .arg2
                    .parse::<u64>()
                    .expect("Invalid step_limit: must be a positive integer");
                (Some(ns), step_limit, out.clone())
            }
            Err(_) => {
                if input_file.is_none() && std::path::Path::new(&args.arg1).exists() {
                    input_file = Some(args.arg1.clone());
                    let step_limit = args
                        .arg2
                        .parse::<u64>()
                        .expect("Invalid step_limit: must be a positive integer");
                    (None, step_limit, out.clone())
                } else {
                    panic!(
                        "Invalid num_states: '{}' is not a valid number of states or input file",
                        args.arg1
                    );
                }
            }
        }
    } else {
        if input_file.is_none() {
            eprintln!(
                "Error: Missing required argument <OUT_FILE>\nUsage: enumerate <NUM_STATES> <STEP_LIMIT> <OUT_FILE> (or -i <INPUT> <STEP_LIMIT> <OUT_FILE>)"
            );
            std::process::exit(1);
        }
        let step_limit = args
            .arg1
            .parse::<u64>()
            .expect("Invalid step_limit: must be a positive integer");
        let out_file = args.arg2;
        (None, step_limit, out_file)
    };

    if let Some(ref in_file) = input_file {
        println!(
            "Starting decider evaluation on '{}', limit: {} steps. Exact Start: {}, Deciders: {:?}",
            in_file, step_limit, args.exact_start, decider_config
        );
        if let Some(l) = args.limit {
            println!("Program limit: {}", l);
        }
        if args.only_unknown {
            println!("Limiting IO output to only unknown programs.");
        }

        evaluate_file(
            in_file,
            step_limit,
            args.exact_start,
            args.limit,
            &decider_config,
            args.only_unknown,
            &out_file,
        );
    } else {
        let num_states =
            num_states.expect("num_states is required when not evaluating an input file");
        println!(
            "Starting enumeration for {} states, limit: {} steps. Allow NoOps: {}, Exact Start: {}, Deciders: {:?}",
            num_states, step_limit, args.allow_no_ops, args.exact_start, decider_config
        );
        if let Some(r) = args.max_regs {
            println!("Max registers restricted to: {}", r);
        } else {
            println!("Max registers default: {}", num_states / 2 + 1);
        }
        if let Some(l) = args.limit {
            println!("Enumeration limit: {}", l);
        }
        if args.only_unknown {
            println!("Limiting IO output to only unknown programs.");
        }

        enumerate(
            num_states,
            step_limit,
            args.max_regs,
            args.allow_no_ops,
            args.exact_start,
            args.limit,
            &decider_config,
            args.only_unknown,
            &out_file,
        );
    }
}
