use clap::Parser;
use mbb::enumerate::enumerate;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Number of states in the program
    num_states: usize,

    /// Step limit for simulation
    step_limit: u64,

    /// Output file to write the results
    out_file: String,

    /// Maximum number of registers allowed. Defaults to num_states / 2 + 1
    #[arg(short, long)]
    max_regs: Option<usize>,

    /// Allow NoOp instructions
    #[arg(short = 'n', long)]
    allow_no_ops: bool,
}

fn main() {
    let args = Args::parse();

    println!("Starting enumeration for {} states, limit: {} steps. Allow NoOps: {}", args.num_states, args.step_limit, args.allow_no_ops);
    if let Some(r) = args.max_regs {
        println!("Max registers restricted to: {}", r);
    } else {
        println!("Max registers default: {}", args.num_states / 2 + 1);
    }

    enumerate(args.num_states, args.step_limit, args.max_regs, args.allow_no_ops, &args.out_file);
}
