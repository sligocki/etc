use mbb::enumerate::enumerate;
use std::env;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 4 {
        eprintln!("Usage: {} <num_states> <step_limit> <out_file> [max_regs]", args[0]);
        std::process::exit(1);
    }

    let num_states: usize = args[1].parse().expect("Invalid num_states");
    let step_limit: u64 = args[2].parse().expect("Invalid step_limit");
    let out_file = &args[3];
    let max_regs = args.get(4).and_then(|s| s.parse::<usize>().ok());

    println!("Starting enumeration for {} states, limit: {} steps.", num_states, step_limit);
    if let Some(r) = max_regs {
        println!("Max registers restricted to: {}", r);
    } else {
        println!("Max registers default: {}", num_states / 2 + 1);
    }

    enumerate(num_states, step_limit, max_regs, out_file);
}
