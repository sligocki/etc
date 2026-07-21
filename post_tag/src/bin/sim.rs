use clap::Parser;
use post_tag::simulate::{HaltCondition, InfiniteReason};
use post_tag::tag_system::TagSystem;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Rule string (e.g. "0->011, 1->eps")
    rules: String,

    /// Deletion number
    #[arg(long = "del", default_value_t = 2)]
    v: usize,

    /// Max steps
    #[arg(long, default_value_t = 1_000_000)]
    max_steps: usize,

    /// Verbose (print every step)
    #[arg(short, long)]
    verbose: bool,
}

fn parse_rules(s: &str) -> Vec<Option<Vec<u8>>> {
    let mut rules = Vec::new();
    for part in s.split(',') {
        let part = part.trim();
        if part.is_empty() {
            continue;
        }
        if let Some((lhs, rhs)) = part.split_once("->") {
            let lhs: usize = lhs.trim().parse().unwrap();
            while rules.len() <= lhs {
                rules.push(None);
            }
            let rhs = rhs.trim();
            if rhs == "?" {
                rules[lhs] = None;
            } else if rhs == "eps" {
                rules[lhs] = Some(vec![]);
            } else {
                let mut rv = vec![];
                for c in rhs.chars() {
                    rv.push(c.to_digit(10).unwrap() as u8);
                }
                rules[lhs] = Some(rv);
            }
        }
    }
    rules
}

fn main() {
    let args = Args::parse();
    let rules = parse_rules(&args.rules);
    let sys = TagSystem { v: args.v, rules };
    
    println!("Simulating: {}", sys.format_rules());
    
    let result = if args.verbose {
        sys.simulate_verbose(args.max_steps)
    } else {
        sys.simulate_fast(args.max_steps)
    };

    match result {
        HaltCondition::Halted(steps, space) => {
            println!("Halted in {} steps! Max space reached: {}", steps, space);
        }
        HaltCondition::Infinite(reason, steps) => {
            let reason_str = match reason {
                InfiniteReason::Cycle(period) => format!("Exact cycle of period {}", period),
            };
            println!("Infinite in {} steps. Reason: {}", steps, reason_str);
        }
        HaltCondition::Unknown => {
            println!("Hit step limit of {}. (Holdout)", args.max_steps);
        }
        HaltCondition::UndefinedRule(c) => {
            println!("Hit undefined rule for symbol {}", c);
        }
    }
}
