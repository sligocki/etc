use clap::Parser;
use post_tag::simulate::{simulate, HaltCondition, InfiniteReason};
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

fn main() {
    let args = Args::parse();
    let sys = TagSystem::parse(args.v, &args.rules);
    
    println!("Simulating: {}", sys.format_rules());
    
    let result = simulate(&sys, args.max_steps, args.verbose);

    match result {
        HaltCondition::Halted(steps, space) => {
            println!("Halted in {} steps! Max space reached: {}", steps, space);
        }
        HaltCondition::Infinite(reason, steps) => {
            let reason_str = match reason {
                InfiniteReason::Cycle(period) => format!("Exact cycle of period {}", period),
                InfiniteReason::ImmortalSubstring(ref w) => {
                    let mut s = String::new();
                    for &c in w {
                        s.push_str(&c.to_string());
                    }
                    format!("Immortal substring detected: {}", s)
                },
                InfiniteReason::NonDecreasingSymbol(c) => format!("Number of symbol {} never decreases", c),
                InfiniteReason::ClosedSymbol(c) => format!("Symbol {} is closed (perfectly aligns and only outputs {})", c, c),
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
