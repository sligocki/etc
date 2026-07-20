use clap::Parser;
use post_tag::simulate::HaltCondition;
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
}

fn parse_rules(s: &str) -> Vec<Vec<u8>> {
    let mut rules = Vec::new();
    for part in s.split(',') {
        let part = part.trim();
        if part.is_empty() {
            continue;
        }
        if let Some((lhs, rhs)) = part.split_once("->") {
            let lhs: usize = lhs.trim().parse().unwrap();
            while rules.len() <= lhs {
                rules.push(vec![]);
            }
            let rhs = rhs.trim();
            if rhs == "eps" {
                rules[lhs] = vec![];
            } else {
                let mut rv = vec![];
                for c in rhs.chars() {
                    rv.push(c.to_digit(10).unwrap() as u8);
                }
                rules[lhs] = rv;
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
    
    match sys.simulate_fast(args.max_steps) {
        HaltCondition::Halted(steps, space) => {
            println!("Halted in {} steps! Max space reached: {}", steps, space);
        }
        HaltCondition::Infinite => {
            println!("Hit step limit of {}. (Holdout)", args.max_steps);
        }
    }
}
