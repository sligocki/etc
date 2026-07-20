use clap::Parser;
use post_tag::enumerate::enumerate_systems;
use post_tag::simulate::HaltCondition;
use post_tag::tag_system::TagSystem;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Max size to search up to
    max_s: usize,

    /// Deletion number
    #[arg(long = "del", default_value_t = 2)]
    v: usize,

    /// Max steps before classifying as holdout
    #[arg(long, default_value_t = 1_000_000)]
    max_steps: usize,
}

fn main() {
    let args = Args::parse();

    println!("Computing BB_PT(v={}, S) up to S={}", args.v, args.max_s);

    for s in 1..=args.max_s {
        let mut total = 0;
        let mut max_halt_steps = 0;
        let mut best_step_sys: Option<TagSystem> = None;
        let mut max_halt_space = 0;
        let mut best_space_sys: Option<TagSystem> = None;
        let mut holdouts = 0;
        let mut infinite = 0; // We don't have exact cycle detection yet

        enumerate_systems(args.v, s, &mut |sys| {
            total += 1;
            match sys.simulate_fast(args.max_steps) {
                HaltCondition::Halted(steps, space) => {
                    if steps > max_halt_steps {
                        max_halt_steps = steps;
                        best_step_sys = Some(sys.clone());
                    }
                    if space > max_halt_space {
                        max_halt_space = space;
                        best_space_sys = Some(sys.clone());
                    }
                }
                HaltCondition::Infinite => {
                    holdouts += 1;
                }
            }
        });

        let halting = total - holdouts - infinite;
        println!("\n=== S={} ===", s);
        println!(
            "Total: {}, Halting: {}, Infinite: {}, Holdouts: {}",
            total, halting, infinite, holdouts
        );

        if let Some(sys) = best_step_sys {
            println!("  BB_PT Time  : {} steps by {}", max_halt_steps, sys.format_rules());
        } else {
            println!("  BB_PT Time  : 0 (No systems halted!)");
        }
        if let Some(sys) = best_space_sys {
            println!("  BB_PT Space : {} length by {}", max_halt_space, sys.format_rules());
        }
    }
}
