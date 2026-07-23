use clap::Parser;
use post_tag::tag_system::TagSystem;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// The tag system rules (e.g. 00110_)
    rules: String,

    /// Maximum number of steps to simulate
    #[arg(short, long, default_value_t = 10_000)]
    max_steps: usize,

    /// Max active tape size limit
    #[arg(long, default_value_t = 1_000_000)]
    max_space: usize,

    /// Print the tape at each step
    #[arg(short, long)]
    verbose: bool,

    /// Print symbol distribution at each step
    #[arg(short, long)]
    distribution: bool,
}

fn main() {
    let args = Args::parse();

    let resolved_rules = post_tag::file_io::resolve_program_string(&args.rules);
    let sys = TagSystem::parse(2, &resolved_rules);

    println!("Simulating: {}", sys.format_rules());

    let mut sim = post_tag::simulate::Simulator::new(&sys);

    while sim.true_length >= sys.v && sim.steps < args.max_steps {
        if sim.tape.len() - sim.head_idx > args.max_space {
            break;
        }
        if args.verbose || args.distribution {
            if args.distribution {
                let current_len = sim.tape.len() - sim.head_idx;
                let counts = &sim.symbol_counts;
                
                print!("Step {}: (", sim.steps);
                for i in 0..sys.rules.len() {
                    let pct = if current_len > 0 {
                        (counts[i] as f64 / current_len as f64) * 100.0
                    } else {
                        0.0
                    };
                    if i > 0 {
                        print!(", ");
                    }
                    print!("{:.1}%", pct);
                }
                print!(") ActiveTape ");
            } else {
                print!("Step {}: ActiveTape ", sim.steps);
            }
            for i in sim.head_idx..sim.tape.len() {
                print!("{}", sim.tape[i]);
            }
            println!(" (phase {})", sim.true_length % sys.v);
        }

        if let Some(cond) = sim.step(false, false) {
            println!("Halted at step {}: {:?}", sim.steps, cond);
            return;
        }
    }

    if sim.true_length < sys.v {
        println!(
            "Halted in {} steps. Space: {}",
            sim.steps,
            sim.max_len
        );
    } else if sim.tape.len() - sim.head_idx > args.max_space {
        println!("Hit space limit of {}.", args.max_space);
    } else {
        println!("Hit step limit of {}.", args.max_steps);
    }
}
