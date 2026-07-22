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

    /// Print the tape at each step
    #[arg(short, long)]
    verbose: bool,
}

fn main() {
    let args = Args::parse();

    let sys = TagSystem::parse(2, &args.rules);

    println!("Simulating: {}", sys.format_rules());

    let mut tape = vec![0u8; sys.v];
    let mut head_idx = 0;
    let mut steps = 0;

    while tape.len() - head_idx >= sys.v && steps < args.max_steps {
        if args.verbose {
            print!("Step {}: Tape ", steps);
            for i in head_idx..tape.len() {
                print!("{}", tape[i]);
            }
            println!();
        }

        let head = tape[head_idx];
        head_idx += sys.v;
        steps += 1;

        match &sys.rules[head as usize] {
            Some(rule) => {
                for &c in rule {
                    tape.push(c);
                }
            }
            None => {
                println!(
                    "Halted at step {}: Undefined rule for symbol {}",
                    steps, head
                );
                return;
            }
        }

        if head_idx > 1_000_000 {
            tape.drain(0..head_idx);
            head_idx = 0;
        }
    }

    if tape.len() - head_idx < sys.v {
        println!(
            "Halted in {} steps. Space: {}",
            steps,
            tape.len() - head_idx
        );
    } else {
        println!("Hit step limit of {}.", args.max_steps);
    }
}
