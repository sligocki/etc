// Directly simulate one program, periodically printing config.

use std::time::Instant;

use clap::Parser;

use fractran::parse::load_program;
use fractran::program::{Int, State};

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    /// Filename with optional record number (0-indexed, defaults to 0).
    #[arg(value_name = "FILE[:NUM]")]
    filename_record: String,

    #[arg(default_value_t = 100_000_000)]
    print_steps: Int,
}

fn main() {
    let args = Args::parse();

    let prog = load_program(&args.filename_record).expect("Couldn't load program from file");
    let mut state = State::start(&prog);
    let mut num_steps: Int = 0;
    let mut halted = false;

    println!(
        "Simulating program with {} instrs and {} registers",
        prog.num_instrs(),
        prog.num_registers()
    );
    let start = Instant::now();
    while !halted {
        let result = prog.run(&mut state, args.print_steps);
        num_steps += result.total_steps;
        halted = result.halted;
        println!(
            "Step: {}  {:?}  ({:.2}s)",
            num_steps,
            state,
            start.elapsed().as_secs_f64()
        );
    }

    println!("Halted at step: {}", num_steps)
}
