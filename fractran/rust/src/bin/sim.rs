// Directly simulate one program, periodically printing config.

use fractran::parse::load_program;
use fractran::program::{Int, State};
use std::env;
use std::time::Instant;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("Usage: {} <programs_file>[:<record_num>]", args[0]);
        std::process::exit(1);
    }
    let filename_record = &args[1];
    let print_steps = 1_000_000_000;

    let prog = load_program(filename_record).expect("Couldn't load program from file");
    let mut state = State::start(&prog);
    let mut num_steps: Int = 0;
    let mut halted = false;

    println!(
        "Simulating program with {} rules and {} registers",
        prog.num_rules(),
        prog.num_registers()
    );
    let start = Instant::now();
    while !halted {
        let result = prog.run(&mut state, print_steps);
        num_steps += result.total_steps;
        halted = result.halted;
        println!(
            "Step: {}  {:?}  ({:.2}s)",
            num_steps,
            state,
            start.elapsed().as_secs_f64()
        );
    }
}
