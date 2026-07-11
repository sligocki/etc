// Simulate one program with accelerated ShfitSim, periodically printing config.

use std::time::Instant;

use clap::Parser;

use fractran::parse::load_program;
use fractran::program::State;
use fractran::shift_sim::{ShiftSim, SimStatus, find_shift_rules};

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    /// Filename with optional record number (0-indexed, defaults to 0).
    #[arg(value_name = "FILE[:NUM]")]
    filename_record: String,

    #[arg(default_value_t = 1_000_000)]
    print_steps: usize,

    #[arg(long, default_value_t = 1_000)]
    transcript_steps: usize,

    #[arg(long, default_value_t = 100_000)]
    check_interval: usize,
}

fn main() {
    let start = Instant::now();
    let args = Args::parse();

    let prog = load_program(&args.filename_record).expect("Couldn't load program from file");
    let mut state = State::start(&prog);

    let shift_rules = find_shift_rules(&prog, state.clone(), args.transcript_steps);
    println!("Discovered {} shift rules", shift_rules.len());

    let mut sim = ShiftSim::new(prog, shift_rules);
    if args.check_interval > 0 {
        sim.set_dynamic_updates(args.transcript_steps, args.check_interval);
    }

    while sim.status == SimStatus::Running {
        let old_rules_len = sim.shift_rules.len();
        state = sim.run(state, args.print_steps);
        let new_rules_len = sim.shift_rules.len();

        if new_rules_len > old_rules_len {
            println!(
                "Dynamically discovered {} new shift rules (total: {})",
                new_rules_len - old_rules_len,
                new_rules_len
            );
        }

        println!(
            "Sim Step: {}  {:?}  ({:.2}s)",
            sim.sim_steps,
            state,
            start.elapsed().as_secs_f64()
        );
    }

    println!("Status: {:?}", sim.status);
    println!("Sim Steps: {}", sim.sim_steps);
    println!("Num Rule Steps: {}", sim.num_shift_steps);
    println!("Base Steps: {}", sim.base_steps);
}
