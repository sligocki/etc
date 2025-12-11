// Simulate program printing out transcript and experimenting with transcript compression.

use std::collections::HashSet;

use clap::Parser;

use fractran::diff_rule::DiffRule;
use fractran::parse::load_program;
use fractran::program::{Int, State};
use fractran::tandem_repeat::{find_rep_blocks, RepBlock, ToStringVec};
use fractran::transcript::{strip_reps, transcript, Trans};

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    /// Filename with optional record number (0-indexed, defaults to 0).
    #[arg(value_name = "FILE[:NUM]")]
    filename_record: String,

    /// Number of TM steps to run simulation for.
    num_steps: Int,
}

fn main() {
    let args = Args::parse();

    let prog = load_program(&args.filename_record).expect("Couldn't load program from file");
    let state = State::start(&prog);

    println!(
        "Simulating program with {} instrs and {} registers",
        prog.num_instrs(),
        prog.num_registers()
    );

    // Load sequence of transitions ("transcript")
    let trans_vec = transcript(&prog, state, args.num_steps);

    // Find repeated patterns in transcript
    let rep_blocks = find_rep_blocks(&trans_vec);
    println!(
        "Compressed Transcript: {}",
        RepBlock::to_string_vec(&rep_blocks)
    );
    println!();

    // Print rules
    let seqs: HashSet<&Vec<Trans>> = rep_blocks
        .iter()
        .filter(|r| r.rep != 1)
        .map(|r| &r.block)
        .collect();
    for seq in seqs.iter() {
        println!("Seq: {}", Trans::to_string_vec(seq));
        let rule = DiffRule::from_trans_vec(&prog, seq).unwrap();
        println!("Rule: {}", rule);
    }
    println!();

    // Find higher level repeated patterns in rep_blocks
    let block_pattern = strip_reps(rep_blocks);
    let meta_rep_blocks = find_rep_blocks(&block_pattern);
    println!(
        "Compressed Transcript: {}",
        RepBlock::to_string_vec(&meta_rep_blocks)
    );
    println!();
}
