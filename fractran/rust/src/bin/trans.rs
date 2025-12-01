// Simulate program printing out transcript and experimenting with transcript compression.

use std::collections::HashSet;

use clap::Parser;

use fractran::parse::load_program;
use fractran::program::{Int, State};
use fractran::tandem_repeat::{as_rep_blocks, RepBlock};
use fractran::transcript::{transcript, DiffRule, Trans};

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    /// Filename with optional record number (0-indexed, defaults to 0).
    #[arg(value_name = "FILE[:NUM]")]
    filename_record: String,

    /// Number of TM steps to run simulation for.
    num_steps: Int,
}

const OFFSET: u8 = 'A' as u8;
fn trans_str(trans: &Trans) -> char {
    let rule_num = trans.reg_fail.len() as u8;
    (OFFSET + rule_num) as char
}

fn trans_vec_str(span: &[Trans]) -> String {
    span.iter().map(trans_str).collect()
}

fn compressed_str(rep_blocks: &Vec<RepBlock<Trans>>) -> String {
    let mut ret = String::new();
    for rep_block in rep_blocks.iter() {
        ret.push_str(&trans_vec_str(&rep_block.block));
        if rep_block.rep != 1 {
            ret.push_str(&format!("^{}", rep_block.rep));
        }
        ret.push(' ');
    }
    ret
}

fn main() {
    let args = Args::parse();

    let prog = load_program(&args.filename_record).expect("Couldn't load program from file");
    let state = State::start(&prog);

    println!(
        "Simulating program with {} rules and {} registers",
        prog.num_rules(),
        prog.num_registers()
    );

    let trans_vec = transcript(&prog, state, args.num_steps);
    let rep_blocks = as_rep_blocks(&trans_vec);
    println!("{}", compressed_str(&rep_blocks));
    println!();

    // Print rules
    let seqs: HashSet<&Vec<Trans>> = rep_blocks
        .iter()
        .filter(|r| r.rep != 1)
        .map(|r| &r.block)
        .collect();
    for seq in seqs.iter() {
        println!("Seq: {}", trans_vec_str(seq));
        let rule = DiffRule::from_trans_vec(&prog, seq).unwrap();
        println!("Rule: {}", rule);
    }
}
