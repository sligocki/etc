// Simulate program printing out transcript and experimenting with transcript compression.

use fractran::parse::load_program;
use fractran::program::{Int, State};
use fractran::tandem_repeat::{find_repeats, RepeatInfo};
use fractran::transcript::{transcript, Trans};
use std::env;

const OFFSET: u8 = 'A' as u8;
fn trans_str(trans: &Trans) -> char {
    let rule_num = trans.reg_fail.len() as u8;
    (OFFSET + rule_num) as char
}

fn trans_vec_str(span: &[Trans]) -> String {
    span.iter().map(trans_str).collect()
}

fn compressed_str(trans: &Vec<Trans>, repeats: &Vec<RepeatInfo>) -> String {
    let mut ret = String::new();
    let mut n = 0;
    for repeat in repeats.iter() {
        if repeat.start > n {
            ret.push_str(&trans_vec_str(&trans[n..repeat.start]));
            ret.push('\n');
        }
        let segment = &trans[repeat.start..repeat.start + repeat.period];
        ret.push_str(&format!("{}^{}\n", &trans_vec_str(segment), repeat.count));
        n = repeat.start + repeat.period * repeat.count;
    }
    if n < trans.len() {
        ret.push_str(&trans_vec_str(&trans[n..]));
    }
    ret
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 3 {
        eprintln!(
            "Usage: {} <programs_file>[:<record_num>] <num_steps>",
            args[0]
        );
        std::process::exit(1);
    }
    let filename_record = &args[1];
    let num_steps: Int = args[2].parse().expect("Invalid step count provided");

    let prog = load_program(filename_record).expect("Couldn't load program from file");
    let state = State::start(&prog);

    println!(
        "Simulating program with {} rules and {} registers",
        prog.num_rules(),
        prog.num_registers()
    );

    let trans_vec = transcript(&prog, state, num_steps);
    let repeats = find_repeats(&trans_vec);
    // println!("# Repeats: {}", repeats.len());
    // for repeat in repeats.iter() {
    //   println!("  start={}  period={}  count={}", repeat.start, repeat.period, repeat.count);
    // }
    println!("{}", compressed_str(&trans_vec, &repeats));
}
