pub mod ast;
pub mod simulator;
pub mod enumerator;

use clap::Parser;
use crate::enumerator::search_programs;
use crate::ast::Instr;
use std::time::Instant;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// The length of programs to search
    #[arg(short, long)]
    length: usize,

    /// Maximum steps for the simulator before timing out
    #[arg(short, long)]
    max_steps: usize,
}

fn var_name(v: usize) -> String {
    if v < 26 {
        ((b'A' + v as u8) as char).to_string()
    } else {
        format!("V{}", v)
    }
}

fn format_program(program: &[Instr]) -> String {
    let mut parts = Vec::new();
    for instr in program {
        match instr {
            Instr::Inc(v) => parts.push(format!("{}++;", var_name(*v))),
            Instr::Dec(v) => parts.push(format!("{}--;", var_name(*v))),
            Instr::While(v, body) => {
                parts.push(format!("while {} {{ {} }}", var_name(*v), format_program(body)));
            }
        }
    }
    parts.join(" ")
}

fn main() {
    let args = Args::parse();
    println!("Streaming and simulating all canonical programs of length {} with max steps {}...", args.length, args.max_steps);
    let start_time = Instant::now();

    let results = search_programs(args.length, args.max_steps);

    println!("Completed in {:?}", start_time.elapsed());
    println!("--- Results ---");
    println!("Total Programs: {}", results.total);
    println!("Halted:         {}", results.halted);
    println!("Timeouts:       {}", results.timeouts);
    println!("Max Score:      {}", results.max_score);
    if let Some(champ) = results.champion {
        println!("Champion Code:  {}", format_program(&champ));
    }
}
