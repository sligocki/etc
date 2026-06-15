pub mod ast;
pub mod simulator;
pub mod enumerator;

use clap::Parser;
use rayon::prelude::*;
use crate::simulator::{Simulator, RunResult};
use crate::enumerator::enumerate_programs;
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
    println!("Enumerating all canonical programs of length {}...", args.length);
    let start_enum = Instant::now();
    let programs = enumerate_programs(args.length);
    println!("Found {} valid canonical programs. Enumeration took {:?}", programs.len(), start_enum.elapsed());

    println!("Simulating with max steps {}...", args.max_steps);
    let start_sim = Instant::now();

    // Use par_iter for parallel execution
    let results: Vec<(RunResult, &Vec<Instr>)> = programs.par_iter().map(|prog| {
        let mut sim = Simulator::new();
        let res = sim.run(prog, args.max_steps);
        (res, prog)
    }).collect();

    let mut halted = 0;
    let mut timeouts = 0;
    let mut max_score = 0;
    let mut champion: Option<&Vec<Instr>> = None;

    for (res, prog) in results {
        match res {
            RunResult::Halted { score } => {
                halted += 1;
                if score > max_score || champion.is_none() {
                    max_score = score;
                    champion = Some(prog);
                }
            }
            RunResult::Timeout => {
                timeouts += 1;
            }
        }
    }

    println!("Simulation took {:?}", start_sim.elapsed());
    println!("--- Results ---");
    println!("Total Programs: {}", programs.len());
    println!("Halted:         {}", halted);
    println!("Timeouts:       {}", timeouts);
    println!("Max Score:      {}", max_score);
    if let Some(champ) = champion {
        println!("Champion Code:  {}", format_program(champ));
    }
}
