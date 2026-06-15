pub mod ast;
pub mod simulator;
pub mod enumerator;

use clap::Parser;
use crate::enumerator::search_programs;
use crate::ast::format_program;
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

    /// Output file to save simulation results
    #[arg(short, long)]
    output: Option<String>,
}

fn main() {
    let args = Args::parse();
    println!("Streaming and simulating all canonical programs of length {} with max steps {}...", args.length, args.max_steps);
    let start_time = Instant::now();

    let results = search_programs(args.length, args.max_steps, args.output);

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
