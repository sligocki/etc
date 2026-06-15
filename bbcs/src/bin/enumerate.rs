use bbcs::enumerator::search_programs;
use clap::Parser;
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

    /// How often to print progress in seconds
    #[arg(short, long, default_value_t = 10)]
    progress: u64,
}

fn main() {
    let args = Args::parse();
    println!(
        "Streaming and simulating all canonical programs of length {} with max steps {}...",
        args.length, args.max_steps
    );
    let start_time = Instant::now();

    let results = search_programs(args.length, args.max_steps, args.output, args.progress);

    println!("Completed in {:?}", start_time.elapsed());
    println!("--- Results ---");
    println!("Total Programs: {}", results.total);
    println!("Halted:         {}", results.halted);
    println!("Timeouts:       {}", results.timeouts);
    println!("Inf (Stat):     {}", results.infinites_stationary);
    println!("Inf (Trans):    {}", results.infinites_translated);
    println!("Inf (Symbolic): {}", results.infinites_symbolic);
    println!("Inf (Sum):      {}", results.infinites_sum);
    println!("Max Score:      {}", results.max_score);
    println!("Max Steps:      {}", results.max_halting_steps);
    if !results.champion_code.is_empty() {
        println!("Champion Code:  {}", results.champion_code);
    }
}


#[test]
fn test_sim_prog1_prog2() {
    use crate::simulator::*;
    use crate::ast::*;
    
    // Prog 1: A++; A++; while A { A--; while B { A--; A++; B--; } B++; C++; }
    let prog1 = vec![
        Instr::Inc(0), Instr::Inc(0),
        Instr::While(0, vec![
            Instr::Dec(0),
            Instr::While(1, vec![
                Instr::Dec(0), Instr::Inc(0), Instr::Dec(1)
            ]),
            Instr::Inc(1),
            Instr::Inc(2)
        ])
    ];

    // Prog 2: A++; A++; while A { A--; B++; while C { A--; A++; C--; } C++; }
    let prog2 = vec![
        Instr::Inc(0), Instr::Inc(0),
        Instr::While(0, vec![
            Instr::Dec(0),
            Instr::Inc(1),
            Instr::While(2, vec![
                Instr::Dec(0), Instr::Inc(0), Instr::Dec(2)
            ]),
            Instr::Inc(2)
        ])
    ];

    let mut sim = Simulator::new();
    println!("Prog 1 result: {:?}", sim.run(&prog1, 1000));
    println!("Prog 2 result: {:?}", sim.run(&prog2, 1000));
    
    // User's program: A++; A++; while A { A--; while B { A--; A++; B--; C++; } B++; }
    let prog_user = vec![
        Instr::Inc(0), Instr::Inc(0),
        Instr::While(0, vec![
            Instr::Dec(0),
            Instr::While(1, vec![
                Instr::Dec(0), Instr::Inc(0), Instr::Dec(1), Instr::Inc(2)
            ]),
            Instr::Inc(1),
        ])
    ];
    println!("Prog user result: {:?}", sim.run(&prog_user, 1000));
}
