pub mod enumerator;
pub mod parser;
pub mod simulator;
pub mod tm;

use clap::{Parser, Subcommand};
use simulator::SimResult;

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Simulate a specific TM
    Simulate {
        /// The TM string in Standard Text Format (e.g. 1RB1GC_1BC0RC)
        tm: String,

        /// The step limit
        #[arg(short, long)]
        steps: Option<u64>,

        /// Disable the stationary cycler decider (Brent's Algorithm)
        #[arg(long)]
        no_stationary: bool,

        /// Disable the translated cycler decider (Blank Subtree)
        #[arg(long)]
        no_translated: bool,

        /// Disable the no-path-to-halt decider
        #[arg(long)]
        no_nopath: bool,
    },
    /// Enumerate all TMs with a given number of states and symbols
    Enumerate {
        /// Number of states
        states: u8,

        /// Number of symbols (default 2)
        #[arg(short, long, default_value_t = 2)]
        symbols: u8,

        /// The step limit
        #[arg(short, long)]
        steps: u64,

        /// Optional file to output all generated TMs to
        #[arg(short, long)]
        output: Option<String>,

        /// Disable the stationary cycler decider (Brent's Algorithm)
        #[arg(long)]
        no_stationary: bool,

        /// Disable the translated cycler decider (Blank Subtree)
        #[arg(long)]
        no_translated: bool,

        /// Disable the no-path-to-halt decider
        #[arg(long)]
        no_nopath: bool,

        /// Time interval in seconds between progress updates
        #[arg(long, default_value_t = 10)]
        progress_interval: u64,
    },
}

fn main() {
    let cli = Cli::parse();

    match &cli.command {
        Commands::Simulate { tm, steps, no_stationary, no_translated, no_nopath } => {
            let turing_machine = match parser::parse_tm(tm) {
                Ok(tm) => tm,
                Err(e) => {
                    eprintln!("Failed to parse TM: {}", e);
                    std::process::exit(1);
                }
            };

            let options = simulator::DeciderOptions {
                stationary: !no_stationary,
                translated: !no_translated,
                nopath: !no_nopath,
            };
            let mut sim = simulator::Simulator::new(options);
            let step_limit = steps.unwrap_or(u64::MAX);
            let (result, transcript) = sim.run_with_transcript(&turing_machine, step_limit);

            let mut trans_str = String::new();
            if turing_machine.num_symbols == 2 {
                for (state, sym) in transcript {
                    let char_base = if sym == 0 { b'a' } else { b'A' };
                    trans_str.push((char_base + state) as char);
                }
            } else {
                for (state, sym) in transcript {
                    trans_str.push_str(&format!("{}{}", (b'A' + state) as char, sym));
                    trans_str.push(' ');
                }
            }

            println!("Transcript:\n{}", trans_str.trim_end());

            match result {
                SimResult::Halt(s, score) => {
                    println!("Halt {} {}", s, score);
                }
                SimResult::LimitReached => {
                    println!("Unknown");
                }
                SimResult::Infinite(simulator::InfReason::Stationary) => {
                    println!("Infinite (Stationary Cycler)");
                }
                SimResult::Infinite(simulator::InfReason::Translated) => {
                    println!("Infinite (Translated Cycler)");
                }
                SimResult::Infinite(simulator::InfReason::NoPath) => {
                    println!("Infinite (No Path)");
                }
                SimResult::UndefinedTrans => {
                    println!("Hit undefined transition");
                }
            }
        }
        Commands::Enumerate {
            states,
            symbols,
            steps,
            output,
            no_stationary,
            no_translated,
            no_nopath,
            progress_interval,
        } => {
            let mut num_halt = 0;
            let mut num_unknown = 0;
            let mut num_inf_stationary = 0;
            let mut num_inf_translated = 0;
            let mut num_inf_nopath = 0;
            let mut num_total = 0;
            let mut max_steps = 0;
            let mut max_steps_tms = Vec::new();
            let mut max_score = 0;
            let mut max_score_tms = Vec::new();
            let mut max_time = std::time::Duration::ZERO;
            
            let mut out_file = output.as_ref().map(|p| std::fs::File::create(p).unwrap());
            
            use std::io::Write;
            let (tx, rx) = std::sync::mpsc::channel();
            let options = simulator::DeciderOptions {
                stationary: !no_stationary,
                translated: !no_translated,
                nopath: !no_nopath,
            };
            enumerator::enumerate(*states, *symbols, *steps, options, tx);

            let start_time = std::time::Instant::now();
            let mut last_print_time = start_time;

            for (tm, result, duration) in rx {
                num_total += 1;
                if duration > max_time {
                    max_time = duration;
                }

                let tm_str = parser::tm_to_string(&tm);

                match result {
                    SimResult::Halt(s, score) => {
                        num_halt += 1;
                        if s > max_steps { 
                            max_steps = s; 
                            max_steps_tms.clear();
                            max_steps_tms.push(tm_str.clone());
                        } else if s == max_steps {
                            max_steps_tms.push(tm_str.clone());
                        }

                        if score > max_score { 
                            max_score = score; 
                            max_score_tms.clear();
                            max_score_tms.push(tm_str.clone());
                        } else if score == max_score {
                            max_score_tms.push(tm_str.clone());
                        }
                    }
                    SimResult::LimitReached => {
                        num_unknown += 1;
                    }
                    SimResult::Infinite(simulator::InfReason::Stationary) => {
                        num_inf_stationary += 1;
                    }
                    SimResult::Infinite(simulator::InfReason::Translated) => {
                        num_inf_translated += 1;
                    }
                    SimResult::Infinite(simulator::InfReason::NoPath) => {
                        num_inf_nopath += 1;
                    }
                    SimResult::UndefinedTrans => unreachable!(),
                }

                if let Some(f) = &mut out_file {
                    let out_str = match result {
                        SimResult::Halt(steps, score) => format!("Halt {} {}", steps, score),
                        SimResult::LimitReached => "Unknown Limit".to_string(),
                        SimResult::Infinite(simulator::InfReason::Stationary) => "Infinite Stationary".to_string(),
                        SimResult::Infinite(simulator::InfReason::Translated) => "Infinite Translated".to_string(),
                        SimResult::Infinite(simulator::InfReason::NoPath) => "Infinite NoPath".to_string(),
                        SimResult::UndefinedTrans => unreachable!(),
                    };
                    writeln!(f, "{} {}", tm_str, out_str).unwrap();
                }

                if last_print_time.elapsed().as_secs() >= *progress_interval {
                    last_print_time = std::time::Instant::now();
                    let pct_halt = if num_total > 0 {
                        (num_halt as f64 / num_total as f64) * 100.0
                    } else {
                        0.0
                    };
                    let pct_inf_stat = if num_total > 0 {
                        (num_inf_stationary as f64 / num_total as f64) * 100.0
                    } else {
                        0.0
                    };
                    let pct_inf_trans = if num_total > 0 {
                        (num_inf_translated as f64 / num_total as f64) * 100.0
                    } else {
                        0.0
                    };
                    let pct_inf_nopath = if num_total > 0 {
                        (num_inf_nopath as f64 / num_total as f64) * 100.0
                    } else {
                        0.0
                    };
                    let now = chrono::Local::now().format("%H:%M:%S").to_string();
                    let step_champ = max_steps_tms.first().map(|s| s.as_str()).unwrap_or("None");
                    let score_champ = max_score_tms.first().map(|s| s.as_str()).unwrap_or("None");
                    
                    println!(
                        "[{}] Total: {} | Halt: {} ({:.2}%) | InfStat: {} ({:.2}%) | InfTrans: {} ({:.2}%) | InfNoPath: {} ({:.2}%) | Max Steps: {} ({}) | Max Score: {} ({})",
                        now, num_total, num_halt, pct_halt, num_inf_stationary, pct_inf_stat, num_inf_translated, pct_inf_trans, num_inf_nopath, pct_inf_nopath, max_steps, step_champ, max_score, score_champ
                    );
                }
            }

            let total_elapsed = start_time.elapsed();
            let avg_time = if num_total > 0 {
                total_elapsed / num_total as u32
            } else {
                std::time::Duration::ZERO
            };

            println!("--- Enumeration Complete ---");
            println!("Total TMs generated : {}", num_total);
            let pct_halt_final = (num_halt as f64 / num_total as f64) * 100.0;
            let num_infinite = num_inf_stationary + num_inf_translated + num_inf_nopath;
            let pct_inf_final = (num_infinite as f64 / num_total as f64) * 100.0;
            let pct_inf_stat_final = (num_inf_stationary as f64 / num_total as f64) * 100.0;
            let pct_inf_trans_final = (num_inf_translated as f64 / num_total as f64) * 100.0;
            let pct_inf_nopath_final = (num_inf_nopath as f64 / num_total as f64) * 100.0;
            let pct_unknown_final = (num_unknown as f64 / num_total as f64) * 100.0;
            println!("Halted              : {} ({:.2}%)", num_halt, pct_halt_final);
            println!("Infinite            : {} ({:.2}%)", num_infinite, pct_inf_final);
            println!("  Stationary        : {} ({:.2}%)", num_inf_stationary, pct_inf_stat_final);
            println!("  Translated        : {} ({:.2}%)", num_inf_translated, pct_inf_trans_final);
            println!("  No Path           : {} ({:.2}%)", num_inf_nopath, pct_inf_nopath_final);
            println!("Unknown (Limit)     : {} ({:.2}%)", num_unknown, pct_unknown_final);
            println!("Max Halt Steps      : {}", max_steps);
            if !max_steps_tms.is_empty() {
                println!("Max Steps TMs       :");
                for (i, t) in max_steps_tms.iter().take(5).enumerate() {
                    println!("  {}", t);
                }
                if max_steps_tms.len() > 5 {
                    println!("  ... and {} more", max_steps_tms.len() - 5);
                }
            }

            println!("Max Halt Score      : {}", max_score);
            if !max_score_tms.is_empty() {
                println!("Max Score TMs       :");
                for (i, t) in max_score_tms.iter().take(5).enumerate() {
                    println!("  {}", t);
                }
                if max_score_tms.len() > 5 {
                    println!("  ... and {} more", max_score_tms.len() - 5);
                }
            }

            println!("Total Wallclock Time: {:?}", total_elapsed);
            println!("Avg Time per TM     : {:?}", avg_time);
            println!("Max Time for a TM   : {:?}", max_time);
        }
    }
}
