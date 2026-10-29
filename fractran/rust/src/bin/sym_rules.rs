use std::time::Instant;

use clap::Parser;
use indicatif::ParallelProgressIterator;
use rayon::prelude::*;

use fractran::parse::{load_lines, load_program, parse_program};
use fractran::symbolic::{
    AnalyzerConfig, ConfigSpec, DecisionStatus, analyze_program_auto, analyze_with_spec,
};

#[derive(Parser, Debug)]
#[command(
    version,
    about = "Symbolic dynamical-system rule analyzer and decider for FRACTRAN programs"
)]
struct Args {
    /// Program string (e.g. "[1/15, 27/77, 49/3, 10/49, 33/2]") or filename[:record]
    #[arg(value_name = "PROG_OR_FILE")]
    input: String,

    /// Optional explicit ConfigSpec (e.g. "[x, 0, 0, 2, y]")
    #[arg(long)]
    spec: Option<String>,

    /// Analyze all programs in the input file in batch mode
    #[arg(long)]
    all: bool,

    /// Maximum symbolic branches to explore before giving up
    #[arg(long, default_value_t = 64)]
    max_branches: usize,

    /// Maximum steps per symbolic branch
    #[arg(long, default_value_t = 200)]
    max_steps: usize,

    /// Maximum modulus when splitting parameters for shift rules
    #[arg(long, default_value_t = 16)]
    max_modulus: i64,

    /// Number of simulation steps for shift-rule & ConfigSpec discovery
    #[arg(long, default_value_t = 2000)]
    transcript_steps: usize,
}

fn main() {
    let args = Args::parse();
    let config = AnalyzerConfig {
        max_branches: args.max_branches,
        max_steps_per_branch: args.max_steps,
        max_modulus: args.max_modulus,
        transcript_steps: args.transcript_steps,
    };

    if args.all {
        let lines = load_lines(&args.input);
        println!(
            "Analyzing {} programs from {}...",
            lines.len(),
            args.input
        );
        let start = Instant::now();

        let results: Vec<(String, Option<_>)> = lines
            .par_iter()
            .progress_count(lines.len() as u64)
            .map(|line| {
                let prog_str = line.split('\t').next().unwrap_or(line);
                let prog = parse_program(prog_str);
                let res = analyze_program_auto(&prog, &config);
                (prog_str.to_string(), res)
            })
            .collect();

        let mut proven_non_halting = 0;
        let mut proven_halting = 0;
        let mut complete_inductive = 0;
        let mut incomplete = 0;

        for (prog_str, res_opt) in &results {
            match res_opt {
                Some(res) => match res.status {
                    DecisionStatus::ProvenNonHalting => {
                        proven_non_halting += 1;
                        println!("NON-HALTING: {}\t({})", prog_str, res.spec);
                    }
                    DecisionStatus::ProvenHalting => {
                        proven_halting += 1;
                        println!("HALTING:     {}\t({})", prog_str, res.spec);
                    }
                    DecisionStatus::InductiveSystemComplete => {
                        complete_inductive += 1;
                        println!(
                            "COMPLETE:    {}\t({}, {} rules)",
                            prog_str,
                            res.spec,
                            res.rules.len()
                        );
                    }
                    DecisionStatus::Incomplete(_) => {
                        incomplete += 1;
                    }
                },
                None => {
                    incomplete += 1;
                }
            }
        }

        println!(
            "\nBatch analysis completed in {:.2}s:",
            start.elapsed().as_secs_f64()
        );
        println!("  Proven Non-Halting:        {}", proven_non_halting);
        println!("  Proven Halting:            {}", proven_halting);
        println!("  Complete Inductive System: {}", complete_inductive);
        println!("  Incomplete / Unknown:      {}", incomplete);
        return;
    }

    let prog = load_program(&args.input).expect("Failed to load FRACTRAN program");
    let start = Instant::now();

    if let Some(spec_str) = &args.spec {
        let spec: ConfigSpec = spec_str.parse().expect("Invalid ConfigSpec format");
        let result = analyze_with_spec(&prog, &spec, &config);
        print!("{}", result);
    } else {
        match analyze_program_auto(&prog, &config) {
            Some(result) => {
                print!("{}", result);
            }
            None => {
                println!("Could not automatically discover a recurring ConfigSpec.");
            }
        }
    }
    println!("(Analyzed in {:.3}s)", start.elapsed().as_secs_f64());
}
