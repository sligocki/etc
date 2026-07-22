use clap::Parser;
use post_tag::file_io::{read_unknowns, write_result};
use post_tag::simulate::simulate;
use post_tag::tag_system::TagSystem;
use std::fs::File;
use std::io::BufWriter;
use std::path::PathBuf;
use std::time::Instant;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Input file
    input: PathBuf,

    /// Max steps
    max_steps: usize,

    /// Output file
    output: PathBuf,
}

fn main() {
    let args = Args::parse();

    let unknowns = match read_unknowns(&args.input) {
        Ok(u) => u,
        Err(e) => {
            eprintln!("Error reading input file: {}", e);
            std::process::exit(1);
        }
    };

    println!("Found {} Unknown programs in {:?}", unknowns.len(), args.input);

    let mut out_file = BufWriter::new(File::create(&args.output).unwrap());
    
    let start_time = Instant::now();

    for prog_str in &unknowns {
        let sys = TagSystem::parse(2, prog_str);
        let result = simulate(&sys, args.max_steps, false);
        write_result(&mut out_file, &sys, &result).unwrap();
        
        // Print progress
        println!("{} -> {:?}", prog_str, result);
    }
    
    let elapsed = start_time.elapsed();
    println!("\nDone. Simulated {} programs in {:.3}s.", unknowns.len(), elapsed.as_secs_f64());
    println!("Wrote results to {:?}", args.output);
}
