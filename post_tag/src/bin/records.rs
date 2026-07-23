use clap::Parser;
use post_tag::tag_system::TagSystem;
use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::PathBuf;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// The tag system rules (e.g. 00110_)
    rules: String,

    /// Maximum number of steps to simulate
    #[arg(short, long, default_value_t = 10_000_000)]
    max_steps: usize,

    /// Max active tape size limit
    #[arg(long, default_value_t = 1_000_000)]
    max_space: usize,

    /// Output CSV file path
    #[arg(short, long)]
    out: Option<PathBuf>,

    /// Sampling rate (output every N steps, rather than only high-water marks). If 0, only outputs high-water marks.
    #[arg(long, default_value_t = 0)]
    sample_rate: usize,
}

fn main() {
    let args = Args::parse();

    let resolved_rules = post_tag::file_io::resolve_program_string(&args.rules);
    let sys = TagSystem::parse(2, &resolved_rules);

    println!("Simulating to record high-water marks: {}", sys.format_rules());

    let mut sim = post_tag::simulate::Simulator::new(&sys);
    
    let mut records: Vec<(usize, usize)> = Vec::new();
    let mut max_seen_len = 0;

    while sim.true_length >= sys.v && sim.steps < args.max_steps {
        let current_len = sim.tape.len() - sim.head_idx;
        
        if current_len > args.max_space {
            println!("Hit space limit of {} at step {}.", args.max_space, sim.steps);
            break;
        }

        if current_len > max_seen_len {
            max_seen_len = current_len;
            if args.sample_rate == 0 {
                records.push((sim.steps, current_len));
            }
        }

        if args.sample_rate > 0 && sim.steps % args.sample_rate == 0 {
            records.push((sim.steps, current_len));
        }

        if let Some(cond) = sim.step(false, false) {
            println!("Halted at step {}: {:?}", sim.steps, cond);
            break;
        }
    }

    if sim.true_length < sys.v {
        println!("Halted in {} steps. Space: {}", sim.steps, sim.max_len);
    } else if sim.tape.len() - sim.head_idx > args.max_space {
        // already printed
    } else {
        println!("Hit step limit of {} at step {}.", args.max_steps, sim.steps);
    }

    if records.len() > 10 {
        let start_idx = records.len() / 2; // Ignore initial transient
        let tail = &records[start_idx..];

        let mut sum_x = 0.0;
        let mut sum_y = 0.0;
        let n = tail.len() as f64;

        for &(step, len) in tail {
            // step > 0 because it's the tail
            sum_x += (step as f64).ln();
            sum_y += if len > 0 { (len as f64).ln() } else { 0.0 };
        }

        let mean_x = sum_x / n;
        let mean_y = sum_y / n;

        let mut num = 0.0;
        let mut den = 0.0;
        for &(step, len) in tail {
            let dx = (step as f64).ln() - mean_x;
            let dy = (if len > 0 { (len as f64).ln() } else { 0.0 }) - mean_y;
            num += dx * dy;
            den += dx * dx;
        }

        if den > 1e-9 {
            let slope = num / den;
            println!("Estimated growth rate: O(N^{:.2})", slope);
            if (slope - 1.0).abs() < 0.15 {
                println!("-> Looks like LINEAR growth.");
            } else if (slope - 2.0).abs() < 0.15 {
                println!("-> Looks like QUADRATIC growth.");
            } else if (slope - 0.5).abs() < 0.15 {
                println!("-> Looks like SQUARE ROOT growth.");
            } else {
                println!("-> Non-standard polynomial growth.");
            }
        }
    }

    if let Some(out_path) = args.out {
        println!("Writing {} records to {:?}", records.len(), out_path);
        let file = File::create(&out_path).expect("Failed to create output file");
        let mut writer = BufWriter::new(file);
        writeln!(writer, "step,tape_size").unwrap();
        for (step, len) in &records {
            writeln!(writer, "{},{}", step, len).unwrap();
        }
    } else {
        println!("Records (step, tape_size):");
        for (step, len) in &records {
            println!("{},{}", step, len);
        }
    }
}
