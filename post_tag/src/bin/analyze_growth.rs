use clap::Parser;
use post_tag::tag_system::TagSystem;
use std::collections::HashMap;
use std::fs::File;
use std::io::{BufRead, BufReader, BufWriter, Write};
use std::path::PathBuf;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Input .ptl file
    input: PathBuf,

    /// Maximum number of steps to simulate
    #[arg(short, long, default_value_t = 10_000_000)]
    max_steps: usize,

    /// Max active tape size limit
    #[arg(long, default_value_t = 1_000_000)]
    max_space: usize,

    /// Output CSV file path
    #[arg(short, long)]
    out: PathBuf,
}

fn main() {
    let args = Args::parse();

    let file = File::open(&args.input).expect("Failed to open input file");
    let reader = BufReader::new(file);

    let out_file = File::create(&args.out).expect("Failed to create output file");
    let mut writer = BufWriter::new(out_file);

    writeln!(writer, "prog,status,final_size,shrink_rate,max_drawdown,p,r_squared,hw_p,hw_r_squared,category").unwrap();

    let mut category_map: HashMap<String, Vec<String>> = HashMap::new();
    let mut total_programs = 0;

    for line in reader.lines() {
        let line = line.unwrap();
        if line.trim().is_empty() {
            continue;
        }

        // Parse program from line, looking for "prog="
        let prog_str = if let Some(idx) = line.find("prog=") {
            let start = idx + 5;
            let end = line[start..].find(' ').map(|i| start + i).unwrap_or(line.len());
            &line[start..end]
        } else {
            line.split(' ').next().unwrap()
        };

        let resolved_rules = post_tag::file_io::resolve_program_string(prog_str);
        let sys = TagSystem::parse(2, &resolved_rules);
        let mut sim = post_tag::simulate::Simulator::new(&sys);

        let mut shrink_steps = 0;
        let mut prev_len = 0;
        
        // Downsampled history for regression: (step, length)
        let mut history = Vec::new();
        let mut hw_records = Vec::new();
        let mut max_seen_len = 0;
        
        let mut status = "Unknown";
        
        while sim.true_length >= sys.v && sim.steps < args.max_steps {
            let current_len = sim.tape.len() - sim.head_idx;
            
            if current_len > args.max_space {
                status = "OverSize";
                break;
            }

            if sim.steps > 0 && current_len < prev_len {
                shrink_steps += 1;
            }
            prev_len = current_len;

            if current_len > max_seen_len {
                max_seen_len = current_len;
                hw_records.push((sim.steps, current_len));
            }

            // Sample every 100 steps to keep history size manageable
            if sim.steps % 100 == 0 {
                history.push((sim.steps, current_len));
            }

            if let Some(_cond) = sim.step(false, false) {
                status = "Halted/Infinite";
                break;
            }
        }
        
        if sim.true_length < sys.v {
            status = "Halted";
        } else if sim.tape.len() - sim.head_idx > args.max_space {
            status = "OverSize";
        } else if sim.steps >= args.max_steps {
            status = "OverSteps";
        }

        let total_steps = std::cmp::max(1, sim.steps);
        let shrink_rate = shrink_steps as f64 / total_steps as f64;
        let final_size = sim.tape.len() - sim.head_idx;

        let mut p = 0.0;
        let mut r_squared = 0.0;
        let mut max_drawdown = 0.0;

        if history.len() > 10 {
            let start_idx = history.len() / 2;
            let tail = &history[start_idx..];

            // 1. Max Drawdown in tail
            let mut highest_seen = tail[0].1;
            for &(_, len) in tail {
                if len > highest_seen {
                    highest_seen = len;
                } else {
                    let drop = highest_seen - len;
                    let pct = drop as f64 / highest_seen as f64;
                    if pct > max_drawdown {
                        max_drawdown = pct;
                    }
                }
            }

            // 2. Linear Regression (log-log)
            let mut sum_x = 0.0;
            let mut sum_y = 0.0;
            let n = tail.len() as f64;

            for &(step, len) in tail {
                let x = (step as f64).ln();
                let y = if len > 0 { (len as f64).ln() } else { 0.0 };
                sum_x += x;
                sum_y += y;
            }

            let mean_x = sum_x / n;
            let mean_y = sum_y / n;

            let mut num = 0.0;
            let mut den = 0.0;
            for &(step, len) in tail {
                let x = (step as f64).ln();
                let y = if len > 0 { (len as f64).ln() } else { 0.0 };
                let dx = x - mean_x;
                let dy = y - mean_y;
                num += dx * dy;
                den += dx * dx;
            }

            if den > 1e-9 {
                p = num / den;
                
                // Calculate R^2
                let mut ss_res = 0.0;
                let mut ss_tot = 0.0;
                for &(step, len) in tail {
                    let x = (step as f64).ln();
                    let y = if len > 0 { (len as f64).ln() } else { 0.0 };
                    
                    let f_i = p * (x - mean_x) + mean_y;
                    
                    ss_res += (y - f_i).powi(2);
                    ss_tot += (y - mean_y).powi(2);
                }
                
                if ss_tot > 1e-9 {
                    r_squared = 1.0 - (ss_res / ss_tot);
                } else {
                    r_squared = 1.0;
                }
            }
        }

        let mut hw_p = 0.0;
        let mut hw_r_squared = 0.0;

        if hw_records.len() > 10 {
            let start_idx = hw_records.len() / 2;
            let tail = &hw_records[start_idx..];

            let mut sum_x = 0.0;
            let mut sum_y = 0.0;
            let n = tail.len() as f64;
            for &(step, len) in tail {
                let x = (step as f64).ln();
                let y = (len as f64).ln();
                sum_x += x;
                sum_y += y;
            }
            let mean_x = sum_x / n;
            let mean_y = sum_y / n;

            let mut num = 0.0;
            let mut den = 0.0;
            for &(step, len) in tail {
                let x = (step as f64).ln();
                let y = (len as f64).ln();
                let dx = x - mean_x;
                let dy = y - mean_y;
                num += dx * dy;
                den += dx * dx;
            }

            if den > 1e-9 {
                hw_p = num / den;
                let mut ss_res = 0.0;
                let mut ss_tot = 0.0;
                for &(step, len) in tail {
                    let x = (step as f64).ln();
                    let y = (len as f64).ln();
                    let f_i = hw_p * (x - mean_x) + mean_y;
                    ss_res += (y - f_i).powi(2);
                    ss_tot += (y - mean_y).powi(2);
                }
                if ss_tot > 1e-9 {
                    hw_r_squared = 1.0 - (ss_res / ss_tot);
                } else {
                    hw_r_squared = 1.0;
                }
            }
        }

        let category = if hw_r_squared < 0.75 {
            "Unknown".to_string()
        } else {
            let shape = if r_squared >= 0.90 { "Smooth" } else { "Oscillating" };
            let power = if hw_p > 0.90 {
                "Linear"
            } else if hw_p > 0.40 && hw_p < 0.60 {
                "SquareRoot"
            } else {
                "Polynomial"
            };
            format!("{}_{}", power, shape)
        };

        writeln!(
            writer,
            "{},{},{},{:.6},{:.6},{:.6},{:.6},{:.6},{:.6},{}",
            prog_str, status, final_size, shrink_rate, max_drawdown, p, r_squared, hw_p, hw_r_squared, category
        ).unwrap();

        category_map.entry(category.to_string()).or_default().push(prog_str.to_string());
        total_programs += 1;
    }
    
    println!("Analysis complete. Results written to {:?}", args.out);
    println!("\n=== Category Summary ===");
    
    let mut categories: Vec<_> = category_map.into_iter().collect();
    categories.sort_by_key(|(_, examples)| std::cmp::Reverse(examples.len()));

    for (cat, examples) in categories {
        let pct = (examples.len() as f64 / total_programs as f64) * 100.0;
        println!("{:<24} | {:>5} ({:>5.1}%) | Examples: {:?}", cat, examples.len(), pct, examples.iter().take(3).collect::<Vec<_>>());
    }
}
