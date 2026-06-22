use gen_rec::grf::Grf;
use gen_rec::mgrf::decompile;
use std::fs::File;
use std::io::{BufRead, BufReader};

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 2 {
        eprintln!("Usage: decompile <holdout.grl>");
        std::process::exit(1);
    }

    let file = File::open(&args[1]).expect("Failed to open file");
    let reader = BufReader::new(file);

    for line in reader.lines() {
        let line = line.unwrap();
        if line.starts_with("grf=") {
            let grf_str = line
                .split_whitespace()
                .next()
                .unwrap()
                .trim_start_matches("grf=");
            let grf = grf_str.parse::<Grf>().expect("Failed to parse GRF");
            println!("Original: {}", grf_str);
            println!("Decompiled: {}", decompile(&grf));
            println!();
        }
    }
}
