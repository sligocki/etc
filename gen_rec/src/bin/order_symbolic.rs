use std::env;
use std::fs;
use gen_rec::closed_form::ClosedForm;
use gen_rec::compare_symbolic::{compare_strict, PointwiseOrder, fgh_level};
use gen_rec::grf::{Grf, GrfKind};

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() != 2 {
        eprintln!("Usage: {} <filename>", args[0]);
        std::process::exit(1);
    }
    let filename = &args[1];

    let content = fs::read_to_string(filename)
        .unwrap_or_else(|_| panic!("Failed to read file {}", filename));

    // Store (orig_idx, name, Grf, ClosedForm, FGH_level, SymVal)
    let mut orig_holdouts: Vec<(usize, String, Grf, ClosedForm, usize, gen_rec::compare_symbolic::SymVal)> = Vec::new();

    let mut idx = 0;
    for line in content.lines() {
        if let Some(grf_str) = line.strip_prefix("grf=") {
            let grf_str = grf_str.split_whitespace().next().unwrap();
            let grf = grf_str.parse::<Grf>().expect("Failed to parse GRF");
            let mut extracted_cf = None;
            if let GrfKind::Comp(h1, _, _) = &grf.kind {
                if let GrfKind::Comp(f, _, _) = &h1.kind {
                    extracted_cf = f.closed_form().cloned();
                }
            }
            if let Some(cf) = extracted_cf {
                let lvl = fgh_level(&cf);
                
                // Dynamically evaluate the full 0-arity GRF syntax tree.
                // It will walk through the `DiagS` and `K[1]` wrappers, evaluate `x=1` exactly,
                // and pass the dynamically computed starting arguments (e.g., [2, 2]) to the inner IteratedFn!
                let sym_val = gen_rec::compare_symbolic::eval_grf_sym(&grf, &[]);
                
                orig_holdouts.push((idx, grf_str.to_string(), grf, cf, lvl, sym_val));
                idx += 1;
            }
        }
    }

    println!("Found {} holdouts with ClosedForm representations.", orig_holdouts.len());

    let n = orig_holdouts.len();
    let mut in_degree = vec![0; n];
    let mut adj = vec![vec![]; n];

    for i in 0..n {
        for j in 0..n {
            if i == j { continue; }
            if gen_rec::compare_symbolic::compare_sym(&orig_holdouts[i].5, &orig_holdouts[j].5) == PointwiseOrder::LessEqual {
                adj[i].push(j);
                in_degree[j] += 1;
            }
        }
    }

    let mut sorted_indices = Vec::new();
    let mut queue: Vec<usize> = (0..n).filter(|&i| in_degree[i] == 0).collect();
    queue.sort_unstable_by(|a, b| b.cmp(a));

    while let Some(u) = queue.pop() {
        sorted_indices.push(u);
        for &v in &adj[u] {
            in_degree[v] -= 1;
            if in_degree[v] == 0 {
                queue.push(v);
                queue.sort_unstable_by(|a, b| b.cmp(a));
            }
        }
    }

    for i in 0..n {
        if !sorted_indices.contains(&i) {
            sorted_indices.push(i);
        }
    }

    // Now sorted_indices maps [sorted_pos] -> orig_idx.
    let holdouts: Vec<_> = sorted_indices.iter().map(|&i| orig_holdouts[i].clone()).collect();

    println!("--- FGH Levels (Ordered by Exact Symbolic Evaluation) ---");
    for (orig_idx, name, grf, _, lvl, sym_val) in &holdouts {
        println!("H{:<2}: Level {} | \x1b[1;36m{}\x1b[0m", orig_idx, lvl, gen_rec::mgrf::decompile(grf));
        println!("      SymVal: \x1b[1;35m{}\x1b[0m", sym_val);
    }

    println!("\n--- Exact Symbolic Strict Dominance Comparison Grid ---");
    // Column headers
    print!("    ");
    for (orig_idx_j, _, _, _, _, _) in &holdouts {
        print!(" H{:<2}", orig_idx_j);
    }
    println!();

    let mut num_uncertain = 0;

    for (orig_idx_i, _, _, _, _, sym_i) in &holdouts {
        print!("H{:<2} ", orig_idx_i);
        for (orig_idx_j, _, _, _, _, sym_j) in &holdouts {
            if orig_idx_i == orig_idx_j {
                print!("  \x1b[1;30m=\x1b[0m "); // dark gray for Equal
            } else {
                let cmp = gen_rec::compare_symbolic::compare_sym(sym_i, sym_j);
                let sym = match cmp {
                    PointwiseOrder::LessEqual => "  \x1b[1;32m≤\x1b[0m ",       // green
                    PointwiseOrder::GreaterEqual => "  \x1b[1;31m≥\x1b[0m ",    // red
                    PointwiseOrder::Equal => "  \x1b[1;30m=\x1b[0m ",     // dark gray
                    PointwiseOrder::Uncertain => "  \x1b[1;33m?\x1b[0m ",  // yellow
                };
                print!("{}", sym);

                if orig_idx_i < orig_idx_j && cmp == PointwiseOrder::Uncertain {
                    num_uncertain += 1;
                }
            }
        }
        println!();
    }

    let total_pairs = n * (n - 1) / 2;
    println!("\nSummary: Total Pairs: {}, Ordered by Strict Domination: {}, Uncertains: {}", 
        total_pairs,
        total_pairs - num_uncertain,
        num_uncertain
    );

    println!("\n--- Champion Candidates ---");
    println!("(Holdouts that are NOT strictly dominated by any other holdout)");
    let mut num_champs = 0;
    // We iterate over the sorted `holdouts` so that champions are printed in top-down order
    for (orig_idx, name, grf, _, _, _) in &holdouts {
        if adj[*orig_idx].is_empty() {
            println!("H{:<2}: {}", orig_idx, gen_rec::mgrf::decompile(grf));
            println!("      RAW: {}", name);
            num_champs += 1;
        }
    }
    println!("Total Champion Candidates: {}", num_champs);
}
