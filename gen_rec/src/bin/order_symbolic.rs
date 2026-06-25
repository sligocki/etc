use gen_rec::closed_form::ClosedForm;
use gen_rec::compare_symbolic::PointwiseOrder;
use gen_rec::grf::Grf;
use std::env;
use std::fs;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() != 2 {
        eprintln!("Usage: {} <filename>", args[0]);
        std::process::exit(1);
    }
    let filename = &args[1];

    let content =
        fs::read_to_string(filename).unwrap_or_else(|_| panic!("Failed to read file {}", filename));

    // Store (orig_idx, name, Grf, Option<ClosedForm>, FGH_level, SymVal)
    let mut orig_holdouts: Vec<(
        usize,
        String,
        Grf,
        Option<ClosedForm>,
        gen_rec::compare_symbolic::SymVal,
    )> = Vec::new();

    let mut total_count = 0;
    for line in content.lines() {
        if let Some(grf_str) = line.strip_prefix("grf=") {
            let grf_str = grf_str.split_whitespace().next().unwrap();
            let grf = grf_str.parse::<Grf>().expect("Failed to parse GRF");
            let sym_val = gen_rec::compare_symbolic::eval_grf_sym(&grf, &[]);
            let cf = grf.closed_form().cloned();

            orig_holdouts.push((total_count, grf_str.to_string(), grf, cf, sym_val));
            total_count += 1;
        }
    }

    println!("Analyzed {} holdouts.", orig_holdouts.len());
    if orig_holdouts.len() < total_count {
        eprintln!(
            "\x1b[31mWARNING: Only {}/{} holdouts analyzed!\x1b[0m",
            orig_holdouts.len(),
            total_count
        );
    }

    // Pre-sort the holdouts by their Knuth10 heuristic upper bound!
    // This allows the dominance table and champions to be ordered primarily by sheer mathematical growth.
    orig_holdouts.sort_by(|a, b| {
        let bound_a = gen_rec::compare_symbolic::compute_bounds(&a.4);
        let bound_b = gen_rec::compare_symbolic::compute_bounds(&b.4);
        match (bound_a, bound_b) {
            (Some(ba), Some(bb)) => ba.1.cmp(&bb.1),
            (Some(_), None) => std::cmp::Ordering::Less,
            (None, Some(_)) => std::cmp::Ordering::Greater,
            (None, None) => std::cmp::Ordering::Equal,
        }
    });

    let n = orig_holdouts.len();
    let mut in_degree = vec![0; n];
    let mut adj = vec![vec![]; n];

    for i in 0..n {
        for j in 0..n {
            if i == j {
                continue;
            }
            let cmp =
                gen_rec::compare_symbolic::compare_sym(&orig_holdouts[i].4, &orig_holdouts[j].4);

            let bounds_i = gen_rec::compare_symbolic::compute_bounds(&orig_holdouts[i].4);
            let bounds_j = gen_rec::compare_symbolic::compute_bounds(&orig_holdouts[j].4);
            if let (Some(bounds_i), Some(bounds_j)) = (bounds_i, bounds_j) {
                if cmp == PointwiseOrder::GreaterEqual && bounds_i.1 < bounds_j.0 {
                    panic!(
                        "Sanity check failed: H{} >= H{}, but H{}.upper ({}) < H{}.lower ({})",
                        orig_holdouts[i].0,
                        orig_holdouts[j].0,
                        orig_holdouts[i].0,
                        bounds_i.1.normalize(),
                        orig_holdouts[j].0,
                        bounds_j.0.normalize()
                    );
                }
                if cmp == PointwiseOrder::LessEqual && bounds_i.0 > bounds_j.1 {
                    panic!(
                        "Sanity check failed: H{} <= H{}, but H{}.lower ({}) > H{}.upper ({})",
                        orig_holdouts[i].0,
                        orig_holdouts[j].0,
                        orig_holdouts[i].0,
                        bounds_i.0.normalize(),
                        orig_holdouts[j].0,
                        bounds_j.1.normalize()
                    );
                }
                if cmp == PointwiseOrder::Equal
                    && (bounds_i.1 < bounds_j.0 || bounds_i.0 > bounds_j.1)
                {
                    panic!(
                        "Sanity check failed: H{} == H{}, but bounds do not overlap: [{}, {}] vs [{}, {}]",
                        orig_holdouts[i].0,
                        orig_holdouts[j].0,
                        bounds_i.0.normalize(),
                        bounds_i.1.normalize(),
                        bounds_j.0.normalize(),
                        bounds_j.1.normalize()
                    );
                }
            }

            if cmp == PointwiseOrder::LessEqual {
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
    let holdouts: Vec<_> = sorted_indices
        .iter()
        .map(|&i| orig_holdouts[i].clone())
        .collect();

    println!("--- FGH Levels (Ordered by Exact Symbolic Evaluation) ---");
    for (orig_idx, _name, grf, _, sym_val) in &holdouts {
        println!(
            "H{:<2}: [1;36m{}[0m",
            orig_idx,
            gen_rec::mgrf::decompile(grf)
        );
        println!("      Score: [1;35m{}[0m", sym_val);
    }

    println!("\n--- Exact Symbolic Strict Dominance Comparison Grid ---");
    let show_grid = holdouts.len() <= 30;

    if show_grid {
        // Column headers
        print!("    ");
        for (orig_idx_j, _, _, _, _) in &holdouts {
            print!(" H{:<2}", orig_idx_j);
        }
        println!();
    } else {
        println!("(Grid hidden because there are more than 30 holdouts)");
    }

    let mut num_uncertain = 0;

    for (orig_idx_i, _, _, _, sym_i) in &holdouts {
        if show_grid {
            print!("H{:<2} ", orig_idx_i);
        }
        for (orig_idx_j, _, _, _, sym_j) in &holdouts {
            let cmp = if orig_idx_i == orig_idx_j {
                PointwiseOrder::Equal
            } else {
                gen_rec::compare_symbolic::compare_sym(sym_i, sym_j)
            };

            if show_grid {
                let sym = match cmp {
                    PointwiseOrder::LessEqual => "  \x1b[1;32m≤\x1b[0m ", // green
                    PointwiseOrder::GreaterEqual => "  \x1b[1;31m≥\x1b[0m ", // red
                    PointwiseOrder::Equal => "  \x1b[1;30m=\x1b[0m ",     // dark gray
                    PointwiseOrder::Uncertain => "  \x1b[1;33m?\x1b[0m ", // yellow
                };
                print!("{}", sym);
            }

            if orig_idx_i != orig_idx_j
                && orig_idx_i < orig_idx_j
                && cmp == PointwiseOrder::Uncertain
            {
                num_uncertain += 1;
            }
        }
        if show_grid {
            println!();
        }
    }

    let total_pairs = n * (n - 1) / 2;
    println!(
        "\nSummary: Total Pairs: {}, Ordered by Strict Domination: {}, Uncertains: {}",
        total_pairs,
        total_pairs - num_uncertain,
        num_uncertain
    );

    println!("\n--- Champion Candidates ---");
    println!("(Holdouts that are NOT strictly dominated by any other holdout)");
    let mut num_champs = 0;
    // We iterate over the sorted `holdouts` so that champions are printed in top-down order
    for (k, (orig_idx, name, grf, _, sym_val)) in holdouts.iter().enumerate() {
        let i = sorted_indices[k];
        if adj[i].is_empty() {
            println!("H{:<2}: {}", orig_idx, gen_rec::mgrf::decompile(grf));
            println!("      RAW: {}", name);
            println!("      Score: {}\n      Debug Score: {:?}", sym_val, sym_val);
            num_champs += 1;
        }
    }
    println!("Total Champion Candidates: {}", num_champs);

    if orig_holdouts.len() < total_count {
        println!(
            "\n\x1b[1;31mWARNING: Only analyzed {} out of {} total holdouts because some lacked ClosedForm representations!\x1b[0m",
            orig_holdouts.len(),
            total_count
        );
    }
}
