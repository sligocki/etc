use clap::Parser;
use pebble::io::read_records_from_file;
use std::collections::BTreeMap;
use std::path::PathBuf;
use std::process;
use std::time::Instant;

#[derive(Parser, Debug)]
#[command(
    name = "prefix_tree",
    about = "Count holdouts by shared prefixes in canonical Prefix Normal Form (PNF) with hierarchical tree display",
    version
)]
struct Cli {
    /// Path to input file of program records or short codes (e.g. results/sz11/ctl_sp3_me4/unk.txt)
    #[arg(value_name = "INFILE")]
    infile: PathBuf,

    /// Maximum tree depth to expand (default: 8, up to program size)
    #[arg(short = 'd', long = "max-depth", visible_alias = "depth", default_value_t = 8)]
    max_depth: usize,

    /// Minimum number of holdouts in a branch to display (default: 1)
    #[arg(short = 'm', long = "min-count", visible_alias = "min", default_value_t = 1)]
    min_count: usize,

    /// Minimum percentage (0.0 to 100.0) of total holdouts in a branch to display
    #[arg(short = 'p', long = "min-pct", visible_alias = "pct")]
    min_pct: Option<f64>,

    /// Maximum branching factor per node (top-N most frequent children shown; remainder collapsed into '[other]')
    #[arg(short = 'b', long = "branch-limit", visible_alias = "limit")]
    branch_limit: Option<usize>,

    /// Do not normalize programs to Prefix Normal Form (keep raw input rule orientation)
    #[arg(long = "no-pnf", visible_alias = "raw")]
    no_pnf: bool,

    /// Also display a depth-by-depth summary table of unique prefixes and diversity
    #[arg(short = 's', long = "summary", default_value_t = true)]
    summary: bool,

    /// Disable path compression (show every single intermediate rule node)
    #[arg(long = "no-collapse", visible_alias = "uncollapsed")]
    no_collapse: bool,

    /// Number of uncommon / rare prefixes and sample programs to display (default: 15)
    #[arg(short = 'u', long = "uncommon", visible_alias = "rare", default_value_t = 15)]
    uncommon: usize,

    /// Prefix depth to use for grouping uncommon families (default: 4)
    #[arg(long = "uncommon-depth", default_value_t = 4)]
    uncommon_depth: usize,

    /// Limit processing to the first <N> records from the input file
    #[arg(short = 'n', long = "limit")]
    record_limit: Option<usize>,
}

#[derive(Default)]
struct PrefixNode {
    count: usize,
    children: BTreeMap<String, PrefixNode>,
}

impl PrefixNode {
    fn insert(&mut self, tokens: &[&str]) {
        self.count += 1;
        if let Some((first, rest)) = tokens.split_first() {
            self.children
                .entry((*first).to_string())
                .or_default()
                .insert(rest);
        }
    }
}

fn print_tree(
    node: &PrefixNode,
    total_roots: usize,
    current_prefix_str: &str,
    tree_indent: &str,
    depth: usize,
    max_depth: usize,
    min_count: usize,
    branch_limit: Option<usize>,
    collapse_chains: bool,
) {
    if depth >= max_depth {
        return;
    }

    // Sort children by count descending, break ties lexicographically
    let mut sorted_children: Vec<(&String, &PrefixNode)> = node.children.iter().collect();
    sorted_children.sort_by(|(k1, n1), (k2, n2)| n2.count.cmp(&n1.count).then_with(|| k1.cmp(k2)));

    // Filter by min_count
    let eligible: Vec<(&String, &PrefixNode)> = sorted_children
        .into_iter()
        .filter(|(_, c)| c.count >= min_count)
        .collect();

    let display_count = if let Some(limit) = branch_limit {
        eligible.len().min(limit)
    } else {
        eligible.len()
    };

    let (visible, collapsed) = eligible.split_at(display_count);
    let collapsed_count: usize = collapsed.iter().map(|(_, c)| c.count).sum();
    let has_collapsed = !collapsed.is_empty();
    let total_branches = visible.len() + if has_collapsed { 1 } else { 0 };

    for (i, (tok, child)) in visible.iter().enumerate() {
        let is_last = (i + 1 == total_branches) && !has_collapsed;
        let connector = if is_last { "└── " } else { "├── " };

        // Path compression / collapsing unbranched single-child chains:
        let mut chain_tokens = vec![(*tok).as_str()];
        let mut curr_node = *child;
        let mut chain_depth = depth + 1;

        if collapse_chains {
            while chain_depth < max_depth && curr_node.children.len() == 1 {
                let (next_tok, next_child) = curr_node.children.iter().next().unwrap();
                if next_child.count < min_count {
                    break;
                }
                chain_tokens.push(next_tok.as_str());
                curr_node = next_child;
                chain_depth += 1;
            }
        }

        let label = chain_tokens.join("_");
        let pct = (curr_node.count as f64 / total_roots.max(1) as f64) * 100.0;
        let full_prefix = if current_prefix_str.is_empty() {
            label.clone()
        } else {
            format!("{current_prefix_str}_{label}")
        };

        println!(
            "{tree_indent}{connector}{:<14} {:>7} ({:>5.1}%)  [{full_prefix}]",
            label, curr_node.count, pct
        );

        let next_indent = format!("{}{}", tree_indent, if is_last { "    " } else { "│   " });
        print_tree(
            curr_node,
            total_roots,
            &full_prefix,
            &next_indent,
            chain_depth,
            max_depth,
            min_count,
            branch_limit,
            collapse_chains,
        );
    }

    if has_collapsed {
        let collapsed_pct = (collapsed_count as f64 / total_roots.max(1) as f64) * 100.0;
        println!(
            "{tree_indent}└── [other {} branch{}] {:>7} ({:>5.1}%)",
            collapsed.len(),
            if collapsed.len() == 1 { "" } else { "es" },
            collapsed_count,
            collapsed_pct
        );
    }
}

fn main() {
    let cli = Cli::parse();

    if !cli.infile.is_file() {
        eprintln!("Error: input file '{}' does not exist.", cli.infile.display());
        process::exit(1);
    }

    let start = Instant::now();
    let mut records = match read_records_from_file(&cli.infile) {
        Ok(r) => r,
        Err(err) => {
            eprintln!("Error reading input file '{}': {err}", cli.infile.display());
            process::exit(1);
        }
    };

    if let Some(limit) = cli.record_limit {
        records.truncate(limit);
    }

    let total_holdouts = records.len();
    if total_holdouts == 0 {
        eprintln!("Error: input file contained no records.");
        process::exit(1);
    }

    println!("=== Holdout Prefix Normal Form (PNF) Hierarchy ===");
    println!("Input file:      {}", cli.infile.display());
    println!("Total holdouts:  {total_holdouts}");
    println!("Normalization:   {}", if cli.no_pnf { "Raw (Original Orientation)" } else { "Prefix Normal Form (Canonical min(P, mirror(P)))" });
    println!("Max tree depth:  {}", cli.max_depth);
    if let Some(pct) = cli.min_pct {
        println!("Min threshold:   {pct:.2}% (>= {} programs)", ((pct / 100.0) * total_holdouts as f64).ceil() as usize);
    } else {
        println!("Min threshold:   >= {} program(s)", cli.min_count);
    }
    if let Some(limit) = cli.branch_limit {
        println!("Branch limit:    Top {limit} branches per node");
    }
    println!();

    // Convert programs to canonical PNF string tokens
    let pnf_token_lists: Vec<Vec<String>> = records
        .iter()
        .map(|rec| {
            let prog_to_use = if cli.no_pnf {
                rec.program.clone()
            } else {
                rec.program.to_prefix_normal_form()
            };
            let short = prog_to_use.to_string();
            short.split('_').map(String::from).collect()
        })
        .collect();

    // Build the prefix tree
    let mut root = PrefixNode::default();
    for tokens in &pnf_token_lists {
        let refs: Vec<&str> = tokens.iter().map(String::as_str).collect();
        root.insert(&refs);
    }

    // Determine effective min count
    let effective_min_count = if let Some(pct) = cli.min_pct {
        ((pct / 100.0) * total_holdouts as f64).ceil() as usize
    } else {
        cli.min_count
    }
    .max(1);

    // Print Tree
    println!("Prefix Tree (Node: [Rule] Count (%)):");
    println!("ROOT  {total_holdouts} (100.0%)");
    print_tree(
        &root,
        total_holdouts,
        "",
        "",
        0,
        cli.max_depth,
        effective_min_count,
        cli.branch_limit,
        !cli.no_collapse,
    );
    println!();

    // Print summary depth table if requested
    if cli.summary {
        println!("--- Prefix Depth Summary Table ---");
        println!("Depth | Distinct Prefixes | Top Prefix                      | Top Count | Top Share");
        println!("------|-------------------|---------------------------------|-----------|----------");
        let max_pebbles = pnf_token_lists.first().map_or(0, |v| v.len());
        for d in 1..=max_pebbles.min(cli.max_depth) {
            let mut prefix_counts: BTreeMap<String, usize> = BTreeMap::new();
            for tokens in &pnf_token_lists {
                let k = d.min(tokens.len());
                let prefix_str = tokens[..k].join("_");
                *prefix_counts.entry(prefix_str).or_default() += 1;
            }
            let distinct = prefix_counts.len();
            let (top_prefix, top_count) = prefix_counts
                .into_iter()
                .max_by_key(|(_, c)| *c)
                .unwrap_or_default();
            let share = (top_count as f64 / total_holdouts as f64) * 100.0;
            println!(
                "k={:<3} | {:>17} | {:<31} | {:>9} | {:>7.1}%",
                d, distinct, top_prefix, top_count, share
            );
        }
        println!();
    }

    // Print uncommon / rare prefixes and sample programs
    if cli.uncommon > 0 {
        let u_depth = cli.uncommon_depth;
        let mut group_map: BTreeMap<String, Vec<usize>> = BTreeMap::new();
        for (idx, tokens) in pnf_token_lists.iter().enumerate() {
            let k = u_depth.min(tokens.len());
            let pref = tokens[..k].join("_");
            group_map.entry(pref).or_default().push(idx);
        }

        // Sort clusters by count ascending (rarest first), break ties by prefix
        let mut sorted_groups: Vec<(String, Vec<usize>)> = group_map.into_iter().collect();
        sorted_groups.sort_by(|(p1, list1), (p2, list2)| {
            list1.len().cmp(&list2.len()).then_with(|| p1.cmp(p2))
        });

        println!("--- Uncommon Prefix Clusters (Depth k={u_depth}, Rarest First) ---");
        println!(
            "{:<16} | {:>7} | {:>7} | Sample Program (PNF) & Original",
            "Prefix", "Count", "Share"
        );
        println!("{:-<16}-|-{:-<7}-|-{:-<7}-|----------------------------------------------------", "", "", "");

        let num_to_show = cli.uncommon.min(sorted_groups.len());
        for (pref, indices) in sorted_groups.iter().take(num_to_show) {
            let count = indices.len();
            let share = (count as f64 / total_holdouts as f64) * 100.0;
            let sample_idx = indices[0];
            let sample_pnf = pnf_token_lists[sample_idx].join("_");
            let orig_prog = &records[sample_idx].program;
            let orig_str = orig_prog.to_string();

            if sample_pnf == orig_str {
                println!(
                    "{:<16} | {:>7} | {:>6.2}% | {}",
                    pref, count, share, sample_pnf
                );
            } else {
                println!(
                    "{:<16} | {:>7} | {:>6.2}% | {}  (orig: {})",
                    pref, count, share, sample_pnf, orig_str
                );
            }
        }
        println!();
    }

    let elapsed = start.elapsed();
    println!("Analysis completed in {elapsed:.3?}");
}
