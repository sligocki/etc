use clap::Parser;
use gen_rec::alias::alias_db_for_stdout;
use gen_rec::enumerate::stream_grf;
use gen_rec::grf::Grf;
use gen_rec::pruning::PruningOpts;
use gen_rec::simulate::{simulate_opts, SimOpts, SimResult};

use std::collections::HashSet;
use std::time::Instant;

#[derive(Parser, Debug)]
#[command(
    about = "Search for 2-arity GRFs that implement well-orders",
    long_about = None
)]
struct Args {
    /// Allow the Minimization combinator
    #[arg(long)]
    allow_min: bool,

    /// Number of exhaustive small inputs to test (0..small_n)
    #[arg(long, default_value_t = 10)]
    small_n: u64,

    /// Number of random inputs to test
    #[arg(long, default_value_t = 10)]
    rand_n: usize,

    /// Maximum value for random inputs
    #[arg(long, default_value_t = 100)]
    rand_max: u64,

    /// Maximum updates in the well-foundedness random walk
    #[arg(long, default_value_t = 10)]
    wf_steps: u32,

    /// Number of iterations for well-foundedness random walk
    #[arg(long, default_value_t = 100)]
    wf_iters: usize,

    /// Maximum steps for simulation
    #[arg(long, default_value_t = 10_000)]
    sim_budget: u64,
    
    /// Starting size (defaults to 1)
    #[arg(long, default_value_t = 1)]
    start_size: usize,
    
    /// Maximum size to enumerate
    #[arg(long, default_value_t = 10)]
    max_size: usize,
}

struct Lcg { state: u64 }
impl Lcg {
    fn new() -> Self { Self { state: 123456789 } }
    fn gen_range(&mut self, min: u64, max: u64) -> u64 {
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1);
        let val = (self.state >> 32) as u64;
        min + val % (max - min + 1)
    }
}

fn main() {
    let args = Args::parse();
    let sim_opts = SimOpts::default();
    let prune_opts = PruningOpts::recommended();
    let alias_db = alias_db_for_stdout(10, false);

    println!("Searching for well-ordering GRFs...");
    println!("Configuration:");
    println!("  small_n: {}", args.small_n);
    println!("  rand_n: {}", args.rand_n);
    println!("  rand_max: {}", args.rand_max);
    println!("  wf_steps: {}", args.wf_steps);
    println!("  wf_iters: {}", args.wf_iters);
    println!("  sim_budget: {}", args.sim_budget);
    
    let mut size = args.start_size;
    let mut seen_signatures = HashSet::new();

    while size <= args.max_size {
        println!("--- Size {} ---", size);
        let mut count_total = 0;
        let mut count_reflexive = 0;
        let mut count_asymmetric = 0;
        let mut count_transitive = 0;
        let mut count_well_founded = 0;

        let start_time = Instant::now();

        stream_grf(size, 2, args.allow_min, prune_opts.clone(), &mut |grf: &Grf| {
            count_total += 1;

            let mut rng = Lcg::new();

            // 1. Generate test subset T
            let mut t_set: HashSet<u64> = (0..args.small_n).collect();
            while t_set.len() < (args.small_n as usize + args.rand_n) {
                t_set.insert(rng.gen_range(0, args.rand_max));
            }
            let t: Vec<u64> = t_set.into_iter().collect();

            // Helper to simulate
            let sim = |x: u64, y: u64| -> Option<bool> {
                let (res, _) = simulate_opts(grf, &[x, y], Some(args.sim_budget), sim_opts);
                match res {
                    SimResult::Value(v) => Some(v == 0),
                    _ => None,
                }
            };

            // 2. Reflexivity: f(x,x) must be consistent boolean value
            let mut reflex_val = None;
            let mut reflex_ok = true;
            for &x in &t {
                if let Some(is_zero) = sim(x, x) {
                    if let Some(r) = reflex_val {
                        if is_zero != r {
                            reflex_ok = false;
                            break;
                        }
                    } else {
                        reflex_val = Some(is_zero);
                    }
                } else {
                    reflex_ok = false;
                    break;
                }
            }
            if !reflex_ok {
                return;
            }
            count_reflexive += 1;

            // 3. Totality/Asymmetry
            let mut asym_ok = true;
            let n = t.len();
            for i in 0..n {
                for j in (i + 1)..n {
                    let x = t[i];
                    let y = t[j];
                    let v1 = sim(x, y);
                    let v2 = sim(y, x);
                    match (v1, v2) {
                        (Some(b1), Some(b2)) => {
                            if b1 == b2 { // Exactly one must be true
                                asym_ok = false;
                                break;
                            }
                        }
                        _ => {
                            asym_ok = false;
                            break;
                        }
                    }
                }
                if !asym_ok {
                    break;
                }
            }
            if !asym_ok {
                return;
            }
            count_asymmetric += 1;

            // 4. Transitivity (cycle detection on strict relation)
            // Strict relation: x < y iff f(x,y) == 0 AND x != y
            // We already checked x != y cases above, we can just build the digraph
            let mut adj = vec![vec![]; n];
            for i in 0..n {
                for j in 0..n {
                    if i != j {
                        if sim(t[i], t[j]) == Some(true) {
                            adj[i].push(j);
                        }
                    }
                }
            }

            let mut visited = vec![0; n]; // 0: unvisited, 1: visiting, 2: visited
            let mut has_cycle = false;
            for i in 0..n {
                if visited[i] == 0 {
                    if dfs_cycle(i, &adj, &mut visited) {
                        has_cycle = true;
                        break;
                    }
                }
            }
            if has_cycle {
                return;
            }
            count_transitive += 1;

            // 5. Well-foundedness
            let mut wf_ok = true;
            let mut curr = rng.gen_range(0, args.rand_max);
            let mut updates = 0;
            for _ in 0..args.wf_iters {
                let y = rng.gen_range(0, args.rand_max);
                // y < curr
                if curr != y && sim(y, curr) == Some(true) {
                    curr = y;
                    updates += 1;
                    if updates > args.wf_steps {
                        wf_ok = false;
                        break;
                    }
                }
            }
            if !wf_ok {
                return;
            }
            count_well_founded += 1;

            // Found a candidate! Check for deduplication
            let sample_max = 4;
            let mut signature = Vec::with_capacity((sample_max + 1) * (sample_max + 1));
            for x in 0..=sample_max {
                for y in 0..=sample_max {
                    signature.push(sim(x as u64, y as u64));
                }
            }
            
            if !seen_signatures.insert(signature.clone()) {
                return; // Duplicate behavior, skip printing
            }

            let alias = alias_db.as_ref().map(|db| db.alias(grf)).unwrap_or_else(|| grf.to_string());
            println!("Candidate found: {}", alias);
            println!("  Raw: {}", grf);
            
            // Print a small sample of evaluations
            print!("  f(x,y) |");
            for y in 0..=sample_max {
                print!(" {:2}", y);
            }
            println!("");
            println!("  -------+----------------");
            let mut sig_idx = 0;
            for x in 0..=sample_max {
                print!("      {:2} |", x);
                for _y in 0..=sample_max {
                    if let Some(b) = signature[sig_idx] {
                        print!("  {}", if b { "T" } else { "F" });
                    } else {
                        print!("  ?");
                    }
                    sig_idx += 1;
                }
                println!("");
            }
            println!("");
        });

        let duration = start_time.elapsed();
        println!("Size {} results ({} ms):", size, duration.as_millis());
        println!("  Total evaluated: {}", count_total);
        println!("  Passed reflexivity: {}", count_reflexive);
        println!("  Passed asymmetry: {}", count_asymmetric);
        println!("  Passed transitivity: {}", count_transitive);
        println!("  Passed well-foundedness: {}", count_well_founded);
        println!();
        
        size += 1;
    }
}

fn dfs_cycle(u: usize, adj: &Vec<Vec<usize>>, visited: &mut Vec<u8>) -> bool {
    visited[u] = 1;
    for &v in &adj[u] {
        if visited[v] == 1 {
            return true; // back edge
        } else if visited[v] == 0 {
            if dfs_cycle(v, adj, visited) {
                return true;
            }
        }
    }
    visited[u] = 2;
    false
}
