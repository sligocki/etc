/// Simulate a single GRF expression given on the command line.
///
/// Usage examples:
///   sim "C(S, Z0)"
///   sim "R(P(1,1), C(S, P(3,2)))" 3 2
///   sim "R(P(1,1), C(S, P(3,2)))"           # sweep 0..=10
///   sim "R(P(1,1), C(S, P(3,2)))" --max-val 20
///   sim --max-steps 1000 "M(S)"
use clap::Parser;
use gen_rec::alias::AliasDb;
use gen_rec::grf::Grf;
use gen_rec::simulate::simulate;

#[derive(Parser, Debug)]
#[command(about = "Simulate a single GRF expression")]
struct Args {
    /// GRF expression or alias name (Add, AckWorm, Plus[2], ...).
    expr: String,

    /// Input arguments to the function. Omit to run a parameter sweep.
    inputs: Vec<u64>,

    /// Maximum simulation steps before giving up (0 = unlimited).
    #[arg(long, default_value_t = 100_000_000)]
    max_steps: u64,

    /// Upper bound (inclusive) for each argument in sweep mode.
    #[arg(long, default_value_t = 10)]
    max_val: u64,
}

fn sim_val(grf: &Grf, inputs: &[u64], max_steps: u64) -> Option<u64> {
    simulate(grf, inputs, max_steps).0.into_value()
}

fn fmt_result(v: Option<u64>) -> String {
    match v {
        Some(n) => n.to_string(),
        None => "?".to_string(),
    }
}

fn print_table_1d(grf: &Grf, n: u64, max_steps: u64) {
    let vals: Vec<Option<u64>> = (0..=n).map(|a| sim_val(grf, &[a], max_steps)).collect();
    let val_w = vals.iter().map(|v| fmt_result(*v).len()).max().unwrap_or(1).max(4); // at least "f(n)"
    let n_w = n.to_string().len().max(1);

    println!("{:>n_w$}  |  {:>val_w$}", "n", "f(n)");
    println!("{}--+--{}", "-".repeat(n_w), "-".repeat(val_w));
    for (a, v) in vals.iter().enumerate() {
        println!("{:>n_w$}  |  {:>val_w$}", a, fmt_result(*v));
    }
}

fn print_table_2d(grf: &Grf, n: u64, max_steps: u64) {
    // rows = first arg (a), columns = second arg (b)
    let vals: Vec<Vec<Option<u64>>> = (0..=n)
        .map(|a| (0..=n).map(|b| sim_val(grf, &[a, b], max_steps)).collect())
        .collect();

    let cell_w = vals.iter().flatten()
        .map(|v| fmt_result(*v).len())
        .chain((0..=n).map(|b| b.to_string().len()))
        .max().unwrap_or(1);
    let row_w = n.to_string().len().max(1);

    // Header row
    let header: String = (0..=n).map(|b| format!("{:>cell_w$}", b)).collect::<Vec<_>>().join("  ");
    println!("{:>row_w$}  |  {}", "", header);
    println!("{}--+--{}", "-".repeat(row_w), "-".repeat(header.len()));

    for (a, row) in vals.iter().enumerate() {
        let cells: String = row.iter()
            .map(|v| format!("{:>cell_w$}", fmt_result(*v)))
            .collect::<Vec<_>>().join("  ");
        println!("{:>row_w$}  |  {}", a, cells);
    }
}

fn print_table_nd(grf: &Grf, arity: usize, n: u64, max_steps: u64) {
    // Enumerate all (n+1)^arity input tuples in lexicographic order.
    let count = (n + 1).pow(arity as u32);
    let mut all_inputs: Vec<Vec<u64>> = Vec::with_capacity(count as usize);
    let mut tuple = vec![0u64; arity];
    loop {
        all_inputs.push(tuple.clone());
        // increment rightmost, carry left
        let mut pos = arity - 1;
        loop {
            tuple[pos] += 1;
            if tuple[pos] <= n { break; }
            tuple[pos] = 0;
            if pos == 0 { break; }
            pos -= 1;
        }
        if tuple.iter().all(|&x| x == 0) { break; }
    }

    let results: Vec<Option<u64>> = all_inputs.iter()
        .map(|inp| sim_val(grf, inp, max_steps))
        .collect();

    let arg_w = n.to_string().len().max(2); // at least "x0" header width
    let val_w = results.iter().map(|v| fmt_result(*v).len()).max().unwrap_or(1).max(6);

    // Header
    let arg_headers: String = (0..arity).map(|i| format!("{:>arg_w$}", format!("x{i}"))).collect::<Vec<_>>().join("  ");
    println!("{}  |  {:>val_w$}", arg_headers, "result");
    println!("{}--+--{}", "-".repeat(arg_w * arity + 2 * (arity - 1)), "-".repeat(val_w));

    for (inp, v) in all_inputs.iter().zip(results.iter()) {
        let args: String = inp.iter().map(|x| format!("{:>arg_w$}", x)).collect::<Vec<_>>().join("  ");
        println!("{}  |  {:>val_w$}", args, fmt_result(*v));
    }
}

fn main() {
    let args = Args::parse();

    let grf = match AliasDb::default().resolve(&args.expr) {
        Ok(g) => g,
        Err(e) => {
            eprintln!("error: {e}");
            std::process::exit(1);
        }
    };

    let arity = grf.arity();

    // Single-run mode: inputs provided, or arity 0.
    if !args.inputs.is_empty() || arity == 0 {
        if args.inputs.len() != arity {
            eprintln!(
                "Arity mismatch: `{}` expects {} input{}, got {}",
                grf,
                arity,
                if arity == 1 { "" } else { "s" },
                args.inputs.len()
            );
            std::process::exit(1);
        }
        println!("expr  : {}", grf);
        println!("arity : {}", arity);
        println!("size  : {}", grf.size());
        if !args.inputs.is_empty() {
            let input_str: Vec<String> = args.inputs.iter().map(|x| x.to_string()).collect();
            println!("inputs: {}", input_str.join(", "));
        }
        println!("---");
        let (result, steps) = simulate(&grf, &args.inputs, args.max_steps);
        match result.into_value() {
            Some(v) => println!("result: {}  ({} steps)", v, steps),
            None => {
                let limit = if args.max_steps == 0 { "unlimited".to_string() } else { args.max_steps.to_string() };
                println!("result: timed out after {} steps (limit: {})", steps, limit);
            }
        }
        return;
    }

    // Sweep mode.
    println!("expr  : {}", grf);
    println!("arity : {}", arity);
    println!("size  : {}", grf.size());
    println!("sweep : 0..={}", args.max_val);
    println!("---");

    match arity {
        1 => print_table_1d(&grf, args.max_val, args.max_steps),
        2 => print_table_2d(&grf, args.max_val, args.max_steps),
        _ => print_table_nd(&grf, arity, args.max_val, args.max_steps),
    }
}
