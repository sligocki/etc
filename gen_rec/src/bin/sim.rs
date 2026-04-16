/// Simulate a single GRF expression given on the command line.
///
/// Usage examples:
///   sim "C(S, Z0)"
///   sim "R(P(1,1), C(S, P(3,2)))" 3 2
///   sim --max-steps 1000 "M(S)"
use clap::Parser;
use gen_rec::grf::Grf;
use gen_rec::simulate::simulate;

#[derive(Parser, Debug)]
#[command(
    about = "Simulate a single GRF expression",
    long_about = "Parse and simulate a GRF expression string.\n\
                  Atoms: Z<k>  S  P(<k>,<i>)\n\
                  Combinators: C(<h>, <g1>, ...) R(<g>, <h>) M(<f>)"
)]
struct Args {
    /// GRF expression to simulate, e.g. \"C(S, Z0)\" or \"R(P(1,1), C(S, P(3,2)))\"
    expr: String,

    /// Input arguments to the function (must match its arity).
    inputs: Vec<u64>,

    /// Maximum simulation steps before giving up.
    #[arg(long, default_value_t = 100_000_000)]
    max_steps: u64,
}

fn main() {
    let args = Args::parse();

    let grf: Grf = match args.expr.parse() {
        Ok(g) => g,
        Err(e) => {
            eprintln!("Parse error: {e}");
            std::process::exit(1);
        }
    };

    let expected_arity = grf.arity();
    if args.inputs.len() != expected_arity {
        eprintln!(
            "Arity mismatch: `{}` expects {} input{}, got {}",
            grf,
            expected_arity,
            if expected_arity == 1 { "" } else { "s" },
            args.inputs.len()
        );
        std::process::exit(1);
    }

    println!("expr  : {}", grf);
    println!("arity : {}", expected_arity);
    println!("size  : {}", grf.size());
    if !args.inputs.is_empty() {
        let input_str: Vec<String> = args.inputs.iter().map(|x| x.to_string()).collect();
        println!("inputs: {}", input_str.join(", "));
    }
    println!("---");

    let (result, steps) = simulate(&grf, &args.inputs, args.max_steps);
    match result.into_value() {
        Some(v) => println!("result: {}  ({} steps)", v, steps),
        None => println!(
            "result: timed out after {} steps (limit: {})",
            steps, args.max_steps
        ),
    }
}
