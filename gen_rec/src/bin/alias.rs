/// Substitute named sub-expressions into a GRF for readability.
///
/// Usage examples:
///   name "R(Z0, P(2,1))"
///   name "C(R(P(1,1), C(S, P(3,2))), C(S,S))"
///   name ack_worm
///   name --max-param 8 'C(R(S, C(R(S, ...), P(3,2), P(3,2))), S, S)'
use clap::Parser;
use gen_rec::alias::AliasDb;
use std::io::IsTerminal;

#[derive(Parser, Debug)]
#[command(
    about = "Substitute named sub-expressions into a GRF",
    long_about = "Walks the GRF AST and replaces sub-expressions matching known\n\
                  named functions with a readable name tag.\n\
                  EXPR may be a raw GRF string or an alias name like \"Add\" or \"AckWorm\"."
)]
struct Args {
    /// GRF expression or alias name (Pred, Add, AckWorm, Plus[2], ...).
    expr: String,

    /// Maximum n for parameterised macros (constant, plus_n, AckDiag, ...).
    #[arg(long, default_value_t = 6)]
    max_param: usize,
}

fn main() {
    let args = Args::parse();
    let db = AliasDb::new_colored(args.max_param, std::io::stdout().is_terminal());

    let grf = match db.resolve(&args.expr) {
        Ok(g) => g,
        Err(e) => {
            eprintln!("error: {e}");
            std::process::exit(1);
        }
    };

    println!("raw  [arity={}, size={}]:", grf.arity(), grf.size());
    println!("  {}", grf);
    println!();
    println!("alias:");
    println!("  {}", db.alias(&grf));
}
