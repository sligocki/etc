/// Substitute named sub-expressions into a GRF for readability.
///
/// Usage examples:
///   name "R(Z0, P(2,1))"
///   name "C(R(P(1,1), C(S, P(3,2))), C(S,S))"
///   name ack_worm
///   name --max-param 8 'C(R(S, C(R(S, ...), P(3,2), P(3,2))), S, S)'
use clap::Parser;
use gen_rec::example_ack::{
    ack, ack_loop, ack_step, ack_worm, add, bit, dec_append, dec_append_n, div2, div2k, graham,
    init_list, mod2, not, omega, plus2, pop_k, pred, rmonus, rmonus_odd, sgn, shift,
};
use gen_rec::grf::Grf;
use gen_rec::alias::AliasDb;
use std::io::IsTerminal;

#[derive(Parser, Debug)]
#[command(
    about = "Substitute named sub-expressions into a GRF",
    long_about = "Walks the GRF AST and replaces sub-expressions matching known\n\
                  named functions with a readable name tag.\n\
                  EXPR may be a raw GRF string or a named function like \"ack_worm\"."
)]
struct Args {
    /// GRF expression or named function (pred, add, ack_worm, ...).
    expr: String,

    /// Maximum n for parameterised macros (constant, plus_n, AckDiag, ...).
    #[arg(long, default_value_t = 6)]
    max_param: usize,
}

fn resolve(expr: &str) -> Result<Grf, String> {
    let grf = match expr {
        "pred"         => pred(),
        "not"          => not(),
        "sgn"          => sgn(),
        "plus2"        => plus2(),
        "add"          => add(),
        "rmonus"       => rmonus(),
        "mod2"         => mod2(),
        "shift"        => shift(),
        "rmonus_odd"   => rmonus_odd(),
        "div2"         => div2(),
        "div2k"        => div2k(),
        "dec_append"   => dec_append(),
        "dec_append_n" => dec_append_n(),
        "bit"          => bit(),
        "pop_k"        => pop_k(),
        "ack_step"     => ack_step(),
        "ack_loop"     => ack_loop(),
        "ack_worm"     => ack_worm(),
        "init_list"    => init_list(),
        "ack"          => ack(),
        "omega"        => omega(),
        "graham"       => graham(),
        _ => return expr.parse::<Grf>().map_err(|e| format!("parse error: {e}")),
    };
    Ok(grf)
}

fn main() {
    let args = Args::parse();

    let grf = match resolve(&args.expr) {
        Ok(g) => g,
        Err(e) => {
            eprintln!("error: {e}");
            std::process::exit(1);
        }
    };

    let db = AliasDb::new_colored(args.max_param, std::io::stdout().is_terminal());

    println!("raw  [arity={}, size={}]:", grf.arity(), grf.size());
    println!("  {}", grf);
    println!();
    println!("alias:");
    println!("  {}", db.alias(&grf));
}
