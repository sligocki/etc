/// Convert a GRF/mGRF expression to LaTeX notation.
///
/// Every operator except S carries a superscript for its arity.
/// P also carries a subscript for its projection index.
///
/// Examples:
///   Z1          -> Z^{1}
///   S           -> S
///   P(3,1)      -> P^{3}_{1}
///   C(Z1,P(3,1))-> C^{3}(Z^{1}, P^{3}_{1})
///   R(Z0,P(2,1))-> R^{1}(Z^{0}, P^{2}_{1})
///   M(f)        -> \mu^{k}(...)
use clap::Parser;
use gen_rec::alias::AliasDb;
use gen_rec::grf::Grf;

#[derive(Parser, Debug)]
#[command(about = "Convert a GRF expression to LaTeX notation")]
struct Args {
    /// GRF expression or alias name.
    expr: String,
}

fn to_latex(grf: &Grf) -> String {
    match grf {
        Grf::Zero(k) => format!("Z^{{{k}}}"),
        Grf::Succ => "S".to_string(),
        Grf::Proj(k, i) => format!("P^{{{k}}}_{{{i}}}"),
        Grf::Comp(h, gs, _) => {
            let arity = grf.arity();
            let mut args = vec![to_latex(h)];
            args.extend(gs.iter().map(to_latex));
            format!("C^{{{arity}}}({})", args.join(", "))
        }
        Grf::Rec(g, h) => {
            let arity = grf.arity();
            format!("R^{{{arity}}}({}, {})", to_latex(g), to_latex(h))
        }
        Grf::Min(f) => {
            let arity = grf.arity();
            format!("M^{{{arity}}}({})", to_latex(f))
        }
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
    println!("{}", to_latex(&grf));
}
