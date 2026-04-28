use std::collections::HashMap;
use std::iter::Peekable;
use std::str::Chars;

use crate::grf::Grf;

// Internal AST for igrf expressions before arity inference.
#[derive(Debug, Clone)]
enum Expr {
    Zero(Option<usize>),        // Z (bare) or Zk
    Succ,                       // S
    Proj(Option<usize>, usize), // Pk (bare) or P(k,i)
    Comp(Box<Expr>, Vec<Expr>),
    Rec(Box<Expr>, Box<Expr>),
    Min(Box<Expr>),
    Name(String),               // named reference
    Const(u64),                 // K[n]
}

/// Parse a `.igrf` file and return each definition as `(name, Grf)` in order.
///
/// Definitions are resolved sequentially; each name can reference only earlier names.
/// Bare `Z` and `Pk` have their arities inferred by a two-phase algorithm:
/// bottom-up minimum arity, then top-down propagation.
pub fn parse_igrf_to_grfs(content: &str) -> Result<Vec<(String, Grf)>, String> {
    let raw = parse_file(content)?;
    let mut arities: HashMap<String, usize> = HashMap::new();
    let mut grfs: HashMap<String, Grf> = HashMap::new();
    let mut result = Vec::new();

    for (name, expr) in &raw {
        let ar = min_arity(expr, &arities)
            .map_err(|e| format!("In definition of {}: {}", name, e))?;
        let grf = resolve(expr, ar, &grfs)
            .map_err(|e| format!("In definition of {}: {}", name, e))?;
        arities.insert(name.clone(), ar);
        grfs.insert(name.clone(), grf.clone());
        result.push((name.clone(), grf));
    }
    Ok(result)
}

// ── File-level parser ─────────────────────────────────────────────────────────

fn parse_file(content: &str) -> Result<Vec<(String, Expr)>, String> {
    let mut defs = Vec::new();
    for (lineno, line) in content.lines().enumerate() {
        let line = if let Some(i) = line.find('#') { &line[..i] } else { line }.trim();
        if line.is_empty() {
            continue;
        }
        let (name, rest) = line
            .split_once(":=")
            .ok_or_else(|| format!("Line {}: no ':=' found in {:?}", lineno + 1, line))?;
        let name = name.trim().to_string();
        let expr_str: String = rest.chars().filter(|c| !c.is_whitespace()).collect();
        let expr = parse_expr_str(&expr_str)
            .map_err(|e| format!("Line {}: parse error in {:?}: {}", lineno + 1, line, e))?;
        defs.push((name, expr));
    }
    Ok(defs)
}

fn parse_expr_str(s: &str) -> Result<Expr, String> {
    let mut chars = s.chars().peekable();
    let e = parse_expr(&mut chars)?;
    if chars.peek().is_some() {
        return Err(format!("Trailing chars: {:?}", chars.collect::<String>()));
    }
    Ok(e)
}

// ── Expression parser ─────────────────────────────────────────────────────────

fn parse_expr(chars: &mut Peekable<Chars>) -> Result<Expr, String> {
    let c = chars.next().ok_or("Unexpected end of input")?;
    match c {
        'Z' => {
            if chars.peek().map_or(false, |x| x.is_ascii_digit()) {
                let k = read_digits(chars).unwrap();
                Ok(Expr::Zero(Some(k)))
            } else if chars.peek().map_or(false, |x| x.is_alphanumeric()) {
                Ok(Expr::Name(format!("Z{}", read_alnum(chars))))
            } else {
                Ok(Expr::Zero(None))
            }
        }
        'S' => {
            if chars.peek().map_or(false, |x| x.is_alphanumeric()) {
                Ok(Expr::Name(format!("S{}", read_alnum(chars))))
            } else {
                Ok(Expr::Succ)
            }
        }
        'P' => {
            if chars.peek() == Some(&'(') {
                chars.next();
                let k = read_digits(chars).ok_or("Expected k in P(k,i)")?;
                eat(chars, ',')?;
                let i = read_digits(chars).ok_or("Expected i in P(k,i)")?;
                eat(chars, ')')?;
                Ok(Expr::Proj(Some(k), i))
            } else if chars.peek().map_or(false, |x| x.is_ascii_digit()) {
                let i = read_digits(chars).unwrap();
                if chars.peek().map_or(false, |x| x.is_alphanumeric()) {
                    Ok(Expr::Name(format!("P{}{}", i, read_alnum(chars))))
                } else {
                    Ok(Expr::Proj(None, i))
                }
            } else if chars.peek().map_or(false, |x| x.is_alphabetic()) {
                Ok(Expr::Name(format!("P{}", read_alnum(chars))))
            } else {
                Err("Bare 'P' without '(' or index digit".to_string())
            }
        }
        'C' => {
            if chars.peek() == Some(&'(') {
                chars.next();
                let h = parse_expr(chars)?;
                eat(chars, ',')?;
                let mut gs = vec![parse_expr(chars)?];
                while chars.peek() == Some(&',') {
                    chars.next();
                    gs.push(parse_expr(chars)?);
                }
                eat(chars, ')')?;
                Ok(Expr::Comp(Box::new(h), gs))
            } else {
                Ok(Expr::Name(format!("C{}", read_alnum(chars))))
            }
        }
        'R' => {
            if chars.peek() == Some(&'(') {
                chars.next();
                let g = parse_expr(chars)?;
                eat(chars, ',')?;
                let h = parse_expr(chars)?;
                eat(chars, ')')?;
                Ok(Expr::Rec(Box::new(g), Box::new(h)))
            } else {
                Ok(Expr::Name(format!("R{}", read_alnum(chars))))
            }
        }
        'M' => {
            if chars.peek() == Some(&'(') {
                chars.next();
                let f = parse_expr(chars)?;
                eat(chars, ')')?;
                Ok(Expr::Min(Box::new(f)))
            } else {
                Ok(Expr::Name(format!("M{}", read_alnum(chars))))
            }
        }
        'K' => {
            if chars.peek() == Some(&'[') {
                chars.next();
                let n = read_digits(chars).ok_or("Expected n in K[n]")?;
                eat(chars, ']')?;
                Ok(Expr::Const(n as u64))
            } else {
                Ok(Expr::Name(format!("K{}", read_alnum(chars))))
            }
        }
        c if c.is_ascii_uppercase() => Ok(Expr::Name(format!("{}{}", c, read_alnum(chars)))),
        other => Err(format!("Unexpected character: {:?}", other)),
    }
}

fn read_digits(chars: &mut Peekable<Chars>) -> Option<usize> {
    let mut s = String::new();
    while chars.peek().map_or(false, |c| c.is_ascii_digit()) {
        s.push(chars.next().unwrap());
    }
    s.parse().ok()
}

fn read_alnum(chars: &mut Peekable<Chars>) -> String {
    let mut s = String::new();
    while chars.peek().map_or(false, |c| c.is_alphanumeric()) {
        s.push(chars.next().unwrap());
    }
    s
}

fn eat(chars: &mut Peekable<Chars>, expected: char) -> Result<(), String> {
    match chars.next() {
        Some(c) if c == expected => Ok(()),
        Some(c) => Err(format!("Expected {:?}, got {:?}", expected, c)),
        None => Err(format!("Expected {:?}, got end of input", expected)),
    }
}

// ── Arity inference ───────────────────────────────────────────────────────────

// Phase 1: bottom-up minimum arity.
// For bare Z: min 0. For Pk: min k (index must be ≤ arity).
// Propagates through R/C/M to find the minimum consistent arity.
fn min_arity(expr: &Expr, known: &HashMap<String, usize>) -> Result<usize, String> {
    Ok(match expr {
        Expr::Zero(Some(k)) => *k,
        Expr::Zero(None) => 0,
        Expr::Succ => 1,
        Expr::Proj(Some(k), _) => *k,
        Expr::Proj(None, i) => *i,
        Expr::Comp(_, gs) => {
            let mut max = 0usize;
            for g in gs {
                max = max.max(min_arity(g, known)?);
            }
            max
        }
        Expr::Rec(g, h) => {
            let gm = min_arity(g, known)?;
            let hm = min_arity(h, known)?;
            // h.arity = g.arity + 2, so min k = max(gm, hm.saturating_sub(2))
            gm.max(hm.saturating_sub(2)) + 1
        }
        Expr::Min(f) => min_arity(f, known)?.saturating_sub(1),
        Expr::Name(n) => *known
            .get(n)
            .ok_or_else(|| format!("Undefined name {:?}", n))?,
        Expr::Const(_) => 0,
    })
}

// Phase 2: top-down resolution.
// Given the target arity for this expression, fill in all unknown arities
// and produce a concrete Grf (with named references substituted inline).
fn resolve(expr: &Expr, target: usize, known: &HashMap<String, Grf>) -> Result<Grf, String> {
    match expr {
        Expr::Zero(Some(k)) => {
            if *k != target {
                return Err(format!("Z{}: explicit arity {} vs required {}", k, k, target));
            }
            Ok(Grf::Zero(*k))
        }
        Expr::Zero(None) => Ok(Grf::Zero(target)),
        Expr::Succ => {
            if target != 1 {
                return Err(format!("S has arity 1, required {}", target));
            }
            Ok(Grf::Succ)
        }
        Expr::Proj(Some(k), i) => {
            if *k != target {
                return Err(format!("P({},{}): explicit arity {} vs required {}", k, i, k, target));
            }
            Ok(Grf::Proj(*k, *i))
        }
        Expr::Proj(None, i) => Ok(Grf::Proj(target, *i)),
        Expr::Comp(h, gs) => {
            let m = gs.len();
            // Each g_i gets the result arity (= input arity of the composition).
            let resolved_gs: Vec<Grf> = gs
                .iter()
                .map(|g| resolve(g, target, known))
                .collect::<Result<_, _>>()?;
            // h takes m inputs (one per g_i).
            let resolved_h = resolve(h, m, known)?;
            Ok(Grf::comp(resolved_h, resolved_gs))
        }
        Expr::Rec(g, h) => {
            let k = target
                .checked_sub(1)
                .ok_or("Rec result arity must be ≥ 1")?;
            let rg = resolve(g, k, known)?;
            let rh = resolve(h, k + 2, known)?;
            Ok(Grf::rec(rg, rh))
        }
        Expr::Min(f) => {
            let rf = resolve(f, target + 1, known)?;
            Ok(Grf::min(rf))
        }
        Expr::Name(n) => {
            let grf = known
                .get(n)
                .ok_or_else(|| format!("Undefined name {:?}", n))?
                .clone();
            if grf.arity() != target {
                return Err(format!(
                    "Name {:?} has arity {} but required {}",
                    n,
                    grf.arity(),
                    target
                ));
            }
            Ok(grf)
        }
        Expr::Const(val) => Ok(make_const(*val, target)),
    }
}

fn make_const(n: u64, arity: usize) -> Grf {
    if n == 0 {
        Grf::Zero(arity)
    } else {
        Grf::comp(Grf::Succ, vec![make_const(n - 1, arity)])
    }
}

// ── Tests ─────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    fn single(content: &str) -> Grf {
        let defs = parse_igrf_to_grfs(content).unwrap();
        assert_eq!(defs.len(), 1);
        defs.into_iter().next().unwrap().1
    }

    #[test]
    fn test_pred() {
        let g = single("Pred := R(Z, P1)");
        assert_eq!(g.arity(), 1);
        assert_eq!(g.to_string(), "R(Z0, P(2,1))");
    }

    #[test]
    fn test_add() {
        let g = single("Add := R(P1, C(S, P2))");
        assert_eq!(g.arity(), 2);
        assert_eq!(g.to_string(), "R(P(1,1), C(S, P(3,2)))");
    }

    #[test]
    fn test_monus2() {
        let g = single("Monus2 := R(Z, R(Z, P1))");
        assert_eq!(g.arity(), 1);
        assert_eq!(g.to_string(), "R(Z0, R(Z1, P(3,1)))");
    }

    #[test]
    fn test_explicit_notation() {
        // Lines that already use full P(k,i) and Zk notation pass through unchanged.
        let g = single("Mod3 := R(Z0, C(R(S, R(P(2,1), Z4)), P(2,2), P(2,2)))");
        assert_eq!(g.arity(), 1);
    }

    #[test]
    fn test_named_ref() {
        let defs = parse_igrf_to_grfs("Pred := R(Z, P1)\nPow2 := C(S, Pred)").unwrap();
        assert_eq!(defs.len(), 2);
        // C(S, Pred) where Pred has arity 1; result has arity 1.
        assert_eq!(defs[1].1.arity(), 1);
    }

    #[test]
    fn test_const() {
        // K[3] of arity 0 = C(S, C(S, C(S, Z0)))
        let g = single("F := C(S, K[3])");
        assert_eq!(g.arity(), 0);
    }

    #[test]
    fn test_erdos_file() {
        let content = std::fs::read_to_string("erdos.igrf").unwrap();
        let defs = parse_igrf_to_grfs(&content).unwrap();
        assert!(!defs.is_empty());
        // ErdosTernConj should be arity 0 (nullary: halts iff conjecture is false)
        let last = defs.last().unwrap();
        assert_eq!(last.0, "ErdosTernConj");
        assert_eq!(last.1.arity(), 0);
    }
}
