use std::collections::HashMap;
use std::iter::Peekable;
use std::path::Path;
use std::str::Chars;

use crate::grf::Grf;

/// A single inline spec test from a `.mgrf` file.
#[derive(Debug, Clone)]
pub struct TestCase {
    pub name: String,
    pub args: Vec<u64>,
    /// `Some(v)` = expects value v; `None` = expects divergence (⊥).
    pub expected: Option<u64>,
}

/// Parsed `.mgrf` file: resolved GRF definitions plus inline spec tests.
pub struct IgrfFile {
    pub defs: Vec<(String, Grf)>,
    pub tests: Vec<TestCase>,
}

// Internal AST for mgrf expressions before arity inference.
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
    Lift(Box<Expr>, usize),     // explicit arity lift: Name^k
}

// A `use module::{Name, ...}` or `use module` import request.
struct UseStatement {
    module: String,
    names: Option<Vec<String>>, // None = import everything
}

/// Parse a `.mgrf` file into resolved GRF definitions and inline spec tests.
///
/// `base_dir` is required when the file contains `use` statements; pass
/// `None` only for content that is known to have no imports.
pub fn parse_mgrf_file(content: &str, base_dir: Option<&Path>) -> Result<IgrfFile, String> {
    let (use_stmts, raw_defs, tests) = parse_file(content, true)?;
    let mut arities: HashMap<String, usize> = HashMap::new();
    let mut grfs: HashMap<String, Grf> = HashMap::new();

    // Process imports before local defs so imported names are in scope.
    if !use_stmts.is_empty() {
        let dir = base_dir.ok_or_else(|| {
            "use statements require a base_dir (file path must be known)".to_string()
        })?;
        for stmt in &use_stmts {
            load_import(stmt, dir, &mut arities, &mut grfs)?;
        }
    }

    let mut defs = Vec::new();
    for (name, expr) in &raw_defs {
        let ar = min_arity(expr, &arities)
            .map_err(|e| format!("In definition of {}: {}", name, e))?;
        let grf = resolve(expr, ar, &grfs)
            .map_err(|e| format!("In definition of {}: {}", name, e))?;
        arities.insert(name.clone(), ar);
        grfs.insert(name.clone(), grf.clone());
        defs.push((name.clone(), grf));
    }
    Ok(IgrfFile { defs, tests })
}

/// Parse a `.mgrf` file and return only the GRF definitions.
pub fn parse_mgrf_to_grfs(content: &str) -> Result<Vec<(String, Grf)>, String> {
    parse_mgrf_file(content, None).map(|f| f.defs)
}

// Load an imported module and insert the requested names into arities/grfs.
fn load_import(
    stmt: &UseStatement,
    dir: &Path,
    arities: &mut HashMap<String, usize>,
    grfs: &mut HashMap<String, Grf>,
) -> Result<(), String> {
    let module_path = dir.join(format!("{}.mgrf", stmt.module));
    let content = std::fs::read_to_string(&module_path).map_err(|e| {
        format!("Cannot load module '{}' ({}): {}", stmt.module, module_path.display(), e)
    })?;

    // allow_use=false: transitive imports are not permitted.
    let (sub_uses, sub_defs, _) = parse_file(&content, false).map_err(|e| {
        format!("In module '{}': {}", stmt.module, e)
    })?;
    debug_assert!(sub_uses.is_empty(), "parse_file with allow_use=false should never return uses");

    // Resolve the imported module's definitions in isolation.
    let mut sub_arities: HashMap<String, usize> = HashMap::new();
    let mut sub_grfs: HashMap<String, Grf> = HashMap::new();
    for (name, expr) in &sub_defs {
        let ar = min_arity(expr, &sub_arities)
            .map_err(|e| format!("In module '{}', def '{}': {}", stmt.module, name, e))?;
        let grf = resolve(expr, ar, &sub_grfs)
            .map_err(|e| format!("In module '{}', def '{}': {}", stmt.module, name, e))?;
        sub_arities.insert(name.clone(), ar);
        sub_grfs.insert(name.clone(), grf);
    }

    // Import the requested names.
    match &stmt.names {
        None => {
            for (name, grf) in &sub_grfs {
                arities.insert(name.clone(), grf.arity());
                grfs.insert(name.clone(), grf.clone());
            }
        }
        Some(names) => {
            for req in names {
                let grf = sub_grfs.get(req).ok_or_else(|| {
                    format!("Name '{}' not found in module '{}'", req, stmt.module)
                })?;
                arities.insert(req.clone(), grf.arity());
                grfs.insert(req.clone(), grf.clone());
            }
        }
    }
    Ok(())
}

// ── File-level parser ─────────────────────────────────────────────────────────

fn parse_file(
    content: &str,
    allow_use: bool,
) -> Result<(Vec<UseStatement>, Vec<(String, Expr)>, Vec<TestCase>), String> {
    let mut use_stmts = Vec::new();
    let mut defs = Vec::new();
    let mut tests = Vec::new();
    for (lineno, line) in content.lines().enumerate() {
        let line = if let Some(i) = line.find('#') { &line[..i] } else { line }.trim();
        if line.is_empty() {
            continue;
        }
        if line.starts_with("use ") {
            if !allow_use {
                return Err(format!(
                    "Line {}: use statements are not allowed in imported modules \
                     (transitive imports are not supported)",
                    lineno + 1
                ));
            }
            let stmt = parse_use_statement(&line["use ".len()..]).ok_or_else(|| {
                format!("Line {}: invalid use statement {:?}", lineno + 1, line)
            })?;
            use_stmts.push(stmt);
        } else if line.contains("==") {
            let tc = parse_test_line(line).ok_or_else(|| {
                format!("Line {}: invalid test line {:?}", lineno + 1, line)
            })?;
            tests.push(tc);
        } else {
            let (name, rest) = line
                .split_once(":=")
                .ok_or_else(|| format!("Line {}: no ':=' found in {:?}", lineno + 1, line))?;
            let name = name.trim().to_string();
            let expr_str: String = rest.chars().filter(|c| !c.is_whitespace()).collect();
            let expr = parse_expr_str(&expr_str)
                .map_err(|e| format!("Line {}: parse error in {:?}: {}", lineno + 1, line, e))?;
            defs.push((name, expr));
        }
    }
    Ok((use_stmts, defs, tests))
}

fn parse_use_statement(s: &str) -> Option<UseStatement> {
    let s = s.trim();
    if let Some(colon_pos) = s.find("::") {
        let module = s[..colon_pos].trim().to_string();
        let names_part = s[colon_pos + 2..].trim();
        if names_part.starts_with('{') && names_part.ends_with('}') {
            let names = names_part[1..names_part.len() - 1]
                .split(',')
                .map(|n| n.trim().to_string())
                .filter(|n| !n.is_empty())
                .collect::<Vec<_>>();
            if names.is_empty() {
                return None;
            }
            Some(UseStatement { module, names: Some(names) })
        } else {
            None
        }
    } else {
        // `use module` — import everything
        let module = s.to_string();
        if module.is_empty() || !module.chars().all(|c| c.is_alphanumeric() || c == '_') {
            return None;
        }
        Some(UseStatement { module, names: None })
    }
}

fn parse_test_line(line: &str) -> Option<TestCase> {
    let (lhs, rhs) = line.split_once("==")?;
    let rhs = rhs.trim();
    let expected: Option<u64> = if rhs == "⊥" {
        None
    } else {
        Some(rhs.parse().ok()?)
    };
    let lhs = lhs.trim();
    let lparen = lhs.find('(')?;
    let rparen = lhs.rfind(')')?;
    if rparen != lhs.len() - 1 {
        return None;
    }
    let name = lhs[..lparen].trim().to_string();
    let args_str = &lhs[lparen + 1..rparen];
    let args: Vec<u64> = if args_str.trim().is_empty() {
        vec![]
    } else {
        args_str
            .split(',')
            .map(|s| s.trim().parse().ok())
            .collect::<Option<Vec<_>>>()?
    };
    Some(TestCase { name, args, expected })
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

// If the next character is `^`, consume it and the following integer to produce
// an explicit arity-lift node; otherwise return a plain Name.
fn name_or_lift(name: String, chars: &mut Peekable<Chars>) -> Result<Expr, String> {
    if chars.peek() == Some(&'^') {
        chars.next();
        let k = read_digits(chars)
            .ok_or_else(|| "Expected number after '^'".to_string())?;
        Ok(Expr::Lift(Box::new(Expr::Name(name)), k))
    } else {
        Ok(Expr::Name(name))
    }
}

fn parse_expr(chars: &mut Peekable<Chars>) -> Result<Expr, String> {
    let c = chars.next().ok_or("Unexpected end of input")?;
    match c {
        'Z' => {
            if chars.peek().map_or(false, |x| x.is_ascii_digit()) {
                let k = read_digits(chars).unwrap();
                Ok(Expr::Zero(Some(k)))
            } else if chars.peek().map_or(false, |x| x.is_alphanumeric()) {
                name_or_lift(format!("Z{}", read_alnum(chars)), chars)
            } else {
                Ok(Expr::Zero(None))
            }
        }
        'S' => {
            if chars.peek().map_or(false, |x| x.is_alphanumeric()) {
                name_or_lift(format!("S{}", read_alnum(chars)), chars)
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
                    name_or_lift(format!("P{}{}", i, read_alnum(chars)), chars)
                } else {
                    Ok(Expr::Proj(None, i))
                }
            } else if chars.peek().map_or(false, |x| x.is_alphabetic()) {
                name_or_lift(format!("P{}", read_alnum(chars)), chars)
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
                name_or_lift(format!("C{}", read_alnum(chars)), chars)
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
                name_or_lift(format!("R{}", read_alnum(chars)), chars)
            }
        }
        'M' => {
            if chars.peek() == Some(&'(') {
                chars.next();
                let f = parse_expr(chars)?;
                eat(chars, ')')?;
                Ok(Expr::Min(Box::new(f)))
            } else {
                name_or_lift(format!("M{}", read_alnum(chars)), chars)
            }
        }
        'K' => {
            if chars.peek() == Some(&'[') {
                chars.next();
                let n = read_digits(chars).ok_or("Expected n in K[n]")?;
                eat(chars, ']')?;
                Ok(Expr::Const(n as u64))
            } else {
                name_or_lift(format!("K{}", read_alnum(chars)), chars)
            }
        }
        c if c.is_ascii_uppercase() => {
            let name = format!("{}{}", c, read_alnum(chars));
            name_or_lift(name, chars)
        }
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
        // Explicit lift overrides the inner arity.
        Expr::Lift(_, k) => *k,
    })
}

// ── Structural arity lifting ──────────────────────────────────────────────────

// Structurally rewrites `grf` to accept `target` inputs instead of its current
// arity, by recursively updating arity annotations on leaf nodes.  The extra
// input positions are ignored by the lifted function.
//
// Errors if target < current arity, or if the tree contains Succ (which has a
// fixed arity of 1 and cannot be structurally lifted).
fn lift_grf(grf: &Grf, target: usize) -> Result<Grf, String> {
    let current = grf.arity();
    if current == target {
        return Ok(grf.clone());
    }
    if current > target {
        return Err(format!(
            "Cannot reduce arity: expression has arity {} but lift target is {}",
            current, target
        ));
    }
    match grf {
        Grf::Zero(_) => Ok(Grf::Zero(target)),
        Grf::Succ => Err(format!(
            "Cannot lift S (arity 1) to arity {}: S has a fixed arity",
            target
        )),
        Grf::Proj(_, i) => Ok(Grf::Proj(target, *i)),
        Grf::Comp(h, gs, _) => {
            if gs.is_empty() {
                // 0-arg Comp: just change the outer arity.
                Ok(Grf::comp0(*h.clone(), target))
            } else {
                let lifted_gs = gs
                    .iter()
                    .map(|g| lift_grf(g, target))
                    .collect::<Result<Vec<_>, _>>()?;
                // h's arity (= number of gs) is unchanged.
                Ok(Grf::comp(*h.clone(), lifted_gs))
            }
        }
        Grf::Rec(g, h) => {
            // R(g,h) has arity g.arity()+1.  Lifting to `target` means lifting
            // g to target-1 and h to target+1.
            let lg = lift_grf(g, target - 1)?;
            let lh = lift_grf(h, target + 1)?;
            Ok(Grf::rec(lg, lh))
        }
        Grf::Min(f) => {
            let lf = lift_grf(f, target + 1)?;
            Ok(Grf::min(lf))
        }
    }
}

// ── Resolution ────────────────────────────────────────────────────────────────

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
            let actual = grf.arity();
            if actual == target {
                Ok(grf)
            } else if actual < target {
                // Implicit structural lift: the extra arguments are ignored.
                lift_grf(&grf, target)
                    .map_err(|e| format!("Implicit lift of {:?}: {}", n, e))
            } else {
                Err(format!(
                    "Name {:?} has arity {} but required {} (cannot reduce arity)",
                    n, actual, target
                ))
            }
        }
        Expr::Const(val) => Ok(make_const(*val, target)),
        Expr::Lift(inner, k) => {
            if *k != target {
                return Err(format!(
                    "Explicit lift to arity {} but context requires arity {}",
                    k, target
                ));
            }
            // Resolve the inner expression at its natural arity, then lift.
            let temp_arities: HashMap<String, usize> =
                known.iter().map(|(n, g)| (n.clone(), g.arity())).collect();
            let natural_ar = min_arity(inner, &temp_arities)
                .map_err(|e| format!("In lift target: {}", e))?;
            let inner_grf = resolve(inner, natural_ar, known)?;
            lift_grf(&inner_grf, *k)
                .map_err(|e| format!("In explicit lift ^{}: {}", k, e))
        }
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
        let defs = parse_mgrf_to_grfs(content).unwrap();
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
        let defs = parse_mgrf_to_grfs("Pred := R(Z, P1)\nPow2 := C(S, Pred)").unwrap();
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
        let content = include_str!("../mgrf/erdos.mgrf");
        let dir = std::path::Path::new("mgrf");
        let file = parse_mgrf_file(content, Some(dir)).unwrap();
        assert!(!file.defs.is_empty());
        let last = file.defs.last().unwrap();
        assert_eq!(last.0, "ErdosTernConj");
        assert_eq!(last.1.arity(), 0);
    }

    // ── Feature 2: arity lifting ──────────────────────────────────────────────

    #[test]
    fn test_implicit_lift() {
        // R(Z, Pred): Z has arity 0 (so g.arity=0, result arity=1), h needs arity 2.
        // Pred has arity 1, so it must be implicitly lifted to arity 2.
        let defs = parse_mgrf_to_grfs("Pred := R(Z, P1)\nMonus2 := R(Z, Pred)").unwrap();
        assert_eq!(defs[1].1.arity(), 1);
    }

    #[test]
    fn test_explicit_lift() {
        // Pred^2 explicitly lifts Pred to arity 2.
        let defs = parse_mgrf_to_grfs("Pred := R(Z, P1)\nMonus2 := R(Z, Pred^2)").unwrap();
        assert_eq!(defs[1].1.arity(), 1);
    }

    #[test]
    fn test_lift_result_correct() {
        // Both implicit and explicit lift of Pred to arity 2 should produce the same GRF.
        let imp = parse_mgrf_to_grfs("Pred := R(Z, P1)\nA := R(Z, Pred)").unwrap();
        let exp = parse_mgrf_to_grfs("Pred := R(Z, P1)\nA := R(Z, Pred^2)").unwrap();
        assert_eq!(imp[1].1, exp[1].1);
    }

    #[test]
    fn test_lift_succ_simple() {
        // Succ (arity 1) cannot be structurally lifted to arity 2.
        // R(Z, S) would require S at arity 2.
        let result = parse_mgrf_to_grfs("Bad := R(Z, S)");
        assert!(result.is_err(), "Expected error lifting S to arity 2");
    }

    #[test]
    fn test_lift_succ_indirect() {
        // AddS cannot be structurally lifted b/c S cannot be lifted.
        let result = parse_mgrf_to_grfs("AddS := R(S, C(S, P2))\nBad := C(AddS, Z, P1, P3)");
        assert!(result.is_err(), "Expected error lifting AddS to arity 3");
    }

    #[test]
    fn test_explicit_lift_arity_mismatch() {
        // Z2 fixes g at arity 2, so k=2 and h must have arity 4.
        // Pred^3 explicitly says arity 3, which conflicts with the required 4.
        let result = parse_mgrf_to_grfs("Pred := R(Z, P1)\nBad := R(Z2, Pred^3)");
        assert!(result.is_err(), "Expected error: explicit lift 3 vs required 4");
    }

    // ── Feature 1: use imports ────────────────────────────────────────────────

    fn write_tmp(filename: &str, content: &str) -> std::path::PathBuf {
        let dir = std::env::temp_dir();
        let path = dir.join(filename);
        std::fs::write(&path, content).unwrap();
        dir
    }

    #[test]
    fn test_use_import() {
        let dir = write_tmp("test_mgrf_mylib.mgrf", "Inc := C(S, P1)\n");
        let content = "use test_mgrf_mylib::{Inc}\nDouble := R(Z, C(Inc, P2))";
        let file = parse_mgrf_file(content, Some(&dir)).unwrap();
        let double = &file.defs.iter().find(|(n, _)| n == "Double").unwrap().1;
        assert_eq!(double.arity(), 1);
    }

    #[test]
    fn test_use_import_all() {
        let dir = write_tmp("test_mgrf_util.mgrf", "Inc := C(S, P1)\nDec := R(Z, P1)\n");
        let content = "use test_mgrf_util\nFoo := C(Inc, Dec)";
        let file = parse_mgrf_file(content, Some(&dir)).unwrap();
        assert!(file.defs.iter().any(|(n, _)| n == "Foo"));
    }

    #[test]
    fn test_use_transitive_import_blocked() {
        let dir = write_tmp("test_mgrf_b.mgrf", "use other\nFoo := P1\n");
        let content = "use test_mgrf_b::{Foo}";
        let result = parse_mgrf_file(content, Some(&dir));
        assert!(result.is_err(), "Expected error: transitive imports blocked");
    }
}
