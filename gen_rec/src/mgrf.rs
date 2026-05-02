use std::collections::HashMap;
use std::iter::Peekable;
use std::path::Path;
use std::str::Chars;

use crate::grf::Grf;

/// A single inline spec test from a `.mgrf` file.
#[derive(Debug, Clone)]
pub struct TestCase {
    pub name: String,
    /// Resolved GRF for tests whose name is a num-macro instantiation (e.g. `Plus[3]`).
    /// `None` means look the GRF up by name at run time.
    pub grf: Option<Grf>,
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
    NumMacroApp(String, NumExpr), // Name[numexpr]: apply a num-parameterized macro
}

// ── Num-parameterized macro types ─────────────────────────────────────────────

// A numeric argument passed to a num-macro application (inside `[...]`).
#[derive(Debug, Clone)]
enum NumExpr {
    Literal(usize),
    Variable(String), // lowercase identifier, valid only inside a macro body
}

// A pattern on the LHS of a num-macro definition.
#[derive(Debug, Clone)]
enum NumPattern {
    Literal(usize), // Name[5] := ...
    Succ(String),   // Name[n+1] := ... (binds the predecessor to the variable)
    Var(String),    // Name[n] := ...   (catch-all: binds n to the argument)
}

// All cases for one num-macro name, tried top-to-bottom.
#[derive(Debug, Default)]
struct NumMacroCases {
    cases: Vec<(NumPattern, Expr)>,
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
    let (use_stmts, raw_items, tests) = parse_file(content, true)?;
    let (num_macros, raw_defs) = split_macros(raw_items);

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
        let expanded = macro_expand(expr, &num_macros)
            .map_err(|e| format!("In macro expansion of {}: {}", name, e))?;
        let ar = min_arity(&expanded, &arities)
            .map_err(|e| format!("In definition of {}: {}", name, e))?;
        let grf = resolve(&expanded, ar, &grfs)
            .map_err(|e| format!("In definition of {}: {}", name, e))?;
        arities.insert(name.clone(), ar);
        grfs.insert(name.clone(), grf.clone());
        defs.push((name.clone(), grf));
    }

    // Resolve test cases whose name is a num-macro instantiation (e.g. `Plus[3]`).
    let tests = tests
        .into_iter()
        .map(|mut tc| {
            if tc.name.contains('[') || tc.name.contains('^') {
                let expr = parse_expr_str(&tc.name)
                    .map_err(|e| format!("In test {:?}: {}", tc.name, e))?;
                let expanded = macro_expand(&expr, &num_macros)
                    .map_err(|e| format!("In test {:?}: {}", tc.name, e))?;
                let ar = min_arity(&expanded, &arities)
                    .map_err(|e| format!("In test {:?}: {}", tc.name, e))?;
                let grf = resolve(&expanded, ar, &grfs)
                    .map_err(|e| format!("In test {:?}: {}", tc.name, e))?;
                tc.grf = Some(grf);
            }
            Ok(tc)
        })
        .collect::<Result<Vec<_>, String>>()?;

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
    let (sub_uses, sub_items, _) = parse_file(&content, false).map_err(|e| {
        format!("In module '{}': {}", stmt.module, e)
    })?;
    debug_assert!(sub_uses.is_empty(), "parse_file with allow_use=false should never return uses");

    let (sub_num_macros, sub_raw_defs) = split_macros(sub_items);

    // Resolve the imported module's definitions in isolation.
    let mut sub_arities: HashMap<String, usize> = HashMap::new();
    let mut sub_grfs: HashMap<String, Grf> = HashMap::new();
    for (name, expr) in &sub_raw_defs {
        let expanded = macro_expand(expr, &sub_num_macros)
            .map_err(|e| format!("In module '{}', macro expansion of '{}': {}", stmt.module, name, e))?;
        let ar = min_arity(&expanded, &sub_arities)
            .map_err(|e| format!("In module '{}', def '{}': {}", stmt.module, name, e))?;
        let grf = resolve(&expanded, ar, &sub_grfs)
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

// Partition raw parsed items into num-macro case tables and regular definitions.
fn split_macros(
    items: Vec<(String, Option<NumPattern>, Expr)>,
) -> (HashMap<String, NumMacroCases>, Vec<(String, Expr)>) {
    let mut num_macros: HashMap<String, NumMacroCases> = HashMap::new();
    let mut regular: Vec<(String, Expr)> = Vec::new();
    for (name, pattern_opt, expr) in items {
        if let Some(pattern) = pattern_opt {
            num_macros
                .entry(name)
                .or_default()
                .cases
                .push((pattern, expr));
        } else {
            regular.push((name, expr));
        }
    }
    (num_macros, regular)
}

// ── File-level parser ─────────────────────────────────────────────────────────

fn parse_file(
    content: &str,
    allow_use: bool,
) -> Result<(Vec<UseStatement>, Vec<(String, Option<NumPattern>, Expr)>, Vec<TestCase>), String> {
    let mut use_stmts = Vec::new();
    let mut items = Vec::new();
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
            let (lhs, rhs) = line
                .split_once(":=")
                .ok_or_else(|| format!("Line {}: no ':=' found in {:?}", lineno + 1, line))?;
            let (name, pattern) = parse_lhs(lhs)
                .map_err(|e| format!("Line {}: bad LHS in {:?}: {}", lineno + 1, line, e))?;
            let expr_str: String = rhs.chars().filter(|c| !c.is_whitespace()).collect();
            let expr = parse_expr_str(&expr_str)
                .map_err(|e| format!("Line {}: parse error in {:?}: {}", lineno + 1, line, e))?;
            items.push((name, pattern, expr));
        }
    }
    Ok((use_stmts, items, tests))
}

// Parse a definition LHS: either `Name` (regular def) or `Name[pattern]` (num-macro case).
fn parse_lhs(s: &str) -> Result<(String, Option<NumPattern>), String> {
    let s = s.trim();
    if let Some(bracket_pos) = s.find('[') {
        if !s.ends_with(']') {
            return Err(format!("Unclosed '[' in LHS {:?}", s));
        }
        let name = s[..bracket_pos].trim().to_string();
        let pattern_str = s[bracket_pos + 1..s.len() - 1].trim();
        let pattern = parse_num_pattern(pattern_str)
            .map_err(|e| format!("invalid pattern {:?}: {}", pattern_str, e))?;
        Ok((name, Some(pattern)))
    } else {
        Ok((s.to_string(), None))
    }
}

// Parse a num-macro LHS pattern: "0"/"k" (literal), "n" (var), "n+1" (succ).
fn parse_num_pattern(s: &str) -> Result<NumPattern, String> {
    if s.is_empty() {
        return Err("empty pattern".to_string());
    }
    if s.chars().all(|c| c.is_ascii_digit()) {
        return Ok(NumPattern::Literal(s.parse().unwrap()));
    }
    if let Some(plus) = s.find('+') {
        let var = s[..plus].trim();
        let inc = s[plus + 1..].trim();
        if inc != "1" {
            return Err(format!("only n+1 successor patterns are supported (got +{})", inc));
        }
        if var.is_empty() || !var.chars().all(|c| c.is_ascii_lowercase() || c.is_ascii_digit()) {
            return Err(format!("variable {:?} must be lowercase", var));
        }
        return Ok(NumPattern::Succ(var.to_string()));
    }
    if s.chars().all(|c| c.is_ascii_lowercase() || c.is_ascii_digit()) {
        return Ok(NumPattern::Var(s.to_string()));
    }
    Err(format!("unrecognised pattern {:?}", s))
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
    Some(TestCase { name, grf: None, args, expected })
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

// After reading an uppercase name, handle any combination of `^k` (explicit lift)
// and `[numexpr]` (num-macro application).  `^` must come before `[`.
fn name_or_suffixes(name: String, chars: &mut Peekable<Chars>) -> Result<Expr, String> {
    // Optional explicit arity lift.
    let lift_k = if chars.peek() == Some(&'^') {
        chars.next();
        Some(read_digits(chars).ok_or_else(|| "Expected number after '^'".to_string())?)
    } else {
        None
    };
    // Optional num-macro application.
    let base = if chars.peek() == Some(&'[') {
        chars.next();
        let num_arg = parse_num_expr(chars)?;
        eat(chars, ']')?;
        Expr::NumMacroApp(name, num_arg)
    } else {
        Expr::Name(name)
    };
    Ok(match lift_k {
        Some(k) => Expr::Lift(Box::new(base), k),
        None => base,
    })
}

// Parse a numeric argument inside `[...]`: either a decimal literal or a
// lowercase variable name.
fn parse_num_expr(chars: &mut Peekable<Chars>) -> Result<NumExpr, String> {
    if chars.peek().map_or(false, |c| c.is_ascii_digit()) {
        let n = read_digits(chars).unwrap();
        Ok(NumExpr::Literal(n))
    } else if chars.peek().map_or(false, |c| c.is_ascii_lowercase()) {
        Ok(NumExpr::Variable(read_lower_alnum(chars)))
    } else {
        Err(format!(
            "Expected number or lowercase variable in [...], got {:?}",
            chars.peek()
        ))
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
                name_or_suffixes(format!("Z{}", read_alnum(chars)), chars)
            } else {
                Ok(Expr::Zero(None))
            }
        }
        'S' => {
            if chars.peek().map_or(false, |x| x.is_alphanumeric()) {
                name_or_suffixes(format!("S{}", read_alnum(chars)), chars)
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
                    name_or_suffixes(format!("P{}{}", i, read_alnum(chars)), chars)
                } else {
                    Ok(Expr::Proj(None, i))
                }
            } else if chars.peek().map_or(false, |x| x.is_alphabetic()) {
                name_or_suffixes(format!("P{}", read_alnum(chars)), chars)
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
                name_or_suffixes(format!("C{}", read_alnum(chars)), chars)
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
                name_or_suffixes(format!("R{}", read_alnum(chars)), chars)
            }
        }
        'M' => {
            if chars.peek() == Some(&'(') {
                chars.next();
                let f = parse_expr(chars)?;
                eat(chars, ')')?;
                Ok(Expr::Min(Box::new(f)))
            } else {
                name_or_suffixes(format!("M{}", read_alnum(chars)), chars)
            }
        }
        'K' => {
            if chars.peek() == Some(&'[') {
                chars.next();
                let n = read_digits(chars).ok_or("Expected n in K[n]")?;
                eat(chars, ']')?;
                Ok(Expr::Const(n as u64))
            } else {
                name_or_suffixes(format!("K{}", read_alnum(chars)), chars)
            }
        }
        c if c.is_ascii_uppercase() => {
            name_or_suffixes(format!("{}{}", c, read_alnum(chars)), chars)
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

fn read_lower_alnum(chars: &mut Peekable<Chars>) -> String {
    let mut s = String::new();
    while chars.peek().map_or(false, |c| c.is_ascii_lowercase() || c.is_ascii_digit()) {
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

// ── Num-macro expansion ───────────────────────────────────────────────────────

// Expand all NumMacroApp nodes in `expr` to concrete Expr trees.
// Must be called before min_arity / resolve.
fn macro_expand(
    expr: &Expr,
    macros: &HashMap<String, NumMacroCases>,
) -> Result<Expr, String> {
    macro_expand_inner(expr, macros, &HashMap::new(), 0)
}

fn macro_expand_inner(
    expr: &Expr,
    macros: &HashMap<String, NumMacroCases>,
    env: &HashMap<String, usize>, // num-variable bindings from the enclosing macro body
    depth: usize,
) -> Result<Expr, String> {
    const MAX_DEPTH: usize = 4096;
    if depth > MAX_DEPTH {
        return Err(format!(
            "Num-macro expansion depth exceeded (limit {}); possible unbounded recursion",
            MAX_DEPTH
        ));
    }
    match expr {
        Expr::NumMacroApp(name, num_arg) => {
            let n = eval_num_expr(num_arg, env)?;
            expand_num_macro(name, n, macros, depth + 1)
        }
        Expr::Lift(inner, k) => Ok(Expr::Lift(
            Box::new(macro_expand_inner(inner, macros, env, depth)?),
            *k,
        )),
        Expr::Comp(h, gs) => {
            let eh = macro_expand_inner(h, macros, env, depth)?;
            let egs = gs
                .iter()
                .map(|g| macro_expand_inner(g, macros, env, depth))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Expr::Comp(Box::new(eh), egs))
        }
        Expr::Rec(g, h) => Ok(Expr::Rec(
            Box::new(macro_expand_inner(g, macros, env, depth)?),
            Box::new(macro_expand_inner(h, macros, env, depth)?),
        )),
        Expr::Min(f) => Ok(Expr::Min(Box::new(macro_expand_inner(
            f, macros, env, depth,
        )?))),
        // All other nodes are leaf-like — return unchanged.
        _ => Ok(expr.clone()),
    }
}

fn eval_num_expr(arg: &NumExpr, env: &HashMap<String, usize>) -> Result<usize, String> {
    match arg {
        NumExpr::Literal(n) => Ok(*n),
        NumExpr::Variable(v) => env
            .get(v)
            .copied()
            .ok_or_else(|| format!("Undefined numeric variable {:?}", v)),
    }
}

fn expand_num_macro(
    name: &str,
    n: usize,
    macros: &HashMap<String, NumMacroCases>,
    depth: usize,
) -> Result<Expr, String> {
    let cases = macros.get(name).ok_or_else(|| {
        format!(
            "Unknown num-macro {:?} — define it with `{}[pattern] := ...`",
            name, name
        )
    })?;
    for (pattern, body) in &cases.cases {
        match pattern {
            NumPattern::Literal(k) if *k == n => {
                // No num-variables in scope; literal case body is fully concrete.
                return macro_expand_inner(body, macros, &HashMap::new(), depth);
            }
            NumPattern::Succ(var) if n >= 1 => {
                let mut env = HashMap::new();
                env.insert(var.clone(), n - 1); // bind var to predecessor
                return macro_expand_inner(body, macros, &env, depth);
            }
            NumPattern::Var(var) => {
                let mut env = HashMap::new();
                env.insert(var.clone(), n);
                return macro_expand_inner(body, macros, &env, depth);
            }
            _ => continue,
        }
    }
    Err(format!("No case in num-macro {} matches argument {}", name, n))
}

// ── Arity inference ───────────────────────────────────────────────────────────

// Phase 1: bottom-up minimum arity.
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
            gm.max(hm.saturating_sub(2)) + 1
        }
        Expr::Min(f) => min_arity(f, known)?.saturating_sub(1),
        Expr::Name(n) => *known
            .get(n)
            .ok_or_else(|| format!("Undefined name {:?}", n))?,
        Expr::Const(_) => 0,
        Expr::Lift(_, k) => *k,
        Expr::NumMacroApp(name, _) => {
            return Err(format!(
                "Unexpanded num-macro {:?} reached arity inference; \
                 this is an internal error",
                name
            ));
        }
    })
}

// ── Structural arity lifting ──────────────────────────────────────────────────

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
                Ok(Grf::comp0(*h.clone(), target))
            } else {
                let lifted_gs = gs
                    .iter()
                    .map(|g| lift_grf(g, target))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Grf::comp(*h.clone(), lifted_gs))
            }
        }
        Grf::Rec(g, h) => {
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
                return Err(format!(
                    "P({},{}): explicit arity {} vs required {}",
                    k, i, k, target
                ));
            }
            Ok(Grf::Proj(*k, *i))
        }
        Expr::Proj(None, i) => Ok(Grf::Proj(target, *i)),
        Expr::Comp(h, gs) => {
            let m = gs.len();
            let resolved_gs: Vec<Grf> = gs
                .iter()
                .map(|g| resolve(g, target, known))
                .collect::<Result<_, _>>()?;
            let resolved_h = resolve(h, m, known)?;
            Ok(Grf::comp(resolved_h, resolved_gs))
        }
        Expr::Rec(g, h) => {
            let k = target.checked_sub(1).ok_or("Rec result arity must be ≥ 1")?;
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
            let temp_arities: HashMap<String, usize> =
                known.iter().map(|(n, g)| (n.clone(), g.arity())).collect();
            let natural_ar = min_arity(inner, &temp_arities)
                .map_err(|e| format!("In lift target: {}", e))?;
            let inner_grf = resolve(inner, natural_ar, known)?;
            lift_grf(&inner_grf, *k)
                .map_err(|e| format!("In explicit lift ^{}: {}", k, e))
        }
        Expr::NumMacroApp(name, _) => Err(format!(
            "Unexpanded num-macro {:?} reached resolution; this is an internal error",
            name
        )),
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

    fn parse_defs(content: &str) -> HashMap<String, Grf> {
        parse_mgrf_to_grfs(content).unwrap().into_iter().collect()
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
        let g = single("Mod3 := R(Z0, C(R(S, R(P(2,1), Z4)), P(2,2), P(2,2)))");
        assert_eq!(g.arity(), 1);
    }

    #[test]
    fn test_named_ref() {
        let defs = parse_mgrf_to_grfs("Pred := R(Z, P1)\nPow2 := C(S, Pred)").unwrap();
        assert_eq!(defs.len(), 2);
        assert_eq!(defs[1].1.arity(), 1);
    }

    #[test]
    fn test_const() {
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
        let defs = parse_mgrf_to_grfs("Pred := R(Z, P1)\nMonus2 := R(Z, Pred)").unwrap();
        assert_eq!(defs[1].1.arity(), 1);
    }

    #[test]
    fn test_explicit_lift() {
        let defs = parse_mgrf_to_grfs("Pred := R(Z, P1)\nMonus2 := R(Z, Pred^2)").unwrap();
        assert_eq!(defs[1].1.arity(), 1);
    }

    #[test]
    fn test_lift_result_correct() {
        let imp = parse_mgrf_to_grfs("Pred := R(Z, P1)\nA := R(Z, Pred)").unwrap();
        let exp = parse_mgrf_to_grfs("Pred := R(Z, P1)\nA := R(Z, Pred^2)").unwrap();
        assert_eq!(imp[1].1, exp[1].1);
    }

    #[test]
    fn test_lift_succ_errors() {
        let result = parse_mgrf_to_grfs("Bad := R(Z, S)");
        assert!(result.is_err(), "Expected error lifting S to arity 2");
    }

    #[test]
    fn test_explicit_lift_arity_mismatch() {
        // Z2 fixes g at arity 2, so k=2 and h must have arity 4.
        // Pred^3 says arity 3, which conflicts.
        let result = parse_mgrf_to_grfs("Pred := R(Z, P1)\nBad := R(Z2, Pred^3)");
        assert!(result.is_err(), "Expected error: explicit lift 3 vs required 4");
    }

    // ── Feature 1: use imports ────────────────────────────────────────────────

    fn write_tmp(filename: &str, content: &str) -> std::path::PathBuf {
        let dir = std::env::temp_dir();
        std::fs::write(dir.join(filename), content).unwrap();
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

    // ── Feature 4: num-parameterized macros ───────────────────────────────────

    // The user's examples verbatim.
    const NUM_EXAMPLES: &str = "
Plus[1] := S
Plus[n+1] := C(S, Plus[n])
Monus[0] := P1
Monus[n+1] := R(Z, Monus^2[n])
Mult[n] := R(Z, C(Plus[n], P2))
";

    #[test]
    fn test_plus_arities() {
        let content = format!("{}\nPlus1 := Plus[1]\nPlus3 := Plus[3]\nPlus5 := Plus[5]", NUM_EXAMPLES);
        let defs = parse_defs(&content);
        assert_eq!(defs["Plus1"].arity(), 1);
        assert_eq!(defs["Plus3"].arity(), 1);
        assert_eq!(defs["Plus5"].arity(), 1);
    }

    #[test]
    fn test_monus_arities() {
        let content = format!("{}\nM0 := Monus[0]\nM1 := Monus[1]\nM3 := Monus[3]", NUM_EXAMPLES);
        let defs = parse_defs(&content);
        assert_eq!(defs["M0"].arity(), 1);
        assert_eq!(defs["M1"].arity(), 1);
        assert_eq!(defs["M3"].arity(), 1);
    }

    #[test]
    fn test_mult_arities() {
        let content = format!("{}\nMult1 := Mult[1]\nMult4 := Mult[4]", NUM_EXAMPLES);
        let defs = parse_defs(&content);
        assert_eq!(defs["Mult1"].arity(), 1);
        assert_eq!(defs["Mult4"].arity(), 1);
    }

    #[test]
    fn test_monus_matches_direct() {
        // Monus[2] should equal R(Z, R(Z, P1)) — the standard Monus2.
        let via_macro = {
            let content = format!("{}\nResult := Monus[2]", NUM_EXAMPLES);
            parse_defs(&content).remove("Result").unwrap()
        };
        let direct = single("Result := R(Z, R(Z, P1))");
        assert_eq!(via_macro, direct);
    }

    #[test]
    fn test_plus_simulation() {
        use crate::simulate::simulate;
        let content = format!("{}\nPlus3 := Plus[3]\nPlus5 := Plus[5]", NUM_EXAMPLES);
        let defs = parse_defs(&content);
        // Plus[3](7) = 10
        let (r, _) = simulate(&defs["Plus3"], &[7], 10_000);
        assert_eq!(r.into_value(), Some(10));
        // Plus[5](0) = 5
        let (r, _) = simulate(&defs["Plus5"], &[0], 10_000);
        assert_eq!(r.into_value(), Some(5));
    }

    #[test]
    fn test_monus_simulation() {
        use crate::simulate::simulate;
        let content = format!("{}\nM1 := Monus[1]\nM3 := Monus[3]", NUM_EXAMPLES);
        let defs = parse_defs(&content);
        // Monus[1] = Pred: Pred(5) = 4, Pred(0) = 0
        let (r, _) = simulate(&defs["M1"], &[5], 10_000);
        assert_eq!(r.into_value(), Some(4));
        let (r, _) = simulate(&defs["M1"], &[0], 10_000);
        assert_eq!(r.into_value(), Some(0));
        // Monus[3](5) = 2, Monus[3](2) = 0
        let (r, _) = simulate(&defs["M3"], &[5], 10_000);
        assert_eq!(r.into_value(), Some(2));
        let (r, _) = simulate(&defs["M3"], &[2], 10_000);
        assert_eq!(r.into_value(), Some(0));
    }

    #[test]
    fn test_mult_simulation() {
        use crate::simulate::simulate;
        let content = format!("{}\nMult3 := Mult[3]\nMult5 := Mult[5]", NUM_EXAMPLES);
        let defs = parse_defs(&content);
        // Mult[3](4) = 12
        let (r, _) = simulate(&defs["Mult3"], &[4], 100_000);
        assert_eq!(r.into_value(), Some(12));
        // Mult[5](3) = 15
        let (r, _) = simulate(&defs["Mult5"], &[3], 100_000);
        assert_eq!(r.into_value(), Some(15));
    }

    #[test]
    fn test_num_macro_no_matching_case() {
        // Plus[n] has no case for n=0, so Plus[0] must error at expansion time.
        let content = format!("{}\nBad := Plus[0]", NUM_EXAMPLES);
        let result = parse_mgrf_to_grfs(&content);
        assert!(result.is_err(), "Expected error: no case for Plus[0]");
    }

    #[test]
    fn test_num_macro_test_cases() {
        let content = format!(
            "{}\nPlus[3](0) == 3\nPlus[3](7) == 10\nMonus[3](5) == 2\nMonus[3](2) == 0",
            NUM_EXAMPLES
        );
        let file = parse_mgrf_file(&content, None).unwrap();
        assert_eq!(file.tests.len(), 4);
        for tc in &file.tests {
            assert!(tc.grf.is_some(), "test {:?} should have a resolved grf", tc.name);
        }
    }

    #[test]
    fn test_num_macro_variable_unbound_outside_body() {
        // 'n' is a num-variable; it must not be usable at top level.
        // Parsing Plus[n] at top level (n not bound) should fail at expansion.
        let content = format!("{}\nBad := Plus[n]", NUM_EXAMPLES);
        let result = parse_mgrf_to_grfs(&content);
        assert!(result.is_err(), "Expected error: 'n' unbound at top level");
    }
}
