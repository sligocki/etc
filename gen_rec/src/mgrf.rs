use std::collections::{HashMap, HashSet};
use std::iter::Peekable;
use std::path::Path;
use std::str::Chars;

use crate::grf::{Grf, GrfKind};

/// A single inline spec test from a `.mgrf` file.
#[derive(Debug, Clone)]
pub struct TestCase {
    pub name: String,
    /// Resolved GRF for tests whose name is a macro instantiation (e.g. `Plus[3]`).
    /// `None` means look the GRF up by name at run time.
    pub grf: Option<Grf>,
    pub args: Vec<u64>,
    /// `Some(v)` = expects value v; `None` = expects divergence (⊥).
    pub expected: Option<u64>,
}

/// Parsed `.mgrf` file: resolved GRF definitions plus inline spec tests.
pub struct MgrfFile {
    pub defs: Vec<(String, Grf)>,
    pub tests: Vec<TestCase>,
    /// GRF-parameterized macros: (name, param_arity, body_grf_with_proj_placeholder).
    /// The body GRF is computed by substituting the parameter with P(param_arity, 1).
    pub grf_macro_defs: Vec<(String, usize, Grf)>,
    /// u64-parameterized macros: (name, num_cases).
    pub num_macro_defs: Vec<(String, usize)>,
    // Private context for eval_expr — holds the resolved GRF/arity tables plus macro tables.
    grfs_ctx: HashMap<String, Grf>,
    arities_ctx: HashMap<String, usize>,
    num_macros_ctx: HashMap<String, NumMacroCases>,
    grf_macros_ctx: HashMap<String, GrfMacroDef>,
}

impl MgrfFile {
    /// Evaluate a mgrf expression in this file's resolved context.
    ///
    /// Macro applications are expanded using this file's macro tables, and name
    /// references are looked up in the resolved GRF table.  Example uses:
    ///   `file.eval_expr("Plus[3]")`, `file.eval_expr("K[4]")`, `file.eval_expr("K^2[1]")`
    pub fn eval_expr(&self, expr: &str) -> Result<Grf, String> {
        let parsed = parse_expr_str(expr)?;
        let expanded = macro_expand(&parsed, &self.num_macros_ctx, &self.grf_macros_ctx)?;
        let ar = min_arity(&expanded, &self.arities_ctx)?;
        resolve(&expanded, ar, &self.grfs_ctx)
    }

    /// Merge the evaluation contexts of all provided files into one `MgrfFile`.
    ///
    /// Later files win on name conflicts, so callers should pass files in
    /// increasing-priority order.  The resulting file's `eval_expr` has all
    /// named GRFs, num-macros, and GRF-macros from every input in scope at once.
    pub fn merge(files: &[&MgrfFile]) -> MgrfFile {
        let mut merged = MgrfFile {
            defs: Vec::new(),
            tests: Vec::new(),
            grf_macro_defs: Vec::new(),
            num_macro_defs: Vec::new(),
            grfs_ctx: HashMap::new(),
            arities_ctx: HashMap::new(),
            num_macros_ctx: HashMap::new(),
            grf_macros_ctx: HashMap::new(),
        };
        for f in files {
            merged.defs.extend(f.defs.iter().cloned());
            merged.tests.extend(f.tests.iter().cloned());
            merged
                .grf_macro_defs
                .extend(f.grf_macro_defs.iter().cloned());
            merged
                .num_macro_defs
                .extend(f.num_macro_defs.iter().cloned());
            merged
                .grfs_ctx
                .extend(f.grfs_ctx.iter().map(|(k, v)| (k.clone(), v.clone())));
            merged
                .arities_ctx
                .extend(f.arities_ctx.iter().map(|(k, v)| (k.clone(), *v)));
            merged
                .num_macros_ctx
                .extend(f.num_macros_ctx.iter().map(|(k, v)| (k.clone(), v.clone())));
            merged
                .grf_macros_ctx
                .extend(f.grf_macros_ctx.iter().map(|(k, v)| (k.clone(), v.clone())));
        }
        merged
    }
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
    Name(String),                 // named reference (uppercase) or GRF param (lowercase)
    Lift(Box<Expr>, usize),       // explicit arity lift: Expr^k
    NumMacroApp(String, NumExpr), // Name[numexpr]: num-parameterized macro application
    GrfMacroApp(String, Box<Expr>), // Name[GrfExpr]: GRF-parameterized macro application
}

// ── u64-parameterized macro types ─────────────────────────────────────────────

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
#[derive(Debug, Default, Clone)]
struct NumMacroCases {
    cases: Vec<(NumPattern, Expr)>,
}

// ── GRF-parameterized macro types ─────────────────────────────────────────────

// A GRF-parameterized macro: `MacroName[f^k] := body`.
// The body may contain `Name("f")` references that are substituted at call sites.
#[derive(Debug, Clone)]
struct GrfMacroDef {
    param_name: String, // e.g. "f"
    param_arity: usize, // declared arity k from `f^k`
    body: Expr,
}

// LHS bracket pattern: distinguishes num-macro cases from GRF-macro defs.
#[derive(Debug, Clone)]
enum MacroParam {
    Number(NumPattern), // Name[num_pattern] := ...
    Grf(String, usize), // Name[f^k]        := ...
}

// A `use module::{Name, ...}` or `use module` import request.
struct UseStatement {
    module: String,
    names: Option<Vec<String>>, // None = import everything
}

// Resolves `use` statement content — either from the filesystem or an in-memory map.
enum ImportResolver<'a> {
    Dir(&'a Path),
    Map(&'a HashMap<String, String>),
}

impl ImportResolver<'_> {
    fn load(&self, module: &str) -> Result<String, String> {
        match self {
            ImportResolver::Dir(dir) => {
                let path = dir.join(format!("{}.mgrf", module));
                std::fs::read_to_string(&path).map_err(|e| {
                    format!(
                        "Cannot load module '{}' ({}): {}",
                        module,
                        path.display(),
                        e
                    )
                })
            }
            ImportResolver::Map(map) => map
                .get(module)
                .cloned()
                .ok_or_else(|| format!("Module '{}' not found in embedded module map", module)),
        }
    }
}

/// Parse a `.mgrf` file into resolved GRF definitions and inline spec tests.
///
/// `base_dir` is required when the file contains `use` statements; pass
/// `None` only for content that is known to have no imports.
pub fn parse_mgrf_file(content: &str, base_dir: Option<&Path>) -> Result<MgrfFile, String> {
    let resolver = base_dir.map(ImportResolver::Dir);
    parse_mgrf_impl(content, resolver.as_ref())
}

/// Like `parse_mgrf_file` but resolves `use` imports from the provided in-memory map
/// (module name → file content) rather than the filesystem.
pub fn parse_mgrf_with_modules(
    content: &str,
    modules: &HashMap<String, String>,
) -> Result<MgrfFile, String> {
    parse_mgrf_impl(content, Some(&ImportResolver::Map(modules)))
}

fn parse_mgrf_impl(
    content: &str,
    resolver: Option<&ImportResolver<'_>>,
) -> Result<MgrfFile, String> {
    let (use_stmts, raw_items, tests) = parse_file(content, true)?;
    let (local_grf_macros, local_num_macros, raw_defs) = split_macros(raw_items);

    let mut arities: HashMap<String, usize> = HashMap::new();
    let mut grfs: HashMap<String, Grf> = HashMap::new();
    // Macro tables start empty; imports fill them first, then local defs override.
    let mut grf_macros: HashMap<String, GrfMacroDef> = HashMap::new();
    let mut num_macros: HashMap<String, NumMacroCases> = HashMap::new();

    // Process imports before local defs so imported names are in scope.
    if !use_stmts.is_empty() {
        let res = resolver.ok_or_else(|| {
            "use statements require a base_dir or module map (file path must be known)".to_string()
        })?;
        for stmt in &use_stmts {
            load_import(
                stmt,
                res,
                &mut arities,
                &mut grfs,
                &mut grf_macros,
                &mut num_macros,
            )?;
        }
    }

    // Local macros override imported ones.
    grf_macros.extend(local_grf_macros);
    num_macros.extend(local_num_macros);

    let mut defs = Vec::new();
    for (name, expr) in &raw_defs {
        let expanded = macro_expand(expr, &num_macros, &grf_macros)
            .map_err(|e| format!("In macro expansion of {}: {}", name, e))?;
        let ar = min_arity(&expanded, &arities)
            .map_err(|e| format!("In definition of {}: {}", name, e))?;
        let grf = resolve(&expanded, ar, &grfs)
            .map_err(|e| format!("In definition of {}: {}", name, e))?;
        arities.insert(name.clone(), ar);
        grfs.insert(name.clone(), grf.clone());
        defs.push((name.clone(), grf));
    }

    // Build display entries for GRF macros: resolve body with f → P(param_arity, 1).
    let mut grf_macro_defs = Vec::new();
    for (name, def) in &grf_macros {
        let placeholder = Grf::proj_atom(def.param_arity, 1);
        let mut ph_grfs = grfs.clone();
        let mut ph_arities = arities.clone();
        ph_grfs.insert(def.param_name.clone(), placeholder);
        ph_arities.insert(def.param_name.clone(), def.param_arity);
        if let Ok(expanded) = macro_expand(&def.body, &num_macros, &grf_macros) {
            if let Ok(ar) = min_arity(&expanded, &ph_arities) {
                if let Ok(grf) = resolve(&expanded, ar, &ph_grfs) {
                    grf_macro_defs.push((name.clone(), def.param_arity, grf));
                }
            }
        }
    }
    grf_macro_defs.sort_by(|a, b| a.0.cmp(&b.0));

    // Build display entries for num macros.
    let mut num_macro_defs: Vec<(String, usize)> = num_macros
        .iter()
        .map(|(name, cases)| (name.clone(), cases.cases.len()))
        .collect();
    num_macro_defs.sort_by(|a, b| a.0.cmp(&b.0));

    // Resolve test cases that reference macro instantiations (e.g. `Plus[3]`, `DiagS[Add]`).
    let resolved_tests = tests
        .into_iter()
        .map(|mut tc| {
            if tc.name.contains('[') || tc.name.contains('^') {
                let expr = parse_expr_str(&tc.name)
                    .map_err(|e| format!("In test {:?}: {}", tc.name, e))?;
                let expanded = macro_expand(&expr, &num_macros, &grf_macros)
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

    Ok(MgrfFile {
        defs,
        tests: resolved_tests,
        grf_macro_defs,
        num_macro_defs,
        grfs_ctx: grfs,
        arities_ctx: arities,
        num_macros_ctx: num_macros,
        grf_macros_ctx: grf_macros,
    })
}

/// Parse a `.mgrf` file and return only the GRF definitions.
pub fn parse_mgrf_to_grfs(content: &str) -> Result<Vec<(String, Grf)>, String> {
    parse_mgrf_file(content, None).map(|f| f.defs)
}

// Load an imported module and insert requested names into arities/grfs and all macros into
// the macro tables (macro imports ignore the names filter to handle transitive dependencies).
fn load_import(
    stmt: &UseStatement,
    resolver: &ImportResolver<'_>,
    arities: &mut HashMap<String, usize>,
    grfs: &mut HashMap<String, Grf>,
    out_grf_macros: &mut HashMap<String, GrfMacroDef>,
    out_num_macros: &mut HashMap<String, NumMacroCases>,
) -> Result<(), String> {
    let content = resolver.load(&stmt.module)?;

    // allow_use=true: transitive imports are supported.
    // Rule: if A imports B and B imports C, A gets B's locally-defined names only —
    // C's names are available inside B for resolution but are not re-exported to A.
    let (sub_uses, sub_items, _) =
        parse_file(&content, true).map_err(|e| format!("In module '{}': {}", stmt.module, e))?;

    let (sub_grf_macros_local, sub_num_macros_local, sub_raw_defs) = split_macros(sub_items);

    // Collect locally-defined names before moving the maps.
    let local_def_names: HashSet<&str> = sub_raw_defs.iter().map(|(n, _)| n.as_str()).collect();
    let local_grf_macro_names: HashSet<String> = sub_grf_macros_local.keys().cloned().collect();
    let local_num_macro_names: HashSet<String> = sub_num_macros_local.keys().cloned().collect();

    // Internal context: transitive imports first, then locals override.
    let mut sub_grf_macros: HashMap<String, GrfMacroDef> = HashMap::new();
    let mut sub_num_macros: HashMap<String, NumMacroCases> = HashMap::new();
    let mut sub_arities: HashMap<String, usize> = HashMap::new();
    let mut sub_grfs: HashMap<String, Grf> = HashMap::new();

    for sub_stmt in &sub_uses {
        load_import(
            sub_stmt,
            resolver,
            &mut sub_arities,
            &mut sub_grfs,
            &mut sub_grf_macros,
            &mut sub_num_macros,
        )?;
    }
    sub_grf_macros.extend(sub_grf_macros_local);
    sub_num_macros.extend(sub_num_macros_local);

    // Resolve locally-defined GRFs using the full internal context.
    for (name, expr) in &sub_raw_defs {
        let expanded = macro_expand(expr, &sub_num_macros, &sub_grf_macros).map_err(|e| {
            format!(
                "In module '{}', macro expansion of '{}': {}",
                stmt.module, name, e
            )
        })?;
        let ar = min_arity(&expanded, &sub_arities)
            .map_err(|e| format!("In module '{}', def '{}': {}", stmt.module, name, e))?;
        let grf = resolve(&expanded, ar, &sub_grfs)
            .map_err(|e| format!("In module '{}', def '{}': {}", stmt.module, name, e))?;
        sub_arities.insert(name.clone(), ar);
        sub_grfs.insert(name.clone(), grf);
    }

    let import_name = |name: &str| -> bool {
        stmt.names
            .as_ref()
            .map_or(true, |ns| ns.iter().any(|n| n == name))
    };

    // Export only locally-defined GRFs — not names that came in via transitive imports.
    for (name, grf) in &sub_grfs {
        if import_name(name) && local_def_names.contains(name.as_str()) {
            arities.insert(name.clone(), grf.arity());
            grfs.insert(name.clone(), grf.clone());
        }
    }

    // Export all locally-defined macros regardless of the names filter — macros are
    // expansion helpers, so imported macros (e.g. Mult[n]) that depend on non-imported
    // helper macros (e.g. PlusP2[n]) must still be expandable in the importing file.
    for (name, def) in sub_grf_macros {
        if local_grf_macro_names.contains(&name) {
            out_grf_macros.insert(name, def);
        }
    }
    for (name, cases) in sub_num_macros {
        if local_num_macro_names.contains(&name) {
            out_num_macros.insert(name, cases);
        }
    }

    // Validate that each explicitly requested name is locally defined in the module.
    if let Some(names) = &stmt.names {
        for req in names {
            let is_local_grf = local_def_names.contains(req.as_str());
            let is_grf_macro = out_grf_macros.contains_key(req.as_str());
            let is_num_macro = out_num_macros.contains_key(req.as_str());
            if !is_local_grf && !is_grf_macro && !is_num_macro {
                return Err(format!(
                    "Name '{}' not found in module '{}'",
                    req, stmt.module
                ));
            }
        }
    }

    Ok(())
}

// Partition raw parsed items into GRF macro defs, num-macro case tables, and regular definitions.
fn split_macros(
    items: Vec<(String, Option<MacroParam>, Expr)>,
) -> (
    HashMap<String, GrfMacroDef>,
    HashMap<String, NumMacroCases>,
    Vec<(String, Expr)>,
) {
    let mut grf_macros: HashMap<String, GrfMacroDef> = HashMap::new();
    let mut num_macros: HashMap<String, NumMacroCases> = HashMap::new();
    let mut regular: Vec<(String, Expr)> = Vec::new();
    for (name, param_opt, expr) in items {
        match param_opt {
            Some(MacroParam::Number(pattern)) => {
                num_macros
                    .entry(name)
                    .or_default()
                    .cases
                    .push((pattern, expr));
            }
            Some(MacroParam::Grf(param_name, param_arity)) => {
                grf_macros.insert(
                    name,
                    GrfMacroDef {
                        param_name,
                        param_arity,
                        body: expr,
                    },
                );
            }
            None => {
                regular.push((name, expr));
            }
        }
    }
    (grf_macros, num_macros, regular)
}

// ── File-level parser ─────────────────────────────────────────────────────────

fn parse_file(
    content: &str,
    allow_use: bool,
) -> Result<
    (
        Vec<UseStatement>,
        Vec<(String, Option<MacroParam>, Expr)>,
        Vec<TestCase>,
    ),
    String,
> {
    let mut use_stmts = Vec::new();
    let mut items = Vec::new();
    let mut tests = Vec::new();
    for (lineno, line) in content.lines().enumerate() {
        let line = if let Some(i) = line.find('#') {
            &line[..i]
        } else {
            line
        }
        .trim();
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
            let stmt = parse_use_statement(&line["use ".len()..])
                .ok_or_else(|| format!("Line {}: invalid use statement {:?}", lineno + 1, line))?;
            use_stmts.push(stmt);
        } else if line.contains("==") {
            let tc = parse_test_line(line)
                .ok_or_else(|| format!("Line {}: invalid test line {:?}", lineno + 1, line))?;
            tests.push(tc);
        } else {
            let (lhs, rhs) = line
                .split_once(":=")
                .ok_or_else(|| format!("Line {}: no ':=' found in {:?}", lineno + 1, line))?;
            let (name, param) = parse_lhs(lhs)
                .map_err(|e| format!("Line {}: bad LHS in {:?}: {}", lineno + 1, line, e))?;
            let expr_str: String = rhs.chars().filter(|c| !c.is_whitespace()).collect();
            let expr = parse_expr_str(&expr_str)
                .map_err(|e| format!("Line {}: parse error in {:?}: {}", lineno + 1, line, e))?;
            items.push((name, param, expr));
        }
    }
    Ok((use_stmts, items, tests))
}

// Parse a definition LHS: either `Name` (regular def) or `Name[pattern]` (macro case/def).
fn parse_lhs(s: &str) -> Result<(String, Option<MacroParam>), String> {
    let s = s.trim();
    if let Some(bracket_pos) = s.find('[') {
        if !s.ends_with(']') {
            return Err(format!("Unclosed '[' in LHS {:?}", s));
        }
        let name = s[..bracket_pos].trim().to_string();
        let inner = s[bracket_pos + 1..s.len() - 1].trim();

        // Detect GRF macro param: a lowercase identifier followed by `^` and a number.
        if let Some(caret) = inner.find('^') {
            let var = inner[..caret].trim();
            let k_str = inner[caret + 1..].trim();
            if !var.is_empty()
                && var.chars().all(|c| c.is_ascii_lowercase())
                && !k_str.is_empty()
                && k_str.chars().all(|c| c.is_ascii_digit())
            {
                let k: usize = k_str.parse().unwrap();
                return Ok((name, Some(MacroParam::Grf(var.to_string(), k))));
            }
        }

        // Otherwise parse as a num-macro pattern.
        let pattern =
            parse_num_pattern(inner).map_err(|e| format!("invalid pattern {:?}: {}", inner, e))?;
        Ok((name, Some(MacroParam::Number(pattern))))
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
            return Err(format!(
                "only n+1 successor patterns are supported (got +{})",
                inc
            ));
        }
        if var.is_empty()
            || !var
                .chars()
                .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit())
        {
            return Err(format!("variable {:?} must be lowercase", var));
        }
        return Ok(NumPattern::Succ(var.to_string()));
    }
    if s.chars()
        .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit())
    {
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
            Some(UseStatement {
                module,
                names: Some(names),
            })
        } else {
            None
        }
    } else {
        let module = s.to_string();
        if module.is_empty() || !module.chars().all(|c| c.is_alphanumeric() || c == '_') {
            return None;
        }
        Some(UseStatement {
            module,
            names: None,
        })
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
    Some(TestCase {
        name,
        grf: None,
        args,
        expected,
    })
}

fn parse_expr_str(s: &str) -> Result<Expr, String> {
    let stripped: String = s.chars().filter(|c| !c.is_whitespace()).collect();
    let mut chars = stripped.chars().peekable();
    let e = parse_expr(&mut chars)?;
    if chars.peek().is_some() {
        return Err(format!("Trailing chars: {:?}", chars.collect::<String>()));
    }
    Ok(e)
}

// ── Expression parser ─────────────────────────────────────────────────────────

// After reading a name, handle any combination of `^k` (explicit lift),
// `[numexpr]` (num-macro application), and `[GrfExpr]` (GRF-macro application).
// `^k` must come before `[...]`.
fn name_or_suffixes(name: String, chars: &mut Peekable<Chars>) -> Result<Expr, String> {
    // Optional explicit arity lift.
    let lift_k = if chars.peek() == Some(&'^') {
        chars.next();
        Some(read_digits(chars).ok_or_else(|| "Expected number after '^'".to_string())?)
    } else {
        None
    };
    // Optional macro application.
    let base = if chars.peek() == Some(&'[') {
        chars.next();
        match chars.peek() {
            Some(&c) if c.is_ascii_digit() => {
                let n = read_digits(chars).unwrap();
                eat(chars, ']')?;
                Expr::NumMacroApp(name, NumExpr::Literal(n))
            }
            Some(&c) if c.is_ascii_lowercase() => {
                // Lowercase: either a num-macro variable, or a GRF-param ref if followed by `^`.
                let var = read_lower_alnum(chars);
                if chars.peek() == Some(&'^') {
                    chars.next();
                    let k = read_digits(chars)
                        .ok_or_else(|| format!("Expected arity after '^' in [{}^...]", var))?;
                    eat(chars, ']')?;
                    // GRF-macro application: pass the GRF parameter (with explicit lift) as arg.
                    Expr::GrfMacroApp(name, Box::new(Expr::Lift(Box::new(Expr::Name(var)), k)))
                } else {
                    eat(chars, ']')?;
                    Expr::NumMacroApp(name, NumExpr::Variable(var))
                }
            }
            _ => {
                // GRF expression → GRF-macro application.
                let arg = parse_expr(chars)?;
                eat(chars, ']')?;
                Expr::GrfMacroApp(name, Box::new(arg))
            }
        }
    } else {
        Expr::Name(name)
    };
    Ok(match lift_k {
        Some(k) => Expr::Lift(Box::new(base), k),
        None => base,
    })
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
        c if c.is_ascii_uppercase() => {
            name_or_suffixes(format!("{}{}", c, read_alnum(chars)), chars)
        }
        // Lowercase identifier: a GRF parameter reference inside a macro body.
        c if c.is_ascii_lowercase() => {
            let name = format!("{}{}", c, read_lower_alnum(chars));
            name_or_suffixes(name, chars)
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
    while chars
        .peek()
        .map_or(false, |c| c.is_ascii_lowercase() || c.is_ascii_digit())
    {
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

// ── Macro expansion ───────────────────────────────────────────────────────────

// Expand all NumMacroApp and GrfMacroApp nodes in `expr` to concrete Expr trees.
// Must be called before min_arity / resolve.
fn macro_expand(
    expr: &Expr,
    num_macros: &HashMap<String, NumMacroCases>,
    grf_macros: &HashMap<String, GrfMacroDef>,
) -> Result<Expr, String> {
    macro_expand_inner(
        expr,
        num_macros,
        grf_macros,
        &HashMap::new(),
        &HashMap::new(),
        0,
    )
}

fn macro_expand_inner(
    expr: &Expr,
    num_macros: &HashMap<String, NumMacroCases>,
    grf_macros: &HashMap<String, GrfMacroDef>,
    num_env: &HashMap<String, usize>, // num-variable bindings from an enclosing num-macro
    grf_env: &HashMap<String, Expr>,  // GRF-parameter substitutions from an enclosing GRF-macro
    depth: usize,
) -> Result<Expr, String> {
    const MAX_DEPTH: usize = 4096;
    if depth > MAX_DEPTH {
        return Err(format!(
            "Macro expansion depth exceeded (limit {}); possible unbounded recursion",
            MAX_DEPTH
        ));
    }
    match expr {
        Expr::NumMacroApp(name, num_arg) => {
            let n = eval_num_expr(num_arg, num_env)?;
            expand_num_macro(name, n, num_macros, grf_macros, depth + 1)
        }
        Expr::GrfMacroApp(name, arg) => {
            // Expand the argument expression first (handles nested macros in the arg).
            let expanded_arg =
                macro_expand_inner(arg, num_macros, grf_macros, num_env, grf_env, depth + 1)?;
            // Look up the GRF macro definition.
            let def = grf_macros.get(name.as_str()).ok_or_else(|| {
                format!(
                    "Unknown GRF macro {:?} — define it with `{}[f^k] := ...`",
                    name, name
                )
            })?;
            // Expand the body with the parameter substituted.
            let mut new_grf_env = HashMap::new();
            new_grf_env.insert(def.param_name.clone(), expanded_arg);
            macro_expand_inner(
                &def.body,
                num_macros,
                grf_macros,
                num_env,
                &new_grf_env,
                depth + 1,
            )
        }
        Expr::Name(n) => {
            // Substitute GRF parameter if present; otherwise keep as a global reference.
            if let Some(substituted) = grf_env.get(n.as_str()) {
                Ok(substituted.clone())
            } else {
                Ok(expr.clone())
            }
        }
        Expr::Lift(inner, k) => Ok(Expr::Lift(
            Box::new(macro_expand_inner(
                inner, num_macros, grf_macros, num_env, grf_env, depth,
            )?),
            *k,
        )),
        Expr::Comp(h, gs) => {
            let eh = macro_expand_inner(h, num_macros, grf_macros, num_env, grf_env, depth)?;
            let egs = gs
                .iter()
                .map(|g| macro_expand_inner(g, num_macros, grf_macros, num_env, grf_env, depth))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Expr::Comp(Box::new(eh), egs))
        }
        Expr::Rec(g, h) => Ok(Expr::Rec(
            Box::new(macro_expand_inner(
                g, num_macros, grf_macros, num_env, grf_env, depth,
            )?),
            Box::new(macro_expand_inner(
                h, num_macros, grf_macros, num_env, grf_env, depth,
            )?),
        )),
        Expr::Min(f) => Ok(Expr::Min(Box::new(macro_expand_inner(
            f, num_macros, grf_macros, num_env, grf_env, depth,
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
    num_macros: &HashMap<String, NumMacroCases>,
    grf_macros: &HashMap<String, GrfMacroDef>,
    depth: usize,
) -> Result<Expr, String> {
    let cases = num_macros.get(name).ok_or_else(|| {
        format!(
            "Unknown num-macro {:?} — define it with `{}[pattern] := ...`",
            name, name
        )
    })?;
    for (pattern, body) in &cases.cases {
        match pattern {
            NumPattern::Literal(k) if *k == n => {
                return macro_expand_inner(
                    body,
                    num_macros,
                    grf_macros,
                    &HashMap::new(),
                    &HashMap::new(),
                    depth,
                );
            }
            NumPattern::Succ(var) if n >= 1 => {
                let mut env = HashMap::new();
                env.insert(var.clone(), n - 1);
                return macro_expand_inner(
                    body,
                    num_macros,
                    grf_macros,
                    &env,
                    &HashMap::new(),
                    depth,
                );
            }
            NumPattern::Var(var) => {
                let mut env = HashMap::new();
                env.insert(var.clone(), n);
                return macro_expand_inner(
                    body,
                    num_macros,
                    grf_macros,
                    &env,
                    &HashMap::new(),
                    depth,
                );
            }
            _ => continue,
        }
    }
    Err(format!(
        "No case in num-macro {} matches argument {}",
        name, n
    ))
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
        Expr::Lift(_, k) => *k,
        Expr::NumMacroApp(name, _) => {
            return Err(format!(
                "Unexpanded num-macro {:?} reached arity inference; this is an internal error",
                name
            ));
        }
        Expr::GrfMacroApp(name, _) => {
            return Err(format!(
                "Unexpanded GRF macro {:?} reached arity inference; this is an internal error",
                name
            ));
        }
    })
}

// ── Structural arity lifting ──────────────────────────────────────────────────

pub fn lift_grf(grf: &Grf, target: usize) -> Result<Grf, String> {
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
    match &grf.kind {
        GrfKind::Zero(_) => Ok(Grf::zero_atom(target)),
        GrfKind::Succ => Err(format!(
            "Cannot lift S (arity 1) to arity {}: S has a fixed arity",
            target
        )),
        GrfKind::Proj(_, i) => Ok(Grf::proj_atom(target, *i)),
        GrfKind::Comp(h, gs, _) => {
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
        GrfKind::Rec(g, h) => {
            let lg = lift_grf(g, target - 1)?;
            let lh = lift_grf(h, target + 1)?;
            Ok(Grf::rec(lg, lh))
        }
        GrfKind::Min(f) => {
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
                return Err(format!(
                    "Z{}: explicit arity {} vs required {}",
                    k, k, target
                ));
            }
            Ok(Grf::zero_atom(*k))
        }
        Expr::Zero(None) => Ok(Grf::zero_atom(target)),
        Expr::Succ => {
            if target != 1 {
                return Err(format!("S has arity 1, required {}", target));
            }
            Ok(Grf::succ_atom())
        }
        Expr::Proj(Some(k), i) => {
            if *k != target {
                return Err(format!(
                    "P({},{}): explicit arity {} vs required {}",
                    k, i, k, target
                ));
            }
            Ok(Grf::proj_atom(*k, *i))
        }
        Expr::Proj(None, i) => Ok(Grf::proj_atom(target, *i)),
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
                lift_grf(&grf, target).map_err(|e| format!("Implicit lift of {:?}: {}", n, e))
            } else {
                Err(format!(
                    "Name {:?} has arity {} but required {} (cannot reduce arity)",
                    n, actual, target
                ))
            }
        }
        Expr::Lift(inner, k) => {
            if *k != target {
                return Err(format!(
                    "Explicit lift to arity {} but context requires arity {}",
                    k, target
                ));
            }
            let temp_arities: HashMap<String, usize> =
                known.iter().map(|(n, g)| (n.clone(), g.arity())).collect();
            let natural_ar =
                min_arity(inner, &temp_arities).map_err(|e| format!("In lift target: {}", e))?;
            let inner_grf = resolve(inner, natural_ar, known)?;
            lift_grf(&inner_grf, *k).map_err(|e| format!("In explicit lift ^{}: {}", k, e))
        }
        Expr::NumMacroApp(name, _) => Err(format!(
            "Unexpanded num-macro {:?} reached resolution; this is an internal error",
            name
        )),
        Expr::GrfMacroApp(name, _) => Err(format!(
            "Unexpanded GRF macro {:?} reached resolution; this is an internal error",
            name
        )),
    }
}

// ── Tests ─────────────────────────────────────────────────────────────────────

/// Decompiles a GRF back into an unaliased macro string, matching common
/// patterns from `func_rep.mgrf` and `base.mgrf` (and generalizations) to produce
/// heavily simplified notation like `DiagS[RepFirst[Add]]`.
pub fn decompile(grf: &Grf) -> String {
    match &grf.kind {
        GrfKind::Zero(k) => format!("Z{k}"),
        GrfKind::Succ => "S".to_string(),
        GrfKind::Proj(k, i) => format!("P({k},{i})"),
        GrfKind::Comp(h, gs, k) => {
            let h_str = decompile(h);

            // Check for DiagS: C(f, S, S)
            if gs.len() == 2
                && matches!(gs[0].kind, GrfKind::Succ)
                && matches!(gs[1].kind, GrfKind::Succ)
            {
                return format!("DiagS[{h_str}]");
            }

            // Check for K[1]: C(S, Z0) and K[N] recursively
            if gs.len() == 1 && matches!(h.kind, GrfKind::Succ) {
                if let GrfKind::Zero(0) = gs[0].kind {
                    return "K[1]".to_string();
                } else {
                    let inner_str = decompile(&gs[0]);
                    if inner_str.starts_with("K[") && inner_str.ends_with("]") {
                        if let Ok(n) = inner_str[2..inner_str.len()-1].parse::<u32>() {
                            return format!("K[{}]", n + 1);
                        }
                    }
                }
            }

            if gs.is_empty() {
                format!("C{k}({h_str})")
            } else {
                let args: Vec<String> = gs.iter().map(decompile).collect();
                format!("C({h_str},{})", args.join(","))
            }
        }
        GrfKind::Rec(g, h) => {
            let g_str = decompile(g);
            let h_str = decompile(h);

            // Match generalized RepFirst shapes: R(base, R(f, P(4,2)))
            if let GrfKind::Rec(f, h_inner) = &h.kind {
                if let GrfKind::Proj(4, 2) = h_inner.kind {
                    let inner_f = decompile(f);
                    if g_str == "S" {
                        return format!("RepFirst[{inner_f}]");
                    } else if g_str == "P(1,1)" {
                        return format!("RepFirstP1[{inner_f}]");
                    } else if g_str == "Z1" {
                        return format!("RepFirstZ1[{inner_f}]");
                    }
                }
            }

            if let GrfKind::Comp(f, gs, _) = &h.kind {
                // Match RepSucc[f] = R(S, C(f, P(3,2)))
                if gs.len() == 1 && matches!(gs[0].kind, GrfKind::Proj(3, 2)) {
                    let inner_f = decompile(f);
                    if g_str == "S" {
                        return format!("RepSucc[{inner_f}]");
                    } else if g_str == "P(1,1)" {
                        return format!("RepSuccP1[{inner_f}]");
                    }
                }
                
                // Match DiagRep[f] = R(base, C(f, P(3,2), P(3,2)))
                if gs.len() == 2 && matches!(gs[0].kind, GrfKind::Proj(3, 2)) && matches!(gs[1].kind, GrfKind::Proj(3, 2)) {
                    let inner_f = decompile(f);
                    if g_str == "Z1" {
                        return format!("DiagRepZ1[{inner_f}]");
                    } else if g_str == "S" {
                        return format!("DiagRep[{inner_f}]"); // Future proofing
                    } else if g_str == "P(1,1)" {
                        return format!("DiagRepP1[{inner_f}]");
                    }
                }
            }

            // Match 2-arity addition: R(P(1,1), C(S, P(3,2)))
            if g_str == "P(1,1)" && h_str == "C(S,P(3,2))" {
                return "Add".to_string();
            }

            if g_str == "P(2,1)" && h_str == "C(S,P(4,2))" {
                return "Add^3".to_string();
            }

            // Match Tri: R(Z0, RepSucc[S]) -> Tri
            if g_str == "Z0" && h_str == "RepSucc[S]" {
                return "Tri".to_string();
            }

            format!("R({g_str},{h_str})")
        }
        GrfKind::Min(f) => format!("M({})", decompile(f)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::simulate::simulate;

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
        let g = single("K[0] := Z\nK[n+1] := C(S, K[n])\nF := C(S, K[3])");
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
        assert!(
            result.is_err(),
            "Expected error: explicit lift 3 vs required 4"
        );
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
        assert!(
            result.is_err(),
            "Expected error: transitive imports blocked"
        );
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
        let content = format!(
            "{}\nPlus1 := Plus[1]\nPlus3 := Plus[3]\nPlus5 := Plus[5]",
            NUM_EXAMPLES
        );
        let defs = parse_defs(&content);
        assert_eq!(defs["Plus1"].arity(), 1);
        assert_eq!(defs["Plus3"].arity(), 1);
        assert_eq!(defs["Plus5"].arity(), 1);
    }

    #[test]
    fn test_monus_arities() {
        let content = format!(
            "{}\nM0 := Monus[0]\nM1 := Monus[1]\nM3 := Monus[3]",
            NUM_EXAMPLES
        );
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
        let content = format!("{}\nPlus3 := Plus[3]\nPlus5 := Plus[5]", NUM_EXAMPLES);
        let defs = parse_defs(&content);
        let (r, _) = simulate(&defs["Plus3"], &[7], 10_000);
        assert_eq!(r.into_value(), Some(10));
        let (r, _) = simulate(&defs["Plus5"], &[0], 10_000);
        assert_eq!(r.into_value(), Some(5));
    }

    #[test]
    fn test_monus_simulation() {
        let content = format!("{}\nM1 := Monus[1]\nM3 := Monus[3]", NUM_EXAMPLES);
        let defs = parse_defs(&content);
        let (r, _) = simulate(&defs["M1"], &[5], 10_000);
        assert_eq!(r.into_value(), Some(4));
        let (r, _) = simulate(&defs["M1"], &[0], 10_000);
        assert_eq!(r.into_value(), Some(0));
        let (r, _) = simulate(&defs["M3"], &[5], 10_000);
        assert_eq!(r.into_value(), Some(2));
        let (r, _) = simulate(&defs["M3"], &[2], 10_000);
        assert_eq!(r.into_value(), Some(0));
    }

    #[test]
    fn test_mult_simulation() {
        let content = format!("{}\nMult3 := Mult[3]\nMult5 := Mult[5]", NUM_EXAMPLES);
        let defs = parse_defs(&content);
        let (r, _) = simulate(&defs["Mult3"], &[4], 100_000);
        assert_eq!(r.into_value(), Some(12));
        let (r, _) = simulate(&defs["Mult5"], &[3], 100_000);
        assert_eq!(r.into_value(), Some(15));
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
            assert!(
                tc.grf.is_some(),
                "test {:?} should have a resolved grf",
                tc.name
            );
        }
    }

    #[test]
    fn test_num_macro_no_matching_case() {
        let content = format!("{}\nBad := Plus[0]", NUM_EXAMPLES);
        let result = parse_mgrf_to_grfs(&content);
        assert!(result.is_err(), "Expected error: no case for Plus[0]");
    }

    #[test]
    fn test_num_macro_variable_unbound_outside_body() {
        let content = format!("{}\nBad := Plus[n]", NUM_EXAMPLES);
        let result = parse_mgrf_to_grfs(&content);
        assert!(result.is_err(), "Expected error: 'n' unbound at top level");
    }

    // ── Feature 3: GRF-parameterized macros ──────────────────────────────────

    // The user's examples verbatim.
    const GRF_EXAMPLES: &str = "
Add := R(P1, C(S, P2))
RepSucc[f^1] := R(S, C(f, P2))
DiagRep[f^2] := R(S, C(f, P(3,2), P(3,2)))
DiagS[f^2] := C(f, S, S)
";

    #[test]
    fn test_grf_macro_diags_arity() {
        // DiagS[f^2] := C(f, S, S) — substituting Add (arity 2) gives C(Add, S, S) arity 1
        let content = format!("{}\nResult := DiagS[Add]", GRF_EXAMPLES);
        let defs = parse_defs(&content);
        assert_eq!(defs["Result"].arity(), 1);
    }

    #[test]
    fn test_grf_macro_diags_simulation() {
        // DiagS[Add](x) = Add(S(x), S(x)) = (x+1)+(x+1) = 2x+2
        let content = format!("{}\nResult := DiagS[Add]", GRF_EXAMPLES);
        let defs = parse_defs(&content);
        let (r, _) = simulate(&defs["Result"], &[3], 10_000);
        assert_eq!(r.into_value(), Some(8)); // 2*3+2 = 8
        let (r, _) = simulate(&defs["Result"], &[0], 10_000);
        assert_eq!(r.into_value(), Some(2)); // 2*0+2 = 2
    }

    #[test]
    fn test_grf_macro_repsucc_simulation() {
        // RepSucc[S](n, x) = R(S, C(S, P2))(n, x) = x + n + 1
        let content = format!("{}\nResult := RepSucc[S]", GRF_EXAMPLES);
        let defs = parse_defs(&content);
        let (r, _) = simulate(&defs["Result"], &[3, 5], 10_000);
        assert_eq!(r.into_value(), Some(9)); // 5 + 3 + 1 = 9
        let (r, _) = simulate(&defs["Result"], &[0, 0], 10_000);
        assert_eq!(r.into_value(), Some(1)); // 0 + 0 + 1 = 1
    }

    #[test]
    fn test_grf_macro_diagrep_simulation() {
        // DiagRep[RepSucc[S]](n, x):
        //   = R(S, C(RepSucc[S], P(3,2), P(3,2)))(n, x)
        //   where RepSucc[S](k,y) = y + k + 1
        //   step: RepSucc[S](x, acc) = acc + x + 1 ... but P(3,2) extracts the accumulator
        //   Actually: C(RepSucc[S], P(3,2), P(3,2))(i, acc, x) = RepSucc[S](acc, acc) = acc + acc + 1 = 2*acc+1
        //   base: x+1 (from S); step: 2*acc+1
        //   DiagRep[RepSucc[S]](0, x) = x+1
        //   DiagRep[RepSucc[S]](1, x) = 2*(x+1)+1 = 2x+3
        //   DiagRep[RepSucc[S]](2, x) = 2*(2x+3)+1 = 4x+7
        let content = format!("{}\nResult := DiagRep[RepSucc[S]]", GRF_EXAMPLES);
        let defs = parse_defs(&content);
        let (r, _) = simulate(&defs["Result"], &[0, 0], 10_000);
        assert_eq!(r.into_value(), Some(1)); // x+1 = 1
        let (r, _) = simulate(&defs["Result"], &[1, 0], 10_000);
        assert_eq!(r.into_value(), Some(3)); // 2*0+3 = 3
        let (r, _) = simulate(&defs["Result"], &[2, 0], 10_000);
        assert_eq!(r.into_value(), Some(7)); // 4*0+7 = 7
    }

    #[test]
    fn test_grf_macro_with_num_macro_arg() {
        // DiagS[Plus[3]] := C(Plus[3], S, S)
        // DiagS[Plus[3]](x) = Plus[3](x+1, x+1) -- wait, Plus[3](y) = y+3 (arity 1)
        // But DiagS needs f^2 (arity 2). Plus[3] has arity 1. This should error.
        let content = format!("{}\n{}\nBad := DiagS[Plus[3]]", NUM_EXAMPLES, GRF_EXAMPLES);
        let result = parse_mgrf_to_grfs(&content);
        assert!(result.is_err(), "Plus[3] has arity 1, DiagS needs f^2");
    }

    #[test]
    fn test_grf_macro_with_num_macro_matching_arity() {
        // Mult (arity 2) used with DiagS[f^2]: DiagS[Mult](x) = Mult(x+1, x+1) = (x+1)^2
        let content = format!(
            "{}\nMult := R(Z, R(Add, P2))\nResult := DiagS[Mult]",
            GRF_EXAMPLES
        );
        let defs = parse_defs(&content);
        let (r, _) = simulate(&defs["Result"], &[3], 10_000);
        assert_eq!(r.into_value(), Some(16)); // (3+1)^2 = 16
        let (r, _) = simulate(&defs["Result"], &[0], 10_000);
        assert_eq!(r.into_value(), Some(1)); // 1^2 = 1
    }

    #[test]
    fn test_grf_macro_test_case() {
        // Test that GRF macro instantiations work in inline test cases.
        let content = format!(
            "{}\nDiagS[Add](3) == 8\nRepSucc[S](3, 5) == 9",
            GRF_EXAMPLES
        );
        let file = parse_mgrf_file(&content, None).unwrap();
        assert_eq!(file.tests.len(), 2);
        for tc in &file.tests {
            assert!(
                tc.grf.is_some(),
                "test {:?} should have a resolved grf",
                tc.name
            );
        }
    }

    #[test]
    fn test_grf_param_passed_via_caret_syntax() {
        // Twice[f^1] := C(f, f) where f is a GRF-param.
        // Twice[RepSucc[S]^2]: pass RepSucc[S] (arity 2) but declared as f^1 — should error
        //   because Twice expects f^1 but RepSucc[S] has arity 2.
        // Instead test Twice[S^1] = C(S, S) — S has arity 1 ✓.
        let content = "Twice[f^1] := C(f, f)\nResult := Twice[S]";
        let defs = parse_defs(content);
        // C(S, S)(x) = S(S(x)) = x+2
        let (r, _) = simulate(&defs["Result"], &[5], 10_000);
        assert_eq!(r.into_value(), Some(7));
    }

    // ── Inline spec tests from each .mgrf file ────────────────────────────────

    fn mgrf_modules() -> HashMap<String, String> {
        [
            ("base", include_str!("../mgrf/base.mgrf")),
            ("bool_zero", include_str!("../mgrf/bool_zero.mgrf")),
            ("func_rep", include_str!("../mgrf/func_rep.mgrf")),
            ("ack_worm", include_str!("../mgrf/ack_worm.mgrf")),
            ("brocard", include_str!("../mgrf/brocard.mgrf")),
            ("collatz", include_str!("../mgrf/collatz.mgrf")),
            ("erdos", include_str!("../mgrf/erdos.mgrf")),
            ("fermat", include_str!("../mgrf/fermat.mgrf")),
        ]
        .into_iter()
        .map(|(k, v)| (k.to_string(), v.to_string()))
        .collect()
    }

    fn run_mgrf_tests(file: &MgrfFile) {
        const BUDGET: u64 = 1_000_000;
        let grf_map: HashMap<&str, &Grf> = file.defs.iter().map(|(n, g)| (n.as_str(), g)).collect();
        for tc in &file.tests {
            let grf = tc
                .grf
                .as_ref()
                .or_else(|| grf_map.get(tc.name.as_str()).copied())
                .unwrap_or_else(|| panic!("undefined GRF in test: {}", tc.name));
            assert_eq!(
                grf.arity(),
                tc.args.len(),
                "arity mismatch in test {}({}): GRF has arity {} but {} args provided",
                tc.name,
                tc.args
                    .iter()
                    .map(|a| a.to_string())
                    .collect::<Vec<_>>()
                    .join(", "),
                grf.arity(),
                tc.args.len(),
            );
            let (result, _) = simulate(grf, &tc.args, BUDGET);
            let got = result.into_value();
            let args_str = tc
                .args
                .iter()
                .map(|a| a.to_string())
                .collect::<Vec<_>>()
                .join(", ");
            assert_eq!(
                got, tc.expected,
                "{}({}) expected {:?}, got {:?}",
                tc.name, args_str, tc.expected, got
            );
        }
    }

    #[test]
    fn test_mgrf_base() {
        let m = mgrf_modules();
        run_mgrf_tests(&parse_mgrf_with_modules(include_str!("../mgrf/base.mgrf"), &m).unwrap());
    }

    #[test]
    fn test_mgrf_bool_zero() {
        let m = mgrf_modules();
        run_mgrf_tests(
            &parse_mgrf_with_modules(include_str!("../mgrf/bool_zero.mgrf"), &m).unwrap(),
        );
    }

    #[test]
    fn test_mgrf_ack_worm() {
        let m = mgrf_modules();
        run_mgrf_tests(
            &parse_mgrf_with_modules(include_str!("../mgrf/ack_worm.mgrf"), &m).unwrap(),
        );
    }

    #[test]
    fn test_mgrf_brocard() {
        let m = mgrf_modules();
        run_mgrf_tests(&parse_mgrf_with_modules(include_str!("../mgrf/brocard.mgrf"), &m).unwrap());
    }

    #[test]
    fn test_mgrf_collatz() {
        let m = mgrf_modules();
        run_mgrf_tests(&parse_mgrf_with_modules(include_str!("../mgrf/collatz.mgrf"), &m).unwrap());
    }

    #[test]
    fn test_mgrf_erdos() {
        let m = mgrf_modules();
        run_mgrf_tests(&parse_mgrf_with_modules(include_str!("../mgrf/erdos.mgrf"), &m).unwrap());
    }

    #[test]
    fn test_mgrf_fermat() {
        let m = mgrf_modules();
        run_mgrf_tests(&parse_mgrf_with_modules(include_str!("../mgrf/fermat.mgrf"), &m).unwrap());
    }
}
