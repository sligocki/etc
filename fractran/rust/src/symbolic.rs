use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt;
use std::str::FromStr;

use infinitable::{Finite, Infinitable, Infinity};

use crate::diff_rule::DiffRule;
use crate::program::{BigInt, Program, SmallInt, State};
use crate::shift_sim::find_shift_rules;
use crate::tandem_repeat::find_rep_blocks;
use crate::transcript::{Trans, transcript};

fn gcd(mut a: i64, mut b: i64) -> i64 {
    a = a.abs();
    b = b.abs();
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

/// Specification for a single register in a `ConfigSpec`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RegSpec {
    Fixed(SmallInt),
    Param(usize),
}

/// Parameterized configuration specification, e.g. `S(x, y) := [x, 0, 0, 2, y]`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ConfigSpec {
    pub regs: Vec<RegSpec>,
    pub param_names: Vec<String>,
}

impl ConfigSpec {
    pub fn new(regs: Vec<RegSpec>, param_names: Vec<String>) -> Self {
        ConfigSpec { regs, param_names }
    }

    pub fn num_params(&self) -> usize {
        self.param_names.len()
    }

    pub fn default_param_name(idx: usize) -> String {
        const NAMES: [&str; 6] = ["x", "y", "z", "w", "u", "v"];
        if idx < NAMES.len() {
            NAMES[idx].to_string()
        } else {
            format!("x{}", idx)
        }
    }

    /// Check if a concrete `State` matches this `ConfigSpec`.
    /// Returns the extracted parameter values if it matches.
    pub fn match_concrete(&self, state: &State) -> Option<Vec<BigInt>> {
        if state.data.len() != self.regs.len() {
            return None;
        }
        let mut params = vec![BigInt::from(0); self.num_params()];
        for (val, spec) in state.data.iter().zip(self.regs.iter()) {
            match spec {
                RegSpec::Fixed(c) => {
                    if *val != BigInt::from(*c) {
                        return None;
                    }
                }
                RegSpec::Param(idx) => {
                    if *val < BigInt::from(0) {
                        return None;
                    }
                    params[*idx] = val.clone();
                }
            }
        }
        Some(params)
    }

    /// Check if a symbolic state's registers match this `ConfigSpec`.
    /// Returns the symbolic expressions for each parameter if it matches.
    pub fn match_symbolic(&self, regs: &[SymExpr]) -> Option<Vec<SymExpr>> {
        if regs.len() != self.regs.len() {
            return None;
        }
        let mut params = vec![SymExpr::constant(0, self.num_params()); self.num_params()];
        for (expr, spec) in regs.iter().zip(self.regs.iter()) {
            match spec {
                RegSpec::Fixed(c) => {
                    if expr.is_const() != Some(*c as i64) {
                        return None;
                    }
                }
                RegSpec::Param(idx) => {
                    if !expr.is_always_non_negative() {
                        return None;
                    }
                    params[*idx] = expr.clone();
                }
            }
        }
        Some(params)
    }
}

impl FromStr for ConfigSpec {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut inner = s.trim();
        if let Some( idx) = inner.find(":=") {
            inner = inner[idx + 2..].trim();
        }
        if let Some(start) = inner.find('[') {
            let end = inner.rfind(']').ok_or("Missing closing ']' in ConfigSpec")?;
            inner = &inner[start + 1..end];
        }

        let mut regs = Vec::new();
        let mut param_names: Vec<String> = Vec::new();
        let mut name_to_idx: HashMap<String, usize> = HashMap::new();

        for part in inner.replace(',', " ").split_whitespace() {
            if let Ok(val) = part.parse::<SmallInt>() {
                regs.push(RegSpec::Fixed(val));
            } else {
                let idx = if let Some(&existing) = name_to_idx.get(part) {
                    existing
                } else {
                    let next_idx = param_names.len();
                    param_names.push(part.to_string());
                    name_to_idx.insert(part.to_string(), next_idx);
                    next_idx
                };
                regs.push(RegSpec::Param(idx));
            }
        }

        if regs.is_empty() {
            return Err("Empty ConfigSpec".to_string());
        }

        Ok(ConfigSpec { regs, param_names })
    }
}

impl fmt::Display for ConfigSpec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "S({}) := [", self.param_names.join(", "))?;
        for (i, reg) in self.regs.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            match reg {
                RegSpec::Fixed(c) => write!(f, "{}", c)?,
                RegSpec::Param(idx) => write!(f, "{}", self.param_names[*idx])?,
            }
        }
        write!(f, "]")
    }
}

/// Affine linear expression over parameters `p_0, ..., p_{k-1} >= 0`:
/// `constant + sum_i coeffs[i] * p_i`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SymExpr {
    pub coeffs: Vec<i64>,
    pub constant: i64,
}

impl SymExpr {
    pub fn constant(val: i64, num_vars: usize) -> Self {
        SymExpr {
            coeffs: vec![0; num_vars],
            constant: val,
        }
    }

    pub fn from_var(num_vars: usize, var_idx: usize) -> Self {
        let mut coeffs = vec![0; num_vars];
        coeffs[var_idx] = 1;
        SymExpr {
            coeffs,
            constant: 0,
        }
    }

    pub fn is_const(&self) -> Option<i64> {
        if self.coeffs.iter().all(|&c| c == 0) {
            Some(self.constant)
        } else {
            None
        }
    }

    pub fn is_always_non_negative(&self) -> bool {
        self.constant >= 0 && self.coeffs.iter().all(|&c| c >= 0)
    }

    /// Minimum value over all `p_i >= 0` (assuming `coeffs[i] >= 0`).
    pub fn min_val(&self) -> Infinitable<i64> {
        if self.coeffs.iter().any(|&c| c < 0) {
            Infinitable::NegativeInfinity
        } else {
            Finite(self.constant)
        }
    }

    /// Maximum value over all `p_i >= 0` (assuming `coeffs[i] >= 0`).
    pub fn max_val(&self) -> Infinitable<i64> {
        if self.coeffs.iter().any(|&c| c > 0) {
            Infinity
        } else {
            Finite(self.constant)
        }
    }

    pub fn add_const(&self, delta: i64) -> Self {
        let mut out = self.clone();
        out.constant += delta;
        out
    }

    pub fn add(&self, other: &Self) -> Self {
        let mut out = self.clone();
        for (c, o) in out.coeffs.iter_mut().zip(other.coeffs.iter()) {
            *c += o;
        }
        out.constant += other.constant;
        out
    }

    pub fn sub(&self, other: &Self) -> Self {
        let mut out = self.clone();
        for (c, o) in out.coeffs.iter_mut().zip(other.coeffs.iter()) {
            *c -= o;
        }
        out.constant -= other.constant;
        out
    }

    pub fn scale(&self, factor: i64) -> Self {
        let mut out = self.clone();
        for c in out.coeffs.iter_mut() {
            *c *= factor;
        }
        out.constant *= factor;
        out
    }

    /// Substitute `p_{var_idx} <- scale * p_{var_idx} + offset`.
    pub fn substitute_var(&self, var_idx: usize, scale: i64, offset: i64) -> Self {
        let mut out = self.clone();
        let coeff = out.coeffs[var_idx];
        out.constant += coeff * offset;
        out.coeffs[var_idx] = coeff * scale;
        out
    }

    /// Evaluate on concrete values.
    pub fn evaluate(&self, vals: &[BigInt]) -> BigInt {
        let mut acc = BigInt::from(self.constant);
        for (&c, v) in self.coeffs.iter().zip(vals.iter()) {
            acc += BigInt::from(c) * v;
        }
        acc
    }

    /// Divide `self` by `d >= 1`, returning `Ok((quotient, remainder))` with `0 <= remainder < d`
    /// if all variable coefficients are divisible by `d`.
    /// Otherwise returns `Err((var_idx, split_modulus))` for the first variable whose coefficient
    /// is not divisible by `d`.
    pub fn div_mod(&self, d: i64) -> Result<(SymExpr, i64), (usize, i64)> {
        assert!(d >= 1);
        for (i, &c) in self.coeffs.iter().enumerate() {
            if c.rem_euclid(d) != 0 {
                let g = gcd(c, d);
                let split_mod = d / g;
                return Err((i, split_mod));
            }
        }
        let r = self.constant.rem_euclid(d);
        let q_const = (self.constant - r) / d;
        let q_coeffs = self.coeffs.iter().map(|&c| c / d).collect();
        Ok((
            SymExpr {
                coeffs: q_coeffs,
                constant: q_const,
            },
            r,
        ))
    }

    pub fn format_with_names(&self, names: &[String]) -> String {
        let mut terms: Vec<String> = Vec::new();
        for (i, &c) in self.coeffs.iter().enumerate() {
            if c == 0 {
                continue;
            }
            let name = &names[i];
            if terms.is_empty() {
                if c == 1 {
                    terms.push(name.clone());
                } else if c == -1 {
                    terms.push(format!("-{}", name));
                } else {
                    terms.push(format!("{}{}", c, name));
                }
            } else if c > 0 {
                if c == 1 {
                    terms.push(format!("+{}", name));
                } else {
                    terms.push(format!("+{}{}", c, name));
                }
            } else if c == -1 {
                terms.push(format!("-{}", name));
            } else {
                terms.push(format!("{}{}", c, name));
            }
        }

        if terms.is_empty() {
            return format!("{}", self.constant);
        }

        if self.constant > 0 {
            terms.push(format!("+{}", self.constant));
        } else if self.constant < 0 {
            terms.push(format!("{}", self.constant));
        }

        terms.join("")
    }
}

/// Right-hand side outcome of a deduced symbolic macro-rule.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum RuleRhs {
    Return(Vec<SymExpr>),
    Halt,
    Infinite,
}

/// A deduced macro-transition rule from `S(lhs_params)` to `rhs`.
/// All variables in `lhs_params` and `rhs` range over natural numbers `>= 0`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SymRule {
    pub lhs_params: Vec<SymExpr>,
    pub rhs: RuleRhs,
}

impl SymRule {
    /// Format rule using constrained style when a parameter is purely offset
    /// (e.g. `S(x, 2y) -> S(x-1, 5y+2)  if x >= 1`).
    pub fn format_rule(&self, param_names: &[String]) -> String {
        let mut display_lhs = self.lhs_params.clone();
        let mut display_rhs = self.rhs.clone();
        let mut conditions: Vec<String> = Vec::new();

        for i in 0..param_names.len() {
            // Check if lhs_params[i] is purely `m * p_i + offset` with `m >= 1` and `offset >= m`.
            let expr = &display_lhs[i];
            let m = expr.coeffs[i];
            let only_var_i = m >= 1
                && expr
                    .coeffs
                    .iter()
                    .enumerate()
                    .all(|(j, &c)| if j == i { true } else { c == 0 });
            if only_var_i && expr.constant >= m {
                let q = expr.constant / m;
                // Rewrite p_i <- p_i - q so lhs[i] becomes `m * p_i + (offset % m)` with condition `p_i >= q`
                display_lhs[i] = display_lhs[i].substitute_var(i, 1, -q);
                if let RuleRhs::Return(ref mut rhs_exprs) = display_rhs {
                    for r_expr in rhs_exprs.iter_mut() {
                        *r_expr = r_expr.substitute_var(i, 1, -q);
                    }
                }
                conditions.push(format!("{} >= {}", param_names[i], q));
            }
        }

        let lhs_strs: Vec<String> = display_lhs
            .iter()
            .map(|e| e.format_with_names(param_names))
            .collect();
        let rhs_str = match &display_rhs {
            RuleRhs::Halt => "Halt".to_string(),
            RuleRhs::Infinite => "Infinite".to_string(),
            RuleRhs::Return(exprs) => {
                let s: Vec<String> = exprs
                    .iter()
                    .map(|e| e.format_with_names(param_names))
                    .collect();
                format!("S({})", s.join(", "))
            }
        };

        if conditions.is_empty() {
            format!("S({}) -> {}", lhs_strs.join(", "), rhs_str)
        } else {
            format!(
                "S({}) -> {}  if {}",
                lhs_strs.join(", "),
                rhs_str,
                conditions.join(", ")
            )
        }
    }
}

/// Symbolic execution state along a branch.
#[derive(Debug, Clone)]
struct SymState {
    regs: Vec<SymExpr>,
    lhs_params: Vec<SymExpr>,
    base_steps: SymExpr,
    sim_steps: usize,
    trans_history: Vec<Trans>,
}

impl SymState {
    fn initial(spec: &ConfigSpec) -> Self {
        let num_params = spec.num_params();
        let regs = spec
            .regs
            .iter()
            .map(|r| match r {
                RegSpec::Fixed(c) => SymExpr::constant(*c as i64, num_params),
                RegSpec::Param(idx) => SymExpr::from_var(num_params, *idx),
            })
            .collect();
        let lhs_params = (0..num_params)
            .map(|i| SymExpr::from_var(num_params, i))
            .collect();
        SymState {
            regs,
            lhs_params,
            base_steps: SymExpr::constant(0, num_params),
            sim_steps: 0,
            trans_history: Vec::new(),
        }
    }

    fn substitute(&self, var_idx: usize, scale: i64, offset: i64) -> Self {
        SymState {
            regs: self
                .regs
                .iter()
                .map(|e| e.substitute_var(var_idx, scale, offset))
                .collect(),
            lhs_params: self
                .lhs_params
                .iter()
                .map(|e| e.substitute_var(var_idx, scale, offset))
                .collect(),
            base_steps: self.base_steps.substitute_var(var_idx, scale, offset),
            sim_steps: self.sim_steps,
            trans_history: self.trans_history.clone(),
        }
    }
}

/// Configuration limits for the symbolic analyzer.
#[derive(Debug, Clone)]
pub struct AnalyzerConfig {
    pub max_branches: usize,
    pub max_steps_per_branch: usize,
    pub max_modulus: i64,
    pub transcript_steps: usize,
}

impl Default for AnalyzerConfig {
    fn default() -> Self {
        AnalyzerConfig {
            max_branches: 64,
            max_steps_per_branch: 200,
            max_modulus: 16,
            transcript_steps: 2000,
        }
    }
}

/// High-level decision status derived from a complete symbolic analysis.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DecisionStatus {
    /// Complete closed ruleset with no halting rules and start state enters `S(...)`.
    ProvenNonHalting,
    /// Start state reaches a halting rule directly.
    ProvenHalting,
    /// Complete ruleset deduced, but contains both halting and recursive rules.
    InductiveSystemComplete,
    /// Could not close the ruleset within configured limits.
    Incomplete(String),
}

/// Result of analyzing a program with a `ConfigSpec`.
#[derive(Debug, Clone)]
pub struct AnalysisResult {
    pub spec: ConfigSpec,
    pub start_step: Option<(usize, Vec<BigInt>)>,
    pub rules: Vec<SymRule>,
    pub status: DecisionStatus,
}

impl fmt::Display for AnalysisResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "{}", self.spec)?;
        if let Some((step, ref vals)) = self.start_step {
            let val_strs: Vec<String> = vals.iter().map(|v| v.to_string()).collect();
            writeln!(f, "Start: S({}) at step {}", val_strs.join(", "), step)?;
        } else {
            writeln!(f, "Start: (does not reach S within simulation limit)")?;
        }
        writeln!(f)?;
        for rule in &self.rules {
            writeln!(f, "{}", rule.format_rule(&self.spec.param_names))?;
        }
        writeln!(f, "\nStatus: {:?}", self.status)
    }
}

/// Find the first step at which `prog` (starting from `[1, 0, ...]`) hits `spec`.
pub fn find_start_config(
    prog: &Program,
    spec: &ConfigSpec,
    max_steps: usize,
) -> Option<(usize, Vec<BigInt>)> {
    let mut state = State::start(prog);
    for step in 0..=max_steps {
        if let Some(params) = spec.match_concrete(&state) {
            return Some((step, params));
        }
        if !prog.step(&mut state) {
            break;
        }
    }
    None
}

/// Attempt to apply a `DiffRule` symbolically to `state`.
enum ShiftAttempt {
    NotApplicable,
    Applied(SymState),
    Infinite,
    NeedModSplit { var_idx: usize, modulus: i64 },
    NeedMagSplit { var_idx: usize },
}

fn try_apply_shift_rule(state: &SymState, rule: &DiffRule) -> ShiftAttempt {
    let num_regs = state.regs.len();

    // 1. Every incrementing register must have max == Infinity so the loop isn't capped by a constant upper bound.
    for j in 0..num_regs {
        if rule.delta.data[j] > 0 && rule.max.data[j] != Infinity {
            return ShiftAttempt::NotApplicable;
        }
    }

    // 2. Check non-decrementing registers satisfy min <= E_j <= max.
    for j in 0..num_regs {
        let expr = &state.regs[j];
        let min_req = rule.min.data[j] as i64;
        if rule.delta.data[j] >= 0 {
            if expr.max_val() < Finite(min_req) {
                return ShiftAttempt::NotApplicable;
            }
            if expr.min_val() < Finite(min_req) {
                // Ambiguous lower bound on non-decrementing register: let basic step handle or split
                return ShiftAttempt::NotApplicable;
            }
        }
        if let Finite(max_req) = rule.max.data[j] {
            let max_req = max_req as i64;
            if expr.min_val() > Finite(max_req) {
                return ShiftAttempt::NotApplicable;
            }
            if expr.max_val() > Finite(max_req) {
                return ShiftAttempt::NotApplicable;
            }
        }
    }

    // 3. Collect all decrementing registers (`delta[j] < 0`).
    let dec_regs: Vec<usize> = (0..num_regs)
        .filter(|&j| rule.delta.data[j] < 0)
        .collect();

    if dec_regs.is_empty() {
        // No register decrements and all bounds hold -> applies infinitely!
        return ShiftAttempt::Infinite;
    }

    // All decrementing registers must be symbolic (have at least one positive parameter coefficient).
    // If a decrementing register is a constant, the rule can only apply a small constant number of times,
    // which basic single-stepping handles directly without over-splitting.
    for &j in &dec_regs {
        if state.regs[j].is_const().is_some() {
            return ShiftAttempt::NotApplicable;
        }
    }

    // 4. For each decrementing register `j`, compute how many times `Q_j` it can decrement.
    // Let `d = -delta[j] >= 1` and `base = min[j] - d >= 0`.
    // We need `E_j >= base`. If `E_j - base = d * Q_j + r_j` with `0 <= r_j < d` and `Q_j >= 0`,
    // then `Q_j` is the exact application count for register `j` for ALL `Q_j >= 0` (including `Q_j = 0`).
    let mut quotients: Vec<(usize, SymExpr)> = Vec::new();
    for &j in &dec_regs {
        let d = (-rule.delta.data[j]) as i64;
        let min_req = rule.min.data[j] as i64;
        let base = min_req - d;
        assert!(base >= 0);

        let shifted = state.regs[j].add_const(-base);
        if !shifted.is_always_non_negative() {
            // Need magnitude split on a parameter in state.regs[j] so shifted >= 0
            if let Some((var_idx, _)) = state.regs[j]
                .coeffs
                .iter()
                .enumerate()
                .find(|&(_, &c)| c > 0)
            {
                return ShiftAttempt::NeedMagSplit { var_idx };
            }
            return ShiftAttempt::NotApplicable;
        }

        match shifted.div_mod(d) {
            Err((var_idx, modulus)) => {
                return ShiftAttempt::NeedModSplit { var_idx, modulus };
            }
            Ok((q_expr, _rem)) => {
                quotients.push((j, q_expr));
            }
        }
    }

    // 5. Find bottleneck quotient `Q` among `quotients` such that `Q_other - Q >= 0` for all other decrementing regs.
    let mut chosen_q: Option<SymExpr> = None;
    for (_, q_cand) in &quotients {
        let dominates_all = quotients.iter().all(|(_, q_other)| {
            let diff = q_other.sub(q_cand);
            diff.is_always_non_negative()
        });
        if dominates_all {
            chosen_q = Some(q_cand.clone());
            break;
        }
    }

    let q_expr = match chosen_q {
        Some(q) => q,
        None => return ShiftAttempt::NotApplicable,
    };

    // Only apply if `q_expr` actually eliminates/reduces a symbolic parameter (i.e. not identically 0).
    if q_expr.is_const() == Some(0) {
        return ShiftAttempt::NotApplicable;
    }

    // 6. Apply `q_expr` times: `E_m <- E_m + delta[m] * Q`.
    let mut next_regs = state.regs.clone();
    for m in 0..num_regs {
        let del = rule.delta.data[m] as i64;
        if del != 0 {
            next_regs[m] = next_regs[m].add(&q_expr.scale(del));
        }
    }

    ShiftAttempt::Applied(SymState {
        regs: next_regs,
        lhs_params: state.lhs_params.clone(),
        base_steps: state
            .base_steps
            .add(&q_expr.scale(rule.num_steps as i64)),
        sim_steps: state.sim_steps + 1,
        trans_history: Vec::new(), // reset basic step history after shift acceleration
    })
}

/// Outcome of attempting a single basic instruction step on a `SymState`.
enum BasicStepOutcome {
    Halted,
    Stepped(SymState),
    Split { var_idx: usize },
}

fn step_symbolic_basic(prog: &Program, state: &SymState) -> BasicStepOutcome {
    let mut reg_fail: Vec<usize> = Vec::new();

    for instr in &prog.instrs {
        // Check if instr can apply to `state.regs`:
        // For each register `j` with `instr.data[j] < 0`, we need `regs[j] >= -instr.data[j]`.
        // First check if ANY register is provably `< -instr.data[j]` for all parameter values >= 0!
        // Choosing a provably failing register first avoids unnecessary parameter splits when
        // another register already guarantees the instruction cannot apply.
        let mut provably_fails_on: Option<usize> = None;
        let mut ambiguous_var: Option<usize> = None;

        for (j, &delta) in instr.data.iter().enumerate() {
            if delta < 0 {
                let req = (-delta) as i64;
                let expr = &state.regs[j];
                if expr.max_val() < Finite(req) {
                    provably_fails_on = Some(j);
                    break;
                } else if expr.min_val() < Finite(req) && ambiguous_var.is_none() {
                    if let Some((var_idx, _)) =
                        expr.coeffs.iter().enumerate().find(|&(_, &c)| c > 0)
                    {
                        ambiguous_var = Some(var_idx);
                    }
                }
            }
        }

        if let Some(fail_reg) = provably_fails_on {
            reg_fail.push(fail_reg);
            continue;
        }

        if let Some(var_idx) = ambiguous_var {
            return BasicStepOutcome::Split { var_idx };
        }

        // All required registers satisfy `regs[j] >= req` unconditionally!
        let next_regs = state
            .regs
            .iter()
            .zip(instr.data.iter())
            .map(|(expr, &delta)| expr.add_const(delta as i64))
            .collect();
        let mut next_history = state.trans_history.clone();
        next_history.push(Trans { reg_fail });

        return BasicStepOutcome::Stepped(SymState {
            regs: next_regs,
            lhs_params: state.lhs_params.clone(),
            base_steps: state.base_steps.add_const(1),
            sim_steps: state.sim_steps + 1,
            trans_history: next_history,
        });
    }

    BasicStepOutcome::Halted
}

/// Attempt to unify sibling rules that were split on `p_i = 0` vs `p_i = p_i + 1`.
pub fn unify_rules(mut rules: Vec<SymRule>) -> Vec<SymRule> {
    let mut changed = true;
    while changed {
        changed = false;
        'outer: for i in 0..rules.len() {
            for j in 0..rules.len() {
                if i == j {
                    continue;
                }
                if let Some(merged) = try_merge_zero_and_pos(&rules[i], &rules[j]) {
                    let first = i.min(j);
                    let second = i.max(j);
                    rules.remove(second);
                    rules[first] = merged;
                    changed = true;
                    break 'outer;
                }
            }
        }
    }
    rules
}

/// Check if `rule_zero` and `rule_pos` are sibling branches where `rule_zero` has `p_v = 0`
/// and `rule_pos` has `p_v = p_v + 1`, and their RHS expressions unify.
fn try_merge_zero_and_pos(rule_zero: &SymRule, rule_pos: &SymRule) -> Option<SymRule> {
    let num_params = rule_zero.lhs_params.len();
    for v in 0..num_params {
        // In rule_pos, moving back to the parent prior to `p_v <- p_v + 1` means substituting `p_v <- p_v - 1`.
        let parent_lhs: Vec<SymExpr> = rule_pos
            .lhs_params
            .iter()
            .map(|e| e.substitute_var(v, 1, -1))
            .collect();

        // Check that parent_lhs has non-negative constants and that substituting `p_v <- 0` gives `rule_zero.lhs_params`.
        if !parent_lhs.iter().all(|e| e.is_always_non_negative()) {
            continue;
        }
        let zero_lhs: Vec<SymExpr> = parent_lhs
            .iter()
            .map(|e| e.substitute_var(v, 0, 0))
            .collect();
        if zero_lhs != rule_zero.lhs_params {
            continue;
        }
        // Ensure `parent_lhs` actually depends on `v` (otherwise `zero_lhs == rule_pos.lhs_params`).
        if parent_lhs == rule_pos.lhs_params {
            continue;
        }

        // Now check if RHS can be unified by substituting `p_v <- p_v - 1` into `rule_pos.rhs`.
        match (&rule_zero.rhs, &rule_pos.rhs) {
            (RuleRhs::Halt, RuleRhs::Halt) => {
                return Some(SymRule {
                    lhs_params: parent_lhs,
                    rhs: RuleRhs::Halt,
                });
            }
            (RuleRhs::Infinite, RuleRhs::Infinite) => {
                return Some(SymRule {
                    lhs_params: parent_lhs,
                    rhs: RuleRhs::Infinite,
                });
            }
            (RuleRhs::Return(rhs_zero), RuleRhs::Return(rhs_pos)) => {
                let parent_rhs: Vec<SymExpr> = rhs_pos
                    .iter()
                    .map(|e| e.substitute_var(v, 1, -1))
                    .collect();
                if !parent_rhs.iter().all(|e| e.is_always_non_negative()) {
                    continue;
                }
                let check_zero: Vec<SymExpr> = parent_rhs
                    .iter()
                    .map(|e| e.substitute_var(v, 0, 0))
                    .collect();
                if &check_zero == rhs_zero {
                    return Some(SymRule {
                        lhs_params: parent_lhs,
                        rhs: RuleRhs::Return(parent_rhs),
                    });
                }
            }
            _ => {}
        }
    }
    None
}

/// Analyze `prog` using the provided `ConfigSpec` to deduce an exhaustive system of macro-rules.
pub fn analyze_with_spec(
    prog: &Program,
    spec: &ConfigSpec,
    config: &AnalyzerConfig,
) -> AnalysisResult {
    let start_step = find_start_config(prog, spec, config.transcript_steps);

    // Discover shift rules from concrete simulation starting from initial state (and from a sample spec state).
    let mut shift_rules = find_shift_rules(prog, State::start(prog), config.transcript_steps);
    let sample_state_data: Vec<BigInt> = spec
        .regs
        .iter()
        .enumerate()
        .map(|(i, r)| match r {
            RegSpec::Fixed(c) => BigInt::from(*c),
            RegSpec::Param(_) => BigInt::from(10 + 3 * (i as i32)),
        })
        .collect();
    for rule in find_shift_rules(prog, State::new(sample_state_data), config.transcript_steps) {
        if !shift_rules.contains(&rule) {
            shift_rules.push(rule);
        }
    }
    shift_rules.sort_by_key(|r| -r.num_steps);

    let mut queue: VecDeque<SymState> = VecDeque::new();
    queue.push_back(SymState::initial(spec));

    let mut deduced_rules: Vec<SymRule> = Vec::new();
    let mut branches_processed = 0;
    let mut incomplete_reason: Option<String> = None;

    while let Some(state) = queue.pop_front() {
        branches_processed += 1;
        if branches_processed > config.max_branches {
            incomplete_reason = Some(format!(
                "Exceeded max_branches limit ({})",
                config.max_branches
            ));
            break;
        }

        if state.sim_steps > 0 {
            if let Some(rhs_exprs) = spec.match_symbolic(&state.regs) {
                if state.base_steps.constant >= 1 {
                    deduced_rules.push(SymRule {
                        lhs_params: state.lhs_params,
                        rhs: RuleRhs::Return(rhs_exprs),
                    });
                    continue;
                } else if let Some((var_idx, _)) = state
                    .base_steps
                    .coeffs
                    .iter()
                    .enumerate()
                    .find(|&(_, &c)| c > 0)
                {
                    // For var_idx >= 1, base_steps >= 1 so it returns to spec;
                    // for var_idx == 0, 0 actual steps were taken so it must continue stepping.
                    let pos_state = state.substitute(var_idx, 1, 1);
                    if let Some(pos_rhs) = spec.match_symbolic(&pos_state.regs) {
                        deduced_rules.push(SymRule {
                            lhs_params: pos_state.lhs_params,
                            rhs: RuleRhs::Return(pos_rhs),
                        });
                    } else {
                        queue.push_front(pos_state);
                    }
                    queue.push_front(state.substitute(var_idx, 0, 0));
                    continue;
                }
            }
        }

        if state.sim_steps >= config.max_steps_per_branch {
            incomplete_reason = Some(format!(
                "Branch exceeded max_steps_per_branch ({})",
                config.max_steps_per_branch
            ));
            break;
        }

        // Dynamically extract any new shift rules from tandem repeats in the symbolic branch's own transition history.
        if state.trans_history.len() >= 2 {
            for rep_block in find_rep_blocks(&state.trans_history) {
                if rep_block.rep > 1 {
                    if let Some(new_rule) = DiffRule::from_trans_vec(prog, &rep_block.block) {
                        if !shift_rules.contains(&new_rule) {
                            shift_rules.push(new_rule);
                            shift_rules.sort_by_key(|r| -r.num_steps);
                        }
                    }
                }
            }
        }

        // 1. Try shift rules in priority order (longest first).
        let mut shift_action: Option<ShiftAttempt> = None;
        for rule in &shift_rules {
            let attempt = try_apply_shift_rule(&state, rule);
            if !matches!(attempt, ShiftAttempt::NotApplicable) {
                shift_action = Some(attempt);
                break;
            }
        }

        if let Some(action) = shift_action {
            match action {
                ShiftAttempt::NotApplicable => unreachable!(),
                ShiftAttempt::Applied(next_state) => {
                    queue.push_front(next_state);
                    continue;
                }
                ShiftAttempt::Infinite => {
                    deduced_rules.push(SymRule {
                        lhs_params: state.lhs_params,
                        rhs: RuleRhs::Infinite,
                    });
                    continue;
                }
                ShiftAttempt::NeedModSplit { var_idx, modulus } => {
                    if modulus > config.max_modulus {
                        incomplete_reason = Some(format!(
                            "Required modulus {} exceeds max_modulus ({})",
                            modulus, config.max_modulus
                        ));
                        break;
                    }
                    for r in (0..modulus).rev() {
                        queue.push_front(state.substitute(var_idx, modulus, r));
                    }
                    continue;
                }
                ShiftAttempt::NeedMagSplit { var_idx } => {
                    queue.push_front(state.substitute(var_idx, 1, 1));
                    queue.push_front(state.substitute(var_idx, 0, 0));
                    continue;
                }
            }
        }

        // 2. Fall back to a single basic instruction step.
        match step_symbolic_basic(prog, &state) {
            BasicStepOutcome::Halted => {
                deduced_rules.push(SymRule {
                    lhs_params: state.lhs_params,
                    rhs: RuleRhs::Halt,
                });
            }
            BasicStepOutcome::Stepped(next_state) => {
                queue.push_front(next_state);
            }
            BasicStepOutcome::Split { var_idx } => {
                queue.push_front(state.substitute(var_idx, 1, 1));
                queue.push_front(state.substitute(var_idx, 0, 0));
            }
        }
    }

    let rules = unify_rules(deduced_rules);

    let status = if let Some(reason) = incomplete_reason {
        DecisionStatus::Incomplete(reason)
    } else {
        check_macro_decision(&start_step, &rules)
    };

    AnalysisResult {
        spec: spec.clone(),
        start_step,
        rules,
        status,
    }
}

/// Match a concrete parameter vector `concrete_params` against `rule.lhs_params`,
/// returning the underlying non-negative branch variable assignment `p` if it matches.
pub fn match_rule_lhs(rule: &SymRule, concrete_params: &[BigInt]) -> Option<Vec<BigInt>> {
    let num_params = concrete_params.len();
    let mut p_vals = vec![BigInt::from(0); num_params];

    for (i, lhs_expr) in rule.lhs_params.iter().enumerate() {
        let target = &concrete_params[i];
        if let Some(c) = lhs_expr.is_const() {
            if *target != BigInt::from(c) {
                return None;
            }
        } else {
            // Expect single variable `i` with positive coefficient `m` and constant `r`
            let m = lhs_expr.coeffs[i];
            if m <= 0 {
                return None;
            }
            let diff = target.clone() - BigInt::from(lhs_expr.constant);
            if diff < BigInt::from(0) {
                return None;
            }
            let m_big = BigInt::from(m);
            let (q, rem) = diff.div_rem(m_big);
            if rem != BigInt::from(0) {
                return None;
            }
            p_vals[i] = q;
        }
    }
    Some(p_vals)
}

/// Evaluate high-level halting/non-halting decision from a complete macro-rule system.
fn check_macro_decision(
    start_step: &Option<(usize, Vec<BigInt>)>,
    rules: &[SymRule],
) -> DecisionStatus {
    let Some((_, start_params)) = start_step else {
        return DecisionStatus::InductiveSystemComplete;
    };
    if rules.is_empty() {
        return DecisionStatus::InductiveSystemComplete;
    }

    // 1. If no rule in the closed system halts, the program can never halt.
    if rules.iter().all(|r| r.rhs != RuleRhs::Halt) {
        return DecisionStatus::ProvenNonHalting;
    }

    // 2. Check if there is a guard parameter `d` where all Halt rules have constant `lhs_params[d] <= max_halt`
    // and all Return rules monotonically preserve `param[d] > max_halt`.
    let num_params = start_params.len();
    let mut non_decreasing_guard: Option<(usize, BigInt)> = None;
    for d in 0..num_params {
        let mut max_halt_const: Option<i64> = None;
        let mut all_halts_const_on_d = true;
        for r in rules.iter().filter(|r| r.rhs == RuleRhs::Halt) {
            if let Some(c) = r.lhs_params[d].is_const() {
                max_halt_const = Some(max_halt_const.map_or(c, |prev| prev.max(c)));
            } else {
                all_halts_const_on_d = false;
                break;
            }
        }
        if !all_halts_const_on_d {
            continue;
        }
        let Some(bound) = max_halt_const else { continue };

        // Check if every Return rule has `rhs[d] - lhs[d] >= 0` for all p >= 0.
        let all_returns_non_decreasing = rules.iter().all(|r| match &r.rhs {
            RuleRhs::Return(rhs_exprs) => rhs_exprs[d].sub(&r.lhs_params[d]).is_always_non_negative(),
            _ => true,
        });
        if all_returns_non_decreasing {
            non_decreasing_guard = Some((d, BigInt::from(bound)));
            break;
        }
    }

    // 3. Simulate the deduced macro-system for up to 50 macro-steps from `start_params`.
    let mut cur = start_params.clone();
    let mut visited: HashSet<Vec<BigInt>> = HashSet::new();

    for _ in 0..50 {
        if !visited.insert(cur.clone()) {
            return DecisionStatus::ProvenNonHalting;
        }
        if let Some((d, ref bound)) = non_decreasing_guard {
            if cur[d] > *bound {
                return DecisionStatus::ProvenNonHalting;
            }
        }

        let mut matched = None;
        for rule in rules {
            if let Some(p_vals) = match_rule_lhs(rule, &cur) {
                matched = Some((&rule.rhs, p_vals));
                break;
            }
        }

        let Some((rhs, p_vals)) = matched else {
            break;
        };
        match rhs {
            RuleRhs::Halt => return DecisionStatus::ProvenHalting,
            RuleRhs::Infinite => return DecisionStatus::ProvenNonHalting,
            RuleRhs::Return(exprs) => {
                cur = exprs.iter().map(|e| e.evaluate(&p_vals)).collect();
            }
        }
    }

    DecisionStatus::InductiveSystemComplete
}

/// Verify that a complete `AnalysisResult` is exhaustive, mutually exclusive, and sound
/// against concrete simulation of `prog` for all parameter tuples in `0..=max_param_val`.
pub fn verify_rules_concretely(
    prog: &Program,
    result: &AnalysisResult,
    max_param_val: i32,
    max_sim_steps: usize,
) -> Result<(), String> {
    let num_params = result.spec.num_params();
    let mut tuples: Vec<Vec<BigInt>> = vec![vec![]];
    for _ in 0..num_params {
        let mut next = Vec::new();
        for t in &tuples {
            for v in 0..=max_param_val {
                let mut t2 = t.clone();
                t2.push(BigInt::from(v));
                next.push(t2);
            }
        }
        tuples = next;
    }

    for params in tuples {
        // 1. Check that exactly one rule matches `params`.
        let matching_rules: Vec<(&SymRule, Vec<BigInt>)> = result
            .rules
            .iter()
            .filter_map(|r| match_rule_lhs(r, &params).map(|p| (r, p)))
            .collect();

        if matching_rules.len() != 1 {
            return Err(format!(
                "Expected exactly 1 matching rule for {:?}, found {}",
                params,
                matching_rules.len()
            ));
        }

        let (rule, p_vals) = &matching_rules[0];

        // 2. Construct concrete state for S(params) and simulate until it returns to S(...) or halts.
        let state_data: Vec<BigInt> = result
            .spec
            .regs
            .iter()
            .map(|r| match r {
                RegSpec::Fixed(c) => BigInt::from(*c),
                RegSpec::Param(idx) => params[*idx].clone(),
            })
            .collect();
        let mut sim_state = State::new(state_data);

        let mut returned_params = None;
        let mut halted = false;
        for _ in 0..max_sim_steps {
            if !prog.step(&mut sim_state) {
                halted = true;
                break;
            }
            if let Some(found_params) = result.spec.match_concrete(&sim_state) {
                returned_params = Some(found_params);
                break;
            }
        }

        match &rule.rhs {
            RuleRhs::Halt => {
                if !halted {
                    return Err(format!(
                        "Rule predicted Halt for {:?}, but simulation did not halt (returned {:?})",
                        params, returned_params
                    ));
                }
            }
            RuleRhs::Return(exprs) => {
                let expected: Vec<BigInt> = exprs.iter().map(|e| e.evaluate(p_vals)).collect();
                if returned_params.as_ref() != Some(&expected) {
                    return Err(format!(
                        "Rule predicted Return({:?}) for {:?}, but simulation gave {:?} (halted={})",
                        expected, params, returned_params, halted
                    ));
                }
            }
            RuleRhs::Infinite => {
                if halted || returned_params.is_some() {
                    return Err(format!(
                        "Rule predicted Infinite for {:?}, but simulation halted={} or returned={:?}",
                        params, halted, returned_params
                    ));
                }
            }
        }
    }

    Ok(())
}

/// Automatically discover candidate `ConfigSpec`s from a concrete simulation transcript of `prog`.
pub fn discover_config_specs(
    prog: &Program,
    sim_steps: usize,
    max_params: usize,
) -> Vec<ConfigSpec> {
    let num_regs = prog.num_registers();
    let max_k = max_params.min(num_regs.saturating_sub(1)).max(1);

    // Collect concrete states visited at (and immediately around) boundaries of repeated blocks in the transcript.
    // A loop like `E (A E)^k` or `B (B C B)^k` may be phase-shifted by 1-2 steps at entry/exit,
    // so sampling a small window around each `rep > 1` block captures canonical entry states like `[x, 0, 0, 2, y]`.
    let start_state = State::start(prog);
    let trans_vec = transcript(prog, start_state.clone(), sim_steps);
    let rep_blocks = find_rep_blocks(&trans_vec);

    let mut all_states: Vec<State> = Vec::with_capacity(trans_vec.len() + 1);
    let mut cur_state = start_state;
    all_states.push(cur_state.clone());
    for _ in 0..trans_vec.len() {
        prog.step(&mut cur_state);
        all_states.push(cur_state.clone());
    }

    let mut sample_indices: HashSet<usize> = HashSet::new();
    let mut pos = 0;
    for block in &rep_blocks {
        let block_steps = block.rep * block.block.len();
        for offset in 0..=2 {
            if pos + offset < all_states.len() {
                sample_indices.insert(pos + offset);
            }
            if pos >= offset {
                sample_indices.insert(pos - offset);
            }
        }
        pos += block_steps;
    }
    if pos < all_states.len() {
        sample_indices.insert(pos);
    }

    let mut sorted_indices: Vec<usize> = sample_indices.into_iter().collect();
    sorted_indices.sort_unstable();
    let boundary_states: Vec<State> = sorted_indices
        .into_iter()
        .map(|i| all_states[i].clone())
        .collect();

    // Group boundary states by their next transition so we look at states in the same control phase.
    // For each candidate mask of `k` parameter positions (1 <= k <= max_k), count how many boundary states
    // match the fixed constants and how many distinct parameter tuples are observed.
    let mut pattern_hits: HashMap<Vec<Option<SmallInt>>, HashSet<Vec<BigInt>>> = HashMap::new();

    for state in &boundary_states {
        let small_vals: Option<Vec<SmallInt>> = state
            .data
            .iter()
            .map(|v| v.to_i32())
            .collect();
        let Some(vals) = small_vals else { continue };

        // Generate masks with 1..=max_k parameter slots.
        // Any register with value > 4 MUST be a parameter slot.
        let forced_params: Vec<usize> = vals
            .iter()
            .enumerate()
            .filter_map(|(i, &v)| if v > 4 { Some(i) } else { None })
            .collect();

        if forced_params.len() > max_k {
            continue;
        }

        // Also try making subsets of the remaining registers parameters up to `max_k`.
        let other_regs: Vec<usize> = (0..num_regs)
            .filter(|i| !forced_params.contains(i))
            .collect();

        let mut param_sets: Vec<Vec<usize>> = Vec::new();
        if !forced_params.is_empty() {
            param_sets.push(forced_params.clone());
        }
        // Add 1 extra parameter beyond forced_params if within max_k
        if forced_params.len() < max_k {
            for &r1 in &other_regs {
                let mut s = forced_params.clone();
                s.push(r1);
                s.sort_unstable();
                param_sets.push(s);
            }
        }
        // Add 2 extra parameters beyond forced_params if within max_k
        if forced_params.len() + 1 < max_k {
            for (idx, &r1) in other_regs.iter().enumerate() {
                for &r2 in &other_regs[idx + 1..] {
                    let mut s = forced_params.clone();
                    s.push(r1);
                    s.push(r2);
                    s.sort_unstable();
                    param_sets.push(s);
                }
            }
        }

        for pset in param_sets {
            let mut key: Vec<Option<SmallInt>> = vals.iter().map(|&v| Some(v)).collect();
            let mut param_vals: Vec<BigInt> = Vec::with_capacity(pset.len());
            for &p_idx in &pset {
                key[p_idx] = None;
                param_vals.push(state.data[p_idx].clone());
            }
            pattern_hits.entry(key).or_default().insert(param_vals);
        }
    }

    // Filter and score candidates:
    // Require that each parameter actually varies across the observed states (so constants aren't turned into fake params).
    let mut scored: Vec<(usize, usize, usize, i32, ConfigSpec)> = Vec::new();
    for (key, distinct_tuples) in pattern_hits {
        if distinct_tuples.len() < 3 {
            continue;
        }
        let num_params = key.iter().filter(|x| x.is_none()).count();
        if num_params == 0 {
            continue;
        }

        // Verify every parameter position takes at least 2 distinct values across `distinct_tuples`.
        let all_params_vary = (0..num_params).all(|p_i| {
            let first = &distinct_tuples.iter().next().unwrap()[p_i];
            distinct_tuples.iter().any(|t| &t[p_i] != first)
        });
        if !all_params_vary {
            continue;
        }

        let mut regs = Vec::with_capacity(num_regs);
        let mut param_names = Vec::with_capacity(num_params);
        for item in key {
            match item {
                Some(c) => regs.push(RegSpec::Fixed(c)),
                None => {
                    let idx = param_names.len();
                    param_names.push(ConfigSpec::default_param_name(idx));
                    regs.push(RegSpec::Param(idx));
                }
            }
        }

        let zero_count = regs
            .iter()
            .filter(|r| matches!(r, RegSpec::Fixed(0)))
            .count();
        let fixed_sum: i32 = regs
            .iter()
            .map(|r| match r {
                RegSpec::Fixed(c) => c.abs(),
                RegSpec::Param(_) => 0,
            })
            .sum();

        let spec = ConfigSpec::new(regs, param_names);
        scored.push((distinct_tuples.len(), num_params, zero_count, fixed_sum, spec));
    }

    // Sort within each parameter count by most distinct hits descending, then more zeros / smaller constants,
    // with deterministic tie-breaking on the spec itself.
    scored.sort_by(|a, b| {
        a.1.cmp(&b.1)
            .then_with(|| b.0.cmp(&a.0))
            .then_with(|| b.2.cmp(&a.2))
            .then_with(|| a.3.cmp(&b.3))
            .then_with(|| a.4.cmp(&b.4))
    });

    // Keep up to top 12 candidates per parameter count k = 1..=max_k so low-parameter specs are tried first
    // and all phases of a macro-cycle are considered.
    let shift_rules = find_shift_rules(prog, State::start(prog), sim_steps);
    let mut result = Vec::new();
    for k in 1..=max_k {
        for (_, _num_p, _, _, spec) in scored.iter().filter(|s| s.1 == k).take(12) {
            let canon = canonicalize_spec(prog, spec, &shift_rules);
            if !result.contains(&canon) {
                result.push(canon);
            }
            if !result.contains(spec) {
                result.push(spec.clone());
            }
        }
    }
    result
}

/// Advance a transient `ConfigSpec` along unconditional basic steps (where no shift rule applies
/// and parameters remain pure 1*p_i variables) to reach the canonical loop/branch head.
pub fn canonicalize_spec(
    prog: &Program,
    spec: &ConfigSpec,
    shift_rules: &[DiffRule],
) -> ConfigSpec {
    let mut cur_spec = spec.clone();
    for _ in 0..prog.num_instrs() {
        let init = SymState::initial(&cur_spec);
        if shift_rules
            .iter()
            .any(|r| !matches!(try_apply_shift_rule(&init, r), ShiftAttempt::NotApplicable))
        {
            break;
        }
        let BasicStepOutcome::Stepped(next_state) = step_symbolic_basic(prog, &init) else {
            break;
        };
        // Convert next_state.regs back to a ConfigSpec if all parameters are still pure `1 * p_i + 0`
        // and all other registers are fixed constants.
        let mut next_regs = Vec::with_capacity(cur_spec.regs.len());
        let mut seen_params = vec![false; cur_spec.num_params()];
        let mut valid = true;
        for expr in &next_state.regs {
            if let Some(c) = expr.is_const() {
                next_regs.push(RegSpec::Fixed(c as SmallInt));
            } else if expr.constant == 0
                && expr.coeffs.iter().filter(|&&c| c != 0).count() == 1
                && expr.coeffs.iter().any(|&c| c == 1)
            {
                let p_idx = expr.coeffs.iter().position(|&c| c == 1).unwrap();
                if seen_params[p_idx] {
                    valid = false;
                    break;
                }
                seen_params[p_idx] = true;
                next_regs.push(RegSpec::Param(p_idx));
            } else {
                valid = false;
                break;
            }
        }
        if valid && seen_params.into_iter().all(|b| b) {
            cur_spec = ConfigSpec::new(next_regs, cur_spec.param_names);
        } else {
            break;
        }
    }
    cur_spec
}

/// Check if `spec` is a transient state that immediately takes an unconditional basic step
/// (with no shift rule applicable at the initial state) rather than being a loop or branch head.
fn is_transient_spec(prog: &Program, spec: &ConfigSpec, shift_rules: &[DiffRule]) -> bool {
    let init = SymState::initial(spec);
    for rule in shift_rules {
        if !matches!(try_apply_shift_rule(&init, rule), ShiftAttempt::NotApplicable) {
            return false;
        }
    }
    matches!(step_symbolic_basic(prog, &init), BasicStepOutcome::Stepped(_))
}

/// Automatically discover a `ConfigSpec` and analyze `prog`.
pub fn analyze_program_auto(prog: &Program, config: &AnalyzerConfig) -> Option<AnalysisResult> {
    let candidates = discover_config_specs(prog, config.transcript_steps, 3);
    let shift_rules = find_shift_rules(prog, State::start(prog), config.transcript_steps);
    let mut best_complete: Option<AnalysisResult> = None;
    let mut best_incomplete: Option<AnalysisResult> = None;

    for spec in candidates {
        let res = analyze_with_spec(prog, &spec, config);
        if !matches!(res.status, DecisionStatus::Incomplete(_)) {
            let is_better = match &best_complete {
                None => true,
                Some(prev) => {
                    let prev_key = (
                        prev.spec.num_params(),
                        prev.rules.len(),
                        is_transient_spec(prog, &prev.spec, &shift_rules),
                        prev.start_step.as_ref().map(|(s, _)| *s).unwrap_or(usize::MAX),
                    );
                    let cur_key = (
                        res.spec.num_params(),
                        res.rules.len(),
                        is_transient_spec(prog, &res.spec, &shift_rules),
                        res.start_step.as_ref().map(|(s, _)| *s).unwrap_or(usize::MAX),
                    );
                    cur_key < prev_key
                }
            };
            if is_better {
                best_complete = Some(res);
            }
        } else if best_incomplete.is_none() {
            best_incomplete = Some(res);
        }
    }

    best_complete.or(best_incomplete)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse::parse_program;

    #[test]
    fn test_user_example_explicit_spec() {
        let prog = parse_program("[1/15, 27/77, 49/3, 10/49, 33/2]");
        let spec: ConfigSpec = "[x, 0, 0, 2, y]".parse().unwrap();
        let config = AnalyzerConfig::default();

        let result = analyze_with_spec(&prog, &spec, &config);
        println!("{}", result);

        assert_eq!(
            result.start_step,
            Some((2, vec![BigInt::from(0), BigInt::from(1)]))
        );
        assert_eq!(result.status, DecisionStatus::InductiveSystemComplete);

        let formatted_rules: Vec<String> = result
            .rules
            .iter()
            .map(|r| r.format_rule(&spec.param_names))
            .collect();

        assert_eq!(
            formatted_rules,
            vec![
                "S(0, 2y) -> Halt",
                "S(x, 2y) -> S(x-1, 5y+2)  if x >= 1",
                "S(x, 2y+1) -> S(x+2, 5y)",
            ]
        );
    }

    #[test]
    fn test_user_example_auto_discovery() {
        let prog = parse_program("[1/15, 27/77, 49/3, 10/49, 33/2]");
        let config = AnalyzerConfig::default();

        let result = analyze_program_auto(&prog, &config).expect("Should discover a ConfigSpec");
        println!("{}", result);

        let expected_spec: ConfigSpec = "[x, 0, 0, 2, y]".parse().unwrap();
        assert_eq!(result.spec, expected_spec);
        assert_eq!(result.status, DecisionStatus::InductiveSystemComplete);
        verify_rules_concretely(&prog, &result, 5, 5000).unwrap();
    }

    #[test]
    fn test_hydra_and_collatz() {
        let config = AnalyzerConfig::default();

        // Hydra: [507/22, 26/33, 245/2, 5/21, 1/3, 11/13, 22/5]
        let hydra = parse_program("[507/22, 26/33, 245/2, 5/21, 1/3, 11/13, 22/5]");
        let hydra_res = analyze_program_auto(&hydra, &config).expect("Hydra spec");
        println!("=== HYDRA ===\n{}", hydra_res);
        assert_eq!(hydra_res.status, DecisionStatus::InductiveSystemComplete);
        verify_rules_concretely(&hydra, &hydra_res, 5, 5000).unwrap();

        // Collatz-like non-halting: [2/45, 25/6, 343/2, 9/7, 2/3]
        let collatz = parse_program("[2/45, 25/6, 343/2, 9/7, 2/3]");
        let collatz_res = analyze_program_auto(&collatz, &config).expect("Collatz spec");
        println!("=== COLLATZ ===\n{}", collatz_res);
        assert_eq!(collatz_res.status, DecisionStatus::ProvenNonHalting);
        verify_rules_concretely(&collatz, &collatz_res, 10, 5000).unwrap();
    }
}
