use crate::macro_program::MacroInst;
use crate::program::Target;
use crate::deciders::symbolic::{AffineExpr, Condition, ConditionType};
use minilp::{Problem, OptimizationDirection, Variable, ComparisonOp};
use std::collections::{HashMap, VecDeque};

pub struct PolyhedralClosedSet {
    pub state: usize,
    pub conditions: Vec<Condition>,
    pub num_registers: usize,
}

#[derive(Clone)]
struct SymbolicState {
    pc: Target,
    regs: Vec<AffineExpr>,
    path_conditions: Vec<Condition>,
    depth: usize,
    trace: Vec<(String, String)>,
}

#[derive(Debug)]
pub enum VerifyResult {
    Verified,
    ConditionFailed(Vec<Condition>),
    Failed(String),
}

fn add_expr_to_problem(prob: &mut Problem, vars: &mut HashMap<usize, Variable>, expr: &AffineExpr, comp: ComparisonOp) {
    let mut term_vars = Vec::new();
    for (&var_idx, &coeff) in &expr.coeffs {
        let v = *vars.entry(var_idx).or_insert_with(|| prob.add_var(0.0, (0.0, f64::INFINITY)));
        term_vars.push((v, coeff as f64));
    }
    prob.add_constraint(&term_vars, comp, -expr.constant as f64);
}

fn is_satisfiable(conditions: &[Condition]) -> bool {
    let mut problem = Problem::new(OptimizationDirection::Maximize);
    let mut vars = HashMap::new();

    for cond in conditions {
        match cond.cond_type {
            ConditionType::GreaterEqualZero => {
                add_expr_to_problem(&mut problem, &mut vars, &cond.expr, ComparisonOp::Ge);
            }
            ConditionType::EqualZero => {
                add_expr_to_problem(&mut problem, &mut vars, &cond.expr, ComparisonOp::Eq);
            }
        }
    }

    match problem.solve() {
        Ok(_) => true,
        Err(minilp::Error::Infeasible) => false,
        Err(minilp::Error::Unbounded) => true,
    }
}

fn implies(conditions: &[Condition], target_expr: &AffineExpr, target_cond_type: &ConditionType) -> bool {
    if !is_satisfiable(conditions) {
        return true;
    }

    match target_cond_type {
        ConditionType::GreaterEqualZero => {
            let mut problem = Problem::new(OptimizationDirection::Minimize);
            let mut vars = HashMap::new();

            // First create all variables used in target_expr so they get the correct objective coeff
            for (&var_idx, &coeff) in &target_expr.coeffs {
                vars.insert(var_idx, problem.add_var(coeff as f64, (0.0, f64::INFINITY)));
            }

            for cond in conditions {
                match cond.cond_type {
                    ConditionType::GreaterEqualZero => {
                        add_expr_to_problem(&mut problem, &mut vars, &cond.expr, ComparisonOp::Ge);
                    }
                    ConditionType::EqualZero => {
                        add_expr_to_problem(&mut problem, &mut vars, &cond.expr, ComparisonOp::Eq);
                    }
                }
            }

            match problem.solve() {
                Ok(solution) => {
                    let min_val = solution.objective() + target_expr.constant as f64;
                    min_val >= -1e-5
                }
                Err(minilp::Error::Infeasible) => true,
                Err(minilp::Error::Unbounded) => false,
            }
        }
        ConditionType::EqualZero => {
            let mut neg_expr = target_expr.clone();
            neg_expr.constant = -neg_expr.constant;
            for v in neg_expr.coeffs.values_mut() {
                *v = -*v;
            }
            implies(conditions, target_expr, &ConditionType::GreaterEqualZero) &&
            implies(conditions, &neg_expr, &ConditionType::GreaterEqualZero)
        }
    }
}

fn format_regs(regs: &[AffineExpr]) -> String {
    let mut s = String::new();
    s.push('[');
    for (i, r) in regs.iter().enumerate() {
        if i > 0 { s.push_str(", "); }
        s.push_str(&r.to_string());
    }
    s.push(']');
    s
}

pub fn verify_polyhedral_closed_set(prog: &[MacroInst], closed_set: &PolyhedralClosedSet, verbose: bool) -> VerifyResult {
    if verbose {
        println!("Macro Abstracted Program:");
        for (i, m) in prog.iter().enumerate() {
            println!("  {}", m.to_string_with_state(i, closed_set.num_registers));
        }
        println!();
    }

    let mut initial_regs = Vec::new();
    let mut initial_conds = closed_set.conditions.clone();

    for i in 0..closed_set.num_registers {
        let var = AffineExpr::var(i);
        initial_regs.push(var.clone());
        initial_conds.push(Condition::geq_zero(var));
    }

    let mut queue = VecDeque::new();
    queue.push_back(SymbolicState {
        pc: Target::Inst(closed_set.state),
        regs: initial_regs,
        path_conditions: initial_conds,
        depth: 0,
        trace: vec![],
    });

    let mut path_count = 0;
    let mut all_failed_conds = Vec::new();

    while let Some(state) = queue.pop_front() {
        if state.depth > 1000 {
            return VerifyResult::Failed("Depth limit exceeded (potential infinite loop)".to_string());
        }

        if state.pc == Target::Halt {
            if is_satisfiable(&state.path_conditions) {
                if verbose {
                    println!("Path failed (reaches Halt):");
                    let mut max_len = 0;
                    for (s, _) in &state.trace { max_len = max_len.max(s.len()); }
                    for (s, a) in &state.trace { println!("      {:<width$}   {}", s, a, width = max_len); }
                    println!("      Halt:{}", format_regs(&state.regs));
                }
                return VerifyResult::Failed("Reachable Halt state found".to_string());
            }
            continue;
        }

        let Target::Inst(pc_idx) = state.pc else { unreachable!() };

        if state.depth > 0 && pc_idx == closed_set.state {
            if is_satisfiable(&state.path_conditions) {
                if verbose {
                    path_count += 1;
                    
                    let new_conditions = &state.path_conditions[closed_set.conditions.len() + closed_set.num_registers..];
                    let cond_strs: Vec<String> = new_conditions.iter().map(|c| c.to_string()).collect();
                    println!("Path {} successfully closed (Branch conditions: [{}]):", path_count, cond_strs.join(", "));
                    
                    let mut max_len = 0;
                    for (s, _) in &state.trace { max_len = max_len.max(s.len()); }
                    for (s, a) in &state.trace { println!("      {:<width$}   {}", s, a, width = max_len); }
                    println!("      {}:{}", (b'A' + pc_idx as u8) as char, format_regs(&state.regs));
                }

                let mut path_failed_conds = Vec::new();
                for cond in &closed_set.conditions {
                    let mut substituted_cond_expr = AffineExpr::new(cond.expr.constant);
                    for (&var_idx, &coeff) in &cond.expr.coeffs {
                        if var_idx < state.regs.len() {
                            substituted_cond_expr.mul_add(coeff, &state.regs[var_idx]);
                        }
                    }

                    if !implies(&state.path_conditions, &substituted_cond_expr, &cond.cond_type) {
                        if verbose {
                            println!("  FAILED to prove condition {} is preserved (evaluates to {} which is not implied by path).", 
                                     cond,
                                     Condition { expr: substituted_cond_expr.clone(), cond_type: cond.cond_type.clone() });
                        }
                        path_failed_conds.push(cond.clone());
                    } else if verbose {
                        println!("  Successfully proved condition {} is preserved (evaluates to {} which is implied by path).", 
                                 cond,
                                 Condition { expr: substituted_cond_expr, cond_type: cond.cond_type.clone() });
                    }
                }
                
                if !path_failed_conds.is_empty() {
                    for c in path_failed_conds {
                        if !all_failed_conds.contains(&c) {
                            all_failed_conds.push(c);
                        }
                    }
                }
                if verbose { println!(); }
            }
            continue;
        }

        if !is_satisfiable(&state.path_conditions) {
            continue;
        }

        let inst = &prog[pc_idx];
        match inst {
            MacroInst::Inc { reg, next } => {
                let mut next_state = state.clone();
                if *reg >= next_state.regs.len() {
                    next_state.regs.resize(*reg + 1, AffineExpr::new(0));
                }
                next_state.regs[*reg].add_const(1);
                next_state.pc = *next;
                next_state.depth += 1;
                if verbose {
                    let st_str = format!("{}:{}", (b'A' + pc_idx as u8) as char, format_regs(&state.regs));
                    let act_str = inst.to_string_with_state(pc_idx, closed_set.num_registers);
                    next_state.trace.push((st_str, act_str));
                }
                queue.push_back(next_state);
            }
            MacroInst::Transfer { reg, incs, next } => {
                let mut next_state = state.clone();
                if *reg >= next_state.regs.len() {
                    next_state.regs.resize(*reg + 1, AffineExpr::new(0));
                }
                let reg_expr = next_state.regs[*reg].clone();
                next_state.regs[*reg] = AffineExpr::new(0);

                for (&target_reg, &count) in incs {
                    if target_reg >= next_state.regs.len() {
                        next_state.regs.resize(target_reg + 1, AffineExpr::new(0));
                    }
                    next_state.regs[target_reg].mul_add(count as i64, &reg_expr);
                }

                next_state.pc = *next;
                next_state.depth += 1;
                if verbose {
                    let st_str = format!("{}:{}", (b'A' + pc_idx as u8) as char, format_regs(&state.regs));
                    let act_str = inst.to_string_with_state(pc_idx, closed_set.num_registers);
                    next_state.trace.push((st_str, act_str));
                }
                queue.push_back(next_state);
            }
            MacroInst::Dec { reg, next_not_zero, next_zero } => {
                let r_expr = if *reg < state.regs.len() {
                    state.regs[*reg].clone()
                } else {
                    AffineExpr::new(0)
                };

                // Zero branch
                let mut zero_state = state.clone();
                zero_state.path_conditions.push(Condition::eq_zero(r_expr.clone()));
                zero_state.pc = *next_zero;
                zero_state.depth += 1;
                if verbose {
                    let st_str = format!("{}:{}", (b'A' + pc_idx as u8) as char, format_regs(&state.regs));
                    let act_str = format!("{} (branch: == 0)", inst.to_string_with_state(pc_idx, closed_set.num_registers));
                    zero_state.trace.push((st_str, act_str));
                }
                queue.push_back(zero_state);

                // Not-zero branch
                let mut nz_state = state.clone();
                let mut r_minus_1 = r_expr.clone();
                r_minus_1.add_const(-1);
                nz_state.path_conditions.push(Condition::geq_zero(r_minus_1));
                
                if *reg >= nz_state.regs.len() {
                    nz_state.regs.resize(*reg + 1, AffineExpr::new(0));
                }
                nz_state.regs[*reg].add_const(-1);
                nz_state.pc = *next_not_zero;
                nz_state.depth += 1;
                if verbose {
                    let st_str = format!("{}:{}", (b'A' + pc_idx as u8) as char, format_regs(&state.regs));
                    let act_str = format!("{} (branch: > 0)", inst.to_string_with_state(pc_idx, closed_set.num_registers));
                    nz_state.trace.push((st_str, act_str));
                }
                queue.push_back(nz_state);
            }
        }
    }

    if !all_failed_conds.is_empty() {
        return VerifyResult::ConditionFailed(all_failed_conds);
    }

    VerifyResult::Verified
}
