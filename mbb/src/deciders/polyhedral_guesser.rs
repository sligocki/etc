use crate::program::{Instruction, Program, Target};
use crate::simulate::State;
use crate::deciders::polyhedral::{PolyhedralClosedSet, verify_polyhedral_closed_set, VerifyResult};
use crate::macro_program::{MacroInst, abstract_program};
use crate::deciders::symbolic::{AffineExpr, Condition};

pub fn record_history(prog: &Program, target_state: usize, step_limit: u64) -> Vec<Vec<u64>> {
    let mut history = Vec::new();
    let mut state = State::new();
    let num_regs = prog.num_regs();

    loop {
        if state.steps >= step_limit {
            break;
        }

        if state.pc == target_state {
            let mut regs = state.registers.clone();
            regs.resize(num_regs, 0);
            history.push(regs);
        }

        if state.pc >= prog.instructions.len() {
            break;
        }

        let inst = &prog.instructions[state.pc];
        state.steps += 1;

        match inst {
            Instruction::Inc { reg, next } => {
                let val = state.get_reg(*reg);
                state.set_reg(*reg, val.wrapping_add(1));
                match next {
                    Target::Halt => break,
                    Target::Inst(i) => state.pc = *i,
                }
            }
            Instruction::Dec { reg, next_not_zero, next_zero } => {
                let val = state.get_reg(*reg);
                if val == 0 {
                    match next_zero {
                        Target::Halt => break,
                        Target::Inst(i) => state.pc = *i,
                    }
                } else {
                    state.set_reg(*reg, val - 1);
                    match next_not_zero {
                        Target::Halt => break,
                        Target::Inst(i) => state.pc = *i,
                    }
                }
            }
        }
    }

    history
}

pub fn guess_conditions(history: &[Vec<u64>], num_regs: usize) -> Vec<Condition> {
    let mut conditions = Vec::new();
    if history.is_empty() { return conditions; }

    let mut min_val = vec![u64::MAX; num_regs];
    let mut max_val = vec![0u64; num_regs];
    let mut min_diff = vec![vec![i64::MAX; num_regs]; num_regs];
    let mut max_diff = vec![vec![i64::MIN; num_regs]; num_regs];

    for regs in history {
        for i in 0..num_regs {
            min_val[i] = min_val[i].min(regs[i]);
            max_val[i] = max_val[i].max(regs[i]);
            for j in 0..num_regs {
                if i == j { continue; }
                let diff = regs[i] as i64 - regs[j] as i64;
                min_diff[i][j] = min_diff[i][j].min(diff);
                max_diff[i][j] = max_diff[i][j].max(diff);
            }
        }
    }

    for i in 0..num_regs {
        if min_val[i] == max_val[i] {
            let mut expr = AffineExpr::var(i);
            expr.add_const(-(min_val[i] as i64));
            conditions.push(Condition::eq_zero(expr));
        } else {
            let mut expr = AffineExpr::var(i);
            expr.add_const(-(min_val[i] as i64));
            conditions.push(Condition::geq_zero(expr));

            // Also guess the generic >= 0 if it holds
            if min_val[i] > 0 {
                conditions.push(Condition::geq_zero(AffineExpr::var(i)));
            }

            let mut expr2 = AffineExpr::new(max_val[i] as i64);
            expr2.coeffs.insert(i, -1);
            conditions.push(Condition::geq_zero(expr2));
        }

        for j in 0..num_regs {
            if i == j { continue; }
            if min_diff[i][j] == max_diff[i][j] {
                let mut expr = AffineExpr::var(i);
                expr.coeffs.insert(j, -1);
                expr.add_const(-min_diff[i][j]);
                conditions.push(Condition::eq_zero(expr));
            } else {
                let mut expr1 = AffineExpr::var(i);
                expr1.coeffs.insert(j, -1);
                expr1.add_const(-min_diff[i][j]);
                conditions.push(Condition::geq_zero(expr1));

                // Also guess the generic >= 0 if it holds
                if min_diff[i][j] > 0 {
                    let mut expr_zero = AffineExpr::var(i);
                    expr_zero.coeffs.insert(j, -1);
                    conditions.push(Condition::geq_zero(expr_zero));
                }

                let mut expr2 = AffineExpr::var(j);
                expr2.coeffs.insert(i, -1);
                expr2.add_const(max_diff[i][j]);
                conditions.push(Condition::geq_zero(expr2));
            }
        }
    }

    let mut unique_conds = Vec::new();
    for c in conditions {
        if !unique_conds.contains(&c) {
            unique_conds.push(c);
        }
    }
    unique_conds
}

pub fn find_closed_set(prog: &Program, verbose: bool) -> Option<PolyhedralClosedSet> {
    let macros = abstract_program(prog);
    let num_regs = prog.num_regs();

    for (state_idx, m) in macros.iter().enumerate() {
        if !matches!(m, MacroInst::Dec { .. }) {
            continue;
        }

        let history = record_history(prog, state_idx, 100_000);
        if history.len() < 10 {
            continue;
        }

        let steady_history = &history[history.len() / 2..];
        let mut candidate_conditions = guess_conditions(steady_history, num_regs);

        if verbose {
            println!("Testing State {} with {} initial guessed conditions...", (b'A' + state_idx as u8) as char, candidate_conditions.len());
            for c in &candidate_conditions { println!("    {}", c); }
        }

        loop {
            let closed_set = PolyhedralClosedSet {
                state: state_idx,
                conditions: candidate_conditions.clone(),
                num_registers: num_regs,
            };

            match verify_polyhedral_closed_set(&macros, &closed_set, false) {
                VerifyResult::Verified => {
                    if verbose {
                        println!("Verified with {} conditions. Minimizing...", candidate_conditions.len());
                    }

                    // Before minimizing the full set, try verifying with ONLY the simple conditions (constant == 0)
                    let simple_conds: Vec<Condition> = candidate_conditions.iter()
                        .filter(|c| c.expr.constant == 0)
                        .cloned()
                        .collect();
                    
                    let mut final_conds = if simple_conds.len() < candidate_conditions.len() && 
                        matches!(verify_polyhedral_closed_set(&macros, &PolyhedralClosedSet { state: state_idx, conditions: simple_conds.clone(), num_registers: num_regs }, false), VerifyResult::Verified) {
                        if verbose { println!("  (Simplified to just constant=0 conditions first)"); }
                        simple_conds
                    } else {
                        candidate_conditions.clone()
                    };
                    
                    loop {
                        // Sort by complexity: larger absolute constant, then FEWER variables
                        final_conds.sort_by_key(|c| (-(c.expr.constant.abs() as i64), c.expr.coeffs.len() as i64));
                        
                        let mut dropped_any = false;
                        let mut i = 0;
                        while i < final_conds.len() {
                            let mut test_conds = final_conds.clone();
                            let dropped = test_conds.remove(i);
                            let test_set = PolyhedralClosedSet {
                                state: state_idx,
                                conditions: test_conds.clone(),
                                num_registers: num_regs,
                            };
                            if matches!(verify_polyhedral_closed_set(&macros, &test_set, false), VerifyResult::Verified) {
                                if verbose { println!("  Dropped unnecessary condition: {}", dropped); }
                                final_conds = test_conds;
                                dropped_any = true;
                            } else {
                                if verbose { println!("  Kept essential condition: {}", dropped); }
                                i += 1;
                            }
                        }
                        if !dropped_any { break; }
                    }

                    if verbose {
                        println!("✅ Found Polyhedral Closed Set at State {}!", (b'A' + state_idx as u8) as char);
                        println!("   Final Conditions: {:?}", final_conds.iter().map(|c| c.to_string()).collect::<Vec<_>>());
                    }
                    
                    return Some(PolyhedralClosedSet {
                        state: state_idx,
                        conditions: final_conds,
                        num_registers: num_regs,
                    });
                }
                VerifyResult::ConditionFailed(failed) => {
                    if verbose {
                        println!("  Dropping {} conditions that failed verification:", failed.len());
                        for c in &failed { println!("    {}", c); }
                    }
                    candidate_conditions.retain(|c| !failed.contains(c));
                    if candidate_conditions.is_empty() {
                        if verbose { println!("  All conditions failed."); }
                        break;
                    }
                }
                VerifyResult::Failed(msg) => {
                    if verbose { println!("  Verification failed: {}", msg); }
                    break;
                }
            }
        }
    }

    None
}
