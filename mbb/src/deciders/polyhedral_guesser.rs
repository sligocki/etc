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
            Instruction::Undef => break,
            Instruction::NoOp { .. } => unreachable!("NoOp not supported in decider"),
            Instruction::Inc { reg, next } => {
                let val = state.get_reg(*reg);
                state.set_reg(*reg, val.wrapping_add(1));
                match next {
                    Target::Halt => break,
                    Target::Inst(i) => state.pc = *i,
                    Target::Undef => break,
                }
            }
            Instruction::Dec { reg, next_not_zero, next_zero } => {
                let val = state.get_reg(*reg);
                if val == 0 {
                    match next_zero {
                        Target::Halt => break,
                        Target::Inst(i) => state.pc = *i,
                        Target::Undef => break,
                    }
                } else {
                    state.set_reg(*reg, val - 1);
                    match next_not_zero {
                        Target::Halt => break,
                        Target::Inst(i) => state.pc = *i,
                        Target::Undef => break,
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

    let num_combinations = 3_usize.pow(num_regs as u32);

    for combo in 1..num_combinations {
        let mut coeffs = vec![0i64; num_regs];
        let mut temp = combo;
        let mut has_non_zero = false;
        for i in 0..num_regs {
            let digit = temp % 3;
            coeffs[i] = match digit {
                0 => 0,
                1 => 1,
                2 => -1,
                _ => unreachable!(),
            };
            if coeffs[i] != 0 { has_non_zero = true; }
            temp /= 3;
        }

        if !has_non_zero { continue; }

        let mut min_val = i64::MAX;
        let mut max_val = i64::MIN;

        for regs in history {
            let mut val = 0i64;
            for i in 0..num_regs {
                val += coeffs[i] * (regs[i] as i64);
            }
            min_val = min_val.min(val);
            max_val = max_val.max(val);
        }

        let mut expr = AffineExpr::new(0);
        for i in 0..num_regs {
            if coeffs[i] != 0 {
                expr.coeffs.insert(i, coeffs[i]);
            }
        }
        
        let mut geq_expr = expr.clone();
        geq_expr.add_const(-min_val);
        conditions.push(Condition::geq_zero(geq_expr));

        if min_val > 0 {
            conditions.push(Condition::geq_zero(expr.clone()));
        }
    }

    let mut unique_conds = Vec::new();
    for c in conditions {
        if !unique_conds.contains(&c) {
            unique_conds.push(c);
        }
    }
    
    // Always include explicit r_i >= 0 just in case
    for i in 0..num_regs {
        let expr = AffineExpr::var(i);
        let c = Condition::geq_zero(expr);
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
