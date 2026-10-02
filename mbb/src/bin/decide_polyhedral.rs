use mbb::parse::parse_program;
use mbb::program::{Instruction, Target};
use mbb::macro_program::abstract_program;
use mbb::deciders::polyhedral::{verify_polyhedral_closed_set, PolyhedralClosedSet, VerifyResult};
use mbb::deciders::symbolic::{AffineExpr, Condition, ConditionType};
use std::env;

fn parse_affine_side(s: &str) -> AffineExpr {
    let mut expr = AffineExpr::new(0);
    if s.is_empty() { return expr; }
    let parts = s.split('+');
    for p in parts {
        let p = p.trim();
        if let Ok(c) = p.parse::<i64>() {
            expr.add_const(c);
        } else if p.len() == 1 {
            let c = p.chars().next().unwrap();
            if c >= 'a' && c <= 'z' {
                expr.coeffs.insert((c as u8 - b'a') as usize, 1);
            }
        }
    }
    expr
}

fn parse_condition(s: &str) -> Condition {
    if let Some((left, right)) = s.split_once(">=") {
        let mut lexpr = parse_affine_side(left);
        let rexpr = parse_affine_side(right);
        lexpr.sub(&rexpr);
        Condition::geq_zero(lexpr)
    } else if let Some((left, right)) = s.split_once("<=") {
        let mut rexpr = parse_affine_side(right);
        let lexpr = parse_affine_side(left);
        rexpr.sub(&lexpr);
        Condition::geq_zero(rexpr)
    } else if let Some((left, right)) = s.split_once("==") {
        let mut lexpr = parse_affine_side(left);
        let rexpr = parse_affine_side(right);
        lexpr.sub(&rexpr);
        Condition::eq_zero(lexpr)
    } else {
        panic!("Unknown condition format: {}", s);
    }
}

fn main() {
    let mut args: Vec<String> = env::args().collect();
    let verbose = args.iter().any(|a| a == "-v" || a == "--verbose");
    args.retain(|a| a != "-v" && a != "--verbose");

    if args.len() < 4 {
        eprintln!("Usage: {} [-v] <program> <state: A, B, ...> <condition1> [condition2] ...", args[0]);
        std::process::exit(1);
    }

    let prog_str = &args[1];
    let state_str = &args[2];

    let prog = parse_program(prog_str).expect("Failed to parse program");
    let state_idx = (state_str.chars().next().unwrap() as u8 - b'A') as usize;
    let num_regs = prog.num_regs();

    let mut conditions = Vec::new();
    for i in 3..args.len() {
        conditions.push(parse_condition(&args[i]));
    }

    let macros = abstract_program(&prog);

    let closed_set = PolyhedralClosedSet {
        state: state_idx,
        conditions,
        num_registers: num_regs,
    };

    println!("Verifying Polyhedral Closed Set at State {} with conditions {:?}", state_str, args[3..].to_vec());
    match verify_polyhedral_closed_set(&macros, &closed_set, verbose) {
        VerifyResult::Verified => {
            println!("✅ Successfully verified that the set is closed and does not halt!");
            
            let mut state = mbb::simulate::State::new();
            let mut found = false;
            
            while state.steps < 100000 {
                if state.pc == state_idx {
                    let mut is_satisfied = true;
                    for cond in &closed_set.conditions {
                        let mut val = cond.expr.constant;
                        for (&v_idx, &coeff) in &cond.expr.coeffs {
                            val += coeff * (state.get_reg(v_idx) as i64);
                        }
                        match cond.cond_type {
                            ConditionType::GreaterEqualZero => {
                                if val < 0 { is_satisfied = false; break; }
                            }
                            ConditionType::EqualZero => {
                                if val != 0 { is_satisfied = false; break; }
                            }
                        }
                    }
                    if is_satisfied {
                        println!("🎉 Program enters the closed set at step {} with regs: {:?}", state.steps, state.registers);
                        found = true;
                        break;
                    }
                }

                if state.pc >= prog.instructions.len() { break; }
                
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

            if !found {
                println!("⚠️ Verified closure, but failed to find entry point within 100,000 steps.");
            }
        }
        VerifyResult::Failed(msg) => {
            println!("❌ Verification failed: {}", msg);
        }
    }
}
