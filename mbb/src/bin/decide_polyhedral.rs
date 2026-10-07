use mbb::parse::parse_program;
use mbb::program::{Instruction, Target};
use mbb::macro_program::abstract_program;
use mbb::deciders::polyhedral::{verify_polyhedral_closed_set, PolyhedralClosedSet, VerifyResult};
use mbb::deciders::polyhedral_guesser::find_closed_set;
use mbb::deciders::symbolic::{AffineExpr, Condition, ConditionType};
use std::env;
use std::fs::File;
use std::io::{self, BufRead, Write};
use std::time::Instant;

fn parse_affine_side(s: &str) -> AffineExpr {
    let mut expr = AffineExpr::new(0);
    if s.is_empty() { return expr; }
    
    let s_replaced = s.replace("-", "+-");
    let parts = s_replaced.split('+');
    for p in parts {
        let p = p.trim();
        if p.is_empty() { continue; }
        
        let is_negative = p.starts_with('-');
        let term = if is_negative { &p[1..] } else { p };
        let term = term.trim();
        let sign = if is_negative { -1 } else { 1 };

        if let Ok(c) = term.parse::<i64>() {
            expr.add_const(c * sign);
        } else if term.len() == 1 {
            let c = term.chars().next().unwrap();
            if c >= 'a' && c <= 'z' {
                expr.coeffs.insert((c as u8 - b'a') as usize, sign);
            } else {
                panic!("Invalid variable '{}' in condition '{}'", c, s);
            }
        } else {
            panic!("Invalid term '{}' in condition '{}'", p, s);
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

    if args.len() < 2 {
        eprintln!("Usage: {} [-v] decide <in.txt> <out.txt>", args[0]);
        eprintln!("       {} [-v] <program> [state: A, B, ...] [condition1] [condition2] ...", args[0]);
        std::process::exit(1);
    }

    if args[1] == "decide" {
        if args.len() < 4 {
            eprintln!("Usage: {} decide <in.txt> <out.txt>", args[0]);
            std::process::exit(1);
        }
        let in_file = &args[2];
        let out_file = &args[3];

        let file = File::open(in_file).expect("Could not open input file");
        let reader = io::BufReader::new(file);
        
        let mut out = File::create(out_file).expect("Could not create output file");

        let mut lines = Vec::new();
        for line in reader.lines() {
            let line = line.expect("Could not read line");
            let prog_str = line.trim().to_string();
            if prog_str.is_empty() || prog_str.starts_with('#') {
                continue;
            }
            lines.push(prog_str);
        }

        let total_count = lines.len();
        let mut success_count = 0;
        let start_time = Instant::now();

        for (i, prog_str) in lines.iter().enumerate() {
            if !verbose {
                eprint!("\rProgress: {}/{} ({:.1}%)", i, total_count, (i as f64 / total_count as f64) * 100.0);
                let _ = io::stderr().flush();
            }

            let prog = parse_program(prog_str).expect("Failed to parse program");
            if let Some(set) = find_closed_set(&prog, verbose) {
                success_count += 1;
                let state_char = (b'A' + set.state as u8) as char;
                let conds: Vec<String> = set.conditions.iter().map(|c| c.to_string()).collect();
                mbb::io::write_result(&mut out, prog_str, mbb::io::ProgramResult::Polyhedral {
                    state: state_char,
                    conditions: &conds.join(", "),
                }).unwrap();
            } else {
                mbb::io::write_result(&mut out, prog_str, mbb::io::ProgramResult::Unknown).unwrap();
            }
        }
        if !verbose {
            eprintln!("\rProgress: {}/{} (100.0%)", total_count, total_count);
        }

        let duration = start_time.elapsed();
        println!("\nSummary:");
        println!("  Proven Infinite: {}", success_count);
        println!("  Undecided:       {}", total_count - success_count);
        println!("  Runtime:         {:.2?}", duration);
        return;
    }

    let prog_str = &args[1];
    let prog = parse_program(prog_str).expect("Failed to parse program");
    let macros = abstract_program(&prog);

    if verbose {
        println!("Macro Abstracted Program:");
        for (i, m) in macros.iter().enumerate() {
            println!("  {}", m.to_string_with_state(i, prog.num_regs()));
        }
        println!();
    }

    if args.len() >= 3 {
        // Manual mode
        let state_str = &args[2];
        let state_idx = (state_str.chars().next().unwrap() as u8 - b'A') as usize;
        let num_regs = prog.num_regs();

        let mut conditions = Vec::new();
        for i in 3..args.len() {
            conditions.push(parse_condition(&args[i]));
        }



        let closed_set = PolyhedralClosedSet {
            state: state_idx,
            conditions,
            num_registers: num_regs,
        };

        println!("Verifying Polyhedral Closed Set at State {} with conditions {:?}", state_str, args[3..].to_vec());
        match verify_polyhedral_closed_set(&macros, &closed_set, verbose) {
            VerifyResult::Verified => {
                println!("✅ Successfully verified that the set is closed and does not halt!");
                
                // Extra: concretely simulate until entry
                let mut state = mbb::simulate::State::new();
                
                loop {
                    if state.pc == state_idx {
                        // verify condition
                        let mut all_match = true;
                        for cond in &closed_set.conditions {
                            let mut val = cond.expr.constant;
                            for (&var_idx, &coeff) in &cond.expr.coeffs {
                                val += coeff * state.get_reg(var_idx) as i64;
                            }
                            match cond.cond_type {
                                ConditionType::GreaterEqualZero => {
                                    if val < 0 { all_match = false; break; }
                                }
                                ConditionType::EqualZero => {
                                    if val != 0 { all_match = false; break; }
                                }
                            }
                        }
                        if all_match {
                            println!("🎉 Program enters the closed set at step {} with regs: {:?}", state.steps, state.registers);
                            break;
                        }
                    }
                    if state.pc >= prog.instructions.len() {
                        println!("Failed to enter closed set");
                        break;
                    }
                    if state.steps > 100_000 {
                        println!("Failed to enter closed set after 100,000 steps");
                        break;
                    }

                    let inst = &prog.instructions[state.pc];
                    state.steps += 1;
                    match inst {
                        Instruction::Undef => {
                            break;
                        }
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
            }
            VerifyResult::ConditionFailed(failed) => {
                println!("❌ Verification failed! The following conditions could not be proven:");
                for c in failed {
                    println!("  {}", c);
                }
            }
            VerifyResult::Failed(msg) => {
                println!("❌ Verification failed! {}", msg);
            }
        }
    } else {
        // Auto-guess mode
        println!("Running Polyhedral Guesser...");
        if let Some(set) = find_closed_set(&prog, verbose) {
            println!("🎉 Automatically found a valid Polyhedral Closed Set!");
            println!("   State: {}", (b'A' + set.state as u8) as char);
            let cond_strs: Vec<String> = set.conditions.iter().map(|c| c.to_string()).collect();
            println!("   Conditions: [{}]", cond_strs.join(", "));

            if verbose {
                println!("\nFinal Verification Trace:");

                verify_polyhedral_closed_set(&macros, &set, true);
            }
        } else {
            println!("❌ Could not find a Polyhedral Closed Set.");
        }
    }
}
