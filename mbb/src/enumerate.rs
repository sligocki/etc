use crate::program::{Instruction, Program, Target};
use crate::simulate::Branch;
use crate::deciders::DeciderResult;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EnumState {
    pub prog: Program,
    pub max_state_referenced: i32,
    pub max_reg_referenced: i32,
}

impl EnumState {
    pub fn new(num_states: usize) -> Self {
        EnumState {
            prog: Program {
                instructions: vec![Instruction::Undef; num_states],
            },
            max_state_referenced: 0,
            max_reg_referenced: -1,
        }
    }
}

pub fn enumerate(num_states: usize, step_limit: u64, max_regs: Option<usize>, allow_no_ops: bool, exact_start: bool, limit: Option<usize>, config: &crate::deciders::DeciderConfig, out_file: &str) {
    use std::fs::File;
    use std::io::BufWriter;

    let file = File::create(out_file).unwrap();
    let mut writer = BufWriter::new(file);

    let max_regs = max_regs.unwrap_or(num_states / 2 + 1);

    let mut stack = vec![EnumState::new(num_states)];

    let mut total_explored = 0u64;
    let mut num_halted = 0u64;
    let mut num_unknown = 0u64;
    let mut num_infinite = 0u64;
    let mut infinite_counts: std::collections::HashMap<&'static str, u64> = std::collections::HashMap::new();
    let mut max_steps = 0u64;
    let mut max_program = String::new();
    let mut last_print_time = std::time::Instant::now();

    let mut total_stats = crate::deciders::DeciderStats::default();

    while let Some(state) = stack.pop() {
        total_explored += 1;
        if total_explored % 100_000 == 0 {
            if last_print_time.elapsed().as_secs() >= 5 {
                let total_leaves = num_halted + num_unknown + num_infinite;
                let halt_pct = if total_leaves > 0 { (num_halted as f64 / total_leaves as f64) * 100.0 } else { 0.0 };
                let inf_pct = if total_leaves > 0 { (num_infinite as f64 / total_leaves as f64) * 100.0 } else { 0.0 };
                let unknown_pct = if total_leaves > 0 { (num_unknown as f64 / total_leaves as f64) * 100.0 } else { 0.0 };
                
                println!("Progress: {} nodes explored | {} programs found", total_explored, total_leaves);
                println!("  Halted: {} ({:.2}%) | Infinite: {} ({:.2}%) | Unknown: {} ({:.2}%) | Max steps: {}", 
                         num_halted, halt_pct, num_infinite, inf_pct, num_unknown, unknown_pct, max_steps);
                last_print_time = std::time::Instant::now();
            }
        }

        if let Some(l) = limit {
            if total_explored >= l as u64 {
                break;
            }
        }

        let decider_res = crate::deciders::decide_with_stats(&state.prog, step_limit, true, exact_start, config, &mut total_stats);
        
        match decider_res {
            DeciderResult::Halt { steps, registers: _, ref hit_undef } => {
                if let Some(undef) = hit_undef {
                    match undef {
                        crate::deciders::HitUndef::Inst(pc) => {
                            let (undef_count, has_inc, has_dec) = state.prog.get_missing_requirements(state.max_reg_referenced);
                            let mut total_missing = 0;
                            if state.max_reg_referenced >= 0 {
                                for i in 0..=(state.max_reg_referenced as usize) {
                                    if !has_inc[i] { total_missing += 1; }
                                    if !has_dec[i] { total_missing += 1; }
                                }
                            }

                            if total_missing > undef_count {
                                continue; // Prune branch: impossible to satisfy all registers
                            }

                            let strict_mode = total_missing == undef_count;

                            let mut max_r = state.max_reg_referenced;
                            if !strict_mode && total_missing + 2 <= undef_count && max_r + 1 < max_regs as i32 {
                                max_r += 1;
                            }

                            if allow_no_ops && !strict_mode {
                                let mut child = state.clone();
                                child.prog.instructions[*pc] = Instruction::NoOp { next: Target::Undef };
                                stack.push(child);
                            }
                            
                            for r in 0..=max_r {
                                let r_usize = r as usize;
                                if strict_mode && r_usize < has_inc.len() && has_inc[r_usize] {
                                    continue;
                                }

                                let mut child = state.clone();
                                child.prog.instructions[*pc] = Instruction::Inc {
                                    reg: r_usize,
                                    next: Target::Undef,
                                };
                                if r > child.max_reg_referenced {
                                    child.max_reg_referenced = r;
                                }
                                stack.push(child);
                            }

                            if *pc != 0 {
                                for r in 0..=max_r {
                                    let r_usize = r as usize;
                                    if strict_mode && r_usize < has_dec.len() && has_dec[r_usize] {
                                        continue;
                                    }

                                    let mut child = state.clone();
                                    child.prog.instructions[*pc] = Instruction::Dec {
                                        reg: r_usize,
                                        next_not_zero: Target::Undef,
                                        next_zero: Target::Undef,
                                    };
                                    if r > child.max_reg_referenced {
                                        child.max_reg_referenced = r;
                                    }
                                    stack.push(child);
                                }
                            }
                        }
                        crate::deciders::HitUndef::Target { pc, branch } => {
                            let (explicit_undef, undef_insts, halt_targets) = state.prog.get_target_counts();
                            let force_halt = halt_targets == 0 && explicit_undef == 1 && undef_insts == 0;

                            let mut max_s = state.max_state_referenced;
                            if max_s + 1 < num_states as i32 {
                                max_s += 1;
                            }

                            let mut targets = vec![Target::Halt];
                            
                            if !force_halt {
                                for s in 0..=max_s {
                                    targets.push(Target::Inst(s as usize));
                                }
                            }

                            for target in targets {
                                let mut child = state.clone();
                                
                                if let Target::Inst(s) = target {
                                    if s as i32 > child.max_state_referenced {
                                        child.max_state_referenced = s as i32;
                                    }
                                }

                                match &mut child.prog.instructions[*pc] {
                                    Instruction::Inc { next, .. } => {
                                        if *branch == Branch::Next {
                                            *next = target;
                                        }
                                    }
                                    Instruction::Dec { next_not_zero, next_zero, .. } => {
                                        if *branch == Branch::NextNotZero {
                                            *next_not_zero = target;
                                        } else if *branch == Branch::NextZero {
                                            *next_zero = target;
                                        }
                                    }
                                    Instruction::NoOp { next } => {
                                        if *branch == Branch::Next {
                                            *next = target;
                                        }
                                    }
                                    _ => {}
                                }
                                
                                stack.push(child);
                            }
                        }
                    }
                } else {
                    num_halted += 1;
                    if steps > max_steps {
                        max_steps = steps;
                        max_program = state.prog.to_string_format(state.max_reg_referenced);
                    }
                    crate::io::write_result(
                        &mut writer,
                        &state.prog.to_string_format(state.max_reg_referenced),
                        &decider_res
                    ).unwrap();
                }
            }
            DeciderResult::Infinite(ref reason) => {
                num_infinite += 1;
                *infinite_counts.entry(reason.decider_name()).or_insert(0) += 1;
                crate::io::write_result(
                    &mut writer,
                    &state.prog.to_string_format(state.max_reg_referenced),
                    &decider_res
                ).unwrap();
            }
            DeciderResult::Unknown => {
                num_unknown += 1;
                crate::io::write_result(
                    &mut writer,
                    &state.prog.to_string_format(state.max_reg_referenced),
                    &decider_res
                ).unwrap();
            }
            DeciderResult::Error(msg) => {
                panic!("Simulation error: {}", msg);
            }
        }
    }
    
    let total_leaves = num_halted + num_unknown + num_infinite;
    let halt_pct = if total_leaves > 0 { (num_halted as f64 / total_leaves as f64) * 100.0 } else { 0.0 };
    let inf_pct = if total_leaves > 0 { (num_infinite as f64 / total_leaves as f64) * 100.0 } else { 0.0 };
    let unknown_pct = if total_leaves > 0 { (num_unknown as f64 / total_leaves as f64) * 100.0 } else { 0.0 };
    
    println!("Enumeration complete! Explored {} total nodes.", total_explored);
    println!("Total programs found: {}", total_leaves);
    println!("  Halted: {} ({:.2}%)", num_halted, halt_pct);
    println!("  Infinite: {} ({:.2}%)", num_infinite, inf_pct);
    if num_infinite > 0 {
        let mut sorted_counts: Vec<_> = infinite_counts.iter().collect();
        // Sort by name or count? Pre-defined order is better but sorting by count is robust
        sorted_counts.sort_by_key(|&(_, &count)| std::cmp::Reverse(count));
        
        for (name, count) in sorted_counts {
            let pct = (*count as f64 / num_infinite as f64) * 100.0;
            println!("    {}: {} ({:.2}%)", name, count, pct);
        }
    }
    println!("  Unknown: {} ({:.2}%)", num_unknown, unknown_pct);
    println!("Max Halting Program: {} ({} steps)", max_program, max_steps);
    println!("Decider Runtime Breakdown:");
    for (name, duration) in &total_stats.runtimes {
        println!("  {}: {:.2?}", name, duration);
    }
}
