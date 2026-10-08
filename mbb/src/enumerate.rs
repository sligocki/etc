use crate::program::{Instruction, Program, Target};
use crate::simulate::Branch;
use crate::deciders::DeciderResult;
use rayon::prelude::*;
use std::io::Write;
use std::sync::atomic::{AtomicU64, Ordering};

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

pub enum WorkerMsg {
    Batch {
        output: Vec<u8>,
        explored: u64,
        halted: u64,
        unknown: u64,
        infinite: u64,
    },
    Done {
        infinite_counts: std::collections::HashMap<&'static str, u64>,
        max_steps: u64,
        max_program: String,
        stats: crate::deciders::DeciderStats,
    }
}

fn process_state<F, G>(
    state: &EnumState,
    num_states: usize,
    max_regs: usize,
    allow_no_ops: bool,
    exact_start: bool,
    step_limit: u64,
    config: &crate::deciders::DeciderConfig,
    stats: &mut crate::deciders::DeciderStats,
    mut push_child: F,
    mut handle_leaf: G,
)
where
    F: FnMut(EnumState),
    G: FnMut(DeciderResult, u64),
{
    let decider_res = crate::deciders::decide_with_stats(&state.prog, step_limit, true, exact_start, config, stats);
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
                            return; // Prune branch: impossible to satisfy all registers
                        }

                        let strict_mode = total_missing == undef_count;

                        let mut max_r = state.max_reg_referenced;
                        if !strict_mode && total_missing + 2 <= undef_count && max_r + 1 < max_regs as i32 {
                            max_r += 1;
                        }

                        if allow_no_ops && !strict_mode {
                            let mut child = state.clone();
                            child.prog.instructions[*pc] = Instruction::NoOp { next: Target::Undef };
                            push_child(child);
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
                            push_child(child);
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
                                push_child(child);
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
                            
                            push_child(child);
                        }
                    }
                }
            } else {
                handle_leaf(decider_res, steps);
            }
        }
        DeciderResult::Infinite(_) | DeciderResult::Unknown => {
            handle_leaf(decider_res, 0);
        }
        DeciderResult::Error(msg) => {
            panic!("Simulation error: {}", msg);
        }
    }
}

pub fn enumerate(num_states: usize, step_limit: u64, max_regs: Option<usize>, allow_no_ops: bool, exact_start: bool, limit: Option<usize>, config: &crate::deciders::DeciderConfig, out_file: &str) {
    use std::fs::File;
    use std::io::BufWriter;

    let file = File::create(out_file).unwrap();
    let mut writer = BufWriter::new(file);

    let max_regs = max_regs.unwrap_or(num_states / 2 + 1);

    // 1. Seed phase using VecDeque for BFS
    let mut queue = std::collections::VecDeque::new();
    queue.push_back(EnumState::new(num_states));
    
    let num_threads = rayon::current_num_threads();
    let target_initial_states = num_threads * 200;
    
    let mut total_explored = 0u64;
    let mut num_halted = 0u64;
    let mut num_unknown = 0u64;
    let mut num_infinite = 0u64;
    let mut infinite_counts: std::collections::HashMap<&'static str, u64> = std::collections::HashMap::new();
    let mut max_steps = 0u64;
    let mut max_program = String::new();
    let mut total_stats = crate::deciders::DeciderStats::default();

    // Generate initial states via BFS
    while let Some(state) = queue.pop_front() {
        if queue.len() >= target_initial_states {
            queue.push_front(state);
            break;
        }

        if let Some(l) = limit {
            if total_explored >= l as u64 {
                queue.push_front(state);
                break;
            }
        }

        total_explored += 1;
        
        process_state(
            &state, num_states, max_regs, allow_no_ops, exact_start, step_limit, config, &mut total_stats,
            |child| queue.push_back(child),
            |res, steps| {
                match &res {
                    DeciderResult::Halt { .. } => {
                        num_halted += 1;
                        if steps > max_steps {
                            max_steps = steps;
                            max_program = state.prog.to_string_format(state.max_reg_referenced);
                        }
                    }
                    DeciderResult::Infinite(reason) => {
                        num_infinite += 1;
                        *infinite_counts.entry(reason.decider_name()).or_insert(0) += 1;
                    }
                    DeciderResult::Unknown => {
                        num_unknown += 1;
                    }
                    _ => {}
                }
                crate::io::write_result(
                    &mut writer,
                    &state.prog.to_string_format(state.max_reg_referenced),
                    &res
                ).unwrap();
            }
        );
    }

    let initial_states: Vec<_> = queue.into();
    
    let global_explored = std::sync::Arc::new(AtomicU64::new(total_explored));
    let (tx, rx) = crossbeam_channel::unbounded();

    let should_run = if let Some(l) = limit { total_explored < l as u64 } else { true };

    if should_run && !initial_states.is_empty() {
        let config = config.clone();
        
        // Spawn a thread to receive results and print progress
        let rx_thread = std::thread::spawn(move || {
            let mut last_print_time = std::time::Instant::now();
            let mut local_total_explored = total_explored;

            for msg in rx {
                match msg {
                    WorkerMsg::Batch { output, explored, halted, unknown, infinite } => {
                        writer.write_all(&output).unwrap();
                        local_total_explored += explored;
                        num_halted += halted;
                        num_unknown += unknown;
                        num_infinite += infinite;
                        
                        if last_print_time.elapsed().as_secs() >= 5 {
                            let total_leaves = num_halted + num_unknown + num_infinite;
                            let halt_pct = if total_leaves > 0 { (num_halted as f64 / total_leaves as f64) * 100.0 } else { 0.0 };
                            let inf_pct = if total_leaves > 0 { (num_infinite as f64 / total_leaves as f64) * 100.0 } else { 0.0 };
                            let unknown_pct = if total_leaves > 0 { (num_unknown as f64 / total_leaves as f64) * 100.0 } else { 0.0 };
                            
                            println!("Progress: {} nodes explored | {} programs found", local_total_explored, total_leaves);
                            println!("  Halted: {} ({:.2}%) | Infinite: {} ({:.2}%) | Unknown: {} ({:.2}%) | Max steps: {}", 
                                     num_halted, halt_pct, num_infinite, inf_pct, num_unknown, unknown_pct, max_steps);
                            last_print_time = std::time::Instant::now();
                        }
                    }
                    WorkerMsg::Done { infinite_counts: ic, max_steps: ms, max_program: mp, stats } => {
                        for (k, v) in ic {
                            *infinite_counts.entry(k).or_insert(0) += v;
                        }
                        if ms > max_steps {
                            max_steps = ms;
                            max_program = mp;
                        }
                        for (name, duration) in stats.runtimes {
                            total_stats.add_time(name, duration);
                        }
                    }
                }
            }
            
            // Return final stats
            (local_total_explored, num_halted, num_unknown, num_infinite, infinite_counts, max_steps, max_program, total_stats)
        });

        // Use rayon to process initial states in parallel
        initial_states.into_par_iter().for_each_with(tx, |tx, initial_state| {
            if let Some(l) = limit {
                if global_explored.load(Ordering::Relaxed) >= l as u64 {
                    return;
                }
            }

            let mut stack = vec![initial_state];
            
            let mut local_explored = 0u64;
            let mut local_halted = 0u64;
            let mut local_unknown = 0u64;
            let mut local_infinite = 0u64;
            let mut local_infinite_counts: std::collections::HashMap<&'static str, u64> = std::collections::HashMap::new();
            let mut local_max_steps = 0u64;
            let mut local_max_program = String::new();
            let mut local_stats = crate::deciders::DeciderStats::default();
            let mut buf = Vec::new();
            
            while let Some(state) = stack.pop() {
                local_explored += 1;

                if local_explored % 1000 == 0 {
                    if let Some(l) = limit {
                        let current_global = global_explored.load(Ordering::Relaxed);
                        if current_global + local_explored >= l as u64 {
                            stack.clear();
                            break;
                        }
                    }
                }

                process_state(
                    &state, num_states, max_regs, allow_no_ops, exact_start, step_limit, &config, &mut local_stats,
                    |child| stack.push(child),
                    |res, steps| {
                        match &res {
                            DeciderResult::Halt { .. } => {
                                local_halted += 1;
                                if steps > local_max_steps {
                                    local_max_steps = steps;
                                    local_max_program = state.prog.to_string_format(state.max_reg_referenced);
                                }
                            }
                            DeciderResult::Infinite(reason) => {
                                local_infinite += 1;
                                *local_infinite_counts.entry(reason.decider_name()).or_insert(0) += 1;
                            }
                            DeciderResult::Unknown => {
                                local_unknown += 1;
                            }
                            _ => {}
                        }
                        crate::io::write_result(
                            &mut buf,
                            &state.prog.to_string_format(state.max_reg_referenced),
                            &res
                        ).unwrap();
                    }
                );

                if buf.len() > 64 * 1024 {
                    global_explored.fetch_add(local_explored, Ordering::Relaxed);
                    tx.send(WorkerMsg::Batch {
                        output: std::mem::take(&mut buf),
                        explored: local_explored,
                        halted: local_halted,
                        unknown: local_unknown,
                        infinite: local_infinite,
                    }).unwrap();
                    
                    local_explored = 0;
                    local_halted = 0;
                    local_unknown = 0;
                    local_infinite = 0;
                }
            }

            // Flush remaining
            if local_explored > 0 || !buf.is_empty() {
                global_explored.fetch_add(local_explored, Ordering::Relaxed);
                tx.send(WorkerMsg::Batch {
                    output: std::mem::take(&mut buf),
                    explored: local_explored,
                    halted: local_halted,
                    unknown: local_unknown,
                    infinite: local_infinite,
                }).unwrap();
            }

            tx.send(WorkerMsg::Done {
                infinite_counts: local_infinite_counts,
                max_steps: local_max_steps,
                max_program: local_max_program,
                stats: local_stats,
            }).unwrap();
        });

        // Wait for rx thread
        let results = rx_thread.join().unwrap();
        total_explored = results.0;
        num_halted = results.1;
        num_unknown = results.2;
        num_infinite = results.3;
        infinite_counts = results.4;
        max_steps = results.5;
        max_program = results.6;
        total_stats = results.7;
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
