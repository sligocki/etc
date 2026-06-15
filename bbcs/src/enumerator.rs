use crate::ast::Instr;
use crate::simulator::{Simulator, RunResult};
use rayon::prelude::*;

#[derive(Clone, PartialEq, Eq)]
pub enum FlatInstr {
    Inc(usize),
    Dec(usize),
    WhileStart(usize),
    WhileEnd,
}

#[derive(Clone)]
struct PrefixState {
    remaining_length: usize,
    max_var: Option<usize>,
    open_loops: Vec<(usize, bool)>,
    flat: Vec<FlatInstr>,
}

pub struct SearchResult {
    pub total: usize,
    pub halted: usize,
    pub timeouts: usize,
    pub max_score: usize,
    pub champion: Option<Vec<Instr>>,
}

impl SearchResult {
    fn new() -> Self {
        Self { total: 0, halted: 0, timeouts: 0, max_score: 0, champion: None }
    }
    
    fn merge(mut self, other: Self) -> Self {
        self.total += other.total;
        self.halted += other.halted;
        self.timeouts += other.timeouts;
        if other.max_score > self.max_score || self.champion.is_none() {
            self.max_score = other.max_score;
            self.champion = other.champion;
        }
        self
    }
}

pub fn search_programs(length: usize, max_steps: usize) -> SearchResult {
    if length == 0 {
        return SearchResult::new();
    }

    let prefix_len = std::cmp::min(length, 4); 
    
    let mut prefixes = Vec::new();
    let mut initial_flat = Vec::new();
    let mut initial_open_loops = Vec::new();
    
    // Rule 1: First instruction must be Inc(0)
    initial_flat.push(FlatInstr::Inc(0));
    generate_prefixes(
        length - 1,
        Some(0),
        &mut initial_open_loops,
        prefix_len - 1,
        &mut initial_flat,
        &mut prefixes,
    );

    prefixes.into_par_iter().map(|prefix| {
        let mut local_res = SearchResult::new();
        let mut sim = Simulator::new();
        let mut current_flat = prefix.flat.clone();
        let mut open_loops = prefix.open_loops.clone();
        
        generate_and_sim(
            prefix.remaining_length,
            prefix.max_var,
            &mut open_loops,
            &mut current_flat,
            &mut local_res,
            &mut sim,
            max_steps,
        );
        local_res
    }).reduce(|| SearchResult::new(), |a, b| a.merge(b))
}

fn is_valid_primitive(last_instr: Option<&FlatInstr>, current_var: usize, is_inc: bool) -> bool {
    match last_instr {
        Some(FlatInstr::Inc(p)) => {
            if current_var < *p { return false; }
            if current_var == *p && !is_inc { return false; } // Ban Inc(p); Dec(p)
            true
        }
        Some(FlatInstr::Dec(p)) => {
            if current_var < *p { return false; }
            true
        }
        _ => true
    }
}

fn generate_prefixes(
    remaining_length: usize,
    max_var: Option<usize>,
    open_loops: &mut Vec<(usize, bool)>,
    steps_left: usize,
    current_flat: &mut Vec<FlatInstr>,
    prefixes: &mut Vec<PrefixState>,
) {
    if steps_left == 0 || remaining_length == 0 {
        if remaining_length == 0 {
            for &(_, has_dec) in open_loops.iter() {
                if !has_dec {
                    return; // Reject invalid unclosed loops
                }
            }
        }
        prefixes.push(PrefixState {
            remaining_length,
            max_var,
            open_loops: open_loops.clone(),
            flat: current_flat.clone(),
        });
        return;
    }

    if !open_loops.is_empty() {
        let last_loop = open_loops.last().unwrap();
        if last_loop.1 { // Only close if it has decremented its loop variable
            current_flat.push(FlatInstr::WhileEnd);
            let popped = open_loops.pop().unwrap();
            generate_prefixes(remaining_length, max_var, open_loops, steps_left, current_flat, prefixes);
            open_loops.push(popped);
            current_flat.pop();
        }
    }

    let next_allowed = match max_var {
        Some(v) => v + 1,
        None => 0,
    };

    let last_instr = current_flat.last().cloned();

    for v in 0..=next_allowed {
        let next_max_var = Some(max_var.unwrap_or(0).max(v));

        if is_valid_primitive(last_instr.as_ref(), v, true) {
            current_flat.push(FlatInstr::Inc(v));
            generate_prefixes(remaining_length - 1, next_max_var, open_loops, steps_left - 1, current_flat, prefixes);
            current_flat.pop();
        }

        if is_valid_primitive(last_instr.as_ref(), v, false) {
            current_flat.push(FlatInstr::Dec(v));
            
            let mut changed_indices = Vec::new();
            for (i, loop_state) in open_loops.iter_mut().enumerate() {
                if loop_state.0 == v && !loop_state.1 {
                    loop_state.1 = true;
                    changed_indices.push(i);
                }
            }
            
            generate_prefixes(remaining_length - 1, next_max_var, open_loops, steps_left - 1, current_flat, prefixes);
            
            for i in changed_indices {
                open_loops[i].1 = false;
            }
            current_flat.pop();
        }

        current_flat.push(FlatInstr::WhileStart(v));
        open_loops.push((v, false));
        generate_prefixes(remaining_length - 1, next_max_var, open_loops, steps_left - 1, current_flat, prefixes);
        open_loops.pop();
        current_flat.pop();
    }
}

fn generate_and_sim(
    remaining_length: usize,
    max_var: Option<usize>,
    open_loops: &mut Vec<(usize, bool)>,
    current_flat: &mut Vec<FlatInstr>,
    local_res: &mut SearchResult,
    sim: &mut Simulator,
    max_steps: usize,
) {
    if remaining_length == 0 {
        for &(_, has_dec) in open_loops.iter() {
            if !has_dec {
                return; // Reject invalid unclosed loops
            }
        }

        for _ in 0..open_loops.len() {
            current_flat.push(FlatInstr::WhileEnd);
        }
        
        let ast = parse_flat(current_flat);
        local_res.total += 1;
        match sim.run(&ast, max_steps) {
            RunResult::Halted { score } => {
                local_res.halted += 1;
                if score > local_res.max_score || local_res.champion.is_none() {
                    local_res.max_score = score;
                    local_res.champion = Some(ast);
                }
            }
            RunResult::Timeout => {
                local_res.timeouts += 1;
            }
        }

        for _ in 0..open_loops.len() {
            current_flat.pop();
        }
        return;
    }

    if !open_loops.is_empty() {
        let last_loop = open_loops.last().unwrap();
        if last_loop.1 { // Only close if it has decremented its loop variable
            current_flat.push(FlatInstr::WhileEnd);
            let popped = open_loops.pop().unwrap();
            generate_and_sim(remaining_length, max_var, open_loops, current_flat, local_res, sim, max_steps);
            open_loops.push(popped);
            current_flat.pop();
        }
    }

    let next_allowed = match max_var {
        Some(v) => v + 1,
        None => 0,
    };

    let last_instr = current_flat.last().cloned();

    for v in 0..=next_allowed {
        let next_max_var = Some(max_var.unwrap_or(0).max(v));

        if is_valid_primitive(last_instr.as_ref(), v, true) {
            current_flat.push(FlatInstr::Inc(v));
            generate_and_sim(remaining_length - 1, next_max_var, open_loops, current_flat, local_res, sim, max_steps);
            current_flat.pop();
        }

        if is_valid_primitive(last_instr.as_ref(), v, false) {
            current_flat.push(FlatInstr::Dec(v));
            
            let mut changed_indices = Vec::new();
            for (i, loop_state) in open_loops.iter_mut().enumerate() {
                if loop_state.0 == v && !loop_state.1 {
                    loop_state.1 = true;
                    changed_indices.push(i);
                }
            }
            
            generate_and_sim(remaining_length - 1, next_max_var, open_loops, current_flat, local_res, sim, max_steps);
            
            for i in changed_indices {
                open_loops[i].1 = false;
            }
            current_flat.pop();
        }

        current_flat.push(FlatInstr::WhileStart(v));
        open_loops.push((v, false));
        generate_and_sim(remaining_length - 1, next_max_var, open_loops, current_flat, local_res, sim, max_steps);
        open_loops.pop();
        current_flat.pop();
    }
}

fn parse_flat(flat: &[FlatInstr]) -> Vec<Instr> {
    let mut ast_stack: Vec<Vec<Instr>> = vec![Vec::new()];
    let mut var_stack: Vec<usize> = Vec::new();

    for instr in flat {
        match instr {
            FlatInstr::Inc(v) => ast_stack.last_mut().unwrap().push(Instr::Inc(*v)),
            FlatInstr::Dec(v) => ast_stack.last_mut().unwrap().push(Instr::Dec(*v)),
            FlatInstr::WhileStart(v) => {
                ast_stack.push(Vec::new());
                var_stack.push(*v);
            }
            FlatInstr::WhileEnd => {
                let body = ast_stack.pop().unwrap();
                let v = var_stack.pop().unwrap();
                ast_stack.last_mut().unwrap().push(Instr::While(v, body));
            }
        }
    }
    ast_stack.pop().unwrap()
}
