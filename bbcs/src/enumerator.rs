use crate::ast::Instr;
use crate::simulator::{Simulator, RunResult};
use rayon::prelude::*;

#[derive(Clone)]
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
    open_loops: usize,
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
    let prefix_len = std::cmp::min(length, 4); 
    
    let mut prefixes = Vec::new();
    let mut initial_flat = Vec::new();
    generate_prefixes(
        length,
        None,
        0,
        prefix_len,
        &mut initial_flat,
        &mut prefixes,
    );

    prefixes.into_par_iter().map(|prefix| {
        let mut local_res = SearchResult::new();
        let mut sim = Simulator::new();
        let mut current_flat = prefix.flat.clone();
        
        generate_and_sim(
            prefix.remaining_length,
            prefix.max_var,
            prefix.open_loops,
            &mut current_flat,
            &mut local_res,
            &mut sim,
            max_steps,
        );
        local_res
    }).reduce(|| SearchResult::new(), |a, b| a.merge(b))
}

fn generate_prefixes(
    remaining_length: usize,
    max_var: Option<usize>,
    open_loops: usize,
    steps_left: usize,
    current_flat: &mut Vec<FlatInstr>,
    prefixes: &mut Vec<PrefixState>,
) {
    if steps_left == 0 || remaining_length == 0 {
        prefixes.push(PrefixState {
            remaining_length,
            max_var,
            open_loops,
            flat: current_flat.clone(),
        });
        return;
    }

    if open_loops > 0 {
        current_flat.push(FlatInstr::WhileEnd);
        generate_prefixes(remaining_length, max_var, open_loops - 1, steps_left, current_flat, prefixes);
        current_flat.pop();
    }

    let next_allowed = match max_var {
        Some(v) => v + 1,
        None => 0,
    };

    for v in 0..=next_allowed {
        let next_max_var = Some(max_var.unwrap_or(0).max(v));

        current_flat.push(FlatInstr::Inc(v));
        generate_prefixes(remaining_length - 1, next_max_var, open_loops, steps_left - 1, current_flat, prefixes);
        current_flat.pop();

        current_flat.push(FlatInstr::Dec(v));
        generate_prefixes(remaining_length - 1, next_max_var, open_loops, steps_left - 1, current_flat, prefixes);
        current_flat.pop();

        current_flat.push(FlatInstr::WhileStart(v));
        generate_prefixes(remaining_length - 1, next_max_var, open_loops + 1, steps_left - 1, current_flat, prefixes);
        current_flat.pop();
    }
}

fn generate_and_sim(
    remaining_length: usize,
    max_var: Option<usize>,
    open_loops: usize,
    current_flat: &mut Vec<FlatInstr>,
    local_res: &mut SearchResult,
    sim: &mut Simulator,
    max_steps: usize,
) {
    if remaining_length == 0 {
        // Close all open loops
        for _ in 0..open_loops {
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

        for _ in 0..open_loops {
            current_flat.pop();
        }
        return;
    }

    if open_loops > 0 {
        current_flat.push(FlatInstr::WhileEnd);
        generate_and_sim(remaining_length, max_var, open_loops - 1, current_flat, local_res, sim, max_steps);
        current_flat.pop();
    }

    let next_allowed = match max_var {
        Some(v) => v + 1,
        None => 0,
    };

    for v in 0..=next_allowed {
        let next_max_var = Some(max_var.unwrap_or(0).max(v));

        current_flat.push(FlatInstr::Inc(v));
        generate_and_sim(remaining_length - 1, next_max_var, open_loops, current_flat, local_res, sim, max_steps);
        current_flat.pop();

        current_flat.push(FlatInstr::Dec(v));
        generate_and_sim(remaining_length - 1, next_max_var, open_loops, current_flat, local_res, sim, max_steps);
        current_flat.pop();

        current_flat.push(FlatInstr::WhileStart(v));
        generate_and_sim(remaining_length - 1, next_max_var, open_loops + 1, current_flat, local_res, sim, max_steps);
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
