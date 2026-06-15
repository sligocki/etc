use crate::ast::Instr;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InfiniteReason {
    StationaryCycle,
    TranslatedCycle,
    SymbolicMonotonic,
    SumMonotonic,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RunResult {
    Halted { score: usize, steps: usize },
    Infinite(InfiniteReason),
    Unknown,
}

// A guaranteed lower bound linear combination: C_0*A + C_1*B + C_2*C + C_3*D + C_4*E + K
#[derive(Clone, Debug, PartialEq, Eq)]
struct LowerBoundExpr {
    coeffs: Vec<usize>,
    k: usize,
}

impl LowerBoundExpr {
    fn new_identity(v: usize, num_vars: usize) -> Self {
        let mut coeffs = vec![0; num_vars];
        coeffs[v] = 1;
        Self { coeffs, k: 0 }
    }
    
    fn is_zero(&self) -> bool {
        self.k == 0 && self.coeffs.iter().all(|&c| c == 0)
    }
    
    // Checks if the expression is exactly V_y + c * V_x
    fn is_transfer_pattern(&self, x: usize, y: usize) -> Option<usize> {
        if self.k != 0 { return None; }
        for i in 0..self.coeffs.len() {
            if i == y {
                if self.coeffs[i] != 1 { return None; }
            } else if i == x {
                // allow any c >= 0
            } else {
                if self.coeffs[i] != 0 { return None; }
            }
        }
        Some(self.coeffs[x])
    }
    
    fn add_scaled(&mut self, other: &LowerBoundExpr, scale: usize) {
        if scale == 0 { return; }
        for i in 0..self.coeffs.len() {
            self.coeffs[i] += other.coeffs[i] * scale;
        }
        self.k += other.k * scale;
    }
}

type LowerBoundState = Vec<LowerBoundExpr>;

fn new_identity_state(num_vars: usize) -> LowerBoundState {
    (0..num_vars).map(|i| LowerBoundExpr::new_identity(i, num_vars)).collect()
}

fn max_var(body: &[Instr]) -> usize {
    body.iter().map(|instr| match instr {
        Instr::Inc(v) | Instr::Dec(v) => *v,
        Instr::While(v, inner) => (*v).max(max_var(inner)),
    }).max().unwrap_or(0)
}

fn evaluate_symbolic(body: &[Instr], num_vars: usize) -> Option<LowerBoundState> {
    let mut state = new_identity_state(num_vars);
    
    for instr in body {
        match instr {
            Instr::Inc(v) => {
                state[*v].k += 1;
            }
            Instr::Dec(_) => {
                return None; 
            }
            Instr::While(v, inner_body) => {
                let x = *v;
                
                let mut has_nested = false;
                let mut decs = vec![0; num_vars];
                let mut incs = vec![0; num_vars];
                
                for inner_instr in inner_body.iter() {
                    match inner_instr {
                        Instr::While(_, _) => { has_nested = true; }
                        Instr::Inc(y) => incs[*y] += 1,
                        Instr::Dec(y) => decs[*y] += 1,
                    }
                }
                
                if !has_nested && decs[x] == 1 {
                    let mut valid_transfer = true;
                    for i in 0..num_vars {
                        if i != x && incs[i] < decs[i] {
                            valid_transfer = false;
                            break;
                        }
                    }
                    if valid_transfer {
                        let state_x = state[x].clone();
                        for i in 0..num_vars {
                            if i != x {
                                let net = incs[i] - decs[i];
                                if net > 0 {
                                    let to_add = state_x.clone();
                                    state[i].add_scaled(&to_add, net);
                                }
                            }
                        }
                        state[x] = LowerBoundExpr { coeffs: vec![0; num_vars], k: 0 };
                        continue;
                    }
                }
                
                if let Some(inner_state) = evaluate_symbolic(inner_body, num_vars) {
                    if inner_state[x].is_zero() {
                        let mut valid_complex = true;
                        let mut scales = vec![0; num_vars];
                        for i in 0..num_vars {
                            if i != x {
                                if let Some(c) = inner_state[i].is_transfer_pattern(x, i) {
                                    scales[i] = c;
                                } else {
                                    valid_complex = false;
                                    break;
                                }
                            }
                        }
                        if valid_complex {
                            let state_x = state[x].clone();
                            for i in 0..num_vars {
                                if i != x && scales[i] > 0 {
                                    let to_add = state_x.clone();
                                    state[i].add_scaled(&to_add, scales[i]);
                                }
                            }
                            state[x] = LowerBoundExpr { coeffs: vec![0; num_vars], k: 0 };
                            continue;
                        }
                    }
                }
                
                return None; 
            }
        }
    }
    //println!("Evaluated body to: {:?}", state);
    Some(state)
}

pub struct Simulator {
    pub counters: Vec<usize>,
    pub last_zero_step: Vec<usize>,
    pub history: Vec<(usize, usize, Vec<usize>, usize)>, // (IP, step, counters, exec_id)
    pub next_exec_id: usize,
}

impl Simulator {
    pub fn new() -> Self {
        Self { 
            counters: Vec::new(), 
            last_zero_step: Vec::new(),
            history: Vec::new(),
            next_exec_id: 0,
        }
    }

    fn is_safe_monotonic_body(body: &[Instr], active_loops: &mut Vec<usize>) -> Option<InfiniteReason> {
        if active_loops.is_empty() {
            let num_vars = max_var(body) + 1;
            if let Some(_) = evaluate_symbolic(body, num_vars) {
                return Some(InfiniteReason::SymbolicMonotonic);
            }
        }
        for instr in body {
            match instr {
                Instr::Inc(_) => {}
                Instr::Dec(z) => {
                    for &l in active_loops.iter() {
                        if l != *z {
                            return None;
                        }
                    }
                }
                Instr::While(y, inner_body) => {
                    active_loops.push(*y);
                    let safe = Self::is_safe_monotonic_body(inner_body, active_loops);
                    active_loops.pop();
                    if safe.is_none() {
                        return None;
                    }
                }
            }
        }
        Some(InfiniteReason::SumMonotonic)
    }

    fn ensure_counter(&mut self, var: usize) {
        if var >= self.counters.len() {
            self.counters.resize(var + 1, 0);
            self.last_zero_step.resize(var + 1, 0);
        }
    }

    pub fn run(&mut self, program: &[Instr], max_steps: usize) -> RunResult {
        let mut steps = 0;
        self.counters.clear();
        self.last_zero_step.clear();
        self.history.clear();
        self.next_exec_id = 0;

        match self.run_block(program, &mut steps, max_steps) {
            Ok(_) => {
                let score = self.counters.iter().copied().max().unwrap_or(0);
                RunResult::Halted { score, steps }
            }
            Err(Some(reason)) => RunResult::Infinite(reason),
            Err(None) => RunResult::Unknown,
        }
    }

    fn run_block(&mut self, program: &[Instr], steps: &mut usize, max_steps: usize) -> Result<(), Option<InfiniteReason>> {
        for instr in program {
            *steps += 1;
            if *steps > max_steps {
                return Err(None);
            }

            match instr {
                Instr::Inc(v) => {
                    self.ensure_counter(*v);
                    self.counters[*v] += 1;
                }
                Instr::Dec(v) => {
                    self.ensure_counter(*v);
                    if self.counters[*v] > 0 {
                        self.counters[*v] -= 1;
                    }
                    if self.counters[*v] == 0 {
                        self.last_zero_step[*v] = *steps;
                    }
                }
                Instr::While(v, body) => {
                    self.ensure_counter(*v);
                    let ip = instr as *const Instr as usize;
                    let is_safe = Self::is_safe_monotonic_body(body, &mut Vec::new());
                    self.next_exec_id += 1;
                    let my_exec_id = self.next_exec_id;
                    
                    while self.counters[*v] > 0 {
                        let current_state = self.counters.clone();
                        
                        for &(hist_ip, hist_step, ref hist_counters, hist_exec_id) in self.history.iter().rev() {
                            if hist_ip == ip {
                                let same_exec = hist_exec_id == my_exec_id;
                                let mut is_inf = true;
                                let mut is_translated = false;
                                for i in 0..current_state.len() {
                                    let m1 = hist_counters.get(i).copied().unwrap_or(0);
                                    let m2 = current_state[i];
                                    
                                    if m2 < m1 {
                                        is_inf = false;
                                        break;
                                    }
                                    if m2 > m1 {
                                        is_translated = true;
                                        if is_safe.is_none() || !same_exec {
                                            if m1 == 0 {
                                                is_inf = false;
                                                break;
                                            }
                                            if self.last_zero_step.get(i).copied().unwrap_or(0) >= hist_step {
                                                is_inf = false;
                                                break;
                                            }
                                        }
                                    }
                                }
                                if is_inf {
                                    if !is_translated {
                                        //println!("Stationary cycle detected! IP: {}, counters: {:?}", ip, current_state);
                                        return Err(Some(InfiniteReason::StationaryCycle));
                                    } else {
                                        if let Some(reason) = is_safe {
                                            if same_exec {
                                                return Err(Some(reason));
                                            }
                                        }
                                        if hist_step > self.last_zero_step[*v] {
                                            return Err(Some(InfiniteReason::TranslatedCycle));
                                        }
                                    }
                                }
                            }
                        }
                        
                        self.history.push((ip, *steps, current_state, my_exec_id));

                        self.run_block(body, steps, max_steps)?;
                        
                        *steps += 1;
                        if *steps > max_steps {
                            return Err(None);
                        }
                    }
                }
            }
        }
        Ok(())
    }
}
