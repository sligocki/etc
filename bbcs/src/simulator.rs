use crate::ast::Instr;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RunResult {
    Halted { score: usize },
    Infinite,
    Unknown,
}

pub struct Simulator {
    pub counters: Vec<usize>,
    pub last_zero_step: Vec<usize>,
    pub history: Vec<(usize, usize, Vec<usize>)>, // (IP, step, counters)
}

impl Simulator {
    pub fn new() -> Self {
        Self { 
            counters: Vec::new(), 
            last_zero_step: Vec::new(),
            history: Vec::new() 
        }
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

        match self.run_block(program, &mut steps, max_steps) {
            Ok(_) => {
                let score = self.counters.iter().copied().max().unwrap_or(0);
                RunResult::Halted { score }
            }
            Err(true) => RunResult::Infinite,
            Err(false) => RunResult::Unknown,
        }
    }

    fn run_block(&mut self, program: &[Instr], steps: &mut usize, max_steps: usize) -> Result<(), bool> {
        for instr in program {
            *steps += 1;
            if *steps > max_steps {
                return Err(false);
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
                    while self.counters[*v] > 0 {
                        let current_state = self.counters.clone();
                        
                        for &(hist_ip, hist_step, ref hist_counters) in self.history.iter().rev() {
                            if hist_ip == ip {
                                let mut is_inf = true;
                                for i in 0..current_state.len() {
                                    let m1 = hist_counters.get(i).copied().unwrap_or(0);
                                    let m2 = current_state[i];
                                    
                                    if m2 < m1 {
                                        is_inf = false;
                                        break;
                                    }
                                    if m2 > m1 {
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
                                if is_inf {
                                    return Err(true);
                                }
                            }
                        }
                        
                        self.history.push((ip, *steps, current_state));

                        self.run_block(body, steps, max_steps)?;
                        
                        *steps += 1;
                        if *steps > max_steps {
                            return Err(false);
                        }
                    }
                }
            }
        }
        Ok(())
    }
}
