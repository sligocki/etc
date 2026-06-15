use crate::ast::Instr;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InfiniteReason {
    StationaryCycle,
    TranslatedCycle,
    SumMonotonic,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RunResult {
    Halted { score: usize },
    Infinite(InfiniteReason),
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
            history: Vec::new(),
        }
    }

    fn is_safe_monotonic_body(body: &[Instr], active_loops: &mut Vec<usize>) -> bool {
        for instr in body {
            match instr {
                Instr::Inc(_) => {}
                Instr::Dec(z) => {
                    if active_loops.is_empty() {
                        return false;
                    }
                    for &l in active_loops.iter() {
                        if l != *z {
                            return false;
                        }
                    }
                }
                Instr::While(y, inner_body) => {
                    active_loops.push(*y);
                    let safe = Self::is_safe_monotonic_body(inner_body, active_loops);
                    active_loops.pop();
                    if !safe {
                        return false;
                    }
                }
            }
        }
        true
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
                    while self.counters[*v] > 0 {
                        let current_state = self.counters.clone();
                        
                        for &(hist_ip, hist_step, ref hist_counters) in self.history.iter().rev() {
                            if hist_ip == ip {
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
                                        if !is_safe {
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
                                    if is_translated {
                                        if is_safe {
                                            return Err(Some(InfiniteReason::SumMonotonic));
                                        } else {
                                            return Err(Some(InfiniteReason::TranslatedCycle));
                                        }
                                    } else {
                                        return Err(Some(InfiniteReason::StationaryCycle));
                                    }
                                }
                            }
                        }
                        
                        self.history.push((ip, *steps, current_state));

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
