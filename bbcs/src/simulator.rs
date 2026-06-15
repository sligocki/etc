use crate::ast::Instr;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RunResult {
    Halted { score: usize },
    Timeout,
}

pub struct Simulator {
    pub counters: Vec<usize>,
}

impl Simulator {
    pub fn new() -> Self {
        Self { counters: Vec::new() }
    }

    fn ensure_counter(&mut self, var: usize) {
        if var >= self.counters.len() {
            self.counters.resize(var + 1, 0);
        }
    }

    pub fn run(&mut self, program: &[Instr], max_steps: usize) -> RunResult {
        let mut steps = 0;
        self.counters.clear();

        match self.run_block(program, &mut steps, max_steps) {
            Ok(_) => {
                let score = self.counters.iter().copied().max().unwrap_or(0);
                RunResult::Halted { score }
            }
            Err(_) => RunResult::Timeout,
        }
    }

    fn run_block(&mut self, program: &[Instr], steps: &mut usize, max_steps: usize) -> Result<(), ()> {
        for instr in program {
            *steps += 1;
            if *steps > max_steps {
                return Err(());
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
                }
                Instr::While(v, body) => {
                    self.ensure_counter(*v);
                    while self.counters[*v] > 0 {
                        self.run_block(body, steps, max_steps)?;
                        
                        *steps += 1;
                        if *steps > max_steps {
                            return Err(());
                        }
                    }
                }
            }
        }
        Ok(())
    }
}
