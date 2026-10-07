use crate::program::{Instruction, Program, Target};

#[derive(Clone, Debug)]
pub struct State {
    pub pc: usize,
    pub registers: Vec<u64>,
    pub steps: u64,
}

impl State {
    pub fn new() -> Self {
        State {
            pc: 0,
            registers: Vec::new(),
            steps: 0,
        }
    }

    pub fn get_reg(&self, r: usize) -> u64 {
        if r < self.registers.len() {
            self.registers[r]
        } else {
            0
        }
    }

    pub fn set_reg(&mut self, r: usize, val: u64) {
        if r >= self.registers.len() {
            self.registers.resize(r + 1, 0);
        }
        self.registers[r] = val;
    }
}

pub enum SimResult {
    Halted(u64), // steps
    OutOfBounds,
    LimitReached,
}

pub fn simulate(prog: &Program, step_limit: Option<u64>, verbose: bool) -> SimResult {
    let mut state = State::new();

    loop {
        if let Some(limit) = step_limit {
            if state.steps >= limit {
                return SimResult::LimitReached;
            }
        }

        if state.pc >= prog.instructions.len() {
            return SimResult::OutOfBounds; // Reached an instruction index not in program
        }

        let inst = &prog.instructions[state.pc];

        if verbose {
            let state_char = (b'A' + state.pc as u8) as char;
            let max_reg = prog.num_regs();
            let mut regs = Vec::new();
            for i in 0..max_reg {
                regs.push(state.get_reg(i));
            }
            println!("{:6} {}:{:?}    {}", state.steps, state_char, regs, inst);
        }

        state.steps += 1;

        match inst {
            Instruction::Undef => {
                return SimResult::Halted(state.steps);
            }
            Instruction::Inc { reg, next } => {
                let val = state.get_reg(*reg);
                state.set_reg(*reg, val.wrapping_add(1));
                match next {
                    Target::Halt => return SimResult::Halted(state.steps),
                    Target::Inst(i) => state.pc = *i,
                }
            }
            Instruction::Dec { reg, next_not_zero, next_zero } => {
                let val = state.get_reg(*reg);
                if val == 0 {
                    match next_zero {
                        Target::Halt => return SimResult::Halted(state.steps),
                        Target::Inst(i) => state.pc = *i,
                    }
                } else {
                    state.set_reg(*reg, val - 1);
                    match next_not_zero {
                        Target::Halt => return SimResult::Halted(state.steps),
                        Target::Inst(i) => state.pc = *i,
                    }
                }
            }
        }
    }
}
