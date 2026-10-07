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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Branch {
    Next,
    NextNotZero,
    NextZero,
}

pub enum SimResult {
    Halted { steps: u64, registers: Vec<u64> },
    OutOfBounds,
    LimitReached,
    CycleDetected { steps: u64 },
    HitUndefInst(usize),
    HitUndefTarget { pc: usize, branch: Branch },
}

pub fn simulate(prog: &Program, step_limit: Option<u64>, detect_cycles: bool, verbose: bool) -> SimResult {
    let mut state = State::new();
    let mut power = 1;
    let mut lam = 1;
    let mut tortoise_pc = state.pc;
    let mut tortoise_registers = state.registers.clone();

    loop {
        if let Some(limit) = step_limit {
            if state.steps >= limit {
                return SimResult::LimitReached;
            }
        }

        if state.pc >= prog.instructions.len() {
            return SimResult::OutOfBounds; // Reached an instruction index not in program
        }

        if detect_cycles && state.steps > 0 {
            if state.pc == tortoise_pc && state.registers == tortoise_registers {
                return SimResult::CycleDetected { steps: state.steps };
            }
            if power == lam {
                tortoise_pc = state.pc;
                tortoise_registers = state.registers.clone();
                power *= 2;
                lam = 0;
            }
            lam += 1;
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

        let current_pc = state.pc;

        match inst {
            Instruction::Undef => {
                return SimResult::HitUndefInst(current_pc);
            }
            Instruction::Inc { reg, next } => {
                state.steps += 1;
                let val = state.get_reg(*reg);
                state.set_reg(*reg, val.wrapping_add(1));
                match next {
                    Target::Undef => return SimResult::HitUndefTarget { pc: current_pc, branch: Branch::Next },
                    Target::Halt => return SimResult::Halted { steps: state.steps, registers: state.registers },
                    Target::Inst(i) => state.pc = *i,
                }
            }
            Instruction::Dec { reg, next_not_zero, next_zero } => {
                state.steps += 1;
                let val = state.get_reg(*reg);
                if val == 0 {
                    match next_zero {
                        Target::Undef => return SimResult::HitUndefTarget { pc: current_pc, branch: Branch::NextZero },
                        Target::Halt => return SimResult::Halted { steps: state.steps, registers: state.registers },
                        Target::Inst(i) => state.pc = *i,
                    }
                } else {
                    state.set_reg(*reg, val - 1);
                    match next_not_zero {
                        Target::Undef => return SimResult::HitUndefTarget { pc: current_pc, branch: Branch::NextNotZero },
                        Target::Halt => return SimResult::Halted { steps: state.steps, registers: state.registers },
                        Target::Inst(i) => state.pc = *i,
                    }
                }
            }
            Instruction::NoOp { next } => {
                state.steps += 1;
                match next {
                    Target::Undef => return SimResult::HitUndefTarget { pc: current_pc, branch: Branch::Next },
                    Target::Halt => return SimResult::Halted { steps: state.steps, registers: state.registers },
                    Target::Inst(i) => state.pc = *i,
                }
            }
        }
    }
}
