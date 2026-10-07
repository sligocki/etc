use crate::program::{Instruction, Program, Target};

#[derive(Clone, Debug)]
pub struct State {
    pub pc: usize,
    pub registers: Vec<u64>,
    pub steps: u64,
    pub last_decr_zero: Vec<u64>,
}

impl State {
    pub fn new() -> Self {
        State {
            pc: 0,
            registers: Vec::new(),
            steps: 0,
            last_decr_zero: Vec::new(),
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

    pub fn set_last_decr_zero(&mut self, r: usize, step: u64) {
        if r >= self.last_decr_zero.len() {
            self.last_decr_zero.resize(r + 1, 0);
        }
        self.last_decr_zero[r] = step;
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
    CycleDetected { start_by: u64, period: u64, is_min_start: bool },
    TranslatedCyclerDetected { start_by: u64, period: u64, is_min_start: bool },
    HitUndefInst(usize),
    HitUndefTarget { pc: usize, branch: Branch },
}

pub fn step(state: &mut State, prog: &Program) -> SimResult {
    if state.pc >= prog.instructions.len() {
        return SimResult::OutOfBounds;
    }

    let current_pc = state.pc;
    let inst = &prog.instructions[state.pc];

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
                Target::Halt => return SimResult::Halted { steps: state.steps, registers: state.registers.clone() },
                Target::Inst(i) => state.pc = *i,
            }
        }
        Instruction::Dec { reg, next_not_zero, next_zero } => {
            state.steps += 1;
            let val = state.get_reg(*reg);
            if val == 0 {
                state.set_last_decr_zero(*reg, state.steps);
                match next_zero {
                    Target::Undef => return SimResult::HitUndefTarget { pc: current_pc, branch: Branch::NextZero },
                    Target::Halt => return SimResult::Halted { steps: state.steps, registers: state.registers.clone() },
                    Target::Inst(i) => state.pc = *i,
                }
            } else {
                state.set_reg(*reg, val - 1);
                match next_not_zero {
                    Target::Undef => return SimResult::HitUndefTarget { pc: current_pc, branch: Branch::NextNotZero },
                    Target::Halt => return SimResult::Halted { steps: state.steps, registers: state.registers.clone() },
                    Target::Inst(i) => state.pc = *i,
                }
            }
        }
        Instruction::NoOp { next } => {
            state.steps += 1;
            match next {
                Target::Undef => return SimResult::HitUndefTarget { pc: current_pc, branch: Branch::Next },
                Target::Halt => return SimResult::Halted { steps: state.steps, registers: state.registers.clone() },
                Target::Inst(i) => state.pc = *i,
            }
        }
    }
    SimResult::LimitReached // placeholder for "successfully stepped"
}

pub fn simulate(prog: &Program, step_limit: Option<u64>, detect_cycles: bool, exact_start_by: bool, verbose: bool) -> SimResult {
    let mut state = State::new();
    let mut power = 1;
    let mut lam = 1;
    let mut tortoise_pc = state.pc;
    let mut tortoise_registers = state.registers.clone();
    let mut tortoise_step = state.steps;

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
            if state.pc == tortoise_pc {
                let mut is_ge = true;
                let mut strict_increase = false;
                let mut valid_tc = true;

                let max_len = std::cmp::max(state.registers.len(), tortoise_registers.len());
                for i in 0..max_len {
                    let hare_val = if i < state.registers.len() { state.registers[i] } else { 0 };
                    let tort_val = if i < tortoise_registers.len() { tortoise_registers[i] } else { 0 };
                    if hare_val < tort_val {
                        is_ge = false;
                        break;
                    } else if hare_val > tort_val {
                        strict_increase = true;
                        let ldz = if i < state.last_decr_zero.len() { state.last_decr_zero[i] } else { 0 };
                        if ldz > tortoise_step {
                            valid_tc = false;
                        }
                    }
                }

                if is_ge && (!strict_increase || valid_tc) {
                    let period = lam;
                    if !exact_start_by {
                        let start_by = tortoise_step;
                        if strict_increase {
                            return SimResult::TranslatedCyclerDetected { start_by, period, is_min_start: false };
                        } else {
                            return SimResult::CycleDetected { start_by, period, is_min_start: false };
                        }
                    }

                    let mut start_by = 0;
                    let mut hare = State::new();
                    for _ in 0..period {
                        let _ = step(&mut hare, prog);
                    }
                    let mut tortoise = State::new();
                    loop {
                        let mut is_ge = true;
                        let mut strict_increase = false;
                        let mut valid_tc = true;

                        if hare.pc == tortoise.pc {
                            let max_len = std::cmp::max(hare.registers.len(), tortoise.registers.len());
                            for i in 0..max_len {
                                let hare_val = if i < hare.registers.len() { hare.registers[i] } else { 0 };
                                let tort_val = if i < tortoise.registers.len() { tortoise.registers[i] } else { 0 };
                                if hare_val < tort_val {
                                    is_ge = false;
                                    break;
                                } else if hare_val > tort_val {
                                    strict_increase = true;
                                    let ldz = if i < hare.last_decr_zero.len() { hare.last_decr_zero[i] } else { 0 };
                                    if ldz > tortoise.steps {
                                        valid_tc = false;
                                    }
                                }
                            }
                            if is_ge && (!strict_increase || valid_tc) {
                                if strict_increase {
                                    return SimResult::TranslatedCyclerDetected { start_by, period, is_min_start: true };
                                } else {
                                    return SimResult::CycleDetected { start_by, period, is_min_start: true };
                                }
                            }
                        }

                        let _ = step(&mut hare, prog);
                        let _ = step(&mut tortoise, prog);
                        start_by += 1;
                    }
                }
            }
            if power == lam {
                tortoise_pc = state.pc;
                tortoise_registers = state.registers.clone();
                tortoise_step = state.steps;
                power *= 2;
                lam = 0;
            }
            lam += 1;
        }

        if verbose {
            let state_char = (b'A' + state.pc as u8) as char;
            let max_reg = prog.num_regs();
            let mut regs = Vec::new();
            for i in 0..max_reg {
                regs.push(state.get_reg(i));
            }
            let inst = &prog.instructions[state.pc];
            println!("{:6} {}:{:?}    {}", state.steps, state_char, regs, inst);
        }

        let res = step(&mut state, prog);
        if !matches!(res, SimResult::LimitReached) {
            return res;
        }
    }
}
