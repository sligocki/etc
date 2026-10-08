//! Backwards reachability decider.
//!
//! Starting at the halting state, this decider explores an abstraction of all
//! predecessor states. If the all-zero initial state cannot be reached, the
//! program cannot halt.

use crate::deciders::{Decider, DeciderResult, InfiniteReason};
use crate::program::{Instruction, Program, Target};
use std::collections::{HashSet, VecDeque};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum RegisterValue {
    Zero,
    NonZero,
    Unknown,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct AbstractState {
    pc: Option<usize>, // None is the halting state.
    registers: Vec<RegisterValue>,
}

fn target_pc(target: Target, program: &Program) -> Option<usize> {
    match target {
        Target::Inst(pc)
            if matches!(
                program.instructions.get(pc),
                Some(instruction) if !matches!(instruction, Instruction::Undef)
            ) =>
        {
            Some(pc)
        }
        Target::Halt | Target::Undef | Target::Inst(_) => None,
    }
}

fn predecessors(program: &Program, state: &AbstractState) -> Vec<AbstractState> {
    let mut result = Vec::new();

    for (previous_pc, instruction) in program.instructions.iter().enumerate() {
        match *instruction {
            Instruction::Undef => {}
            Instruction::Inc { reg, next }
                if target_pc(next, program) == state.pc
                    && state.registers[reg] != RegisterValue::Zero =>
            {
                let mut registers = state.registers.clone();
                registers[reg] = RegisterValue::Unknown;
                result.push(AbstractState {
                    pc: Some(previous_pc),
                    registers,
                });
            }
            Instruction::Dec {
                reg,
                next_not_zero,
                next_zero,
            } => {
                if target_pc(next_not_zero, program) == state.pc {
                    let mut registers = state.registers.clone();
                    registers[reg] = RegisterValue::NonZero;
                    result.push(AbstractState {
                        pc: Some(previous_pc),
                        registers,
                    });
                }

                if target_pc(next_zero, program) == state.pc
                    && state.registers[reg] != RegisterValue::NonZero
                {
                    let mut registers = state.registers.clone();
                    registers[reg] = RegisterValue::Zero;
                    result.push(AbstractState {
                        pc: Some(previous_pc),
                        registers,
                    });
                }
            }
            Instruction::NoOp { next } if target_pc(next, program) == state.pc => {
                result.push(AbstractState {
                    pc: Some(previous_pc),
                    registers: state.registers.clone(),
                });
            }
            Instruction::Inc { .. } | Instruction::NoOp { .. } => {}
        }
    }

    result
}

/// Returns true when backwards abstract exploration proves that the all-zero
/// initial state cannot reach a halt.
pub fn start_unreachable(program: &Program) -> bool {
    // An undefined initial instruction halts immediately. Keeping this case
    // explicit also makes the decider safe to use on partial programs.
    if matches!(
        program.instructions.first(),
        None | Some(Instruction::Undef)
    ) {
        return false;
    }

    let halt = AbstractState {
        pc: None,
        registers: vec![RegisterValue::Unknown; program.num_regs()],
    };
    let mut queue = VecDeque::from([halt.clone()]);
    let mut seen = HashSet::from([halt]);

    while let Some(state) = queue.pop_front() {
        if state.pc == Some(0)
            && state
                .registers
                .iter()
                .all(|value| *value != RegisterValue::NonZero)
        {
            return false;
        }

        for predecessor in predecessors(program, &state) {
            if seen.insert(predecessor.clone()) {
                queue.push_back(predecessor);
            }
        }
    }

    true
}

pub struct BackwardsDecider;

impl Decider for BackwardsDecider {
    fn decide(&self, program: &Program) -> DeciderResult {
        if start_unreachable(program) {
            DeciderResult::Infinite(InfiniteReason::BackwardsUnreachable)
        } else {
            DeciderResult::Unknown
        }
    }
}
