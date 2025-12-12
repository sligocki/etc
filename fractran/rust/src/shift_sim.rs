/// Accelerated simulation by detecting and applying "shift rules".
use std::collections::HashSet;

use crate::diff_rule::DiffRule;
use crate::program::{BigInt, Program, State};
use crate::rule::{ApplyResult, Rule};
use crate::tandem_repeat::find_rep_blocks;
use crate::transcript::{Trans, transcript};

pub fn find_shift_rules(prog: &Program, state: State, transcript_steps: usize) -> Vec<DiffRule> {
    let trans_vec = transcript(prog, state.clone(), transcript_steps);
    let rep_blocks = find_rep_blocks(&trans_vec);
    // Trans sequences that tandem repeat.
    let seqs: HashSet<&Vec<Trans>> = rep_blocks
        .iter()
        .filter(|r| r.rep != 1)
        .map(|r| &r.block)
        .collect();

    seqs.iter()
        .map(|seq| DiffRule::from_trans_vec(&prog, seq).expect("Illegal tandem repeat"))
        .collect()
}

#[derive(Debug, PartialEq, Clone)]
pub enum SimStatus {
    Running,
    Halted,
    Infinite,
}

#[derive(Debug)]
pub struct ShiftSim {
    pub prog: Program,
    pub shift_rules: Vec<DiffRule>,

    pub status: SimStatus,
    pub base_steps: BigInt,
    pub sim_steps: usize,
    pub num_shift_steps: usize,
}

impl ShiftSim {
    pub fn new(prog: Program, shift_rules: Vec<DiffRule>) -> ShiftSim {
        ShiftSim {
            prog,
            shift_rules,
            status: SimStatus::Running,
            base_steps: 0.into(),
            sim_steps: 0,
            num_shift_steps: 0,
        }
    }

    // Returns true if a step was applied, false if halted.
    pub fn step(&mut self, mut state: State) -> State {
        if self.status != SimStatus::Running {
            return state;
        }

        self.sim_steps += 1;
        // First, try to apply each rule
        for rule in self.shift_rules.iter() {
            match rule.apply(&state) {
                ApplyResult::Infinite => {
                    self.num_shift_steps += 1;
                    self.status = SimStatus::Infinite;
                    return state;
                }
                ApplyResult::Some {
                    num_apps: _,
                    result,
                } => {
                    self.num_shift_steps += 1;
                    // TODO: Calculate number of base steps.
                    return result;
                }
                ApplyResult::None => {}
            }
        }

        // If no shift rules apply, fall back to doing a basic rule
        if self.prog.step(&mut state) {
            // TODO: self.base_steps += 1;
        } else {
            self.status = SimStatus::Halted;
        }
        state
    }

    pub fn run(&mut self, mut state: State, num_steps: usize) -> State {
        for _ in 0..num_steps {
            state = self.step(state);
            if self.status != SimStatus::Running {
                break;
            }
        }
        state
    }
}
