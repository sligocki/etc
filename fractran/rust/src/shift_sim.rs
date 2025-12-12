/// Accelerated simulation by detecting and applying "shift rules".

use std::collections::HashSet;

use crate::diff_rule::DiffRule;
use crate::program::{Int, Program, State};
use crate::rule::{ApplyResult, Rule};
use crate::tandem_repeat::find_rep_blocks;
use crate::transcript::{transcript, Trans};


fn find_shift_rules(prog: &Program, state: State, transcript_steps: Int) -> Vec<DiffRule> {
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
struct ShiftSim {
    prog: Program,
    shift_rules: Vec<DiffRule>,

    status: SimStatus,
    base_steps: Int,
    sim_steps: Int,
    num_shift_steps: Int,
}

impl ShiftSim {
    fn new(prog: Program, shift_rules: Vec<DiffRule>) -> ShiftSim {
        ShiftSim {
            prog,
            shift_rules,
            status: SimStatus::Running,
            base_steps: 0,
            sim_steps: 0,
            num_shift_steps: 0,
        }
    }

    // Returns true if a step was applied, false if halted.
    fn step(&mut self, mut state: State) -> State {
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
                ApplyResult::Some { num_apps: _, result } => {
                    self.num_shift_steps += 1;
                    // TODO: Calculate number of base steps.
                    return result;
                }
                ApplyResult::None => {}
            }
        }

        // Second fall back to doing a basic rule
        if self.prog.step(&mut state) {
            // TODO: self.base_steps += 1;
        } else {
            self.status = SimStatus::Halted;
        }
        state
    }

    pub fn run(&mut self, mut state: State, num_steps: Int) -> State {
        while self.status == SimStatus::Running && self.sim_steps < num_steps {
            state = self.step(state);
        }
        state
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct ShiftSimResult {
    pub sim_status: SimStatus,
    // Number of base Fractran steps
    pub base_steps: Int,
    // Number of "simulator steps" where applying a shift rule counts as 1 sim_step.
    pub sim_steps: Int,
    // Number of shift rules added
    pub num_shift_rules: usize,
    // Number of times shift rules were used
    pub num_shift_steps: Int,
}

// Do accelerated simulation via a two part process:
//      1) Load transcript and find tandem repeats (shift rules).
//      2) Add those rules to simulator and accelerate applying them.
pub fn shift_sim(
    prog: Program,
    state: State,
    transcript_steps: Int,
    sim_steps: Int,
) -> ShiftSimResult {
    let shift_rules = find_shift_rules(&prog, state.clone(), transcript_steps);
    let mut sim = ShiftSim::new(prog, shift_rules);
    sim.run(state, sim_steps);

    ShiftSimResult {
        sim_status: sim.status,
        base_steps: sim.base_steps,
        sim_steps: sim.sim_steps,
        num_shift_rules: sim.shift_rules.len(),
        num_shift_steps: sim.num_shift_steps,
    }
}
