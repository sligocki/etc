// Evaluate the "transcript" or rule history for a simulation.

use crate::program::{Int, Program, State};
use crate::state_diff::StateDiff;
use std::cmp;

// A transition is a description of which rule applied at each step and
// why the previous rules did not apply.
pub struct Trans {
    // For each previous rule, which register caused the rule to not apply
    // (because it would go negative).
    pub reg_fail: Vec<usize>,
}

pub fn step(prog: &Program, state: &mut State) -> Trans {
    let reg_fail = prog
        .rules
        .iter()
        .filter_map(|r| r.can_apply(state).err())
        .collect();
    Trans { reg_fail }
}

pub fn transcript(prog: &Program, state: &mut State, num_steps: Int) -> Vec<Trans> {
    let mut ret: Vec<Trans> = Vec::new();
    for _ in 0..num_steps {
        ret.push(step(prog, state))
    }
    ret
}

// Inductive Diff Rule based on a Trans.
// If min ≤ state ≤ max:
//    state -> state + delta
pub struct DiffRule {
    pub min: StateDiff,
    pub max: StateDiff,
    pub delta: StateDiff,
}

impl DiffRule {
    pub fn from_trans(prog: &Program, trans: &Trans) -> DiffRule {
        let mut max_vals = vec![Int::MAX; prog.num_registers()];
        for (rule, reg_fail) in prog.rules.iter().zip(trans.reg_fail.iter()) {
            max_vals[*reg_fail] = cmp::min(max_vals[*reg_fail], -rule.data[*reg_fail])
        }
        let delta = prog.rules[trans.reg_fail.len()].data.clone();
        let min_vals = delta.iter().map(|n| cmp::max(-n, 0)).collect();
        DiffRule {
            min: StateDiff::new(min_vals),
            max: StateDiff::new(max_vals),
            delta: StateDiff::new(delta),
        }
    }

    pub fn combine(&self, other: &DiffRule) -> DiffRule {
        let other_min = &other.min - &self.delta;
        let other_max = &other.max - &self.delta;

        DiffRule {
            min: self.min.pointwise_max(&other_min),
            max: self.max.pointwise_min(&other_max),
            delta: &self.delta + &other.delta,
        }
    }
}

// TODO: Add tests
