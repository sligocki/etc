// Evaluate the "transcript" or rule history for a simulation.

use crate::program::{Int, Program, State};
use crate::state_diff::StateDiff;
use std::cmp;

// A transition is a description of which rule applied at each step and
// why the previous rules did not apply.
#[derive(Debug, PartialEq)]
pub struct Trans {
    // For each previous rule, which register caused the rule to not apply
    // (because it would go negative).
    pub reg_fail: Vec<usize>,
}

pub fn step(prog: &Program, state: &mut State) -> Trans {
    let mut reg_fail: Vec<usize> = Vec::new();
    for rule in prog.rules.iter() {
        match rule.can_apply(state) {
            Err(reg) => {
                reg_fail.push(reg);
            }
            Ok(_) => {
                break;
            }
        }
    }
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
#[derive(Debug, PartialEq)]
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

#[macro_export]
macro_rules! trans {
    ($($x:expr),* $(,)?) => {
        Trans { reg_fail: vec![$($x),*] }
    };
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::program::Rule;
    use crate::{prog, state};

    #[test]
    fn test_trans() {
        let prog = prog![ 1, -1, -1;
                         -1,  2,  0;
                          0,  1, -2];

        let a = state![1, 2, 3];
        assert_eq!(step(&prog, &mut a.clone()), trans![]);

        let b = state![1, 2, 0];
        assert_eq!(step(&prog, &mut b.clone()), trans![2]);

        let c = state![1, 0, 3];
        assert_eq!(step(&prog, &mut c.clone()), trans![1]);

        let d = state![0, 0, 3];
        assert_eq!(step(&prog, &mut d.clone()), trans![1, 0]);

        let e = state![0, 0, 1];
        assert_eq!(step(&prog, &mut e.clone()), trans![1, 0, 2]);
    }
}
