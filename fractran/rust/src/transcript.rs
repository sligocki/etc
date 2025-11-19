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

// Evaluate details of which rule applies and why prev do not.
pub fn eval_trans(prog: &Program, state: &State) -> Trans {
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

// Evaluate Trans and also apply applicable rule.
pub fn step(prog: &Program, state: &mut State) -> Trans {
    let trans = eval_trans(prog, state);
    let rule_num = trans.reg_fail.len();
    if rule_num < prog.num_rules() {
        prog.rules[rule_num].apply(state);
    }
    trans
}

// Simulate for num_steps keeping track of Trans at each step.
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
    // Compute DiffRule corresponding to an single transition.
    // Based on one transition, the delta is just the applicable rule and
    // the min is just the the negation of all the negaive values in rule.
    // The max is based off of all the previous rules failing to apply and
    // depends on the specific Trans.reg_fail values.
    pub fn from_trans(prog: &Program, trans: &Trans) -> DiffRule {
        let mut max_vals = vec![Int::MAX; prog.num_registers()];
        for (rule, reg_fail) in prog.rules.iter().zip(trans.reg_fail.iter()) {
            // if rule r += -n failed, then r <= n-1
            let max_val = (-rule.data[*reg_fail]) - 1;
            max_vals[*reg_fail] = cmp::min(max_vals[*reg_fail], max_val);
        }
        let delta = prog.rules[trans.reg_fail.len()].data.clone();
        let min_vals = delta.iter().map(|n| cmp::max(-n, 0)).collect();
        DiffRule {
            min: StateDiff::new(min_vals),
            max: StateDiff::new(max_vals),
            delta: StateDiff::new(delta),
        }
    }

    // Compute the DiffRule that corresponds to applying self and then other if possible.
    // Returns None if it is impossible to apply both rules in sequence.
    pub fn combine(&self, other: &DiffRule) -> Option<DiffRule> {
        // Compute min values for state before applying self.delta and then comparing to other.min.
        let other_min = &other.min - &self.delta;
        // Note: self.min: [0, 1, 2]  and  other_min: [1, 0, 0]   ->   min: [1, 1, 2]
        // ie: we need to choose max values pointwise.
        let min = self.min.pointwise_max(&other_min);

        let other_max = &other.max - &self.delta;
        let max = self.max.pointwise_min(&other_max);

        if min <= max {
            Some(DiffRule {
                min,
                max,
                delta: &self.delta + &other.delta,
            })
        } else {
            None
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
    use crate::{prog, sd, state};

    #[test]
    fn test_trans() {
        let prog = prog![ 1, -1, -1;
                         -1,  2,  0;
                          0,  1, -2];

        let sa = state![1, 2, 3];
        let ta = trans![];
        let ra = DiffRule {
            max: sd![Int::MAX, Int::MAX, Int::MAX],
            min: sd![0, 1, 1],
            delta: sd![1, -1, -1],
        };
        assert_eq!(eval_trans(&prog, &sa), ta);
        assert_eq!(DiffRule::from_trans(&prog, &ta), ra);

        let sb = state![1, 2, 0];
        let tb = trans![2];
        let rb = DiffRule {
            max: sd![Int::MAX, Int::MAX, 0],
            min: sd![1, 0, 0],
            delta: sd![-1, 2, 0],
        };
        assert_eq!(eval_trans(&prog, &sb), tb);
        assert_eq!(DiffRule::from_trans(&prog, &tb), rb);

        let sc = state![1, 0, 3];
        let tc = trans![1];
        let rc = DiffRule {
            max: sd![Int::MAX, 0, Int::MAX],
            min: sd![1, 0, 0],
            delta: sd![-1, 2, 0],
        };
        assert_eq!(eval_trans(&prog, &sc), tc);
        assert_eq!(DiffRule::from_trans(&prog, &tc), rc);

        let sd = state![0, 0, 3];
        let td = trans![1, 0];
        let rd = DiffRule {
            max: sd![0, 0, Int::MAX],
            min: sd![0, 0, 2],
            delta: sd![0, 1, -2],
        };
        assert_eq!(eval_trans(&prog, &sd), td);
        assert_eq!(DiffRule::from_trans(&prog, &td), rd);

        let se = state![0, 0, 1];
        let te = trans![1, 0, 2];
        assert_eq!(eval_trans(&prog, &se), te);
        // prog halts on se, so no DiffRule
    }
}
