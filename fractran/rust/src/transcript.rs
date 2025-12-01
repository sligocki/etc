// Evaluate the "transcript" or rule history for a simulation.

use std::cmp;
use std::fmt;

use infinitable::{Finite, Infinitable, Infinity, NegativeInfinity};
use itertools::Itertools;

use crate::program::{Int, Program, State};
use crate::state_diff::{StateDiff, StateDiffBound};
use crate::tandem_repeat::ToStringVec;

// A transition is a description of which rule applied at each step and
// why the previous rules did not apply.
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Trans {
    // For each previous rule, which register caused the rule to not apply
    // (because it would go negative).
    pub reg_fail: Vec<usize>,
}

const OFFSET: u8 = 'A' as u8;
impl ToStringVec for Trans {
    fn to_string_one(&self) -> String {
        let rule_num = self.reg_fail.len() as u8;
        let rule_char = (OFFSET + rule_num) as char;
        rule_char.to_string()
    }

    fn to_string_vec(xs: &Vec<Self>) -> String {
        xs.iter().map(|x| x.to_string_one()).join("")
    }
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
pub fn transcript(prog: &Program, mut state: State, num_steps: Int) -> Vec<Trans> {
    let mut ret: Vec<Trans> = Vec::new();
    for _ in 0..num_steps {
        ret.push(step(prog, &mut state))
    }
    ret
}

// Inductive Diff Rule based on a Trans.
// If min ≤ state ≤ max:
//    state -> state + delta
#[derive(Debug, PartialEq)]
pub struct DiffRule {
    pub min: StateDiff,
    pub max: StateDiffBound,
    pub delta: StateDiff,
}

impl DiffRule {
    // Create a no-op DiffRule that always applies and does nothing.
    pub fn noop(size: usize) -> DiffRule {
        DiffRule {
            min: StateDiff::new(vec![0; size]),
            max: StateDiffBound::new(vec![Infinity; size]),
            delta: StateDiff::new(vec![0; size]),
        }
    }

    // Compute DiffRule corresponding to an single transition if possible.
    // Based on one transition, the delta is just the applicable rule and
    // the min is just the the negation of all the negaive values in rule.
    // The max is based off of all the previous rules failing to apply and
    // depends on the specific Trans.reg_fail values.
    // Only fails (returns None) if trans is a halting transition (no rule applies).
    pub fn from_trans(prog: &Program, trans: &Trans) -> Option<DiffRule> {
        if trans.reg_fail.len() >= prog.num_rules() {
            return None;
        }
        let mut max_vals = vec![Infinity; prog.num_registers()];
        for (rule, reg_fail) in prog.rules.iter().zip(trans.reg_fail.iter()) {
            // if rule r += -n failed, then r <= n-1
            let max_val = (-rule.data[*reg_fail]) - 1;
            max_vals[*reg_fail] = cmp::min(max_vals[*reg_fail], Finite(max_val));
        }
        let delta = prog.rules[trans.reg_fail.len()].data.clone();
        let min_vals = delta.iter().map(|n| if *n < 0 { -n } else { 0 }).collect();
        Some(DiffRule {
            min: StateDiff::new(min_vals),
            max: StateDiffBound::new(max_vals),
            delta: StateDiff::new(delta),
        })
    }

    // Compute DiffRule for a sequence of transitions (if possible).
    // This leads to more complex rules than from_trans().
    pub fn from_trans_vec(prog: &Program, trans_vec: &[Trans]) -> Option<DiffRule> {
        let rules = trans_vec.iter().map(|t| DiffRule::from_trans(prog, t));
        let mut comb_rule = DiffRule::noop(prog.num_registers());
        for rule in rules {
            comb_rule = comb_rule.combine(&rule?)?;
        }
        Some(comb_rule)
    }

    // Compute the DiffRule that corresponds to applying self and then other if possible.
    // Returns None if it is impossible to apply both rules in sequence.
    pub fn combine(&self, other: &DiffRule) -> Option<DiffRule> {
        // Compute min values for state before applying first_delta and then comparing to other.min.
        let other_min = &other.min - &self.delta;
        // Note: self.min: [0, 1, 2]  and  other_min: [1, 0, 0]   ->   min: [1, 1, 2]
        // ie: we need to choose max values pointwise.
        let min = self.min.pointwise_max(&other_min);

        let other_max = &other.max - &(&self.delta).into();
        let max = self.max.pointwise_min(&other_max);

        if max >= StateDiffBound::from(&min) {
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

fn inf_str(val: &Infinitable<Int>) -> String {
    match val {
        Finite(n) => format!("{}", n),
        Infinity => "∞".to_string(),
        NegativeInfinity => "∞".to_string(),
    }
}

impl fmt::Display for DiffRule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "DiffRule: [")?;
        for (low, high) in self.min.data.iter().zip(self.max.data.iter()) {
            write!(f, "{}-{}, ", low, inf_str(high))?;
        }
        write!(f, "]  {:?}", self.delta.data)
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
    use crate::{prog, sd, sdb, state};

    #[test]
    fn test_trans() {
        let prog = prog![ 1, -1, -1;
                         -1,  2,  0;
                          0,  1, -2];

        let sa = state![1, 2, 3];
        let ta = trans![];
        let ra = DiffRule {
            max: sdb![Infinity, Infinity, Infinity],
            min: sd![0, 1, 1],
            delta: sd![1, -1, -1],
        };
        assert_eq!(eval_trans(&prog, &sa), ta);
        assert_eq!(DiffRule::from_trans(&prog, &ta), Some(ra));

        let sb = state![1, 2, 0];
        let tb = trans![2];
        let rb = DiffRule {
            max: sdb![Infinity, Infinity, Finite(0)],
            min: sd![1, 0, 0],
            delta: sd![-1, 2, 0],
        };
        assert_eq!(eval_trans(&prog, &sb), tb);
        assert_eq!(DiffRule::from_trans(&prog, &tb), Some(rb));

        let sc = state![1, 0, 3];
        let tc = trans![1];
        let rc = DiffRule {
            max: sdb![Infinity, Finite(0), Infinity],
            min: sd![1, 0, 0],
            delta: sd![-1, 2, 0],
        };
        assert_eq!(eval_trans(&prog, &sc), tc);
        assert_eq!(DiffRule::from_trans(&prog, &tc), Some(rc));

        let sd = state![0, 0, 3];
        let td = trans![1, 0];
        let rd = DiffRule {
            max: sdb![Finite(0), Finite(0), Infinity],
            min: sd![0, 0, 2],
            delta: sd![0, 1, -2],
        };
        assert_eq!(eval_trans(&prog, &sd), td);
        assert_eq!(DiffRule::from_trans(&prog, &td), Some(rd));

        let se = state![0, 0, 1];
        let te = trans![1, 0, 2];
        assert_eq!(eval_trans(&prog, &se), te);
        assert_eq!(DiffRule::from_trans(&prog, &te), None);
    }

    #[test]
    fn test_transcript() {
        // Hydra simulator: [507/22, 26/33, 245/2, 5/21, 1/3, 11/13, 22/5]
        // S(h, w) = [1, 0, 0, w, h-3, 0]
        let hydra = prog![
            -1,  1,  0,  0, -1,  2;
             1, -1,  0,  0, -1,  1;
            -1,  0,  1,  2,  0,  0;
             0, -1,  1, -1,  0,  0;
             0, -1,  0,  0,  0,  0;
             0,  0,  0,  0,  1, -1;
             1,  0, -1,  0,  1,  0;
        ];

        // [1, 0, 0, w, h+2, H] -> [1, 0, 0, w, h, H+3]
        {
            let st = state![1, 0, 0, 10, 10, 0];
            let trans_vec = transcript(&hydra, st, 2);
            let rule = DiffRule::from_trans_vec(&hydra, &trans_vec).unwrap();
            assert!(rule.min <= sd![1, 0, 0, 0, 2, 0]);
            assert!(
                rule.max
                    >= sdb![
                        Finite(1),
                        Finite(0),
                        Finite(0),
                        Infinity,
                        Infinity,
                        Infinity
                    ]
            );
            assert_eq!(rule.delta, sd![0, 0, 0, 0, -2, 3]);
        }

        // [1, 0, 0, w, 0, H] -> [0, 0, 1, w+2, 0, H]
        {
            let st = state![1, 0, 0, 10, 0, 10];
            let trans_vec = transcript(&hydra, st, 1);
            let rule = DiffRule::from_trans_vec(&hydra, &trans_vec).unwrap();
            assert!(rule.min <= sd![1, 0, 0, 0, 0, 0]);
            assert!(
                rule.max
                    >= sdb![
                        Finite(1),
                        Finite(0),
                        Finite(0),
                        Infinity,
                        Finite(0),
                        Infinity
                    ]
            );
            assert_eq!(rule.delta, sd![-1, 0, 1, 2, 0, 0]);
        }

        // [1, 0, 0, w+1, 1, H] -> [0, 0, 1, w, 0, H+2]
        {
            let st = state![1, 0, 0, 10, 1, 10];
            let trans_vec = transcript(&hydra, st, 2);
            let rule = DiffRule::from_trans_vec(&hydra, &trans_vec).unwrap();
            assert!(rule.min <= sd![1, 0, 0, 1, 1, 0]);
            assert!(
                rule.max
                    >= sdb![
                        Finite(1),
                        Finite(0),
                        Finite(0),
                        Infinity,
                        Finite(1),
                        Infinity
                    ]
            );
            assert_eq!(rule.delta, sd![-1, 0, 1, -1, -1, 2]);
        }

        // [0, 0, 1, w, h, H+1] -> [0, 0, 1, w, h+1, H]
        {
            let st = state![0, 0, 1, 10, 0, 10];
            let trans_vec = transcript(&hydra, st, 1);
            let rule = DiffRule::from_trans_vec(&hydra, &trans_vec).unwrap();
            assert!(rule.min <= sd![0, 0, 1, 0, 0, 1]);
            assert!(
                rule.max
                    >= sdb![
                        Finite(0),
                        Finite(0),
                        Finite(1),
                        Infinity,
                        Infinity,
                        Infinity
                    ]
            );
            assert_eq!(rule.delta, sd![0, 0, 0, 0, 1, -1]);
        }
    }
}
