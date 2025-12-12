// The simplest transition rules in which each register changes by a fixed constant (aka diff).
// These rules are based upon a fixed sequence of Transitions from a Transcript.

use std::cmp;
use std::fmt;

use infinitable::{Finite, Infinitable, Infinity, NegativeInfinity};
use itertools::izip;

use crate::program::{BigInt, Program, SmallInt, State};
use crate::rule::{ApplyResult, Rule};
use crate::state_diff::{StateDiff, StateDiffBig, StateDiffBound};
use crate::transcript::Trans;

// Inductive Diff Rule based on a Trans.
// If min ≤ state ≤ max:
//    state -> state + delta
#[derive(Debug, PartialEq)]
pub struct DiffRule {
    pub min: StateDiff,
    pub max: StateDiffBound,
    pub delta: StateDiff,
    pub num_steps: SmallInt,
}

impl DiffRule {
    // Create a no-op DiffRule that always applies and does nothing.
    pub fn noop(size: usize) -> DiffRule {
        DiffRule {
            min: StateDiff::new(vec![0; size]),
            max: StateDiffBound::new(vec![Infinity; size]),
            delta: StateDiff::new(vec![0; size]),
            num_steps: 0,
        }
    }

    // Compute DiffRule corresponding to an single transition if possible.
    // Based on one transition, the delta is just the applicable rule and
    // the min is just the the negation of all the negaive values in rule.
    // The max is based off of all the previous instrs failing to apply and
    // depends on the specific Trans.reg_fail values.
    // Only fails (returns None) if trans is a halting transition (no rule applies).
    pub fn from_trans(prog: &Program, trans: &Trans) -> Option<DiffRule> {
        if trans.reg_fail.len() >= prog.num_instrs() {
            return None;
        }
        let mut max_vals: Vec<Infinitable<SmallInt>> = vec![Infinity; prog.num_registers()];
        for (rule, reg_fail) in prog.instrs.iter().zip(trans.reg_fail.iter()) {
            // if rule r += -n failed, then r <= n-1
            let max_val = (-rule.data[*reg_fail]) - 1;
            max_vals[*reg_fail] = cmp::min(max_vals[*reg_fail].clone(), Finite(max_val.into()));
        }
        let delta: Vec<SmallInt> = prog.instrs[trans.reg_fail.len()]
            .data
            .iter()
            .map(|x| (*x).into())
            .collect();
        let min_vals: Vec<SmallInt> = delta.iter().map(|n| if *n < 0 { -n } else { 0 }).collect();
        Some(DiffRule {
            min: StateDiff::new(min_vals),
            max: StateDiffBound::new(max_vals),
            delta: StateDiff::new(delta),
            num_steps: 1,
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
                num_steps: self.num_steps + other.num_steps,
            })
        } else {
            None
        }
    }
}

impl Rule for DiffRule {
    // Can a rule be applied at all?
    fn is_applicable(&self, state: &State) -> bool {
        for ((min, max), val) in self
            .min
            .data
            .iter()
            .zip(self.max.data.iter())
            .zip(state.data.iter())
        {
            if val < min {
                return false;
            }
            if let Finite(max_f) = max
                && val > max_f
            {
                return false;
            }
        }
        // All values are in the correct range
        return true;
    }

    // Apply this DiffRull as many times as possible to a given state.
    // Returns None if rule applies infinitely.
    fn apply(&self, state: &State) -> ApplyResult {
        if !self.is_applicable(state) {
            return ApplyResult::None;
        }
        // Return number of times del can be applied to val, while staying withing min to max.
        // Returns None, if there is no limit.
        fn num_apps_reg(
            val: BigInt,
            min: SmallInt,
            max: Infinitable<SmallInt>,
            del: SmallInt,
        ) -> Option<BigInt> {
            if del < 0 {
                // Applies as long as val >= min, reducing by -del each time.
                // This happens (val - min) / -del times and then one more.
                Some((val - min) / -del + 1)
            } else if del > 0
                && let Finite(max_f) = max
            {
                Some((max_f - val) / del + 1)
            } else {
                None
            }
        }
        let num_apps_op = izip!(
            &state.data,
            &self.min.data,
            &self.max.data,
            &self.delta.data
        )
        .filter_map(|(val, min, max, del)| num_apps_reg(val.clone(), *min, *max, *del))
        .min();

        match num_apps_op {
            None => ApplyResult::Infinite,
            Some(num_apps) => {
                let mut result = StateDiffBig::new(state.data.clone());
                result += &self.delta * &num_apps;
                ApplyResult::Some {
                    result: State { data: result.data },
                    num_apps: num_apps.clone(),
                    base_steps: self.num_steps * num_apps,
                }
            }
        }
    }
}

fn inf_str(val: &Infinitable<SmallInt>) -> String {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::program::{Instr, State};
    use crate::transcript::{eval_trans, transcript};
    use crate::{prog, sd, sdb, state, trans};

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
            num_steps: 1,
        };
        assert_eq!(eval_trans(&prog, &sa), ta);
        assert_eq!(DiffRule::from_trans(&prog, &ta), Some(ra));

        let sb = state![1, 2, 0];
        let tb = trans![2];
        let rb = DiffRule {
            max: sdb![Infinity, Infinity, Finite(0)],
            min: sd![1, 0, 0],
            delta: sd![-1, 2, 0],
            num_steps: 1,
        };
        assert_eq!(eval_trans(&prog, &sb), tb);
        assert_eq!(DiffRule::from_trans(&prog, &tb), Some(rb));

        let sc = state![1, 0, 3];
        let tc = trans![1];
        let rc = DiffRule {
            max: sdb![Infinity, Finite(0), Infinity],
            min: sd![1, 0, 0],
            delta: sd![-1, 2, 0],
            num_steps: 1,
        };
        assert_eq!(eval_trans(&prog, &sc), tc);
        assert_eq!(DiffRule::from_trans(&prog, &tc), Some(rc));

        let sd = state![0, 0, 3];
        let td = trans![1, 0];
        let rd = DiffRule {
            max: sdb![Finite(0), Finite(0), Infinity],
            min: sd![0, 0, 2],
            delta: sd![0, 1, -2],
            num_steps: 1,
        };
        assert_eq!(eval_trans(&prog, &sd), td);
        assert_eq!(DiffRule::from_trans(&prog, &td), Some(rd));

        let se = state![0, 0, 1];
        let te = trans![1, 0, 2];
        assert_eq!(eval_trans(&prog, &se), te);
        assert_eq!(DiffRule::from_trans(&prog, &te), None);
    }

    #[test]
    fn test_apply() {
        // Simple rule with only one decrementing index.
        let rule = DiffRule {
            max: sdb![Infinity, Infinity],
            min: sd![0, 1],
            delta: sd![1, -1],
            num_steps: 1,
        };
        assert_eq!(
            rule.apply(&state![8, 13]),
            ApplyResult::Some {
                result: state![21, 0],
                num_apps: 13.into(),
                base_steps: 13.into(),
            }
        );

        // Multiple decrementing
        let rule = DiffRule {
            max: sdb![Infinity, Infinity, Infinity],
            min: sd![0, 1, 2],
            delta: sd![2, -1, -1],
            num_steps: 1,
        };
        assert_eq!(
            rule.apply(&state![8, 13, 7]),
            ApplyResult::Some {
                result: state![20, 7, 1],
                num_apps: 6.into(),
                base_steps: 6.into(),
            }
        );

        // Larger decrease
        let rule = DiffRule {
            max: sdb![Infinity, Infinity, Infinity],
            min: sd![0, 6, 2],
            delta: sd![1, -3, -2],
            num_steps: 1,
        };
        assert_eq!(
            rule.apply(&state![8, 13, 5]),
            ApplyResult::Some {
                result: state![10, 7, 1],
                num_apps: 2.into(),
                base_steps: 2.into(),
            }
        );
        assert_eq!(
            rule.apply(&state![8, 13, 10]),
            ApplyResult::Some {
                result: state![11, 4, 4],
                num_apps: 3.into(),
                base_steps: 3.into(),
            }
        );

        // Infinite rule
        let rule = DiffRule {
            max: sdb![Infinity, Infinity],
            min: sd![0, 1],
            delta: sd![1, 1],
            num_steps: 1,
        };
        assert_eq!(rule.apply(&state![8, 13]), ApplyResult::Infinite);

        // Rule doesn't apply at all
        let rule = DiffRule {
            max: sdb![Infinity, Infinity],
            min: sd![0, 2],
            delta: sd![1, -1],
            num_steps: 1,
        };
        assert_eq!(rule.apply(&state![8, 1]), ApplyResult::None);

        let rule = DiffRule {
            max: sdb![Infinity, Finite(138)],
            min: sd![0, 1],
            delta: sd![0, 1],
            num_steps: 1,
        };
        assert_eq!(
            rule.apply(&state![8, 13]),
            ApplyResult::Some {
                result: state![8, 139],
                num_apps: 126.into(),
                base_steps: 126.into(),
            }
        );

        let rule = DiffRule {
            max: sdb![Finite(17), Infinity],
            min: sd![0, 1],
            delta: sd![1, -1],
            num_steps: 1,
        };
        assert_eq!(
            rule.apply(&state![8, 13]),
            ApplyResult::Some {
                result: state![18, 3],
                num_apps: 10.into(),
                base_steps: 10.into(),
            }
        );
    }

    #[test]
    fn test_hydra() {
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
