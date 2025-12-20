// Evaluate the "transcript" or rule history for a simulation.

use itertools::Itertools;

use crate::program::{Program, State};
use crate::tandem_repeat::{RepBlock, ToStringVec};

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
        let instr_num = self.reg_fail.len() as u8;
        let instr_char = (OFFSET + instr_num) as char;
        instr_char.to_string()
    }

    fn to_string_vec(xs: &Vec<Self>) -> String {
        xs.iter().map(|x| x.to_string_one()).join("")
    }
}

// Evaluate details of which rule applies and why prev do not.
pub fn eval_trans(prog: &Program, state: &State) -> Trans {
    let mut reg_fail: Vec<usize> = Vec::new();
    for instr in prog.instrs.iter() {
        match instr.can_apply(state) {
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
pub fn step(prog: &Program, state: &mut State) -> Option<Trans> {
    let trans = eval_trans(prog, state);
    let instr_num = trans.reg_fail.len();
    if instr_num < prog.num_instrs() {
        prog.instrs[instr_num].apply(state);
        Some(trans)
    } else {
        // Halted
        None
    }
}

// Simulate for num_steps keeping track of Trans at each step.
pub fn transcript(prog: &Program, mut state: State, num_steps: usize) -> Vec<Trans> {
    let mut ret: Vec<Trans> = Vec::new();
    for _ in 0..num_steps {
        if let Some(trans) = step(prog, &mut state) {
            ret.push(trans)
        } else {
            // Halted
            break;
        }
    }
    ret
}

/// Block of transitions stripped of explicit repeat count (only whether it is repeated or not).
#[derive(Debug, PartialEq, Clone)]
pub struct StrippedBlock {
    pub block: Vec<Trans>,
    pub is_rep: bool,
}

impl ToStringVec for StrippedBlock {
    fn to_string_one(&self) -> String {
        let mut ret = Trans::to_string_vec(&self.block);
        if self.is_rep {
            ret.push_str("+");
        }
        ret
    }

    fn to_string_vec(xs: &Vec<Self>) -> String {
        format!("({})", xs.iter().map(|x| x.to_string_one()).join(" "))
    }
}

/// Strip repeat counts from a RepBlock
pub fn strip_reps(rep_blocks: Vec<RepBlock<Trans>>) -> Vec<StrippedBlock> {
    rep_blocks
        .into_iter()
        .map(|r| StrippedBlock {
            block: r.block,
            is_rep: r.rep > 1,
        })
        .collect()
}

#[macro_export]
macro_rules! trans {
    ($($x:expr),* $(,)?) => {
        $crate::transcript::Trans { reg_fail: vec![$($x),*] }
    };
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{prog, state};

    #[test]
    fn test_small() {
        // Size 8 champion
        let prog = prog![-1,  4;
                          0, -1];
        let start_state = state![1, 0];
        let trans_vec = transcript(&prog, start_state, 10);
        // Halts in 5 steps
        assert_eq!(trans_vec.len(), 5);
        // List of rules used
        let rules: Vec<usize> = trans_vec.iter().map(|x| x.reg_fail.len()).collect();
        assert_eq!(rules, vec![0, 1, 1, 1, 1]);
        // Exact vector of Trans
        assert_eq!(
            trans_vec,
            vec![trans![], trans![0], trans![0], trans![0], trans![0],]
        );
    }

    #[test]
    fn test_medium() {
        // Size 14 champion
        let prog = prog![-1,  5,  0;
                          0, -1,  3;
                          0,  0, -1];
        let start_state = state![1, 0, 0];
        let trans_vec = transcript(&prog, start_state, 100);
        // Halts in 5 steps
        assert_eq!(trans_vec.len(), 21);
        // List of rules used
        let rules: Vec<usize> = trans_vec.iter().map(|x| x.reg_fail.len()).collect();
        let expected_rules = [&vec![0][..], &vec![1; 5][..], &vec![2; 15][..]].concat();
        assert_eq!(rules, expected_rules);
    }
}
