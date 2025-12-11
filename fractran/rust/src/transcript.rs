// Evaluate the "transcript" or rule history for a simulation.

use itertools::Itertools;

use crate::program::{Int, Program, State};
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
pub fn step(prog: &Program, state: &mut State) -> Trans {
    let trans = eval_trans(prog, state);
    let instr_num = trans.reg_fail.len();
    if instr_num < prog.num_instrs() {
        prog.instrs[instr_num].apply(state);
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
        Trans { reg_fail: vec![$($x),*] }
    };
}
