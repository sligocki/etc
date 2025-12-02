// Evaluate the "transcript" or rule history for a simulation.

use itertools::Itertools;

use crate::program::{Int, Program, State};
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

#[macro_export]
macro_rules! trans {
    ($($x:expr),* $(,)?) => {
        Trans { reg_fail: vec![$($x),*] }
    };
}
