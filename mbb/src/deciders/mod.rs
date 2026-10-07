use crate::program::Program;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DeciderResult {
    Halt,
    NonHalt,
    Unknown,
}

pub trait Decider {
    fn decide(&self, prog: &Program) -> DeciderResult;
}
pub mod symbolic;
pub mod polyhedral;
pub mod polyhedral_guesser;

pub enum DecideResult {
    Sim(crate::simulate::SimResult),
    Polyhedral { state: usize, conditions_str: String },
}

pub fn decide(
    prog: &Program,
    step_limit: u64,
    detect_cycles: bool,
    exact_start: bool,
    use_transfer: bool,
) -> DecideResult {
    let sim_res = crate::simulate::simulate(prog, Some(step_limit), detect_cycles, exact_start, use_transfer, false);
    
    if matches!(sim_res, crate::simulate::SimResult::LimitReached) {
        if let Some(set) = polyhedral_guesser::find_closed_set(prog, false) {
            let cond_strs: Vec<String> = set.conditions.iter().map(|c| c.to_string()).collect();
            return DecideResult::Polyhedral {
                state: set.state,
                conditions_str: cond_strs.join(", "),
            };
        }
    }
    
    DecideResult::Sim(sim_res)
}
