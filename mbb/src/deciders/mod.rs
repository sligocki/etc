use crate::program::Program;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InfiniteReason {
    Cycle { start_by: u64, period: u64, is_min_start: bool },
    TranslatedCycler { start_by: u64, period: u64, is_min_start: bool },
    Polyhedral { state: char, conditions: String },
    Bouncer { start_by: u64, period: u64, is_min_start: bool },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DeciderResult {
    Halt { steps: u64, registers: Vec<u64> },
    Infinite(InfiniteReason),
    Unknown,
    HitUndefInst(usize),
    HitUndefTarget { pc: usize, branch: crate::simulate::Branch },
    OutOfBounds,
}

pub trait Decider {
    fn decide(&self, prog: &Program) -> DeciderResult;
}
pub mod symbolic;
pub mod polyhedral;
pub mod polyhedral_guesser;
pub mod bouncers;

pub fn decide(
    prog: &Program,
    step_limit: u64,
    detect_cycles: bool,
    exact_start: bool,
) -> DeciderResult {
    let sim_res = crate::simulate::simulate_direct(prog, Some(step_limit), detect_cycles, exact_start, false);
    if !matches!(sim_res, DeciderResult::Unknown) {
        return sim_res;
    }
    
    let bouncers_res = crate::deciders::bouncers::BouncersDecider { step_limit }.decide(prog);
    if !matches!(bouncers_res, DeciderResult::Unknown) {
        return bouncers_res;
    }
    
    let poly_res = polyhedral_guesser::decide_polyhedral(prog);
    if !matches!(poly_res, DeciderResult::Unknown) {
        return poly_res;
    }
    
    DeciderResult::Unknown
}
