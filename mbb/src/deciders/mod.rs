use crate::program::Program;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InfiniteReason {
    Cycle { start_by: u64, period: u64, is_min_start: bool },
    TranslatedCycler { start_by: u64, period: u64, is_min_start: bool },
    Polyhedral { state: char, conditions: String },
    Bouncer { start_by: u64, period: u64, is_min_start: bool },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HitUndef {
    Inst(usize),
    Target { pc: usize, branch: crate::simulate::Branch },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum UnknownReason {
    /// Simulation exceeded the maximum allowed step limit without halting or definitively proving infinite behavior.
    StepLimitReached,
    /// Simulation execution jumped to an instruction index outside the program's defined bounds.
    OutOfBounds,
    /// A heuristic decider (like Polyhedral or Bouncers) could not definitively prove the program's behavior.
    Undecided,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DeciderResult {
    Halt { steps: u64, registers: Vec<u64>, hit_undef: Option<HitUndef> },
    Infinite(InfiniteReason),
    Unknown(UnknownReason),
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
    
    if let DeciderResult::Unknown(UnknownReason::StepLimitReached) = sim_res {
        let bouncers_res = crate::deciders::bouncers::BouncersDecider { step_limit }.decide(prog);
        if let DeciderResult::Infinite(_) = bouncers_res {
            return bouncers_res;
        }
        
        let poly_res = polyhedral_guesser::decide_polyhedral(prog);
        if let DeciderResult::Infinite(_) = poly_res {
            return poly_res;
        }
        
        return sim_res;
    }
    
    sim_res
}
