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
    
    match sim_res {
        crate::simulate::SimResult::Halted { steps, registers } => {
            return DeciderResult::Halt { steps, registers };
        }
        crate::simulate::SimResult::CycleDetected { start_by, period, is_min_start } => {
            return DeciderResult::Infinite(InfiniteReason::Cycle { start_by, period, is_min_start });
        }
        crate::simulate::SimResult::TranslatedCyclerDetected { start_by, period, is_min_start } => {
            return DeciderResult::Infinite(InfiniteReason::TranslatedCycler { start_by, period, is_min_start });
        }
        crate::simulate::SimResult::LimitReached => {
            // Fallback to Bouncers decider
            let bouncers_res = crate::deciders::bouncers::BouncersDecider { step_limit }.decide(prog);
            if let DeciderResult::Infinite(_) = bouncers_res {
                return bouncers_res;
            }
        }
        _ => {
            return DeciderResult::Unknown;
        }
    }
    
    // Polyhedral Guesser is slower, run it after Bouncers
    if let Some(set) = polyhedral_guesser::find_closed_set(prog, false) {
        let cond_strs: Vec<String> = set.conditions.iter().map(|c| c.to_string()).collect();
        let conditions_str = cond_strs.join(", ");
        let state_char = (b'A' + set.state as u8) as char;
        return DeciderResult::Infinite(InfiniteReason::Polyhedral {
            state: state_char,
            conditions: conditions_str,
        });
    }
    
    DeciderResult::Unknown
}
