use crate::program::Program;
use crate::simulate::{simulate_macro, SimResult};
use crate::deciders::{Decider, DeciderResult, InfiniteReason};

pub struct BouncersDecider {
    pub step_limit: u64,
}

impl Decider for BouncersDecider {
    fn decide(&self, prog: &Program) -> DeciderResult {
        let res = simulate_macro(prog, Some(self.step_limit), true, false, false);
        
        match res {
            SimResult::TranslatedCyclerDetected { start_by, period, is_min_start } => {
                DeciderResult::Infinite(InfiniteReason::Bouncer { start_by, period, is_min_start })
            }
            SimResult::CycleDetected { start_by, period, is_min_start } => {
                DeciderResult::Infinite(InfiniteReason::Bouncer { start_by, period, is_min_start })
            }
            _ => DeciderResult::Unknown,
        }
    }
}
