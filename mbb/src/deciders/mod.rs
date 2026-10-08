use crate::program::Program;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InfiniteReason {
    Cycle { start_by: u64, period: u64, is_min_start: bool },
    TranslatedCycler { start_by: u64, period: u64, is_min_start: bool },
    Polyhedral { state: char, conditions: String },
    Bouncer { start_by: u64, period: u64, is_min_start: bool },
    BackwardsUnreachable,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HitUndef {
    Inst(usize),
    Target { pc: usize, branch: crate::simulate::Branch },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DeciderResult {
    Halt { steps: u64, registers: Vec<u64>, hit_undef: Option<HitUndef> },
    Infinite(InfiniteReason),
    Unknown,
    Error(String),
}

pub trait Decider {
    fn decide(&self, prog: &Program) -> DeciderResult;
}
pub mod symbolic;
pub mod polyhedral;
pub mod polyhedral_guesser;
pub mod bouncers;
pub mod backwards;

#[derive(Default, Clone, Debug)]
pub struct DeciderStats {
    pub time_simulate_direct: std::time::Duration,
    pub time_bouncers: std::time::Duration,
    pub time_polyhedral: std::time::Duration,
    pub time_backwards: std::time::Duration,
}

pub fn decide_with_stats(
    prog: &Program,
    step_limit: u64,
    detect_cycles: bool,
    exact_start: bool,
    use_polyhedral: bool,
    stats: &mut DeciderStats,
) -> DeciderResult {
    let t0 = std::time::Instant::now();
    let sim_res = crate::simulate::simulate_direct(prog, Some(step_limit), detect_cycles, exact_start, false);
    stats.time_simulate_direct += t0.elapsed();
    if sim_res != DeciderResult::Unknown {
        return sim_res;
    }

    let t0 = std::time::Instant::now();
    let backwards_res = crate::deciders::backwards::BackwardsDecider.decide(prog);
    stats.time_backwards += t0.elapsed();
    if backwards_res != DeciderResult::Unknown {
        return backwards_res;
    }

    let t0 = std::time::Instant::now();
    let bouncers_res = crate::deciders::bouncers::BouncersDecider { step_limit }.decide(prog);
    stats.time_bouncers += t0.elapsed();
    if bouncers_res != DeciderResult::Unknown {
        return bouncers_res;
    }

    if use_polyhedral {
        let t0 = std::time::Instant::now();
        let poly_res = polyhedral_guesser::decide_polyhedral(prog, step_limit);
        stats.time_polyhedral += t0.elapsed();
        if poly_res != DeciderResult::Unknown {
            return poly_res;
        }
    }

    DeciderResult::Unknown
}

pub fn decide(
    prog: &Program,
    step_limit: u64,
    detect_cycles: bool,
    exact_start: bool,
    use_polyhedral: bool,
) -> DeciderResult {
    let mut stats = DeciderStats::default();
    decide_with_stats(prog, step_limit, detect_cycles, exact_start, use_polyhedral, &mut stats)
}
