use crate::program::Program;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InfiniteReason {
    Cycle { start_by: u64, period: u64, is_min_start: bool },
    TranslatedCycler { start_by: u64, period: u64, is_min_start: bool },
    Polyhedral { state: char, conditions: String },
    Semilinear1D { state: char, base: Vec<u32>, period: Vec<u32> },
    Congruence { state: char, moduli: Vec<u32>, seed: Vec<crate::deciders::congruence::Val> },
    Bouncer { start_by: u64, period: u64, is_min_start: bool },
    BackwardsUnreachable,
}

impl InfiniteReason {
    pub fn decider_name(&self) -> &'static str {
        match self {
            InfiniteReason::Cycle { .. } => "Cycle",
            InfiniteReason::TranslatedCycler { .. } => "Translated Cycler",
            InfiniteReason::Polyhedral { .. } => "Polyhedral",
            InfiniteReason::Semilinear1D { .. } => "Semilinear1D",
            InfiniteReason::Congruence { .. } => "Congruence",
            InfiniteReason::Bouncer { .. } => "Bouncer",
            InfiniteReason::BackwardsUnreachable => "Backwards Unreachable",
        }
    }
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
pub mod semilinear1d;
pub mod semilinear1d_guesser;
pub mod congruence;
pub mod congruence_guesser;
pub mod bouncers;
pub mod backwards;

#[derive(Default, Clone, Debug)]
pub struct DeciderStats {
    pub runtimes: Vec<(&'static str, std::time::Duration)>,
}

impl DeciderStats {
    pub fn add_time(&mut self, name: &'static str, duration: std::time::Duration) {
        if let Some(entry) = self.runtimes.iter_mut().find(|(n, _)| *n == name) {
            entry.1 += duration;
        } else {
            self.runtimes.push((name, duration));
        }
    }
}

pub fn decide_with_stats(
    prog: &Program,
    step_limit: u64,
    detect_cycles: bool,
    exact_start: bool,
    use_polyhedral: bool,
    use_semilinear1d: bool,
    use_congruence: bool,
    stats: &mut DeciderStats,
) -> DeciderResult {
    let t0 = std::time::Instant::now();
    let sim_res = crate::simulate::simulate_direct(prog, Some(step_limit), detect_cycles, exact_start, false);
    stats.add_time("Simulate Direct", t0.elapsed());
    if sim_res != DeciderResult::Unknown {
        return sim_res;
    }

    let t0 = std::time::Instant::now();
    let (is_unreachable, _) = crate::deciders::backwards::start_unreachable(prog);
    stats.add_time("Backwards", t0.elapsed());
    if is_unreachable {
        return DeciderResult::Infinite(InfiniteReason::BackwardsUnreachable);
    }

    let t0 = std::time::Instant::now();
    let bouncers_res = crate::deciders::bouncers::BouncersDecider { step_limit }.decide(prog);
    stats.add_time("Bouncers", t0.elapsed());
    if bouncers_res != DeciderResult::Unknown {
        return bouncers_res;
    }
    
    if use_congruence {
        let t0 = std::time::Instant::now();
        let cong_res = congruence_guesser::decide_congruence(prog, step_limit, false);
        stats.add_time("Congruence", t0.elapsed());
        if cong_res != DeciderResult::Unknown {
            return cong_res;
        }
    }

    if use_semilinear1d {
        let t0 = std::time::Instant::now();
        let sl_res = semilinear1d_guesser::decide_semilinear1d(prog, step_limit, false);
        stats.add_time("Semilinear1D", t0.elapsed());
        if sl_res != DeciderResult::Unknown {
            return sl_res;
        }
    }

    if use_polyhedral {
        let t0 = std::time::Instant::now();
        let poly_res = polyhedral_guesser::decide_polyhedral(prog, step_limit);
        stats.add_time("Polyhedral", t0.elapsed());
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
    use_semilinear1d: bool,
    use_congruence: bool,
) -> DeciderResult {
    let mut stats = DeciderStats::default();
    decide_with_stats(prog, step_limit, detect_cycles, exact_start, use_polyhedral, use_semilinear1d, use_congruence, &mut stats)
}
