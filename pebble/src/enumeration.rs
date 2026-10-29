use crate::deciders::{
    check_edge_glider_sparse, decide_bouncer_outcome, decide_ctl_from_sim_outcome_with_params,
    decide_cycler_from_sim, decide_separated_components_from_sim, decide_static_backtrack, Decider,
    StepDeciderOutcome,
};
use crate::io::{format_count, read_records_from_file, write_records_to_file, ProgramRecord};
use crate::program::{Program, Rule};
use crate::simulation::{SimOutcome, Simulator};
use clap::Parser;
use std::collections::BTreeMap;
use std::fmt;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::time::{Duration, Instant};

pub static STOP_REQUESTED: AtomicBool = AtomicBool::new(false);
pub static INTERRUPTED: AtomicBool = AtomicBool::new(false);
static INTERRUPT_COUNT: AtomicUsize = AtomicUsize::new(0);

#[cfg(unix)]
extern "C" fn sigint_handler(_sig: std::os::raw::c_int) {
    let count = INTERRUPT_COUNT.fetch_add(1, Ordering::SeqCst) + 1;
    if count == 1 {
        STOP_REQUESTED.store(true, Ordering::SeqCst);
        INTERRUPTED.store(true, Ordering::SeqCst);
        let msg = b"\nInterrupted! Stopping gracefully and printing report (press Ctrl+C again to force exit)...\n";
        extern "C" {
            fn write(fd: std::os::raw::c_int, buf: *const u8, count: usize) -> isize;
        }
        unsafe {
            let _ = write(2, msg.as_ptr(), msg.len());
        }
    } else {
        std::process::exit(130);
    }
}

#[cfg(unix)]
pub fn register_signal_handler() {
    extern "C" {
        fn signal(
            sig: std::os::raw::c_int,
            handler: extern "C" fn(std::os::raw::c_int),
        ) -> extern "C" fn(std::os::raw::c_int);
    }
    unsafe {
        signal(2, sigint_handler);  // SIGINT (Ctrl+C)
        signal(15, sigint_handler); // SIGTERM
    }
}

#[cfg(not(unix))]
pub fn register_signal_handler() {}

#[inline]
pub fn is_interrupted() -> bool {
    INTERRUPTED.load(Ordering::SeqCst)
}

#[inline]
pub fn reset_interrupted() {
    INTERRUPTED.store(false, Ordering::SeqCst);
    STOP_REQUESTED.store(false, Ordering::SeqCst);
    INTERRUPT_COUNT.store(0, Ordering::SeqCst);
}

/// Configuration parameters for the CTL pipeline stage.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CtlConfig {
    pub steps: u64,
    pub max_states: usize,
    pub split_thresh: Vec<usize>,
    pub floors: Vec<usize>,
    pub moduli: Vec<usize>,
}

pub type Ctl = CtlConfig;

impl Default for CtlConfig {
    fn default() -> Self {
        Self {
            steps: 100,
            max_states: 1024,
            split_thresh: vec![2],
            floors: vec![6],
            moduli: vec![1, 2, 3, 4, 6, 12],
        }
    }
}

impl CtlConfig {
    pub fn new(steps: u64) -> Self {
        Self {
            steps,
            ..Default::default()
        }
    }

    pub fn with_states(mut self, max_states: usize) -> Self {
        self.max_states = max_states;
        self
    }

    pub fn with_split_thresh(mut self, split_thresh: Vec<usize>) -> Self {
        self.split_thresh = split_thresh;
        self
    }

    pub fn with_floors(mut self, floors: Vec<usize>) -> Self {
        self.floors = floors;
        self
    }

    pub fn with_moduli(mut self, moduli: Vec<usize>) -> Self {
        self.moduli = moduli;
        self
    }
}

impl From<CtlConfig> for PipelineStage {
    fn from(cfg: CtlConfig) -> Self {
        PipelineStage::Ctl(cfg)
    }
}

/// Individual pipeline stage identifier in order of execution.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PipelineStage {
    /// Simulation of the program up to `steps` (splitting on missing rules).
    Simulation { steps: u64 },
    /// Static backtracking analysis on program rules.
    StaticBacktrack,
    /// Edge glider analysis on the current simulation tape.
    EdgeGliderCurrent,
    /// Cycler and translated cycler detection up to `steps`.
    Cycler { steps: u64 },
    /// Separated components detection up to `steps`.
    SeparatedComponents { steps: u64 },
    /// Bouncer detection up to `steps`.
    Bouncer { steps: u64 },
    /// CTL regular language verification up to `steps`.
    Ctl(CtlConfig),
}

impl PipelineStage {
    /// Convenience constructor for a default CTL stage with specified steps.
    pub fn ctl(steps: u64) -> Self {
        PipelineStage::Ctl(CtlConfig::new(steps))
    }

    /// Returns true if this stage is a mathematical decider (as opposed to raw simulation).
    #[inline]
    pub fn is_decider(&self) -> bool {
        !matches!(self, PipelineStage::Simulation { .. })
    }

    /// Automatically generates a descriptive name based on the stage type and its parameters.
    pub fn name(&self) -> String {
        match self {
            PipelineStage::StaticBacktrack => "StaticBacktrack".to_string(),
            PipelineStage::Simulation { steps } => format!("Simulation ({steps} steps)"),
            PipelineStage::EdgeGliderCurrent => "EdgeGliderCurrent".to_string(),
            PipelineStage::Cycler { steps } => format!("Cycler ({steps} steps)"),
            PipelineStage::SeparatedComponents { steps } => {
                format!("SeparatedComponents ({steps} steps)")
            }
            PipelineStage::Bouncer { steps } => format!("Bouncer ({steps} steps)"),
            PipelineStage::Ctl(cfg) => {
                let default_floors = &[6];
                let default_moduli = &[1, 2, 3, 4, 6, 12];
                let default_split = &[2];
                if cfg.max_states == 1024
                    && cfg.split_thresh.as_slice() == default_split
                    && cfg.floors.as_slice() == default_floors
                    && cfg.moduli.as_slice() == default_moduli
                {
                    format!("CTL ({} steps)", cfg.steps)
                } else {
                    let mut extra = Vec::new();
                    if cfg.max_states != 1024 {
                        extra.push(format!("states={}", cfg.max_states));
                    }
                    if cfg.split_thresh.as_slice() != default_split {
                        extra.push(format!("thresh={:?}", cfg.split_thresh));
                    }
                    if cfg.floors.as_slice() != default_floors {
                        extra.push(format!("floors={:?}", cfg.floors));
                    }
                    if cfg.moduli.as_slice() != default_moduli {
                        extra.push(format!("moduli={:?}", cfg.moduli));
                    }
                    format!("CTL ({} steps, {})", cfg.steps, extra.join(", "))
                }
            }
        }
    }
}

impl fmt::Display for PipelineStage {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name())
    }
}

/// Overall pipeline configuration defining the execution stages.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PipelineConfig {
    pub stages: Vec<PipelineStage>,
}

impl PipelineConfig {
    /// Generates the data-driven default pipeline configuration for a given program size and maximum steps.
    pub fn default_for(_size: usize, early_steps: u64, deep_steps: u64) -> Self {
        let mut stages = vec![
            PipelineStage::StaticBacktrack,
            PipelineStage::Simulation { steps: early_steps },
            PipelineStage::Cycler { steps: early_steps },
            PipelineStage::SeparatedComponents { steps: early_steps },
            PipelineStage::Bouncer { steps: early_steps },
            PipelineStage::Ctl(CtlConfig {
                steps: early_steps,
                ..Default::default()
            }),
        ];

        if deep_steps > early_steps {
            stages.push(PipelineStage::Simulation { steps: deep_steps });
            stages.push(PipelineStage::Cycler { steps: deep_steps });
            stages.push(PipelineStage::SeparatedComponents { steps: deep_steps });
            stages.push(PipelineStage::Bouncer { steps: deep_steps });
            stages.push(PipelineStage::Ctl(CtlConfig {
                steps: deep_steps,
                ..Default::default()
            }));
        }

        Self { stages }
    }

    /// Index of the primary simulation stage in `stages`.
    #[inline]
    pub fn sim_stage_index(&self) -> usize {
        self.stages
            .iter()
            .position(|s| matches!(s, PipelineStage::Simulation { .. }))
            .unwrap_or(0)
    }

    /// Returns the maximum simulation step count found in any stage of the pipeline.
    pub fn max_simulation_steps(&self) -> u64 {
        self.stages
            .iter()
            .filter_map(|s| match s {
                PipelineStage::Simulation { steps } => Some(*steps),
                _ => None,
            })
            .max()
            .unwrap_or(0)
    }
}

/// Execution metrics tracked for a single pipeline stage or decider.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct StageMetrics {
    pub invocations: u64,
    pub splits: u64,
    pub decided_halting: u64,
    pub decided_inf: u64,
    pub total_time_nanos: u64,
}

impl StageMetrics {
    pub fn merge(&mut self, other: &StageMetrics) {
        self.invocations += other.invocations;
        self.splits += other.splits;
        self.decided_halting += other.decided_halting;
        self.decided_inf += other.decided_inf;
        self.total_time_nanos += other.total_time_nanos;
    }

    pub fn total_time(&self) -> Duration {
        Duration::from_nanos(self.total_time_nanos)
    }

    pub fn avg_time(&self) -> Option<Duration> {
        if self.invocations == 0 {
            None
        } else {
            Some(Duration::from_nanos(self.total_time_nanos / self.invocations))
        }
    }
}

/// Result item produced when enumerating and simulating a TNF program.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EnumEntry {
    pub program: Program,
    pub outcome: SimOutcome,
}

/// Recorded report for a single stage in the execution pipeline.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct StageReport {
    pub name: String,
    pub metrics: StageMetrics,
}

/// Summary statistics accumulated across a TNF enumeration run.
#[derive(Debug, Clone, Default)]
pub struct EnumStats {
    pub size: usize,
    pub max_steps: u64,
    /// Number of TNF programs enumerated and simulated.
    pub total_programs: u64,
    /// Number of enumerated TNF programs that halted.
    pub halted_programs: u64,
    /// Number of enumerated TNF programs proven infinite by the decider pipeline.
    pub inf_programs: u64,
    /// Breakdown of infinite programs by decider:
    /// `[EdgeGlider, Cycler, SeparatedComponents, Bouncer, Ctl, StaticBacktrack]`.
    pub decided_by_kind: [u64; 6],
    /// Maximum halting step count observed across all halted programs.
    pub max_halting_steps: Option<u64>,
    /// Minimum halting step count observed across all halted programs.
    pub min_halting_steps: Option<u64>,
    /// Total halting steps simulated across all halted programs.
    pub total_halting_steps: u64,
    /// Number of halted programs that halted in 0 steps (if any).
    pub halting_zero_steps: u64,
    /// Distribution of halting step counts bucketed by power of two: [2^k, 2^{k+1}) -> count.
    pub halting_step_histogram: std::collections::BTreeMap<u32, u64>,
    /// First champion program achieving `max_halting_steps`.
    pub champion: Option<Program>,
    /// Runtime and decision metrics for each pipeline stage.
    pub stages: Vec<StageReport>,
    /// Number of CTL proofs found.
    pub ctl_proofs_count: u64,
    /// Minimum steps simulated across CTL proofs.
    pub ctl_min_steps: u64,
    /// Maximum steps simulated across CTL proofs.
    pub ctl_max_steps: u64,
    /// Total steps simulated across CTL proofs.
    pub ctl_total_steps: u64,
    /// Minimum states in closed language across CTL proofs.
    pub ctl_min_states: usize,
    /// Maximum states in closed language across CTL proofs.
    pub ctl_max_states: usize,
    /// Total states in closed language across CTL proofs.
    pub ctl_total_states: u64,
    /// Distribution of floors in CTL proofs.
    pub ctl_floor_counts: std::collections::BTreeMap<usize, u64>,
    /// Distribution of moduli in CTL proofs.
    pub ctl_mod_counts: std::collections::BTreeMap<usize, u64>,

    /// Number of Cycler proofs found.
    pub cycler_proofs_count: u64,
    pub cycler_min_period: u64,
    pub cycler_max_period: u64,
    pub cycler_total_period: u64,
    pub cycler_period_counts: std::collections::BTreeMap<u64, u64>,
    pub cycler_dx_counts: std::collections::BTreeMap<isize, u64>,

    /// Number of SeparatedComponents proofs found.
    pub sep_comp_proofs_count: u64,
    pub sep_comp_min_period: u64,
    pub sep_comp_max_period: u64,
    pub sep_comp_total_period: u64,
    pub sep_comp_period_counts: std::collections::BTreeMap<u64, u64>,

    /// Number of Bouncer proofs found.
    pub bouncer_proofs_count: u64,
    pub bouncer_min_bounce_steps: u64,
    pub bouncer_max_bounce_steps: u64,
    pub bouncer_total_bounce_steps: u64,
    pub bouncer_bounce_steps_counts: std::collections::BTreeMap<u64, u64>,
    pub bouncer_gap_growth_counts: std::collections::BTreeMap<usize, u64>,
}

impl PartialEq for EnumStats {
    fn eq(&self, other: &Self) -> bool {
        self.size == other.size
            && self.max_steps == other.max_steps
            && self.total_programs == other.total_programs
            && self.halted_programs == other.halted_programs
            && self.inf_programs == other.inf_programs
            && self.decided_by_kind == other.decided_by_kind
            && self.max_halting_steps == other.max_halting_steps
            && self.min_halting_steps == other.min_halting_steps
            && self.total_halting_steps == other.total_halting_steps
            && self.halting_zero_steps == other.halting_zero_steps
            && self.halting_step_histogram == other.halting_step_histogram
            && self.champion == other.champion
            && self.ctl_proofs_count == other.ctl_proofs_count
            && self.ctl_min_steps == other.ctl_min_steps
            && self.ctl_max_steps == other.ctl_max_steps
            && self.ctl_total_steps == other.ctl_total_steps
            && self.ctl_min_states == other.ctl_min_states
            && self.ctl_max_states == other.ctl_max_states
            && self.ctl_total_states == other.ctl_total_states
            && self.ctl_floor_counts == other.ctl_floor_counts
            && self.ctl_mod_counts == other.ctl_mod_counts
            && self.cycler_proofs_count == other.cycler_proofs_count
            && self.cycler_period_counts == other.cycler_period_counts
            && self.cycler_dx_counts == other.cycler_dx_counts
            && self.sep_comp_proofs_count == other.sep_comp_proofs_count
            && self.sep_comp_period_counts == other.sep_comp_period_counts
            && self.bouncer_proofs_count == other.bouncer_proofs_count
            && self.bouncer_bounce_steps_counts == other.bouncer_bounce_steps_counts
            && self.bouncer_gap_growth_counts == other.bouncer_gap_growth_counts
    }
}

impl Eq for EnumStats {}

impl EnumStats {
    pub fn new(size: usize, early_steps: u64, deep_steps: u64) -> Self {
        let pipeline = PipelineConfig::default_for(size, early_steps, deep_steps);
        Self::with_pipeline(size, deep_steps, &pipeline)
    }

    /// Create a fresh statistics accumulator configured with an explicit `PipelineConfig`.
    pub fn with_pipeline(size: usize, max_steps: u64, pipeline: &PipelineConfig) -> Self {
        let stages = pipeline
            .stages
            .iter()
            .map(|s| StageReport {
                name: s.name(),
                metrics: StageMetrics::default(),
            })
            .collect();
        Self {
            size,
            max_steps,
            stages,
            ..Self::default()
        }
    }

    /// Record a single `EnumEntry` into the running statistics.
    pub fn record(&mut self, entry: &EnumEntry) {
        self.total_programs += 1;

        match entry.outcome {
            SimOutcome::Halted { steps } => {
                self.halted_programs += 1;
                self.total_halting_steps += steps;

                if self.min_halting_steps.is_none() || Some(steps) < self.min_halting_steps {
                    self.min_halting_steps = Some(steps);
                }

                let is_new_max = match self.max_halting_steps {
                    None => true,
                    Some(prev_max) => steps > prev_max,
                };
                if is_new_max {
                    self.max_halting_steps = Some(steps);
                    self.champion = Some(entry.program.clone());
                }

                if steps == 0 {
                    self.halting_zero_steps += 1;
                } else {
                    let k = steps.ilog2();
                    *self.halting_step_histogram.entry(k).or_insert(0) += 1;
                }
            }
            SimOutcome::Inf { decider, .. } => {
                self.inf_programs += 1;
                let idx = match decider {
                    Decider::EdgeGlider => 0,
                    Decider::Cycler(proof_opt) => {
                        if let Some(proof) = proof_opt {
                            self.cycler_proofs_count += 1;
                            if self.cycler_proofs_count == 1 {
                                self.cycler_min_period = proof.period;
                                self.cycler_max_period = proof.period;
                            } else {
                                self.cycler_min_period = self.cycler_min_period.min(proof.period);
                                self.cycler_max_period = self.cycler_max_period.max(proof.period);
                            }
                            self.cycler_total_period += proof.period;
                            *self.cycler_period_counts.entry(proof.period).or_insert(0) += 1;
                            *self.cycler_dx_counts.entry(proof.dx).or_insert(0) += 1;
                        }
                        1
                    }
                    Decider::SeparatedComponents(proof_opt) => {
                        if let Some(proof) = proof_opt {
                            self.sep_comp_proofs_count += 1;
                            if self.sep_comp_proofs_count == 1 {
                                self.sep_comp_min_period = proof.period;
                                self.sep_comp_max_period = proof.period;
                            } else {
                                self.sep_comp_min_period = self.sep_comp_min_period.min(proof.period);
                                self.sep_comp_max_period = self.sep_comp_max_period.max(proof.period);
                            }
                            self.sep_comp_total_period += proof.period;
                            *self.sep_comp_period_counts.entry(proof.period).or_insert(0) += 1;
                        }
                        2
                    }
                    Decider::Bouncer(proof_opt) => {
                        if let Some(proof) = proof_opt {
                            self.bouncer_proofs_count += 1;
                            if self.bouncer_proofs_count == 1 {
                                self.bouncer_min_bounce_steps = proof.bounce_steps;
                                self.bouncer_max_bounce_steps = proof.bounce_steps;
                            } else {
                                self.bouncer_min_bounce_steps =
                                    self.bouncer_min_bounce_steps.min(proof.bounce_steps);
                                self.bouncer_max_bounce_steps =
                                    self.bouncer_max_bounce_steps.max(proof.bounce_steps);
                            }
                            self.bouncer_total_bounce_steps += proof.bounce_steps;
                            *self
                                .bouncer_bounce_steps_counts
                                .entry(proof.bounce_steps)
                                .or_insert(0) += 1;
                            *self
                                .bouncer_gap_growth_counts
                                .entry(proof.gap_growth)
                                .or_insert(0) += 1;
                        }
                        3
                    }
                    Decider::Ctl(proof_opt) => {
                        if let Some(proof) = proof_opt {
                            self.ctl_proofs_count += 1;
                            if self.ctl_proofs_count == 1 {
                                self.ctl_min_steps = proof.num_steps;
                                self.ctl_max_steps = proof.num_steps;
                                self.ctl_min_states = proof.num_states;
                                self.ctl_max_states = proof.num_states;
                            } else {
                                self.ctl_min_steps = self.ctl_min_steps.min(proof.num_steps);
                                self.ctl_max_steps = self.ctl_max_steps.max(proof.num_steps);
                                self.ctl_min_states = self.ctl_min_states.min(proof.num_states);
                                self.ctl_max_states = self.ctl_max_states.max(proof.num_states);
                            }
                            self.ctl_total_steps += proof.num_steps;
                            self.ctl_total_states += proof.num_states as u64;
                            *self.ctl_floor_counts.entry(proof.floor).or_insert(0) += 1;
                            *self.ctl_mod_counts.entry(proof.modulus).or_insert(0) += 1;
                        }
                        4
                    }
                    Decider::StaticBacktrack => 5,
                };
                self.decided_by_kind[idx] += 1;
            }
            SimOutcome::Unknown { .. } | SimOutcome::MissingRule { .. } => {}
        }
    }

    /// Return the count of programs decided by a specific `Decider`.
    pub fn decided_count(&self, decider: Decider) -> u64 {
        let idx = match decider {
            Decider::EdgeGlider => 0,
            Decider::Cycler(_) => 1,
            Decider::SeparatedComponents(_) => 2,
            Decider::Bouncer(_) => 3,
            Decider::Ctl(_) => 4,
            Decider::StaticBacktrack => 5,
        };
        self.decided_by_kind[idx]
    }

    /// Number of remaining undecided unknown programs (`total - halted - inf`).
    #[inline]
    pub fn unknown_programs(&self) -> u64 {
        self.total_programs
            .saturating_sub(self.halted_programs)
            .saturating_sub(self.inf_programs)
    }

    /// Backward-compatibility alias for `unknown_programs`.
    #[inline]
    pub fn holdout_programs(&self) -> u64 {
        self.unknown_programs()
    }

    /// Backward-compatibility alias for `inf_programs`.
    #[inline]
    pub fn decided_programs(&self) -> u64 {
        self.inf_programs
    }

    /// Percentage of enumerated TNF programs that halted (`0.0..=100.0`).
    pub fn halted_percentage(&self) -> f64 {
        if self.total_programs == 0 {
            0.0
        } else {
            (self.halted_programs as f64 / self.total_programs as f64) * 100.0
        }
    }

    /// Percentage of enumerated TNF programs proven infinite by deciders (`0.0..=100.0`).
    pub fn inf_percentage(&self) -> f64 {
        if self.total_programs == 0 {
            0.0
        } else {
            (self.inf_programs as f64 / self.total_programs as f64) * 100.0
        }
    }

    /// Backward-compatibility alias for `inf_percentage`.
    pub fn decided_percentage(&self) -> f64 {
        self.inf_percentage()
    }

    /// Percentage of enumerated TNF programs that remain undecided holdouts (`0.0..=100.0`).
    pub fn unknown_percentage(&self) -> f64 {
        if self.total_programs == 0 {
            0.0
        } else {
            (self.unknown_programs() as f64 / self.total_programs as f64) * 100.0
        }
    }

    /// Backward-compatibility alias for `unknown_percentage`.
    pub fn holdout_percentage(&self) -> f64 {
        self.unknown_percentage()
    }

    /// Merge an external stage metrics slice into `self`.
    pub fn merge_metrics(&mut self, metrics: &[StageMetrics]) {
        for (stage, m) in self.stages.iter_mut().zip(metrics.iter()) {
            stage.metrics.merge(m);
        }
    }

    /// Merge another `EnumStats` into `self` (preserving first-seen champion on ties).
    pub fn merge(&mut self, other: EnumStats) {
        self.total_programs += other.total_programs;
        self.halted_programs += other.halted_programs;
        self.inf_programs += other.inf_programs;
        for (dst, src) in self
            .decided_by_kind
            .iter_mut()
            .zip(other.decided_by_kind.iter())
        {
            *dst += *src;
        }
        for (dst, src) in self.stages.iter_mut().zip(other.stages.iter()) {
            dst.metrics.merge(&src.metrics);
        }
        if let Some(other_max) = other.max_halting_steps {
            let is_better = match self.max_halting_steps {
                None => true,
                Some(cur_max) => other_max > cur_max,
            };
            if is_better {
                self.max_halting_steps = Some(other_max);
                self.champion = other.champion;
            }
        }
        if let Some(other_min) = other.min_halting_steps {
            self.min_halting_steps = match self.min_halting_steps {
                None => Some(other_min),
                Some(cur_min) => Some(cur_min.min(other_min)),
            };
        }
        self.total_halting_steps += other.total_halting_steps;
        self.halting_zero_steps += other.halting_zero_steps;
        for (k, v) in other.halting_step_histogram {
            *self.halting_step_histogram.entry(k).or_insert(0) += v;
        }
        if other.cycler_proofs_count > 0 {
            if self.cycler_proofs_count == 0 {
                self.cycler_min_period = other.cycler_min_period;
                self.cycler_max_period = other.cycler_max_period;
            } else {
                self.cycler_min_period = self.cycler_min_period.min(other.cycler_min_period);
                self.cycler_max_period = self.cycler_max_period.max(other.cycler_max_period);
            }
            self.cycler_proofs_count += other.cycler_proofs_count;
            self.cycler_total_period += other.cycler_total_period;
            for (k, v) in other.cycler_period_counts {
                *self.cycler_period_counts.entry(k).or_insert(0) += v;
            }
            for (k, v) in other.cycler_dx_counts {
                *self.cycler_dx_counts.entry(k).or_insert(0) += v;
            }
        }
        if other.sep_comp_proofs_count > 0 {
            if self.sep_comp_proofs_count == 0 {
                self.sep_comp_min_period = other.sep_comp_min_period;
                self.sep_comp_max_period = other.sep_comp_max_period;
            } else {
                self.sep_comp_min_period = self.sep_comp_min_period.min(other.sep_comp_min_period);
                self.sep_comp_max_period = self.sep_comp_max_period.max(other.sep_comp_max_period);
            }
            self.sep_comp_proofs_count += other.sep_comp_proofs_count;
            self.sep_comp_total_period += other.sep_comp_total_period;
            for (k, v) in other.sep_comp_period_counts {
                *self.sep_comp_period_counts.entry(k).or_insert(0) += v;
            }
        }
        if other.bouncer_proofs_count > 0 {
            if self.bouncer_proofs_count == 0 {
                self.bouncer_min_bounce_steps = other.bouncer_min_bounce_steps;
                self.bouncer_max_bounce_steps = other.bouncer_max_bounce_steps;
            } else {
                self.bouncer_min_bounce_steps =
                    self.bouncer_min_bounce_steps.min(other.bouncer_min_bounce_steps);
                self.bouncer_max_bounce_steps =
                    self.bouncer_max_bounce_steps.max(other.bouncer_max_bounce_steps);
            }
            self.bouncer_proofs_count += other.bouncer_proofs_count;
            self.bouncer_total_bounce_steps += other.bouncer_total_bounce_steps;
            for (k, v) in other.bouncer_bounce_steps_counts {
                *self.bouncer_bounce_steps_counts.entry(k).or_insert(0) += v;
            }
            for (k, v) in other.bouncer_gap_growth_counts {
                *self.bouncer_gap_growth_counts.entry(k).or_insert(0) += v;
            }
        }
        if other.ctl_proofs_count > 0 {
            if self.ctl_proofs_count == 0 {
                self.ctl_min_steps = other.ctl_min_steps;
                self.ctl_max_steps = other.ctl_max_steps;
                self.ctl_min_states = other.ctl_min_states;
                self.ctl_max_states = other.ctl_max_states;
            } else {
                self.ctl_min_steps = self.ctl_min_steps.min(other.ctl_min_steps);
                self.ctl_max_steps = self.ctl_max_steps.max(other.ctl_max_steps);
                self.ctl_min_states = self.ctl_min_states.min(other.ctl_min_states);
                self.ctl_max_states = self.ctl_max_states.max(other.ctl_max_states);
            }
            self.ctl_proofs_count += other.ctl_proofs_count;
            self.ctl_total_steps += other.ctl_total_steps;
            self.ctl_total_states += other.ctl_total_states;
            for (k, v) in other.ctl_floor_counts {
                *self.ctl_floor_counts.entry(k).or_insert(0) += v;
            }
            for (k, v) in other.ctl_mod_counts {
                *self.ctl_mod_counts.entry(k).or_insert(0) += v;
            }
        }
    }
}

/// Tree-Normal-Form (TNF) enumerator that lazily branches on rules for pebble counts `k`
/// only when a cell with `k` pebbles is actually reached during simulation.
///
/// Evaluates programs through the configured pipeline stages, splitting on missing rules.
pub struct TnfEnumerator {
    max_steps: u64,
    use_deciders: bool,
    break_symmetry: bool,
    pipeline: PipelineConfig,
    /// DFS stack of `(partial_program, is_symmetric)`.
    stack: Vec<(Program, bool)>,
    /// Precomputed valid rules for each pebble count `1..=size`.
    rule_table: Vec<Vec<Rule>>,
    /// Accumulated runtime and decision metrics across tree traversal.
    pub metrics: Vec<StageMetrics>,
}

impl TnfEnumerator {
    /// Create a new TNF enumerator for programs of `size` running with `early_steps` and `deep_steps`,
    /// breaking left-right symmetry by default and enabling the decider pipeline on holdouts.
    pub fn new(size: usize, early_steps: u64, deep_steps: u64) -> Self {
        Self::with_options(size, early_steps, deep_steps, true, true)
    }

    /// Create a new TNF enumerator with explicit control over whether the decider pipeline is run on holdouts,
    /// breaking left-right symmetry by default.
    pub fn with_deciders(
        size: usize,
        early_steps: u64,
        deep_steps: u64,
        use_deciders: bool,
    ) -> Self {
        Self::with_options(size, early_steps, deep_steps, use_deciders, true)
    }

    /// Create a new TNF enumerator with explicit control over deciders and left-right symmetry reduction.
    pub fn with_options(
        size: usize,
        early_steps: u64,
        deep_steps: u64,
        use_deciders: bool,
        break_symmetry: bool,
    ) -> Self {
        let pipeline = PipelineConfig::default_for(size, early_steps, deep_steps);
        Self::with_pipeline(size, deep_steps, use_deciders, break_symmetry, pipeline)
    }

    /// Create a new TNF enumerator with an explicit `PipelineConfig`.
    pub fn with_pipeline(
        size: usize,
        max_steps: u64,
        use_deciders: bool,
        break_symmetry: bool,
        pipeline: PipelineConfig,
    ) -> Self {
        let metrics = vec![StageMetrics::default(); pipeline.stages.len()];
        if size == 0 {
            return Self {
                max_steps,
                use_deciders,
                break_symmetry,
                pipeline,
                stack: Vec::new(),
                rule_table: Vec::new(),
                metrics,
            };
        }
        let rule_table: Vec<Vec<Rule>> = (1..=size as u8).map(Rule::all_for_pebbles).collect();
        let initial_prog = Program::empty(size).expect("size > 0");
        Self {
            max_steps,
            use_deciders,
            break_symmetry,
            pipeline,
            stack: vec![(initial_prog, break_symmetry)],
            rule_table,
            metrics,
        }
    }

    /// Returns whether left-right symmetry reduction is enabled.
    pub fn break_symmetry(&self) -> bool {
        self.break_symmetry
    }

    /// Returns the maximum step limit for the enumerator.
    pub fn max_steps(&self) -> u64 {
        self.max_steps
    }

    pub fn from_subtree(
        prog: Program,
        max_steps: u64,
        use_deciders: bool,
        break_symmetry: bool,
        is_symmetric: bool,
        rule_table: Vec<Vec<Rule>>,
        pipeline: PipelineConfig,
    ) -> Self {
        let metrics = vec![StageMetrics::default(); pipeline.stages.len()];
        Self {
            max_steps,
            use_deciders,
            break_symmetry,
            pipeline,
            stack: vec![(prog, is_symmetric)],
            rule_table,
            metrics,
        }
    }

    /// Returns true if the enumerator stack is empty and traversal has finished.
    #[inline]
    pub fn is_finished(&self) -> bool {
        self.stack.is_empty()
    }
}

/// Outcome of evaluating a single stage on a candidate program.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PipelineStepOutcome {
    Inf { decider: Decider, steps: u64 },
    Halted { steps: u64 },
    Split { pebbles: u8, steps: u64 },
    Undecided,
}

#[inline]
pub fn run_stage(
    stage: &PipelineStage,
    prog: &Program,
    sim: &mut Option<Simulator>,
) -> PipelineStepOutcome {
    match stage {
        PipelineStage::StaticBacktrack => {
            if let Some(d) = decide_static_backtrack(prog) {
                let steps = sim.as_ref().map_or(0, |s| s.steps());
                PipelineStepOutcome::Inf { decider: d, steps }
            } else {
                PipelineStepOutcome::Undecided
            }
        }
        PipelineStage::Simulation { steps } => {
            let s = sim.get_or_insert_with(|| Simulator::new(prog.size()));
            let outcome = if s.steps() < *steps {
                s.run(prog, *steps)
            } else {
                SimOutcome::Unknown { steps: s.steps() }
            };
            match outcome {
                SimOutcome::Halted { steps } => PipelineStepOutcome::Halted { steps },
                SimOutcome::MissingRule { pebbles, steps } => {
                    PipelineStepOutcome::Split { pebbles, steps }
                }
                SimOutcome::Inf { decider, steps } => {
                    PipelineStepOutcome::Inf { decider, steps }
                }
                SimOutcome::Unknown { .. } => {
                    if let Some(d) = check_edge_glider_sparse(prog, s.sparse_entries()) {
                        PipelineStepOutcome::Inf {
                            decider: d,
                            steps: s.steps(),
                        }
                    } else {
                        PipelineStepOutcome::Undecided
                    }
                }
            }
        }
        PipelineStage::EdgeGliderCurrent => {
            let s = sim.get_or_insert_with(|| Simulator::new(prog.size()));
            if let Some(d) = check_edge_glider_sparse(prog, s.sparse_entries()) {
                PipelineStepOutcome::Inf {
                    decider: d,
                    steps: s.steps(),
                }
            } else {
                PipelineStepOutcome::Undecided
            }
        }
        PipelineStage::Cycler { steps } => {
            let s = sim.get_or_insert_with(|| Simulator::new(prog.size()));
            let res = decide_cycler_from_sim(prog, s, *steps);
            match res {
                StepDeciderOutcome::Proved(d) => PipelineStepOutcome::Inf {
                    decider: d,
                    steps: s.steps(),
                },
                StepDeciderOutcome::Halted { steps } => PipelineStepOutcome::Halted { steps },
                StepDeciderOutcome::MissingRule { pebbles, steps } => {
                    PipelineStepOutcome::Split { pebbles, steps }
                }
                StepDeciderOutcome::Undecided => PipelineStepOutcome::Undecided,
            }
        }
        PipelineStage::SeparatedComponents { steps } => {
            let s = sim.get_or_insert_with(|| Simulator::new(prog.size()));
            let res = decide_separated_components_from_sim(prog, s, *steps);
            match res {
                StepDeciderOutcome::Proved(d) => PipelineStepOutcome::Inf {
                    decider: d,
                    steps: s.steps(),
                },
                StepDeciderOutcome::Halted { steps } => PipelineStepOutcome::Halted { steps },
                StepDeciderOutcome::MissingRule { pebbles, steps } => {
                    PipelineStepOutcome::Split { pebbles, steps }
                }
                StepDeciderOutcome::Undecided => PipelineStepOutcome::Undecided,
            }
        }
        PipelineStage::Bouncer { steps } => {
            let res = decide_bouncer_outcome(prog, *steps);
            match res {
                StepDeciderOutcome::Proved(d) => {
                    let s_steps = sim.as_ref().map_or(0, |s| s.steps());
                    PipelineStepOutcome::Inf {
                        decider: d,
                        steps: s_steps,
                    }
                }
                StepDeciderOutcome::Halted { steps } => PipelineStepOutcome::Halted { steps },
                StepDeciderOutcome::MissingRule { pebbles, steps } => {
                    PipelineStepOutcome::Split { pebbles, steps }
                }
                StepDeciderOutcome::Undecided => PipelineStepOutcome::Undecided,
            }
        }
        PipelineStage::Ctl(cfg) => {
            let s = sim.get_or_insert_with(|| Simulator::new(prog.size()));
            let res = decide_ctl_from_sim_outcome_with_params(
                prog,
                s,
                cfg.steps,
                cfg.max_states,
                &cfg.split_thresh,
                &cfg.floors,
                &cfg.moduli,
            );
            match res {
                StepDeciderOutcome::Proved(d) => {
                    let proof_steps = match d {
                        Decider::Ctl(Some(ref proof)) => proof.num_steps,
                        _ => s.steps(),
                    };
                    PipelineStepOutcome::Inf {
                        decider: d,
                        steps: proof_steps,
                    }
                }
                StepDeciderOutcome::Halted { steps } => PipelineStepOutcome::Halted { steps },
                StepDeciderOutcome::MissingRule { pebbles, steps } => {
                    PipelineStepOutcome::Split { pebbles, steps }
                }
                StepDeciderOutcome::Undecided => PipelineStepOutcome::Undecided,
            }
        }
    }
}

/// Evaluation result of running all pipeline stages on a candidate program.
pub enum PipelineEvalResult {
    Done(EnumEntry),
    Split {
        children: Vec<(Program, bool)>,
    },
}

#[inline]
pub fn evaluate_pipeline(
    prog: Program,
    is_symmetric: bool,
    use_deciders: bool,
    pipeline: &PipelineConfig,
    metrics: &mut [StageMetrics],
    rule_table: &[Vec<Rule>],
) -> PipelineEvalResult {
    let mut sim: Option<Simulator> = None;

    for (stage_idx, stage) in pipeline.stages.iter().enumerate() {
        if !use_deciders && stage.is_decider() {
            continue;
        }

        metrics[stage_idx].invocations += 1;
        let t0 = Instant::now();
        let outcome = run_stage(stage, &prog, &mut sim);
        metrics[stage_idx].total_time_nanos += t0.elapsed().as_nanos() as u64;

        match outcome {
            PipelineStepOutcome::Inf { decider, steps } => {
                metrics[stage_idx].decided_inf += 1;
                return PipelineEvalResult::Done(EnumEntry {
                    program: prog,
                    outcome: SimOutcome::Inf { decider, steps },
                });
            }
            PipelineStepOutcome::Halted { steps } => {
                metrics[stage_idx].decided_halting += 1;
                return PipelineEvalResult::Done(EnumEntry {
                    program: prog,
                    outcome: SimOutcome::Halted { steps },
                });
            }
            PipelineStepOutcome::Split { pebbles, .. } => {
                metrics[stage_idx].splits += 1;
                let choices = &rule_table[pebbles as usize - 1];
                let mut children = Vec::with_capacity(choices.len());
                for &rule in choices.iter().rev() {
                    if is_symmetric && rule.left > rule.right {
                        continue;
                    }
                    let child_is_symmetric = is_symmetric && (rule.left == rule.right);
                    let mut child_prog = prog.clone();
                    child_prog
                        .set_rule(pebbles, Some(rule))
                        .expect("valid rule for pebbles");
                    children.push((child_prog, child_is_symmetric));
                }
                return PipelineEvalResult::Split { children };
            }
            PipelineStepOutcome::Undecided => {}
        }
    }

    let final_steps = sim.as_ref().map_or(0, |s| s.steps());
    PipelineEvalResult::Done(EnumEntry {
        program: prog,
        outcome: SimOutcome::Unknown { steps: final_steps },
    })
}

/// Ultra-fast non-cryptographic 64-bit PRNG (SplitMix64) for Monte Carlo tree sampling.
#[derive(Debug, Clone)]
pub struct FastRng {
    state: u64,
}

impl FastRng {
    #[inline]
    pub fn new(seed: u64) -> Self {
        Self {
            state: if seed == 0 { 0xda942042e4dd58b5 } else { seed },
        }
    }

    #[inline]
    pub fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_add(0x9e3779b97f4a7c15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
        z ^ (z >> 31)
    }

    #[inline]
    pub fn next_usize(&mut self, bound: usize) -> usize {
        debug_assert!(bound > 0);
        (self.next_u64() as usize) % bound
    }
}

/// Evaluates a single random descent path from a partial program down to a leaf or decider outcome.
pub fn sample_random_descent(
    start_prog: &Program,
    start_symmetric: bool,
    use_deciders: bool,
    pipeline: &PipelineConfig,
    rule_table: &[Vec<Rule>],
    rng: &mut FastRng,
    metrics: &mut [StageMetrics],
) -> EnumEntry {
    let mut cur_prog = start_prog.clone();
    let mut cur_symmetric = start_symmetric;

    loop {
        let res = evaluate_pipeline(
            cur_prog,
            cur_symmetric,
            use_deciders,
            pipeline,
            metrics,
            rule_table,
        );
        match res {
            PipelineEvalResult::Done(entry) => {
                return entry;
            }
            PipelineEvalResult::Split { mut children } => {
                if children.is_empty() {
                    return EnumEntry {
                        program: Program::empty(start_prog.size()).expect("valid size"),
                        outcome: SimOutcome::Unknown { steps: 0 },
                    };
                }
                let idx = rng.next_usize(children.len());
                let (next_prog, next_symmetric) = children.swap_remove(idx);
                cur_prog = next_prog;
                cur_symmetric = next_symmetric;
            }
        }
    }
}

impl Iterator for TnfEnumerator {
    type Item = EnumEntry;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some((prog, is_symmetric)) = self.stack.pop() {
            let res = evaluate_pipeline(
                prog,
                is_symmetric,
                self.use_deciders,
                &self.pipeline,
                &mut self.metrics,
                &self.rule_table,
            );
            match res {
                PipelineEvalResult::Split { children } => {
                    for child in children {
                        self.stack.push(child);
                    }
                }
                PipelineEvalResult::Done(entry) => {
                    return Some(entry);
                }
            }
        }
        None
    }
}

enum FrontierNode {
    Leaf(EnumEntry),
    Branch(Program, bool),
}

/// Expand the TNF tree in deterministic left-to-right DFS order until at least `target_width`
/// frontier nodes are produced or all branches terminate.
fn build_frontier(
    size: usize,
    pipeline: &PipelineConfig,
    use_deciders: bool,
    break_symmetry: bool,
    rule_table: &[Vec<Rule>],
    target_width: usize,
    metrics: &mut [StageMetrics],
) -> Vec<FrontierNode> {
    if size == 0 {
        return Vec::new();
    }
    let mut frontier = vec![FrontierNode::Branch(
        Program::empty(size).expect("size > 0"),
        break_symmetry,
    )];

    while frontier.len() < target_width
        && frontier.iter().any(|n| matches!(n, FrontierNode::Branch(_, _)))
    {
        let mut next_frontier = Vec::with_capacity(frontier.len() * 4);
        for node in frontier {
            match node {
                FrontierNode::Leaf(entry) => next_frontier.push(FrontierNode::Leaf(entry)),
                FrontierNode::Branch(prog, is_symmetric) => {
                    let res = evaluate_pipeline(
                        prog,
                        is_symmetric,
                        use_deciders,
                        pipeline,
                        metrics,
                        rule_table,
                    );
                    match res {
                        PipelineEvalResult::Split { children } => {
                            for (child_prog, child_is_symmetric) in children.into_iter().rev() {
                                next_frontier.push(FrontierNode::Branch(
                                    child_prog,
                                    child_is_symmetric,
                                ));
                            }
                        }
                        PipelineEvalResult::Done(entry) => {
                            next_frontier.push(FrontierNode::Leaf(entry));
                        }
                    }
                }
            }
        }
        frontier = next_frontier;
    }

    frontier
}

/// Snapshot of live atomic progress counters during parallel enumeration.
#[derive(Debug, Clone, Copy)]
pub struct ProgressSnapshot {
    pub total_programs: u64,
    pub halted_programs: u64,
    pub inf_programs: u64,
    pub unknown_programs: u64,
    pub max_halting_steps: Option<u64>,
}

impl ProgressSnapshot {
    #[inline]
    pub fn decided_programs(&self) -> u64 {
        self.inf_programs
    }

    #[inline]
    pub fn holdout_programs(&self) -> u64 {
        self.unknown_programs
    }
}

fn find_coprime_stride(n: usize) -> usize {
    if n <= 1 {
        return 1;
    }
    let candidate = 257.min(n - 1).max(1);
    for stride in (candidate..n).chain(1..candidate) {
        if gcd(stride, n) == 1 {
            return stride;
        }
    }
    1
}

fn gcd(mut a: usize, mut b: usize) -> usize {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

/// Enumerate TNF programs of `size` in parallel using Rayon with support for sampling,
/// checkpointing/resumption, and graceful interruption.
pub fn enumerate_parallel_advanced<F, P>(
    size: usize,
    pipeline: PipelineConfig,
    use_deciders: bool,
    break_symmetry: bool,
    collect_entries: bool,
    holdouts_only: bool,
    options: EnumerateOptions,
    on_progress: P,
    filter_fn: F,
) -> (EnumStats, Vec<EnumEntry>)
where
    F: Fn(&ProgressSnapshot) -> bool + Sync,
    P: Fn(&ProgressSnapshot) + Sync,
{
    use rayon::prelude::*;
    use std::collections::HashSet;
    use std::sync::atomic::{AtomicU64, Ordering};
    use std::sync::Mutex;

    reset_interrupted();
    let collect_entries = collect_entries || options.output_path.is_some();

    let deep_steps = pipeline.max_simulation_steps();
    if size == 0 {
        return (EnumStats::with_pipeline(0, deep_steps, &pipeline), Vec::new());
    }

    let rule_table: Vec<Vec<Rule>> = (1..=size as u8).map(Rule::all_for_pebbles).collect();
    let mut frontier_metrics = vec![StageMetrics::default(); pipeline.stages.len()];
    let target_width = 4096;
    let frontier = build_frontier(
        size,
        &pipeline,
        use_deciders,
        break_symmetry,
        &rule_table,
        target_width,
        &mut frontier_metrics,
    );

    let mut start_total_nanos: u128 = 0;
    let mut completed_set: HashSet<usize> = HashSet::new();
    let mut completed_vec: Vec<usize> = Vec::new();
    let mut base_stats = EnumStats::with_pipeline(size, deep_steps, &pipeline);

    if let Some(ref ckpt_path) = options.checkpoint_path {
        if ckpt_path.exists() {
            match CheckpointData::load_from_file(ckpt_path) {
                Ok(ckpt) => {
                    if ckpt.size == size
                        && ckpt.max_steps == deep_steps
                        && ckpt.use_deciders == use_deciders
                        && ckpt.break_symmetry == break_symmetry
                        && ckpt.total_chunks == frontier.len()
                    {
                        eprintln!(
                            "[Checkpoint] Resuming from '{}': {}/{} chunks ({:.1}%) completed, {} programs previously evaluated",
                            ckpt_path.display(),
                            ckpt.completed_chunks.len(),
                            frontier.len(),
                            if frontier.is_empty() {
                                0.0
                            } else {
                                ckpt.completed_chunks.len() as f64 / frontier.len() as f64 * 100.0
                            },
                            format_count(ckpt.stats.total_programs)
                        );
                        start_total_nanos = ckpt.elapsed_nanos;
                        for &idx in &ckpt.completed_chunks {
                            completed_set.insert(idx);
                        }
                        completed_vec = ckpt.completed_chunks;
                        base_stats = ckpt.stats;
                    } else {
                        eprintln!(
                            "[Checkpoint] Warning: Checkpoint '{}' configuration mismatch. Starting fresh.",
                            ckpt_path.display()
                        );
                        base_stats.merge_metrics(&frontier_metrics);
                    }
                }
                Err(err) => {
                    eprintln!(
                        "[Checkpoint] Warning: Failed to load '{}' ({err}). Starting fresh.",
                        ckpt_path.display()
                    );
                    base_stats.merge_metrics(&frontier_metrics);
                }
            }
        } else {
            base_stats.merge_metrics(&frontier_metrics);
        }
    } else {
        base_stats.merge_metrics(&frontier_metrics);
    }

    let mut resumed_records = Vec::new();
    if !completed_set.is_empty() {
        if let Some(ref out_path) = options.output_path {
            if out_path.exists() {
                match read_records_from_file(out_path) {
                    Ok(records) => {
                        eprintln!(
                            "[Checkpoint] Loaded {} previously written records from '{}'",
                            format_count(records.len() as u64),
                            out_path.display()
                        );
                        resumed_records = records;
                    }
                    Err(e) => {
                        eprintln!(
                            "[Checkpoint] Warning: could not read existing records from '{}': {e}",
                            out_path.display()
                        );
                    }
                }
            }
        }
    }

    let run_start = Instant::now();

    // Check if already finished
    if completed_set.len() >= frontier.len() {
        let entries = resumed_records
            .into_iter()
            .map(|r| EnumEntry {
                program: r.program,
                outcome: r.outcome.unwrap_or(SimOutcome::Unknown { steps: 0 }),
            })
            .collect();
        return (base_stats, entries);
    }

    // If a sample limit is configured, execute random path sampling (Option A) across all frontier branches
    if let Some(sample_limit) = options.sample_limit {
        let total_chunks = frontier.len();
        if total_chunks == 0 {
            return (base_stats, Vec::new());
        }

        let mut chunk_budgets = vec![0u64; total_chunks];
        if sample_limit >= total_chunks as u64 {
            let base = sample_limit / (total_chunks as u64);
            let remainder = (sample_limit % (total_chunks as u64)) as usize;
            for i in 0..total_chunks {
                chunk_budgets[i] = base + if i < remainder { 1 } else { 0 };
            }
        } else {
            let stride = find_coprime_stride(total_chunks);
            for i in 0..(sample_limit as usize) {
                let idx = (i * stride) % total_chunks;
                chunk_budgets[idx] += 1;
            }
        }

        let chunk_indices: Vec<usize> = (0..total_chunks)
            .filter(|&idx| chunk_budgets[idx] > 0)
            .collect();

        let live_total = AtomicU64::new(base_stats.total_programs);
        let live_halted = AtomicU64::new(base_stats.halted_programs);
        let live_decided = AtomicU64::new(base_stats.inf_programs);
        let live_max_steps = AtomicU64::new(base_stats.max_halting_steps.unwrap_or(u64::MAX));
        let progress_lock = Mutex::new(());

        let flush_batch = |b_tot: u64, b_halt: u64, b_dec: u64, b_max: Option<u64>| {
            if b_tot == 0 {
                return;
            }
            let tot = live_total.fetch_add(b_tot, Ordering::Relaxed) + b_tot;
            let halt = live_halted.fetch_add(b_halt, Ordering::Relaxed) + b_halt;
            let dec = live_decided.fetch_add(b_dec, Ordering::Relaxed) + b_dec;
            if let Some(m) = b_max {
                let mut cur = live_max_steps.load(Ordering::Relaxed);
                while cur == u64::MAX || m > cur {
                    match live_max_steps.compare_exchange_weak(
                        cur,
                        m,
                        Ordering::Relaxed,
                        Ordering::Relaxed,
                    ) {
                        Ok(_) => break,
                        Err(actual) => cur = actual,
                    }
                }
            }
            let raw_max = live_max_steps.load(Ordering::Relaxed);
            let snap = ProgressSnapshot {
                total_programs: tot,
                halted_programs: halt,
                inf_programs: dec,
                unknown_programs: tot.saturating_sub(halt).saturating_sub(dec),
                max_halting_steps: if raw_max == u64::MAX {
                    None
                } else {
                    Some(raw_max)
                },
            };
            if filter_fn(&snap) {
                if let Ok(_guard) = progress_lock.try_lock() {
                    if filter_fn(&snap) {
                        on_progress(&snap);
                    }
                }
            }
        };

        let mut chunk_results: Vec<(usize, EnumStats, Vec<EnumEntry>)> = chunk_indices
            .into_par_iter()
            .map(|idx| {
                if STOP_REQUESTED.load(Ordering::Relaxed) {
                    return (
                        idx,
                        EnumStats::with_pipeline(size, deep_steps, &pipeline),
                        Vec::new(),
                    );
                }

                let mut local_stats = EnumStats::with_pipeline(size, deep_steps, &pipeline);
                let mut local_entries = Vec::new();
                let chunk_seed = (idx as u64).wrapping_mul(0x9e3779b97f4a7c15) ^ 0x517cc1b727220a95;
                let mut rng = FastRng::new(chunk_seed);

                match &frontier[idx] {
                    FrontierNode::Leaf(entry) => {
                        let entry = entry.clone();
                        local_stats.record(&entry);
                        let b_halt = u64::from(matches!(entry.outcome, SimOutcome::Halted { .. }));
                        let b_dec = u64::from(matches!(entry.outcome, SimOutcome::Inf { .. }));
                        flush_batch(1, b_halt, b_dec, local_stats.max_halting_steps);
                        if collect_entries && (!holdouts_only || entry.outcome.is_holdout()) {
                            local_entries.push(entry);
                        }
                    }
                    FrontierNode::Branch(prog, is_symmetric) => {
                        let budget = chunk_budgets[idx];
                        let mut b_tot = 0u64;
                        let mut b_halt = 0u64;
                        let mut b_dec = 0u64;
                        let mut b_max: Option<u64> = None;
                        let mut descent_metrics = vec![StageMetrics::default(); pipeline.stages.len()];

                        for _ in 0..budget {
                            if STOP_REQUESTED.load(Ordering::Relaxed) {
                                break;
                            }
                            let entry = sample_random_descent(
                                prog,
                                *is_symmetric,
                                use_deciders,
                                &pipeline,
                                &rule_table,
                                &mut rng,
                                &mut descent_metrics,
                            );
                            local_stats.record(&entry);
                            b_tot += 1;
                            match entry.outcome {
                                SimOutcome::Halted { steps } => {
                                    b_halt += 1;
                                    b_max = Some(b_max.map_or(steps, |prev| prev.max(steps)));
                                }
                                SimOutcome::Inf { .. } => {
                                    b_dec += 1;
                                }
                                _ => {}
                            }
                            if collect_entries && (!holdouts_only || entry.outcome.is_holdout()) {
                                local_entries.push(entry);
                            }
                            if b_tot >= 256 {
                                flush_batch(b_tot, b_halt, b_dec, b_max);
                                b_tot = 0;
                                b_halt = 0;
                                b_dec = 0;
                                b_max = None;
                            }
                        }
                        local_stats.merge_metrics(&descent_metrics);
                        flush_batch(b_tot, b_halt, b_dec, b_max);
                    }
                }

                (idx, local_stats, local_entries)
            })
            .collect();

        chunk_results.sort_by_key(|(idx, _, _)| *idx);

        let mut final_stats = base_stats;
        let mut final_entries = Vec::new();
        for (_idx, local_stats, mut local_entries) in chunk_results {
            final_stats.merge(local_stats);
            if collect_entries {
                final_entries.append(&mut local_entries);
            }
        }

        return (final_stats, final_entries);
    }

    // Otherwise, perform exhaustive deterministic parallel DFS enumeration
    let remaining_indices: Vec<usize> = {
        let mut indices = Vec::with_capacity(frontier.len() - completed_set.len());
        for idx in 0..frontier.len() {
            if !completed_set.contains(&idx) {
                indices.push(idx);
            }
        }
        indices
    };

    let live_total = AtomicU64::new(base_stats.total_programs);
    let live_halted = AtomicU64::new(base_stats.halted_programs);
    let live_decided = AtomicU64::new(base_stats.inf_programs);
    let live_max_steps = AtomicU64::new(base_stats.max_halting_steps.unwrap_or(u64::MAX));
    let progress_lock = Mutex::new(());

    let flush_batch = |b_tot: u64, b_halt: u64, b_dec: u64, b_max: Option<u64>| {
        if b_tot == 0 {
            return;
        }
        let tot = live_total.fetch_add(b_tot, Ordering::Relaxed) + b_tot;
        let halt = live_halted.fetch_add(b_halt, Ordering::Relaxed) + b_halt;
        let dec = live_decided.fetch_add(b_dec, Ordering::Relaxed) + b_dec;
        if let Some(m) = b_max {
            let mut cur = live_max_steps.load(Ordering::Relaxed);
            while cur == u64::MAX || m > cur {
                match live_max_steps.compare_exchange_weak(
                    cur,
                    m,
                    Ordering::Relaxed,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => break,
                    Err(actual) => cur = actual,
                }
            }
        }
        let raw_max = live_max_steps.load(Ordering::Relaxed);
        let snap = ProgressSnapshot {
            total_programs: tot,
            halted_programs: halt,
            inf_programs: dec,
            unknown_programs: tot.saturating_sub(halt).saturating_sub(dec),
            max_halting_steps: if raw_max == u64::MAX {
                None
            } else {
                Some(raw_max)
            },
        };
        if filter_fn(&snap) {
            if let Ok(_guard) = progress_lock.try_lock() {
                if filter_fn(&snap) {
                    on_progress(&snap);
                }
            }
        }
    };

    let completed_chunks_lock = Mutex::new(completed_vec);
    let completed_entries_lock = Mutex::new(BTreeMap::<usize, Vec<EnumEntry>>::new());
    let periodic_stats_lock = Mutex::new(base_stats.clone());
    let last_ckpt_save = Mutex::new(Instant::now());

    let batch_flush_size = 2048u64;

    let mut chunk_results: Vec<(usize, EnumStats, Vec<EnumEntry>, bool)> = remaining_indices
        .into_par_iter()
        .map(|idx| {
            if STOP_REQUESTED.load(Ordering::Relaxed) {
                return (
                    idx,
                    EnumStats::with_pipeline(size, deep_steps, &pipeline),
                    Vec::new(),
                    false,
                );
            }

            let mut local_stats = EnumStats::with_pipeline(size, deep_steps, &pipeline);
            let mut local_entries = Vec::new();
            let is_finished: bool;

            match &frontier[idx] {
                FrontierNode::Leaf(entry) => {
                    let entry = entry.clone();
                    local_stats.record(&entry);
                    let b_halt = u64::from(matches!(entry.outcome, SimOutcome::Halted { .. }));
                    let b_dec = u64::from(matches!(entry.outcome, SimOutcome::Inf { .. }));
                    flush_batch(1, b_halt, b_dec, local_stats.max_halting_steps);
                    if collect_entries && (!holdouts_only || entry.outcome.is_holdout()) {
                        local_entries.push(entry);
                    }
                    is_finished = true;
                }
                FrontierNode::Branch(prog, is_symmetric) => {
                    let mut sub_enum = TnfEnumerator::from_subtree(
                        prog.clone(),
                        deep_steps,
                        use_deciders,
                        break_symmetry,
                        *is_symmetric,
                        rule_table.clone(),
                        pipeline.clone(),
                    );
                    let mut b_tot = 0u64;
                    let mut b_halt = 0u64;
                    let mut b_dec = 0u64;
                    let mut b_max: Option<u64> = None;

                    for entry in &mut sub_enum {
                        local_stats.record(&entry);
                        b_tot += 1;
                        match entry.outcome {
                            SimOutcome::Halted { steps } => {
                                b_halt += 1;
                                b_max = Some(b_max.map_or(steps, |prev| prev.max(steps)));
                            }
                            SimOutcome::Inf { .. } => {
                                b_dec += 1;
                            }
                            _ => {}
                        }
                        if collect_entries && (!holdouts_only || entry.outcome.is_holdout()) {
                            local_entries.push(entry);
                        }
                        if b_tot >= batch_flush_size {
                            flush_batch(b_tot, b_halt, b_dec, b_max);
                            b_tot = 0;
                            b_halt = 0;
                            b_dec = 0;
                            b_max = None;
                        }
                        if STOP_REQUESTED.load(Ordering::Relaxed) {
                            break;
                        }
                    }
                    local_stats.merge_metrics(&sub_enum.metrics);
                    flush_batch(b_tot, b_halt, b_dec, b_max);
                    is_finished = sub_enum.is_finished();
                }
            }

            if is_finished {
                let mut comp = completed_chunks_lock.lock().unwrap();
                comp.push(idx);
                let mut st = periodic_stats_lock.lock().unwrap();
                st.merge(local_stats.clone());
                if collect_entries {
                    let mut entries_map = completed_entries_lock.lock().unwrap();
                    entries_map.insert(idx, local_entries.clone());
                }

                // Periodic checkpoint save check
                if options.checkpoint_path.is_some() {
                    if let Ok(mut last_save) = last_ckpt_save.try_lock() {
                        if last_save.elapsed() >= options.checkpoint_interval {
                            *last_save = Instant::now();
                            let ckpt = CheckpointData {
                                version: 1,
                                size,
                                max_steps: deep_steps,
                                use_deciders,
                                break_symmetry,
                                target_width,
                                elapsed_nanos: start_total_nanos
                                    + run_start.elapsed().as_nanos(),
                                total_chunks: frontier.len(),
                                completed_chunks: comp.clone(),
                                stats: st.clone(),
                            };
                            if let Some(path) = &options.checkpoint_path {
                                let _ = ckpt.save_to_file(path);
                            }
                            if let Some(ref out_path) = options.output_path {
                                let entries_map = completed_entries_lock.lock().unwrap();
                                let mut records = resumed_records.clone();
                                let mut seen: HashSet<Program> =
                                    records.iter().map(|r| r.program.clone()).collect();
                                for (_chunk_idx, chunk_entries) in entries_map.iter() {
                                    for e in chunk_entries {
                                        if seen.insert(e.program.clone()) {
                                            records.push(ProgramRecord::new(
                                                e.program.clone(),
                                                Some(e.outcome),
                                            ));
                                        }
                                    }
                                }
                                if let Err(e) = write_records_to_file(out_path, &records) {
                                    eprintln!(
                                        "[Checkpoint] Error flushing output file '{}': {e}",
                                        out_path.display()
                                    );
                                } else if let Some(path) = &options.checkpoint_path {
                                    eprintln!(
                                        "[Checkpoint] Saved progress to '{}' ({}/{} chunks completed, {} records flushed to '{}')",
                                        path.display(),
                                        comp.len(),
                                        frontier.len(),
                                        format_count(records.len() as u64),
                                        out_path.display(),
                                    );
                                }
                            }
                        }
                    }
                }
            }

            (idx, local_stats, local_entries, is_finished)
        })
        .collect();

    // Sort chunk results by original frontier index for 100% deterministic merge order
    chunk_results.sort_by_key(|(idx, _, _, _)| *idx);

    let mut final_completed_set = completed_set;
    let mut final_completed_vec = Vec::new();
    let mut final_stats = base_stats;
    let mut partial_stats = Vec::new();
    let mut final_entries = Vec::new();
    let mut seen_final: HashSet<Program> = HashSet::new();

    for r in resumed_records {
        if seen_final.insert(r.program.clone()) {
            final_entries.push(EnumEntry {
                program: r.program,
                outcome: r.outcome.unwrap_or(SimOutcome::Unknown { steps: 0 }),
            });
        }
    }

    for (idx, local_stats, local_entries, is_finished) in chunk_results {
        if is_finished {
            final_completed_set.insert(idx);
            final_stats.merge(local_stats);
        } else if local_stats.total_programs > 0 {
            partial_stats.push(local_stats);
        }
        if collect_entries {
            for e in local_entries {
                if seen_final.insert(e.program.clone()) {
                    final_entries.push(e);
                }
            }
        }
    }

    final_completed_vec.extend(final_completed_set.into_iter());
    final_completed_vec.sort_unstable();

    // Save final checkpoint if configured
    if let Some(ckpt_path) = &options.checkpoint_path {
        let ckpt = CheckpointData {
            version: 1,
            size,
            max_steps: deep_steps,
            use_deciders,
            break_symmetry,
            target_width,
            elapsed_nanos: start_total_nanos + run_start.elapsed().as_nanos(),
            total_chunks: frontier.len(),
            completed_chunks: final_completed_vec.clone(),
            stats: final_stats.clone(),
        };
        if let Err(e) = ckpt.save_to_file(ckpt_path) {
            eprintln!("[Checkpoint] Error saving to '{}': {e}", ckpt_path.display());
        } else if let Some(ref out_path) = options.output_path {
            let records: Vec<ProgramRecord> = final_entries
                .iter()
                .map(|e| ProgramRecord::new(e.program.clone(), Some(e.outcome)))
                .collect();
            if let Err(e) = write_records_to_file(out_path, &records) {
                eprintln!(
                    "[Checkpoint] Error flushing output file '{}': {e}",
                    out_path.display()
                );
            } else {
                eprintln!(
                    "[Checkpoint] Saved progress to '{}' ({}/{} chunks completed, {} records flushed to '{}')",
                    ckpt_path.display(),
                    ckpt.completed_chunks.len(),
                    frontier.len(),
                    format_count(records.len() as u64),
                    out_path.display(),
                );
            }
        } else {
            eprintln!(
                "[Checkpoint] Saved progress to '{}' ({}/{} chunks completed)",
                ckpt_path.display(),
                ckpt.completed_chunks.len(),
                frontier.len(),
            );
        }
    }

    // Merge partial stats for reporting
    for p in partial_stats {
        final_stats.merge(p);
    }

    (final_stats, final_entries)
}

/// Enumerate all TNF programs of `size` in parallel using Rayon and a custom `PipelineConfig`.
pub fn enumerate_parallel_with_pipeline<F, P>(
    size: usize,
    pipeline: PipelineConfig,
    use_deciders: bool,
    break_symmetry: bool,
    collect_entries: bool,
    holdouts_only: bool,
    on_progress: P,
    filter_fn: F,
) -> (EnumStats, Vec<EnumEntry>)
where
    F: Fn(&ProgressSnapshot) -> bool + Sync,
    P: Fn(&ProgressSnapshot) + Sync,
{
    enumerate_parallel_advanced(
        size,
        pipeline,
        use_deciders,
        break_symmetry,
        collect_entries,
        holdouts_only,
        EnumerateOptions::default(),
        on_progress,
        filter_fn,
    )
}

/// Enumerate all TNF programs of `size` in parallel using Rayon and `EnumerateOptions`.
pub fn enumerate_parallel_options<F, P>(
    size: usize,
    early_steps: u64,
    deep_steps: u64,
    use_deciders: bool,
    break_symmetry: bool,
    collect_entries: bool,
    holdouts_only: bool,
    options: EnumerateOptions,
    on_progress: P,
    filter_fn: F,
) -> (EnumStats, Vec<EnumEntry>)
where
    F: Fn(&ProgressSnapshot) -> bool + Sync,
    P: Fn(&ProgressSnapshot) + Sync,
{
    let pipeline = PipelineConfig::default_for(size, early_steps, deep_steps);
    enumerate_parallel_advanced(
        size,
        pipeline,
        use_deciders,
        break_symmetry,
        collect_entries,
        holdouts_only,
        options,
        on_progress,
        filter_fn,
    )
}

/// Enumerate all TNF programs of `size` in parallel using Rayon, returning the exact
/// `EnumStats` and any collected `EnumEntry` items matching `filter_entry`.
///
/// Calls `on_progress` periodically with a live `ProgressSnapshot`.
pub fn enumerate_parallel<F, P>(
    size: usize,
    early_steps: u64,
    deep_steps: u64,
    use_deciders: bool,
    break_symmetry: bool,
    collect_entries: bool,
    holdouts_only: bool,
    on_progress: P,
    filter_fn: F,
) -> (EnumStats, Vec<EnumEntry>)
where
    F: Fn(&ProgressSnapshot) -> bool + Sync,
    P: Fn(&ProgressSnapshot) + Sync,
{
    enumerate_parallel_options(
        size,
        early_steps,
        deep_steps,
        use_deciders,
        break_symmetry,
        collect_entries,
        holdouts_only,
        EnumerateOptions::default(),
        on_progress,
        filter_fn,
    )
}

/// Formats a `Duration` into a clean human-readable string.
pub fn format_duration(d: Duration) -> String {
    let nanos = d.as_nanos();
    if nanos < 1_000 {
        format!("{nanos} ns")
    } else if nanos < 1_000_000 {
        format!("{:.2} µs", nanos as f64 / 1_000.0)
    } else if nanos < 1_000_000_000 {
        format!("{:.2} ms", nanos as f64 / 1_000_000.0)
    } else {
        format!("{:.2} s", nanos as f64 / 1_000_000_000.0)
    }
}

/// Parses a human duration string (e.g. "10s", "500ms") into a `Duration`.
pub fn parse_duration_arg(raw: &str) -> Result<Duration, String> {
    let s = raw.trim();
    if let Some(ms_str) = s.strip_suffix("ms") {
        let ms: f64 = ms_str
            .trim()
            .parse()
            .map_err(|_| format!("invalid duration '{raw}'"))?;
        if ms < 0.0 || !ms.is_finite() {
            return Err(format!("invalid duration '{raw}'"));
        }
        return Ok(Duration::from_secs_f64(ms / 1000.0));
    }
    let secs_str = s.strip_suffix('s').unwrap_or(s).trim();
    let secs: f64 = secs_str
        .parse()
        .map_err(|_| format!("invalid duration '{raw}'"))?;
    if secs < 0.0 || !secs.is_finite() {
        return Err(format!("invalid duration '{raw}'"));
    }
    Ok(Duration::from_secs_f64(secs))
}

/// Parses a human program count string (e.g. "100k", "1M", "10B", "1_000_000") into a `u64`.
pub fn parse_count_arg(raw: &str) -> Result<u64, String> {
    let s: String = raw.chars().filter(|c| !c.is_whitespace() && *c != '_').collect();
    if s.is_empty() {
        return Err("empty count argument".to_string());
    }
    let (num_str, multiplier) = if let Some(stripped) = s.strip_suffix(|c| c == 'k' || c == 'K') {
        (stripped, 1_000u64)
    } else if let Some(stripped) = s.strip_suffix(|c| c == 'm' || c == 'M') {
        (stripped, 1_000_000u64)
    } else if let Some(stripped) = s.strip_suffix(|c| c == 'b' || c == 'B') {
        (stripped, 1_000_000_000u64)
    } else {
        (s.as_str(), 1u64)
    };

    let base: u64 = num_str
        .parse()
        .map_err(|_| format!("invalid program count '{raw}'"))?;
    Ok(base.saturating_mul(multiplier))
}

fn format_ranges(indices: &[usize]) -> String {
    if indices.is_empty() {
        return String::new();
    }
    let mut sorted = indices.to_vec();
    sorted.sort_unstable();
    sorted.dedup();
    let mut out = Vec::new();
    let mut start = sorted[0];
    let mut prev = sorted[0];
    for &idx in &sorted[1..] {
        if idx == prev + 1 {
            prev = idx;
        } else {
            if start == prev {
                out.push(format!("{start}"));
            } else {
                out.push(format!("{start}-{prev}"));
            }
            start = idx;
            prev = idx;
        }
    }
    if start == prev {
        out.push(format!("{start}"));
    } else {
        out.push(format!("{start}-{prev}"));
    }
    out.join(",")
}

fn parse_ranges(raw: &str) -> Result<Vec<usize>, String> {
    let s = raw.trim();
    if s.is_empty() {
        return Ok(Vec::new());
    }
    let mut out = Vec::new();
    for part in s.split(',') {
        let part = part.trim();
        if part.is_empty() {
            continue;
        }
        if let Some((start_s, end_s)) = part.split_once('-') {
            let start: usize = start_s.trim().parse().map_err(|e| format!("{e}"))?;
            let end: usize = end_s.trim().parse().map_err(|e| format!("{e}"))?;
            for i in start..=end {
                out.push(i);
            }
        } else {
            let single: usize = part.parse().map_err(|e| format!("{e}"))?;
            out.push(single);
        }
    }
    out.sort_unstable();
    out.dedup();
    Ok(out)
}

fn format_map<K: std::fmt::Display, V: std::fmt::Display>(map: &BTreeMap<K, V>) -> String {
    map.iter().map(|(k, v)| format!("{k}:{v}")).collect::<Vec<_>>().join(",")
}

fn parse_map<K: std::str::FromStr + Ord, V: std::str::FromStr>(raw: &str) -> Result<BTreeMap<K, V>, String> {
    let s = raw.trim();
    if s.is_empty() {
        return Ok(BTreeMap::new());
    }
    let mut map = BTreeMap::new();
    for item in s.split(',') {
        let item = item.trim();
        if item.is_empty() {
            continue;
        }
        if let Some((k_s, v_s)) = item.split_once(':') {
            let k = k_s.trim().parse::<K>().map_err(|_| format!("key error in '{item}'"))?;
            let v = v_s.trim().parse::<V>().map_err(|_| format!("val error in '{item}'"))?;
            map.insert(k, v);
        }
    }
    Ok(map)
}

/// Options for advanced parallel enumeration including sampling, checkpointing, and output flushing.
#[derive(Debug, Clone, Default)]
pub struct EnumerateOptions {
    /// Stop evaluation after evaluating at least this many programs (sample run).
    pub sample_limit: Option<u64>,
    /// Path to checkpoint file for saving progress and resuming interrupted runs.
    pub checkpoint_path: Option<PathBuf>,
    /// Checkpoint save interval.
    pub checkpoint_interval: Duration,
    /// Path to output file for recording evaluated programs / holdouts (flushed on checkpoint updates).
    pub output_path: Option<PathBuf>,
}

/// Persistent state saved for resuming interrupted enumerations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckpointData {
    pub version: u32,
    pub size: usize,
    pub max_steps: u64,
    pub use_deciders: bool,
    pub break_symmetry: bool,
    pub target_width: usize,
    pub elapsed_nanos: u128,
    pub total_chunks: usize,
    pub completed_chunks: Vec<usize>,
    pub stats: EnumStats,
}

impl CheckpointData {
    pub fn save_to_file(&self, path: &Path) -> Result<(), std::io::Error> {
        let text = self.serialize();
        let tmp_path = path.with_extension("tmp");
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent)?;
        }
        std::fs::write(&tmp_path, text)?;
        std::fs::rename(&tmp_path, path)?;
        Ok(())
    }

    pub fn load_from_file(path: &Path) -> Result<Self, String> {
        let text = std::fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))?;
        Self::deserialize(&text)
    }

    pub fn serialize(&self) -> String {
        let mut out = String::new();
        out.push_str("# PEBBLE ENUMERATION CHECKPOINT v1\n");
        out.push_str(&format!("version={}\n", self.version));
        out.push_str(&format!("size={}\n", self.size));
        out.push_str(&format!("max_steps={}\n", self.max_steps));
        out.push_str(&format!("use_deciders={}\n", self.use_deciders));
        out.push_str(&format!("break_symmetry={}\n", self.break_symmetry));
        out.push_str(&format!("target_width={}\n", self.target_width));
        out.push_str(&format!("elapsed_nanos={}\n", self.elapsed_nanos));
        out.push_str(&format!("total_chunks={}\n", self.total_chunks));
        out.push_str(&format!("completed_chunks={}\n", format_ranges(&self.completed_chunks)));

        out.push_str("[stats]\n");
        let s = &self.stats;
        out.push_str(&format!("total_programs={}\n", s.total_programs));
        out.push_str(&format!("halted_programs={}\n", s.halted_programs));
        out.push_str(&format!("inf_programs={}\n", s.inf_programs));
        out.push_str(&format!(
            "decided_by_kind={}\n",
            s.decided_by_kind
                .iter()
                .map(|x| x.to_string())
                .collect::<Vec<_>>()
                .join(",")
        ));
        out.push_str(&format!(
            "max_halting_steps={}\n",
            s.max_halting_steps
                .map(|x| x.to_string())
                .unwrap_or_else(|| "None".to_string())
        ));
        out.push_str(&format!(
            "min_halting_steps={}\n",
            s.min_halting_steps
                .map(|x| x.to_string())
                .unwrap_or_else(|| "None".to_string())
        ));
        out.push_str(&format!("total_halting_steps={}\n", s.total_halting_steps));
        out.push_str(&format!("halting_zero_steps={}\n", s.halting_zero_steps));
        out.push_str(&format!(
            "halting_step_histogram={}\n",
            format_map(&s.halting_step_histogram)
        ));
        out.push_str(&format!(
            "champion={}\n",
            s.champion
                .as_ref()
                .map(|p| p.to_string())
                .unwrap_or_else(|| "None".to_string())
        ));
        out.push_str(&format!("ctl_proofs_count={}\n", s.ctl_proofs_count));
        out.push_str(&format!("ctl_min_steps={}\n", s.ctl_min_steps));
        out.push_str(&format!("ctl_max_steps={}\n", s.ctl_max_steps));
        out.push_str(&format!("ctl_total_steps={}\n", s.ctl_total_steps));
        out.push_str(&format!("ctl_min_states={}\n", s.ctl_min_states));
        out.push_str(&format!("ctl_max_states={}\n", s.ctl_max_states));
        out.push_str(&format!("ctl_total_states={}\n", s.ctl_total_states));
        out.push_str(&format!("ctl_floor_counts={}\n", format_map(&s.ctl_floor_counts)));
        out.push_str(&format!("ctl_mod_counts={}\n", format_map(&s.ctl_mod_counts)));

        out.push_str(&format!("cycler_proofs_count={}\n", s.cycler_proofs_count));
        out.push_str(&format!("cycler_min_period={}\n", s.cycler_min_period));
        out.push_str(&format!("cycler_max_period={}\n", s.cycler_max_period));
        out.push_str(&format!("cycler_total_period={}\n", s.cycler_total_period));
        out.push_str(&format!("cycler_period_counts={}\n", format_map(&s.cycler_period_counts)));
        out.push_str(&format!("cycler_dx_counts={}\n", format_map(&s.cycler_dx_counts)));

        out.push_str(&format!("sep_comp_proofs_count={}\n", s.sep_comp_proofs_count));
        out.push_str(&format!("sep_comp_min_period={}\n", s.sep_comp_min_period));
        out.push_str(&format!("sep_comp_max_period={}\n", s.sep_comp_max_period));
        out.push_str(&format!("sep_comp_total_period={}\n", s.sep_comp_total_period));
        out.push_str(&format!("sep_comp_period_counts={}\n", format_map(&s.sep_comp_period_counts)));

        out.push_str(&format!("bouncer_proofs_count={}\n", s.bouncer_proofs_count));
        out.push_str(&format!("bouncer_min_bounce_steps={}\n", s.bouncer_min_bounce_steps));
        out.push_str(&format!("bouncer_max_bounce_steps={}\n", s.bouncer_max_bounce_steps));
        out.push_str(&format!("bouncer_total_bounce_steps={}\n", s.bouncer_total_bounce_steps));
        out.push_str(&format!("bouncer_bounce_steps_counts={}\n", format_map(&s.bouncer_bounce_steps_counts)));
        out.push_str(&format!("bouncer_gap_growth_counts={}\n", format_map(&s.bouncer_gap_growth_counts)));

        out.push_str("[stages]\n");
        for stage in &s.stages {
            let m = &stage.metrics;
            out.push_str(&format!(
                "{}|{}|{}|{}|{}|{}\n",
                stage.name,
                m.invocations,
                m.splits,
                m.decided_halting,
                m.decided_inf,
                m.total_time_nanos
            ));
        }

        out
    }

    pub fn deserialize(text: &str) -> Result<Self, String> {
        let mut section = "header";
        let mut kv = BTreeMap::new();
        let mut stage_lines = Vec::new();

        for line in text.lines() {
            let line = line.trim();
            if line.is_empty() || line.starts_with('#') {
                continue;
            }
            if line == "[stats]" {
                section = "stats";
                continue;
            }
            if line == "[stages]" {
                section = "stages";
                continue;
            }

            if section == "stages" {
                stage_lines.push(line.to_string());
            } else if let Some((k, v)) = line.split_once('=') {
                kv.insert(k.trim().to_string(), v.trim().to_string());
            }
        }

        let get = |k: &str| -> Result<&String, String> {
            kv.get(k).ok_or_else(|| format!("missing key '{k}'"))
        };
        let get_u64 = |k: &str| -> Result<u64, String> {
            get(k)?.parse().map_err(|e| format!("{k}: {e}"))
        };
        let get_usize = |k: &str| -> Result<usize, String> {
            get(k)?.parse().map_err(|e| format!("{k}: {e}"))
        };

        let version: u32 = get("version")?.parse().map_err(|e| format!("version: {e}"))?;
        let size = get_usize("size")?;
        let max_steps = get_u64("max_steps")?;
        let use_deciders: bool = get("use_deciders")?.parse().map_err(|e| format!("use_deciders: {e}"))?;
        let break_symmetry: bool = get("break_symmetry")?.parse().map_err(|e| format!("break_symmetry: {e}"))?;
        let target_width = get_usize("target_width")?;
        let elapsed_nanos: u128 = get("elapsed_nanos")?.parse().map_err(|e| format!("elapsed_nanos: {e}"))?;
        let total_chunks = get_usize("total_chunks")?;
        let completed_chunks = parse_ranges(get("completed_chunks")?)?;

        let total_programs = get_u64("total_programs")?;
        let halted_programs = get_u64("halted_programs")?;
        let inf_programs = get_u64("inf_programs")?;

        let kind_parts: Vec<u64> = get("decided_by_kind")?
            .split(',')
            .map(|s| s.trim().parse().map_err(|e| format!("decided_by_kind: {e}")))
            .collect::<Result<_, _>>()?;
        if kind_parts.len() != 6 {
            return Err("decided_by_kind must have 6 items".to_string());
        }
        let mut decided_by_kind = [0u64; 6];
        decided_by_kind.copy_from_slice(&kind_parts);

        let max_halting_steps = match get("max_halting_steps")?.as_str() {
            "None" | "" => None,
            v => Some(v.parse().map_err(|e| format!("max_halting_steps: {e}"))?),
        };
        let min_halting_steps = match kv.get("min_halting_steps").map(|s| s.as_str()) {
            Some("None") | Some("") | None => None,
            Some(v) => Some(v.parse().map_err(|e| format!("min_halting_steps: {e}"))?),
        };
        let total_halting_steps = match kv.get("total_halting_steps") {
            Some(s) => s.parse().map_err(|e| format!("total_halting_steps: {e}"))?,
            None => 0,
        };
        let halting_zero_steps = match kv.get("halting_zero_steps") {
            Some(s) => s.parse().map_err(|e| format!("halting_zero_steps: {e}"))?,
            None => 0,
        };
        let halting_step_histogram = match kv.get("halting_step_histogram") {
            Some(s) => parse_map(s)?,
            None => BTreeMap::new(),
        };
        let champion = match get("champion")?.as_str() {
            "None" | "" => None,
            v => Some(v.parse::<Program>().map_err(|e| format!("champion: {e}"))?),
        };

        let mut stages = Vec::new();
        for sl in stage_lines {
            let parts: Vec<&str> = sl.split('|').collect();
            if parts.len() != 6 {
                return Err(format!("invalid stage line: '{sl}'"));
            }
            stages.push(StageReport {
                name: parts[0].to_string(),
                metrics: StageMetrics {
                    invocations: parts[1].parse().map_err(|e| format!("{e}"))?,
                    splits: parts[2].parse().map_err(|e| format!("{e}"))?,
                    decided_halting: parts[3].parse().map_err(|e| format!("{e}"))?,
                    decided_inf: parts[4].parse().map_err(|e| format!("{e}"))?,
                    total_time_nanos: parts[5].parse().map_err(|e| format!("{e}"))?,
                },
            });
        }

        let stats = EnumStats {
            size,
            max_steps,
            total_programs,
            halted_programs,
            inf_programs,
            decided_by_kind,
            max_halting_steps,
            min_halting_steps,
            total_halting_steps,
            halting_zero_steps,
            halting_step_histogram,
            champion,
            stages,
            ctl_proofs_count: get_u64("ctl_proofs_count")?,
            ctl_min_steps: get_u64("ctl_min_steps")?,
            ctl_max_steps: get_u64("ctl_max_steps")?,
            ctl_total_steps: get_u64("ctl_total_steps")?,
            ctl_min_states: get_usize("ctl_min_states")?,
            ctl_max_states: get_usize("ctl_max_states")?,
            ctl_total_states: get_u64("ctl_total_states")?,
            ctl_floor_counts: parse_map(get("ctl_floor_counts")?)?,
            ctl_mod_counts: parse_map(get("ctl_mod_counts")?)?,
            cycler_proofs_count: get_u64("cycler_proofs_count")?,
            cycler_min_period: get_u64("cycler_min_period")?,
            cycler_max_period: get_u64("cycler_max_period")?,
            cycler_total_period: get_u64("cycler_total_period")?,
            cycler_period_counts: parse_map(get("cycler_period_counts")?)?,
            cycler_dx_counts: parse_map(get("cycler_dx_counts")?)?,
            sep_comp_proofs_count: get_u64("sep_comp_proofs_count")?,
            sep_comp_min_period: get_u64("sep_comp_min_period")?,
            sep_comp_max_period: get_u64("sep_comp_max_period")?,
            sep_comp_total_period: get_u64("sep_comp_total_period")?,
            sep_comp_period_counts: parse_map(get("sep_comp_period_counts")?)?,
            bouncer_proofs_count: get_u64("bouncer_proofs_count")?,
            bouncer_min_bounce_steps: get_u64("bouncer_min_bounce_steps")?,
            bouncer_max_bounce_steps: get_u64("bouncer_max_bounce_steps")?,
            bouncer_total_bounce_steps: get_u64("bouncer_total_bounce_steps")?,
            bouncer_bounce_steps_counts: parse_map(get("bouncer_bounce_steps_counts")?)?,
            bouncer_gap_growth_counts: parse_map(get("bouncer_gap_growth_counts")?)?,
        };

        Ok(CheckpointData {
            version,
            size,
            max_steps,
            use_deciders,
            break_symmetry,
            target_width,
            elapsed_nanos,
            total_chunks,
            completed_chunks,
            stats,
        })
    }
}

fn format_top_counts<K: std::fmt::Display + Ord>(
    map: &std::collections::BTreeMap<K, u64>,
    prefix: &str,
    limit: usize,
) -> String {
    let mut pairs: Vec<(&K, &u64)> = map.iter().collect();
    pairs.sort_by(|a, b| b.1.cmp(a.1).then_with(|| a.0.cmp(b.0)));
    let formatted: Vec<String> = pairs
        .into_iter()
        .take(limit)
        .map(|(k, count)| format!("{prefix}{k} ({})", format_count(*count)))
        .collect();
    if formatted.is_empty() {
        "-".to_string()
    } else {
        formatted.join(", ")
    }
}

/// Prints the formatted summary and decider metrics report for an enumeration run.
pub fn print_enum_report(stats: &EnumStats, elapsed: Duration, use_deciders: bool) {
    let secs = elapsed.as_secs_f64();
    let programs_per_sec = if secs > 0.0 {
        stats.total_programs as f64 / secs
    } else {
        stats.total_programs as f64
    };

    println!("=== Final Statistics (peBBle({}), max_steps = {}) ===", stats.size, stats.max_steps);
    println!("Total programs:         {}", format_count(stats.total_programs));
    println!(
        "Halted programs:        {} ({:.2}%)",
        format_count(stats.halted_programs),
        stats.halted_percentage()
    );
    if use_deciders {
        println!(
            "Infinite programs:      {} ({:.2}%)",
            format_count(stats.inf_programs),
            stats.inf_percentage()
        );
    }
    println!(
        "Unknown programs:       {} ({:.2}%)",
        format_count(stats.unknown_programs()),
        stats.unknown_percentage()
    );
    match (&stats.max_halting_steps, &stats.champion) {
        (Some(max_s), Some(champ)) => {
            println!("Max halting step count: {}", format_count(*max_s));
            println!("Champion program:       {champ}");
        }
        _ => {
            println!("Max halting step count: none");
        }
    }
    println!("Wallclock runtime:      {:.3?}", elapsed);
    println!("Throughput:             {} programs/s", format_count(programs_per_sec as u64));

    if use_deciders {
        println!();
        println!("=== Pipeline & Decider Performance ===");
        println!(
            "{:<48} {:>12} {:>12} {:>12} {:>12} {:>14} {:>14}",
            "Stage / Decider", "Run On", "Split On", "Halted", "Inf", "Total Time", "Avg / Prog"
        );
        println!("{:-<120}", "");
        for stage in &stats.stages {
            let m = &stage.metrics;
            let tot_time_str = format_duration(m.total_time());
            let avg_time_str = m
                .avg_time()
                .map(format_duration)
                .unwrap_or_else(|| "-".to_string());
            println!(
                "{:<48} {:>12} {:>12} {:>12} {:>12} {:>14} {:>14}",
                stage.name,
                format_count(m.invocations),
                format_count(m.splits),
                format_count(m.decided_halting),
                format_count(m.decided_inf),
                tot_time_str,
                avg_time_str,
            );
        }
        println!("{:-<120}", "");
    }

    if stats.halted_programs > 0 {
        println!();
        println!(
            "=== Halting Step Distribution ({} halted) ===",
            format_count(stats.halted_programs)
        );
        let min_s = stats.min_halting_steps.unwrap_or(0);
        let max_s = stats.max_halting_steps.unwrap_or(0);
        let avg_s = stats.total_halting_steps as f64 / stats.halted_programs as f64;
        println!(
            "Steps:            min = {}, avg = {:.1}, max = {}",
            format_count(min_s),
            avg_s,
            format_count(max_s)
        );
        println!();
        println!(
            "{:<24} {:<8} {:>14} {:>12}  {:<25}",
            "Step Range", "k", "Count", "Pct Halted", "Distribution"
        );
        println!("{:-<88}", "");
        if stats.halting_zero_steps > 0 {
            let pct = (stats.halting_zero_steps as f64 / stats.halted_programs as f64) * 100.0;
            let bar_len = ((pct / 100.0) * 25.0).round() as usize;
            let bar = "█".repeat(bar_len);
            println!(
                "{:<24} {:<8} {:>14} {:>11.2}%  {}",
                "0", "-", format_count(stats.halting_zero_steps), pct, bar
            );
        }
        if !stats.halting_step_histogram.is_empty() {
            let min_k = *stats.halting_step_histogram.keys().next().unwrap();
            let max_k = *stats.halting_step_histogram.keys().next_back().unwrap();
            for k in min_k..=max_k {
                let count = stats.halting_step_histogram.get(&k).copied().unwrap_or(0);
                if count > 0 || (max_k - min_k <= 32) {
                    let low_str = format_count(1u64.checked_shl(k).unwrap_or(u64::MAX));
                    let high_str = if k >= 63 {
                        "inf".to_string()
                    } else {
                        format_count(1u64 << (k + 1))
                    };
                    let range_str = format!("[{}, {})", low_str, high_str);
                    let pct = (count as f64 / stats.halted_programs as f64) * 100.0;
                    let bar_len = ((pct / 100.0) * 25.0).round() as usize;
                    let bar = "█".repeat(bar_len);
                    println!(
                        "{:<24} {:<8} {:>14} {:>11.2}%  {}",
                        range_str,
                        format!("k={k}"),
                        format_count(count),
                        pct,
                        bar
                    );
                }
            }
        }
        println!("{:-<88}", "");
    }

    if use_deciders {

        if stats.cycler_proofs_count > 0 {
            println!();
            println!(
                "=== Cycler Proof Statistics ({} proved) ===",
                format_count(stats.cycler_proofs_count)
            );
            let avg_p = stats.cycler_total_period as f64 / stats.cycler_proofs_count as f64;
            println!(
                "Periods:          min = {}, avg = {:.1}, max = {}",
                format_count(stats.cycler_min_period),
                avg_p,
                format_count(stats.cycler_max_period)
            );
            let top_periods = format_top_counts(&stats.cycler_period_counts, "p=", 8);
            println!("Top periods:      {}", top_periods);
            let dx_str = format_top_counts(&stats.cycler_dx_counts, "dx=", 8);
            println!("Displacements:    {}", dx_str);
        }

        if stats.sep_comp_proofs_count > 0 {
            println!();
            println!(
                "=== SeparatedComponents Proof Statistics ({} proved) ===",
                format_count(stats.sep_comp_proofs_count)
            );
            let avg_p = stats.sep_comp_total_period as f64 / stats.sep_comp_proofs_count as f64;
            println!(
                "Periods:          min = {}, avg = {:.1}, max = {}",
                format_count(stats.sep_comp_min_period),
                avg_p,
                format_count(stats.sep_comp_max_period)
            );
            let top_periods = format_top_counts(&stats.sep_comp_period_counts, "p=", 8);
            println!("Top periods:      {}", top_periods);
        }

        if stats.bouncer_proofs_count > 0 {
            println!();
            println!(
                "=== Bouncer Proof Statistics ({} proved) ===",
                format_count(stats.bouncer_proofs_count)
            );
            let avg_bounce =
                stats.bouncer_total_bounce_steps as f64 / stats.bouncer_proofs_count as f64;
            println!(
                "Bounce steps:     min = {}, avg = {:.1}, max = {}",
                format_count(stats.bouncer_min_bounce_steps),
                avg_bounce,
                format_count(stats.bouncer_max_bounce_steps)
            );
            let top_bounce = format_top_counts(&stats.bouncer_bounce_steps_counts, "s=", 8);
            println!("Top bounce steps: {}", top_bounce);
            let growth_str = format_top_counts(&stats.bouncer_gap_growth_counts, "Δg=", 8);
            println!("Gap growths:      {}", growth_str);
        }

        if stats.ctl_proofs_count > 0 {
            println!();
            println!(
                "=== CTL Proof Statistics ({} proved) ===",
                format_count(stats.ctl_proofs_count)
            );
            let avg_steps = stats.ctl_total_steps as f64 / stats.ctl_proofs_count as f64;
            println!(
                "Steps:            min = {}, avg = {:.1}, max = {}",
                format_count(stats.ctl_min_steps),
                avg_steps,
                format_count(stats.ctl_max_steps)
            );
            let avg_states = stats.ctl_total_states as f64 / stats.ctl_proofs_count as f64;
            println!(
                "States:           min = {}, avg = {:.1}, max = {}",
                format_count(stats.ctl_min_states as u64),
                avg_states,
                format_count(stats.ctl_max_states as u64)
            );

            let floor_str = stats
                .ctl_floor_counts
                .iter()
                .map(|(f, c)| format!("floor={f} ({})", format_count(*c)))
                .collect::<Vec<_>>()
                .join(", ");
            println!("Floors:           {}", floor_str);

            let mod_str = stats
                .ctl_mod_counts
                .iter()
                .map(|(m, c)| format!("mod={m} ({})", format_count(*c)))
                .collect::<Vec<_>>()
                .join(", ");
            println!("Moduli:           {}", mod_str);
        }
    }
}

/// Standard command line options for custom enumeration binaries.
#[derive(Parser, Debug)]
#[command(
    about = "Enumerate pebble programs in Tree Normal Form (TNF) with custom pipeline.",
    version
)]
pub struct CustomPipelineCli {
    /// Number of Rayon worker threads (default: all cores)
    #[arg(short = 'j', long = "threads")]
    pub threads: Option<usize>,

    /// Progress update interval in seconds (default: 10s)
    #[arg(short = 'p', long = "progress", default_value = "10s", value_parser = parse_duration_arg)]
    pub progress: Duration,

    /// Stop enumeration after evaluating a sample of at least this many programs (e.g. 50k, 1M, 1B)
    #[arg(long = "sample", visible_alias = "limit", value_parser = parse_count_arg)]
    pub sample: Option<u64>,

    /// Checkpoint file path to save progress and resume interrupted runs
    #[arg(long = "checkpoint")]
    pub checkpoint: Option<PathBuf>,

    /// Checkpoint save interval (default: 60s)
    #[arg(long = "checkpoint-interval", default_value = "60s", value_parser = parse_duration_arg)]
    pub checkpoint_interval: Duration,

    /// Write program results to <FILE>
    #[arg(short = 'o', long = "output")]
    pub output: Option<PathBuf>,

    /// When using -o, only write undecided holdout programs
    #[arg(long = "holdouts-only")]
    pub holdouts_only: bool,

    /// Disable non-halting decider pipeline on holdouts
    #[arg(long = "no-deciders")]
    pub no_deciders: bool,

    /// Disable left-right symmetry reduction (enumerate full space)
    #[arg(long = "no-symmetry", visible_alias = "all-symmetries")]
    pub no_symmetry: bool,

    /// Enable left-right symmetry reduction (default: true)
    #[arg(long = "symmetry")]
    pub symmetry: bool,
}

/// Convenience driver for custom size binaries (`bb8`, `bb9`, `bb10`, etc.).
pub fn run_enumeration_cli(size: usize, pipeline: PipelineConfig) {
    register_signal_handler();
    let cli = CustomPipelineCli::parse();

    if let Some(threads) = cli.threads {
        if let Err(err) = rayon::ThreadPoolBuilder::new()
            .num_threads(threads)
            .build_global()
        {
            eprintln!("Error configuring Rayon thread pool: {err}");
            std::process::exit(1);
        }
    }

    let use_deciders = !cli.no_deciders;
    let break_symmetry = !cli.no_symmetry || cli.symmetry;
    let progress_interval = cli.progress;
    let output_path = cli.output;
    let holdouts_only = cli.holdouts_only;

    println!("=== Pebble Automaton Custom Enumerator: bb{size} (TNF) ===");
    println!("Size (n):         {size}");
    println!("Max sim steps:    {}", pipeline.max_simulation_steps());
    println!("Stages ({}):", pipeline.stages.len());
    for (i, stage) in pipeline.stages.iter().enumerate() {
        println!("  {}. {}", i + 1, stage.name());
    }
    println!("Threads:          {}", rayon::current_num_threads());
    println!("Deciders:         {}", if use_deciders { "enabled" } else { "disabled" });
    println!(
        "Symmetry:         {}",
        if break_symmetry {
            "reduced (breaking left-right mirror symmetry)"
        } else {
            "full"
        }
    );
    if let Some(sample) = cli.sample {
        println!("Sample limit:     {} programs", format_count(sample));
    }
    if let Some(ref ckpt) = cli.checkpoint {
        println!("Checkpoint file:  {}", ckpt.display());
        println!("Save interval:    {:?}", cli.checkpoint_interval);
    }
    println!();

    let start = Instant::now();
    let last_report = std::sync::Mutex::new(Instant::now());

    let should_report = |_snap: &ProgressSnapshot| -> bool {
        if progress_interval.is_zero() {
            return false;
        }
        last_report
            .try_lock()
            .map(|t| t.elapsed() >= progress_interval)
            .unwrap_or(false)
    };

    let on_progress = |snap: &ProgressSnapshot| {
        if let Ok(mut t) = last_report.lock() {
            *t = Instant::now();
        }
        let tot_f = snap.total_programs.max(1) as f64;
        let halt_pct = (snap.halted_programs as f64 / tot_f) * 100.0;
        let inf_pct = (snap.inf_programs as f64 / tot_f) * 100.0;
        let unk_pct = (snap.unknown_programs as f64 / tot_f) * 100.0;
        let max_steps_str = snap
            .max_halting_steps
            .map(format_count)
            .unwrap_or_else(|| "-".to_string());
        println!(
            "[Progress] programs: {} | halted: {} ({:.2}%) | inf: {} ({:.2}%) | unknown: {} ({:.2}%) | max steps: {} | elapsed: {:.2?}",
            format_count(snap.total_programs),
            format_count(snap.halted_programs),
            halt_pct,
            format_count(snap.inf_programs),
            inf_pct,
            format_count(snap.unknown_programs),
            unk_pct,
            max_steps_str,
            start.elapsed()
        );
    };

    let options = EnumerateOptions {
        sample_limit: cli.sample,
        checkpoint_path: cli.checkpoint.clone(),
        checkpoint_interval: cli.checkpoint_interval,
        output_path: output_path.clone(),
    };

    let (stats, entries) = enumerate_parallel_advanced(
        size,
        pipeline,
        use_deciders,
        break_symmetry,
        output_path.is_some(),
        holdouts_only,
        options,
        on_progress,
        should_report,
    );

    let elapsed = start.elapsed();

    if let Some(ref path) = output_path {
        let records_to_write: Vec<ProgramRecord> = entries
            .into_iter()
            .map(|e| ProgramRecord::new(e.program, Some(e.outcome)))
            .collect();
        if let Err(err) = write_records_to_file(path, &records_to_write) {
            eprintln!("Error writing output file '{}': {err}", path.display());
            std::process::exit(1);
        }
        println!(
            "Wrote {} records to {}",
            format_count(records_to_write.len() as u64),
            path.display()
        );
        println!();
    }

    if is_interrupted() {
        println!();
        println!("Run interrupted early by user. Partial statistics below:");
    } else if let Some(sample) = cli.sample {
        if stats.total_programs >= sample {
            println!();
            println!(
                "Sample limit reached ({} evaluated >= {} requested). Sample statistics below:",
                format_count(stats.total_programs),
                format_count(sample)
            );
        }
    }

    print_enum_report(&stats, elapsed, use_deciders);

    if is_interrupted() {
        std::process::exit(130);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tnf_enumerator_with_deciders_sizes_1_to_4() {
        let expected = [
            // (size, expected_total, expected_halted, expected_decided, expected_holdouts, expected_max_steps)
            (1, 3u64, 1u64, 2u64, 0u64, 0u64),
            (2, 12, 4, 8, 0, 1),
            (3, 102, 26, 76, 0, 3),
            (4, 921, 217, 704, 0, 6),
        ];

        for (size, exp_total, exp_halted, exp_decided, exp_holdouts, exp_max_steps) in expected {
            let max_steps = 25;
            let mut stats = EnumStats::new(size, max_steps, max_steps);

            for entry in TnfEnumerator::with_options(size, max_steps, max_steps, true, false) {
                stats.record(&entry);
            }

            assert_eq!(stats.total_programs, exp_total, "size {size} total");
            assert_eq!(stats.halted_programs, exp_halted, "size {size} halted");
            assert_eq!(stats.inf_programs, exp_decided, "size {size} inf");
            assert_eq!(
                stats.holdout_programs(),
                exp_holdouts,
                "size {size} holdouts"
            );
            assert_eq!(stats.max_halting_steps, Some(exp_max_steps));
        }
    }

    #[test]
    fn test_tnf_pebble_5_champion_and_zero_holdouts() {
        let size = 5;
        let max_steps = 50;
        let mut stats = EnumStats::new(size, max_steps, max_steps);
        for entry in TnfEnumerator::with_options(size, max_steps, max_steps, true, false) {
            stats.record(&entry);
        }
        assert_eq!(stats.total_programs, 11_725);
        assert_eq!(stats.halted_programs, 2_365);
        assert_eq!(stats.inf_programs, 9_360);
        assert_eq!(stats.holdout_programs(), 0);
        assert_eq!(stats.max_halting_steps, Some(11));

        // Verify parallel enumeration produces identical stats and champion
        let (par_stats, _) =
            enumerate_parallel(size, max_steps, max_steps, true, false, false, false, |_| {}, |_| false);
        assert_eq!(par_stats, stats);
    }

    #[test]
    fn test_tnf_enumerator_symmetry_reduction_sizes_1_to_5() {
        let expected = [
            // (size, expected_total, expected_halted, expected_decided, expected_holdouts, expected_max_steps)
            (1, 2u64, 1u64, 1u64, 0u64, 0u64),
            (2, 7, 3, 4, 0, 1),
            (3, 54, 14, 40, 0, 3),
            (4, 465, 111, 354, 0, 6),
            (5, 5866, 1186, 4680, 0, 11),
        ];

        for (size, exp_total, exp_halted, exp_decided, exp_holdouts, exp_max_steps) in expected {
            let max_steps = 50;
            let mut stats = EnumStats::new(size, max_steps, max_steps);

            for entry in TnfEnumerator::new(size, max_steps, max_steps) {
                stats.record(&entry);
            }

            assert_eq!(stats.total_programs, exp_total, "size {size} total");
            assert_eq!(stats.halted_programs, exp_halted, "size {size} halted");
            assert_eq!(stats.inf_programs, exp_decided, "size {size} inf");
            assert_eq!(
                stats.holdout_programs(),
                exp_holdouts,
                "size {size} holdouts"
            );
            assert_eq!(stats.max_halting_steps, Some(exp_max_steps));

            // Verify parallel enumeration matches sequential exactly
            let (par_stats, _) =
                enumerate_parallel(size, max_steps, max_steps, true, true, false, false, |_| {}, |_| false);
            assert_eq!(par_stats, stats, "parallel matches sequential for size {size}");
        }
    }

    #[test]
    fn test_extended_sim_missing_rule_splits_and_finds_champion_9() {
        let partial_prog: Program = "00_20_10_04_41_21_--_25_18".parse().unwrap();
        assert!(partial_prog.rule(7).is_none());
        let pipeline = PipelineConfig::default_for(9, 100, 70_000);
        let rule_table: Vec<Vec<Rule>> = (1..=9u8).map(Rule::all_for_pebbles).collect();

        let mut sub_enum = TnfEnumerator::from_subtree(
            partial_prog,
            70_000,
            true,
            false,
            false,
            rule_table,
            pipeline.clone(),
        );

        let mut stats = EnumStats::with_pipeline(9, 70_000, &pipeline);
        for entry in &mut sub_enum {
            stats.record(&entry);
        }

        println!("Total programs from partial split: {}", stats.total_programs);
        println!("Halted: {}", stats.halted_programs);
        println!("Inf: {}", stats.inf_programs);
        println!("Holdouts: {}", stats.holdout_programs());
        println!("Max halting steps: {:?}", stats.max_halting_steps);
        println!("Champion: {:?}", stats.champion);
        assert_eq!(stats.max_halting_steps, Some(63577));
        let champ = stats.champion.expect("champion found");
        let expected_champ: Program = "00_20_10_04_41_21_00_25_18".parse().unwrap();
        assert_eq!(champ, expected_champ);
    }

    #[test]
    fn test_enum_stats_ctl_proof_recording_and_merging() {
        use crate::ctl::{CtlProof, CtlSearchMethod};
        let proof1 = CtlProof {
            num_steps: 60,
            num_states: 4757,
            split_threshold: 5,
            floor: 12,
            modulus: 1,
            method: CtlSearchMethod::Manual,
        };
        let proof2 = CtlProof {
            num_steps: 80,
            num_states: 120,
            split_threshold: 2,
            floor: 0,
            modulus: 2,
            method: CtlSearchMethod::Manual,
        };

        let mut stats1 = EnumStats::default();
        stats1.record(&EnumEntry {
            program: "00_20_10_04_21_21_07_50_17_01".parse().unwrap(),
            outcome: SimOutcome::Inf {
                decider: Decider::Ctl(Some(proof1)),
                steps: 60,
            },
        });

        assert_eq!(stats1.ctl_proofs_count, 1);
        assert_eq!(stats1.ctl_min_steps, 60);
        assert_eq!(stats1.ctl_max_steps, 60);
        assert_eq!(stats1.ctl_total_steps, 60);
        assert_eq!(stats1.ctl_min_states, 4757);
        assert_eq!(stats1.ctl_max_states, 4757);
        assert_eq!(stats1.ctl_total_states, 4757);
        assert_eq!(stats1.ctl_floor_counts.get(&12), Some(&1));
        assert_eq!(stats1.ctl_mod_counts.get(&1), Some(&1));

        let mut stats2 = EnumStats::default();
        stats2.record(&EnumEntry {
            program: "01_01".parse().unwrap(),
            outcome: SimOutcome::Inf {
                decider: Decider::Ctl(Some(proof2)),
                steps: 80,
            },
        });

        stats1.merge(stats2);
        assert_eq!(stats1.ctl_proofs_count, 2);
        assert_eq!(stats1.ctl_min_steps, 60);
        assert_eq!(stats1.ctl_max_steps, 80);
        assert_eq!(stats1.ctl_total_steps, 60 + 80);
        assert_eq!(stats1.ctl_min_states, 120);
        assert_eq!(stats1.ctl_max_states, 4757);
        assert_eq!(stats1.ctl_total_states, 4757 + 120);
        assert_eq!(stats1.ctl_floor_counts.get(&0), Some(&1));
        assert_eq!(stats1.ctl_floor_counts.get(&12), Some(&1));
        assert_eq!(stats1.ctl_mod_counts.get(&1), Some(&1));
        assert_eq!(stats1.ctl_mod_counts.get(&2), Some(&1));
    }

    #[test]
    fn test_enum_stats_halting_histogram_and_merging() {
        let mut stats1 = EnumStats::default();
        let p1: Program = "00_01_00".parse().unwrap();
        let p2: Program = "00_01_01".parse().unwrap();
        let p3: Program = "00_01_02".parse().unwrap();

        stats1.record(&EnumEntry {
            program: p1.clone(),
            outcome: SimOutcome::Halted { steps: 1 }, // 2^0 <= 1 < 2^1 -> k=0
        });
        stats1.record(&EnumEntry {
            program: p2.clone(),
            outcome: SimOutcome::Halted { steps: 3 }, // 2^1 <= 3 < 2^2 -> k=1
        });
        stats1.record(&EnumEntry {
            program: p3.clone(),
            outcome: SimOutcome::Halted { steps: 7 }, // 2^2 <= 7 < 2^3 -> k=2
        });

        assert_eq!(stats1.halted_programs, 3);
        assert_eq!(stats1.min_halting_steps, Some(1));
        assert_eq!(stats1.max_halting_steps, Some(7));
        assert_eq!(stats1.total_halting_steps, 11);
        assert_eq!(stats1.halting_step_histogram.get(&0), Some(&1));
        assert_eq!(stats1.halting_step_histogram.get(&1), Some(&1));
        assert_eq!(stats1.halting_step_histogram.get(&2), Some(&1));

        let mut stats2 = EnumStats::default();
        let p4: Program = "00_01_03".parse().unwrap();
        let p5: Program = "00_01_10".parse().unwrap();
        stats2.record(&EnumEntry {
            program: p4.clone(),
            outcome: SimOutcome::Halted { steps: 15 }, // 2^3 <= 15 < 2^4 -> k=3
        });
        stats2.record(&EnumEntry {
            program: p5.clone(),
            outcome: SimOutcome::Halted { steps: 2 }, // 2^1 <= 2 < 2^2 -> k=1
        });

        stats1.merge(stats2);
        assert_eq!(stats1.halted_programs, 5);
        assert_eq!(stats1.min_halting_steps, Some(1));
        assert_eq!(stats1.max_halting_steps, Some(15));
        assert_eq!(stats1.total_halting_steps, 28);
        assert_eq!(stats1.halting_step_histogram.get(&0), Some(&1));
        assert_eq!(stats1.halting_step_histogram.get(&1), Some(&2)); // steps 3 and 2
        assert_eq!(stats1.halting_step_histogram.get(&2), Some(&1));
        assert_eq!(stats1.halting_step_histogram.get(&3), Some(&1));
    }

    #[test]
    fn test_enum_stats_decider_proof_recording_and_merging() {
        use crate::deciders::{BouncerProof, CyclerProof, SeparatedComponentsProof};
        let mut stats1 = EnumStats::default();
        stats1.record(&EnumEntry {
            program: "00_20_02".parse().unwrap(),
            outcome: SimOutcome::Inf {
                decider: Decider::Cycler(Some(CyclerProof { period: 2, dx: 0 })),
                steps: 3,
            },
        });
        stats1.record(&EnumEntry {
            program: "00_02_01".parse().unwrap(),
            outcome: SimOutcome::Inf {
                decider: Decider::Cycler(Some(CyclerProof { period: 4, dx: 1 })),
                steps: 4,
            },
        });
        stats1.record(&EnumEntry {
            program: "00_02_01_13_04_01".parse().unwrap(),
            outcome: SimOutcome::Inf {
                decider: Decider::SeparatedComponents(Some(SeparatedComponentsProof {
                    period: 8,
                    dx_left: -1,
                    dx_right: 1,
                })),
                steps: 8,
            },
        });
        stats1.record(&EnumEntry {
            program: "00_02_01_40_12_01".parse().unwrap(),
            outcome: SimOutcome::Inf {
                decider: Decider::Bouncer(Some(BouncerProof {
                    bounce_steps: 18,
                    gap_growth: 2,
                })),
                steps: 18,
            },
        });

        assert_eq!(stats1.cycler_proofs_count, 2);
        assert_eq!(stats1.cycler_min_period, 2);
        assert_eq!(stats1.cycler_max_period, 4);
        assert_eq!(stats1.cycler_total_period, 6);
        assert_eq!(stats1.cycler_period_counts.get(&2), Some(&1));
        assert_eq!(stats1.cycler_period_counts.get(&4), Some(&1));
        assert_eq!(stats1.cycler_dx_counts.get(&0), Some(&1));
        assert_eq!(stats1.cycler_dx_counts.get(&1), Some(&1));

        assert_eq!(stats1.sep_comp_proofs_count, 1);
        assert_eq!(stats1.sep_comp_min_period, 8);

        assert_eq!(stats1.bouncer_proofs_count, 1);
        assert_eq!(stats1.bouncer_min_bounce_steps, 18);
        assert_eq!(stats1.bouncer_gap_growth_counts.get(&2), Some(&1));

        let mut stats2 = EnumStats::default();
        stats2.record(&EnumEntry {
            program: "00_01_10_00_03".parse().unwrap(),
            outcome: SimOutcome::Inf {
                decider: Decider::Cycler(Some(CyclerProof { period: 6, dx: 0 })),
                steps: 10,
            },
        });

        stats1.merge(stats2);
        assert_eq!(stats1.cycler_proofs_count, 3);
        assert_eq!(stats1.cycler_min_period, 2);
        assert_eq!(stats1.cycler_max_period, 6);
        assert_eq!(stats1.cycler_total_period, 12);
        assert_eq!(stats1.cycler_period_counts.get(&2), Some(&1));
        assert_eq!(stats1.cycler_period_counts.get(&4), Some(&1));
        assert_eq!(stats1.cycler_period_counts.get(&6), Some(&1));
        assert_eq!(stats1.cycler_dx_counts.get(&0), Some(&2));
        assert_eq!(stats1.cycler_dx_counts.get(&1), Some(&1));
    }

    #[test]
    fn test_pipeline_config_and_stage_names() {
        let pipeline = PipelineConfig {
            stages: vec![
                PipelineStage::StaticBacktrack,
                PipelineStage::Simulation { steps: 50 },
                PipelineStage::Cycler { steps: 50 },
                PipelineStage::SeparatedComponents { steps: 50 },
                PipelineStage::Bouncer { steps: 50 },
                PipelineStage::Ctl(CtlConfig {
                    steps: 50,
                    ..Default::default()
                }),
                PipelineStage::Simulation { steps: 10_000 },
                PipelineStage::Ctl(CtlConfig {
                    steps: 10_000,
                    max_states: 8000,
                    floors: vec![6, 8, 10],
                    moduli: vec![1, 2, 4],
                    ..Default::default()
                }),
            ],
        };

        assert_eq!(pipeline.stages[0].name(), "StaticBacktrack");
        assert_eq!(pipeline.stages[1].name(), "Simulation (50 steps)");
        assert_eq!(pipeline.stages[2].name(), "Cycler (50 steps)");
        assert_eq!(pipeline.stages[3].name(), "SeparatedComponents (50 steps)");
        assert_eq!(pipeline.stages[4].name(), "Bouncer (50 steps)");
        assert_eq!(pipeline.stages[5].name(), "CTL (50 steps)");
        assert_eq!(pipeline.stages[6].name(), "Simulation (10000 steps)");
        assert_eq!(
            pipeline.stages[7].name(),
            "CTL (10000 steps, states=8000, floors=[6, 8, 10], moduli=[1, 2, 4])"
        );

        let stats = EnumStats::with_pipeline(5, 10_000, &pipeline);
        assert_eq!(stats.stages.len(), 8);
        assert_eq!(stats.stages[7].name, pipeline.stages[7].name());
    }

    #[test]
    fn test_sample_count_parsing() {
        assert_eq!(parse_count_arg("50k"), Ok(50_000));
        assert_eq!(parse_count_arg("1M"), Ok(1_000_000));
        assert_eq!(parse_count_arg("1B"), Ok(1_000_000_000));
        assert_eq!(parse_count_arg("100"), Ok(100));
        assert_eq!(parse_count_arg("100_000"), Ok(100_000));
    }

    #[test]
    fn test_checkpoint_and_output_file_flushing() {
        let temp_dir = std::env::temp_dir().join(format!("pebble_test_{}", std::process::id()));
        let _ = std::fs::create_dir_all(&temp_dir);
        let ckpt_path = temp_dir.join("test.ckpt");
        let out_path = temp_dir.join("test.out");

        let options = EnumerateOptions {
            sample_limit: None,
            checkpoint_path: Some(ckpt_path.clone()),
            checkpoint_interval: Duration::from_millis(1),
            output_path: Some(out_path.clone()),
        };

        let (stats, entries) = enumerate_parallel_options(
            3,
            100,
            100,
            true,
            true,
            true,
            false,
            options.clone(),
            |_| {},
            |_| false,
        );

        assert_eq!(stats.total_programs, 54);
        assert_eq!(entries.len(), 54);

        assert!(ckpt_path.exists());
        assert!(out_path.exists());

        let records = crate::io::read_records_from_file(&out_path).expect("read records");
        assert_eq!(records.len(), 54);

        // Now test checkpoint resumption with output file:
        // Create a synthetic partial checkpoint with half the chunks completed
        let loaded_ckpt = CheckpointData::load_from_file(&ckpt_path).expect("load ckpt");
        let half_count = loaded_ckpt.completed_chunks.len() / 2;
        let partial_chunks = loaded_ckpt.completed_chunks[..half_count].to_vec();

        // Write partial output file containing only records from the partial chunks
        let partial_records = records[..half_count].to_vec();
        crate::io::write_records_to_file(&out_path, &partial_records).expect("write partial out");

        let partial_ckpt = CheckpointData {
            total_chunks: loaded_ckpt.total_chunks,
            completed_chunks: partial_chunks,
            stats: EnumStats::with_pipeline(3, 100, &PipelineConfig::default_for(3, 100, 100)),
            ..loaded_ckpt
        };
        partial_ckpt.save_to_file(&ckpt_path).expect("save partial ckpt");

        // Resume enumeration from partial checkpoint and output file
        let (_resumed_stats, resumed_entries) = enumerate_parallel_options(
            3,
            100,
            100,
            true,
            true,
            true,
            false,
            options.clone(),
            |_| {},
            |_| false,
        );

        assert_eq!(resumed_entries.len(), 54);
        let final_disk_records = crate::io::read_records_from_file(&out_path).expect("read final disk records");
        assert_eq!(final_disk_records.len(), 54);

        let _ = std::fs::remove_file(&ckpt_path);
        let _ = std::fs::remove_file(&out_path);
        let _ = std::fs::remove_dir_all(&temp_dir);
    }
}
