use crate::deciders::{
    check_edge_glider_sparse, decide_bouncer_outcome, decide_ctl_from_sim_outcome,
    decide_cycler_from_sim, decide_separated_components_from_sim, decide_static_backtrack,
    Decider, StepDeciderOutcome,
};
use crate::program::{Program, Rule};
use crate::simulation::{SimOutcome, Simulator};
use std::time::{Duration, Instant};

/// Individual pipeline stage identifier in order of execution.
/// Kind of pipeline step executed during enumeration.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PipelineStageKind {
    /// Simulation of the program up to `steps` (including prefix branching).
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
    Ctl { steps: u64 },
    /// Extended simulation continuing from current step count up to `steps`.
    ExtendedSim { steps: u64 },
}

impl PipelineStageKind {
    /// Returns true if this stage is a mathematical decider (as opposed to raw simulation).
    #[inline]
    pub fn is_decider(&self) -> bool {
        !matches!(
            self,
            PipelineStageKind::Simulation { .. } | PipelineStageKind::ExtendedSim { .. }
        )
    }
}

/// Specification of a single stage in the pipeline.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PipelineStageSpec {
    pub name: String,
    pub kind: PipelineStageKind,
}

/// Overall pipeline configuration defining the execution stages.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PipelineConfig {
    pub initial_steps: u64,
    pub stages: Vec<PipelineStageSpec>,
}

impl PipelineConfig {
    /// Generates the data-driven default pipeline configuration for a given program size and maximum steps.
    pub fn default_for(_size: usize, early_steps: u64, deep_steps: u64) -> Self {
        let mut stages = vec![
            PipelineStageSpec {
                name: "StaticBacktrack".to_string(),
                kind: PipelineStageKind::StaticBacktrack,
            },
            PipelineStageSpec {
                name: format!("Simulation ({early_steps} steps)"),
                kind: PipelineStageKind::Simulation { steps: early_steps },
            },
            PipelineStageSpec {
                name: "EdgeGlider (sparse)".to_string(),
                kind: PipelineStageKind::EdgeGliderCurrent,
            },
            PipelineStageSpec {
                name: format!("Cycler / TransCycler ({early_steps} steps)"),
                kind: PipelineStageKind::Cycler { steps: early_steps },
            },
            PipelineStageSpec {
                name: format!("SeparatedComponents ({early_steps} steps)"),
                kind: PipelineStageKind::SeparatedComponents { steps: early_steps },
            },
            PipelineStageSpec {
                name: format!("Bouncer ({early_steps} steps)"),
                kind: PipelineStageKind::Bouncer { steps: early_steps },
            },
            PipelineStageSpec {
                name: format!("CTL ({early_steps} steps)"),
                kind: PipelineStageKind::Ctl { steps: early_steps },
            },
        ];

        if deep_steps > early_steps {
            stages.push(PipelineStageSpec {
                name: format!("Simulation ({deep_steps} steps)"),
                kind: PipelineStageKind::ExtendedSim { steps: deep_steps },
            });
            stages.push(PipelineStageSpec {
                name: "EdgeGlider (deep)".to_string(),
                kind: PipelineStageKind::EdgeGliderCurrent,
            });
            stages.push(PipelineStageSpec {
                name: format!("Cycler / TransCycler ({deep_steps} steps)"),
                kind: PipelineStageKind::Cycler { steps: deep_steps },
            });
            stages.push(PipelineStageSpec {
                name: format!("SeparatedComponents ({deep_steps} steps)"),
                kind: PipelineStageKind::SeparatedComponents { steps: deep_steps },
            });
            stages.push(PipelineStageSpec {
                name: format!("Bouncer ({deep_steps} steps)"),
                kind: PipelineStageKind::Bouncer { steps: deep_steps },
            });
            stages.push(PipelineStageSpec {
                name: format!("CTL ({deep_steps} steps)"),
                kind: PipelineStageKind::Ctl { steps: deep_steps },
            });
        }

        Self {
            initial_steps: early_steps,
            stages,
        }
    }

    /// Index of the primary simulation stage in `stages`.
    #[inline]
    pub fn sim_stage_index(&self) -> usize {
        self.stages
            .iter()
            .position(|s| matches!(s.kind, PipelineStageKind::Simulation { .. }))
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
    /// `[EdgeGlider, Cycler, TranslatedCycler, SeparatedComponents, Bouncer, Ctl, StaticBacktrack]`.
    pub decided_by_kind: [u64; 7],
    /// Maximum halting step count observed across all halted programs.
    pub max_halting_steps: Option<u64>,
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
                name: s.name.clone(),
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

                let is_new_max = match self.max_halting_steps {
                    None => true,
                    Some(prev_max) => steps > prev_max,
                };
                if is_new_max {
                    self.max_halting_steps = Some(steps);
                    self.champion = Some(entry.program.clone());
                }
            }
            SimOutcome::Inf { decider, .. } => {
                self.inf_programs += 1;
                let idx = match decider {
                    Decider::EdgeGlider => 0,
                    Decider::Cycler => 1,
                    Decider::TranslatedCycler => 2,
                    Decider::SeparatedComponents => 3,
                    Decider::Bouncer => 4,
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
                        5
                    }
                    Decider::StaticBacktrack => 6,
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
            Decider::Cycler => 1,
            Decider::TranslatedCycler => 2,
            Decider::SeparatedComponents => 3,
            Decider::Bouncer => 4,
            Decider::Ctl(_) => 5,
            Decider::StaticBacktrack => 6,
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
/// Shares simulation prefixes across branches by snapshotting the `Simulator` at the branch point.
/// When a leaf reaches the step limit without halting, executes the configured pipeline stages.
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
        _sim: Simulator,
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
    stage: &PipelineStageSpec,
    prog: &Program,
    sim: &mut Option<Simulator>,
) -> PipelineStepOutcome {
    match stage.kind {
        PipelineStageKind::StaticBacktrack => {
            if let Some(d) = decide_static_backtrack(prog) {
                let steps = sim.as_ref().map_or(0, |s| s.steps());
                PipelineStepOutcome::Inf { decider: d, steps }
            } else {
                PipelineStepOutcome::Undecided
            }
        }
        PipelineStageKind::Simulation { steps } => {
            let s = sim.get_or_insert_with(|| Simulator::new(prog.size()));
            let outcome = if s.steps() < steps {
                s.run(prog, steps)
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
                SimOutcome::Unknown { .. } => PipelineStepOutcome::Undecided,
            }
        }
        PipelineStageKind::EdgeGliderCurrent => {
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
        PipelineStageKind::Cycler { steps } => {
            let s = sim.get_or_insert_with(|| Simulator::new(prog.size()));
            let res = decide_cycler_from_sim(prog, s, steps);
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
        PipelineStageKind::SeparatedComponents { steps } => {
            let s = sim.get_or_insert_with(|| Simulator::new(prog.size()));
            let res = decide_separated_components_from_sim(prog, s, steps);
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
        PipelineStageKind::Bouncer { steps } => {
            let res = decide_bouncer_outcome(prog, steps);
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
        PipelineStageKind::Ctl { steps } => {
            let s = sim.get_or_insert_with(|| Simulator::new(prog.size()));
            let res = decide_ctl_from_sim_outcome(prog, s, steps);
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
        PipelineStageKind::ExtendedSim { steps } => {
            let s = sim.get_or_insert_with(|| Simulator::new(prog.size()));
            let outcome = if s.steps() < steps {
                s.run(prog, steps)
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
        if !use_deciders && stage.kind.is_decider() {
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
    use rayon::prelude::*;
    use std::sync::atomic::{AtomicU64, Ordering};
    use std::sync::Mutex;

    if size == 0 {
        return (EnumStats::new(0, early_steps, deep_steps), Vec::new());
    }

    let pipeline = PipelineConfig::default_for(size, early_steps, deep_steps);
    let rule_table: Vec<Vec<Rule>> = (1..=size as u8).map(Rule::all_for_pebbles).collect();
    let mut frontier_metrics = vec![StageMetrics::default(); pipeline.stages.len()];
    let frontier = build_frontier(
        size,
        &pipeline,
        use_deciders,
        break_symmetry,
        &rule_table,
        4096,
        &mut frontier_metrics,
    );

    let live_total = AtomicU64::new(0);
    let live_halted = AtomicU64::new(0);
    let live_decided = AtomicU64::new(0);
    let live_max_steps = AtomicU64::new(u64::MAX);
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

    let chunk_results: Vec<(EnumStats, Vec<EnumEntry>)> = frontier
        .into_par_iter()
        .map(|node| {
            let mut local_stats = EnumStats::with_pipeline(size, deep_steps, &pipeline);
            let mut local_entries = Vec::new();
            match node {
                FrontierNode::Leaf(entry) => {
                    local_stats.record(&entry);
                    let b_halt = u64::from(matches!(entry.outcome, SimOutcome::Halted { .. }));
                    let b_dec =
                        u64::from(matches!(entry.outcome, SimOutcome::Inf { .. }));
                    flush_batch(1, b_halt, b_dec, local_stats.max_halting_steps);
                    if collect_entries && (!holdouts_only || entry.outcome.is_holdout()) {
                        local_entries.push(entry);
                    }
                }
                FrontierNode::Branch(prog, is_symmetric) => {
                    let mut sub_enum = TnfEnumerator::from_subtree(
                        prog,
                        Simulator::new(size),
                        deep_steps,
                        use_deciders,
                        break_symmetry,
                        is_symmetric,
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
                        if b_tot >= 2048 {
                            flush_batch(b_tot, b_halt, b_dec, b_max);
                            b_tot = 0;
                            b_halt = 0;
                            b_dec = 0;
                            b_max = None;
                        }
                    }
                    local_stats.merge_metrics(&sub_enum.metrics);
                    flush_batch(b_tot, b_halt, b_dec, b_max);
                }
            }
            (local_stats, local_entries)
        })
        .collect();

    let mut final_stats = EnumStats::with_pipeline(size, deep_steps, &pipeline);
    final_stats.merge_metrics(&frontier_metrics);
    let mut final_entries = Vec::new();
    for (sub_stats, mut sub_entries) in chunk_results {
        final_stats.merge(sub_stats);
        if collect_entries {
            final_entries.append(&mut sub_entries);
        }
    }

    (final_stats, final_entries)
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
            (3, 114, 26, 88, 0, 3),
            (4, 933, 217, 716, 0, 6),
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
        assert_eq!(stats.total_programs, 12_161);
        assert_eq!(stats.halted_programs, 2_365);
        assert_eq!(stats.inf_programs, 9_796);
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
            (3, 58, 14, 44, 0, 3),
            (4, 469, 111, 358, 0, 6),
            (5, 6084, 1186, 4898, 0, 11),
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
            Simulator::new(9),
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
}
