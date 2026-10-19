use crate::deciders::{
    check_edge_glider_sparse, decide_bouncer, decide_ctl, decide_cycler,
    decide_separated_components, decide_static_backtrack, Decider,
};
use crate::program::{Program, Rule};
use crate::simulation::{SimOutcome, Simulator};
use std::time::{Duration, Instant};

/// Individual pipeline stage identifier in order of execution.
/// Kind of pipeline step executed during enumeration.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PipelineStageKind {
    /// Intermediate branching point in TNF tree.
    PrefixSim,
    /// Initial simulation of the leaf program up to `steps`.
    LeafSim { steps: u64 },
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
    pub fn default_for(size: usize, max_steps: u64) -> Self {
        let early_steps = if max_steps >= 100 { 100 } else { max_steps.min(50) };
        let deep_steps = if size >= 9 {
            max_steps.max(70_000)
        } else if size == 8 {
            max_steps.max(200)
        } else {
            max_steps.max(200)
        };

        let mut stages = vec![
            PipelineStageSpec {
                name: "Prefix Sim (Branching)".to_string(),
                kind: PipelineStageKind::PrefixSim,
            },
            PipelineStageSpec {
                name: format!("Simulation ({early_steps} steps)"),
                kind: PipelineStageKind::LeafSim { steps: early_steps },
            },
            PipelineStageSpec {
                name: "StaticBacktrack".to_string(),
                kind: PipelineStageKind::StaticBacktrack,
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
}

/// Execution metrics tracked for a single pipeline stage or decider.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct StageMetrics {
    pub invocations: u64,
    pub decided_halting: u64,
    pub decided_infinite: u64,
    pub total_time_nanos: u64,
}

impl StageMetrics {
    pub fn merge(&mut self, other: &StageMetrics) {
        self.invocations += other.invocations;
        self.decided_halting += other.decided_halting;
        self.decided_infinite += other.decided_infinite;
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
    /// Number of enumerated TNF programs proven non-halting by the decider pipeline.
    pub decided_programs: u64,
    /// Breakdown of decided non-halting programs by decider:
    /// `[EdgeGlider, Cycler, TranslatedCycler, SeparatedComponents, Bouncer, Ctl, StaticBacktrack]`.
    pub decided_by_kind: [u64; 7],
    /// Maximum halting step count observed across all halted programs.
    pub max_halting_steps: Option<u64>,
    /// First champion program achieving `max_halting_steps`.
    pub champion: Option<Program>,
    /// Runtime and decision metrics for each pipeline stage.
    pub stages: Vec<StageReport>,
}

impl PartialEq for EnumStats {
    fn eq(&self, other: &Self) -> bool {
        self.size == other.size
            && self.max_steps == other.max_steps
            && self.total_programs == other.total_programs
            && self.halted_programs == other.halted_programs
            && self.decided_programs == other.decided_programs
            && self.decided_by_kind == other.decided_by_kind
            && self.max_halting_steps == other.max_halting_steps
            && self.champion == other.champion
    }
}

impl Eq for EnumStats {}

impl EnumStats {
    /// Create a fresh statistics accumulator for `size` and `max_steps`.
    pub fn new(size: usize, max_steps: u64) -> Self {
        let pipeline = PipelineConfig::default_for(size, max_steps);
        Self::with_pipeline(size, max_steps, &pipeline)
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
            SimOutcome::DecidedNonHalting { decider, .. } => {
                self.decided_programs += 1;
                let idx = match decider {
                    Decider::EdgeGlider => 0,
                    Decider::Cycler => 1,
                    Decider::TranslatedCycler => 2,
                    Decider::SeparatedComponents => 3,
                    Decider::Bouncer => 4,
                    Decider::Ctl => 5,
                    Decider::StaticBacktrack => 6,
                };
                self.decided_by_kind[idx] += 1;
            }
            SimOutcome::MaxStepsReached { .. } | SimOutcome::MissingRule { .. } => {}
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
            Decider::Ctl => 5,
            Decider::StaticBacktrack => 6,
        };
        self.decided_by_kind[idx]
    }

    /// Number of remaining undecided holdout programs (`total - halted - decided`).
    #[inline]
    pub fn holdout_programs(&self) -> u64 {
        self.total_programs
            .saturating_sub(self.halted_programs)
            .saturating_sub(self.decided_programs)
    }

    /// Percentage of enumerated TNF programs that halted (`0.0..=100.0`).
    pub fn halted_percentage(&self) -> f64 {
        if self.total_programs == 0 {
            0.0
        } else {
            (self.halted_programs as f64 / self.total_programs as f64) * 100.0
        }
    }

    /// Percentage of enumerated TNF programs proven non-halting by deciders (`0.0..=100.0`).
    pub fn decided_percentage(&self) -> f64 {
        if self.total_programs == 0 {
            0.0
        } else {
            (self.decided_programs as f64 / self.total_programs as f64) * 100.0
        }
    }

    /// Percentage of enumerated TNF programs that remain undecided holdouts (`0.0..=100.0`).
    pub fn holdout_percentage(&self) -> f64 {
        if self.total_programs == 0 {
            0.0
        } else {
            (self.holdout_programs() as f64 / self.total_programs as f64) * 100.0
        }
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
        self.decided_programs += other.decided_programs;
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
    /// DFS stack of `(partial_program, simulator_at_branch_point, is_symmetric)`.
    stack: Vec<(Program, Simulator, bool)>,
    /// Precomputed valid rules for each pebble count `1..=size`.
    rule_table: Vec<Vec<Rule>>,
    /// Accumulated runtime and decision metrics across tree traversal.
    pub metrics: Vec<StageMetrics>,
}

impl TnfEnumerator {
    /// Create a new TNF enumerator for programs of `size` running up to `max_steps`,
    /// breaking left-right symmetry by default and enabling the decider pipeline on holdouts.
    pub fn new(size: usize, max_steps: u64) -> Self {
        Self::with_options(size, max_steps, true, true)
    }

    /// Create a new TNF enumerator with explicit control over whether the decider pipeline is run on holdouts,
    /// breaking left-right symmetry by default.
    pub fn with_deciders(size: usize, max_steps: u64, use_deciders: bool) -> Self {
        Self::with_options(size, max_steps, use_deciders, true)
    }

    /// Create a new TNF enumerator with explicit control over deciders and left-right symmetry reduction.
    pub fn with_options(
        size: usize,
        max_steps: u64,
        use_deciders: bool,
        break_symmetry: bool,
    ) -> Self {
        let pipeline = PipelineConfig::default_for(size, max_steps);
        Self::with_pipeline(size, max_steps, use_deciders, break_symmetry, pipeline)
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
        let initial_sim = Simulator::new(size);
        Self {
            max_steps,
            use_deciders,
            break_symmetry,
            pipeline,
            stack: vec![(initial_prog, initial_sim, break_symmetry)],
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

    fn from_subtree(
        prog: Program,
        sim: Simulator,
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
            stack: vec![(prog, sim, is_symmetric)],
            rule_table,
            metrics,
        }
    }
}

#[inline]
pub fn resolve_leaf_outcome_timed(
    prog: &Program,
    sim: &mut Simulator,
    use_deciders: bool,
    pipeline: &PipelineConfig,
    metrics: &mut [StageMetrics],
) -> SimOutcome {
    if !use_deciders {
        return SimOutcome::MaxStepsReached { steps: sim.steps() };
    }

    // Stages 0 and 1 are PrefixSim and LeafSim; subsequent stages are evaluated on holdouts.
    for (i, spec) in pipeline.stages.iter().enumerate().skip(2) {
        match spec.kind {
            PipelineStageKind::PrefixSim | PipelineStageKind::LeafSim { .. } => unreachable!(),
            PipelineStageKind::StaticBacktrack => {
                metrics[i].invocations += 1;
                let t0 = Instant::now();
                let res = decide_static_backtrack(prog);
                metrics[i].total_time_nanos += t0.elapsed().as_nanos() as u64;
                if let Some(decider) = res {
                    metrics[i].decided_infinite += 1;
                    return SimOutcome::DecidedNonHalting {
                        decider,
                        steps: sim.steps(),
                    };
                }
            }
            PipelineStageKind::EdgeGliderCurrent => {
                metrics[i].invocations += 1;
                let t0 = Instant::now();
                let res = check_edge_glider_sparse(prog, sim.sparse_entries());
                metrics[i].total_time_nanos += t0.elapsed().as_nanos() as u64;
                if let Some(decider) = res {
                    metrics[i].decided_infinite += 1;
                    return SimOutcome::DecidedNonHalting {
                        decider,
                        steps: sim.steps(),
                    };
                }
            }
            PipelineStageKind::Cycler { steps } => {
                metrics[i].invocations += 1;
                let t0 = Instant::now();
                let res = decide_cycler(prog, steps);
                metrics[i].total_time_nanos += t0.elapsed().as_nanos() as u64;
                if let Some(decider) = res {
                    metrics[i].decided_infinite += 1;
                    return SimOutcome::DecidedNonHalting {
                        decider,
                        steps: sim.steps(),
                    };
                }
            }
            PipelineStageKind::SeparatedComponents { steps } => {
                metrics[i].invocations += 1;
                let t0 = Instant::now();
                let res = decide_separated_components(prog, steps);
                metrics[i].total_time_nanos += t0.elapsed().as_nanos() as u64;
                if let Some(decider) = res {
                    metrics[i].decided_infinite += 1;
                    return SimOutcome::DecidedNonHalting {
                        decider,
                        steps: sim.steps(),
                    };
                }
            }
            PipelineStageKind::Bouncer { steps } => {
                metrics[i].invocations += 1;
                let t0 = Instant::now();
                let res = decide_bouncer(prog, steps);
                metrics[i].total_time_nanos += t0.elapsed().as_nanos() as u64;
                if let Some(decider) = res {
                    metrics[i].decided_infinite += 1;
                    return SimOutcome::DecidedNonHalting {
                        decider,
                        steps: sim.steps(),
                    };
                }
            }
            PipelineStageKind::Ctl { steps } => {
                metrics[i].invocations += 1;
                let t0 = Instant::now();
                let res = decide_ctl(prog, steps);
                metrics[i].total_time_nanos += t0.elapsed().as_nanos() as u64;
                if let Some(decider) = res {
                    metrics[i].decided_infinite += 1;
                    return SimOutcome::DecidedNonHalting {
                        decider,
                        steps: sim.steps(),
                    };
                }
            }
            PipelineStageKind::ExtendedSim { steps } => {
                metrics[i].invocations += 1;
                let t0 = Instant::now();
                let outcome = if sim.steps() < steps {
                    sim.run(prog, steps)
                } else {
                    SimOutcome::MaxStepsReached { steps: sim.steps() }
                };
                metrics[i].total_time_nanos += t0.elapsed().as_nanos() as u64;
                match outcome {
                    SimOutcome::Halted { steps } => {
                        metrics[i].decided_halting += 1;
                        return SimOutcome::Halted { steps };
                    }
                    SimOutcome::DecidedNonHalting { decider, steps } => {
                        metrics[i].decided_infinite += 1;
                        return SimOutcome::DecidedNonHalting { decider, steps };
                    }
                    _ => {}
                }
            }
        }
    }

    SimOutcome::MaxStepsReached { steps: sim.steps() }
}

impl Iterator for TnfEnumerator {
    type Item = EnumEntry;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some((prog, mut sim, is_symmetric)) = self.stack.pop() {
            let t0 = Instant::now();
            let outcome = sim.run(&prog, self.pipeline.initial_steps);
            let elapsed_nanos = t0.elapsed().as_nanos() as u64;

            match outcome {
                SimOutcome::MissingRule { pebbles, .. } => {
                    self.metrics[0].invocations += 1;
                    self.metrics[0].total_time_nanos += elapsed_nanos;

                    let choices = &self.rule_table[pebbles as usize - 1];
                    // Push in reverse so the stack pops in standard lexicographical order.
                    for &rule in choices.iter().rev() {
                        if is_symmetric && rule.left > rule.right {
                            continue;
                        }
                        let child_is_symmetric = is_symmetric && (rule.left == rule.right);
                        let mut child_prog = prog.clone();
                        child_prog
                            .set_rule(pebbles, Some(rule))
                            .expect("valid rule for pebbles");
                        let child_sim = sim;
                        self.stack.push((child_prog, child_sim, child_is_symmetric));
                    }
                }
                SimOutcome::Halted { steps } => {
                    self.metrics[1].invocations += 1;
                    self.metrics[1].decided_halting += 1;
                    self.metrics[1].total_time_nanos += elapsed_nanos;

                    return Some(EnumEntry {
                        program: prog,
                        outcome: SimOutcome::Halted { steps },
                    });
                }
                SimOutcome::MaxStepsReached { .. } => {
                    self.metrics[1].invocations += 1;
                    self.metrics[1].total_time_nanos += elapsed_nanos;

                    let outcome = resolve_leaf_outcome_timed(
                        &prog,
                        &mut sim,
                        self.use_deciders,
                        &self.pipeline,
                        &mut self.metrics,
                    );
                    return Some(EnumEntry {
                        program: prog,
                        outcome,
                    });
                }
                outcome @ SimOutcome::DecidedNonHalting { .. } => {
                    self.metrics[1].invocations += 1;
                    self.metrics[1].decided_infinite += 1;
                    self.metrics[1].total_time_nanos += elapsed_nanos;

                    return Some(EnumEntry {
                        program: prog,
                        outcome,
                    });
                }
            }
        }
        None
    }
}

enum FrontierNode {
    Leaf(EnumEntry),
    Branch(Program, Simulator, bool),
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
        Simulator::new(size),
        break_symmetry,
    )];

    while frontier.len() < target_width
        && frontier
            .iter()
            .any(|n| matches!(n, FrontierNode::Branch(_, _, _)))
    {
        let mut next_frontier = Vec::with_capacity(frontier.len() * 4);
        for node in frontier {
            match node {
                FrontierNode::Leaf(entry) => next_frontier.push(FrontierNode::Leaf(entry)),
                FrontierNode::Branch(prog, mut sim, is_symmetric) => {
                    let start = Instant::now();
                    let outcome = sim.run(&prog, pipeline.initial_steps);
                    let elapsed_nanos = start.elapsed().as_nanos() as u64;

                    match outcome {
                        SimOutcome::MissingRule { pebbles, .. } => {
                            metrics[0].invocations += 1;
                            metrics[0].total_time_nanos += elapsed_nanos;

                            let choices = &rule_table[pebbles as usize - 1];
                            for &rule in choices {
                                if is_symmetric && rule.left > rule.right {
                                    continue;
                                }
                                let child_is_symmetric = is_symmetric && (rule.left == rule.right);
                                let mut child_prog = prog.clone();
                                child_prog
                                    .set_rule(pebbles, Some(rule))
                                    .expect("valid rule for pebbles");
                                let child_sim = sim.clone();
                                next_frontier.push(FrontierNode::Branch(
                                    child_prog,
                                    child_sim,
                                    child_is_symmetric,
                                ));
                            }
                        }
                        SimOutcome::Halted { steps } => {
                            metrics[1].invocations += 1;
                            metrics[1].decided_halting += 1;
                            metrics[1].total_time_nanos += elapsed_nanos;

                            next_frontier.push(FrontierNode::Leaf(EnumEntry {
                                program: prog,
                                outcome: SimOutcome::Halted { steps },
                            }));
                        }
                        SimOutcome::MaxStepsReached { .. } => {
                            metrics[1].invocations += 1;
                            metrics[1].total_time_nanos += elapsed_nanos;

                            let outcome = resolve_leaf_outcome_timed(
                                &prog,
                                &mut sim,
                                use_deciders,
                                pipeline,
                                metrics,
                            );
                            next_frontier.push(FrontierNode::Leaf(EnumEntry {
                                program: prog,
                                outcome,
                            }));
                        }
                        outcome @ SimOutcome::DecidedNonHalting { .. } => {
                            metrics[1].invocations += 1;
                            metrics[1].decided_infinite += 1;
                            metrics[1].total_time_nanos += elapsed_nanos;

                            next_frontier.push(FrontierNode::Leaf(EnumEntry {
                                program: prog,
                                outcome,
                            }));
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
    pub decided_programs: u64,
    pub holdout_programs: u64,
    pub max_halting_steps: Option<u64>,
}

/// Enumerate all TNF programs of `size` in parallel using Rayon, returning the exact
/// `EnumStats` and any collected `EnumEntry` items matching `filter_entry`.
///
/// Calls `on_progress` periodically with a live `ProgressSnapshot`.
pub fn enumerate_parallel<F, P>(
    size: usize,
    max_steps: u64,
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
        return (EnumStats::new(0, max_steps), Vec::new());
    }

    let pipeline = PipelineConfig::default_for(size, max_steps);
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
            decided_programs: dec,
            holdout_programs: tot.saturating_sub(halt).saturating_sub(dec),
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
            let mut local_stats = EnumStats::with_pipeline(size, max_steps, &pipeline);
            let mut local_entries = Vec::new();
            match node {
                FrontierNode::Leaf(entry) => {
                    local_stats.record(&entry);
                    let b_halt = u64::from(matches!(entry.outcome, SimOutcome::Halted { .. }));
                    let b_dec =
                        u64::from(matches!(entry.outcome, SimOutcome::DecidedNonHalting { .. }));
                    flush_batch(1, b_halt, b_dec, local_stats.max_halting_steps);
                    if collect_entries && (!holdouts_only || entry.outcome.is_holdout()) {
                        local_entries.push(entry);
                    }
                }
                FrontierNode::Branch(prog, sim, is_symmetric) => {
                    let mut sub_enum = TnfEnumerator::from_subtree(
                        prog,
                        sim,
                        max_steps,
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
                            SimOutcome::DecidedNonHalting { .. } => {
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

    let mut final_stats = EnumStats::with_pipeline(size, max_steps, &pipeline);
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
            (3, 114, 30, 84, 0, 3),
            (4, 933, 223, 710, 0, 6),
        ];

        for (size, exp_total, exp_halted, exp_decided, exp_holdouts, exp_max_steps) in expected {
            let max_steps = 25;
            let mut stats = EnumStats::new(size, max_steps);

            for entry in TnfEnumerator::with_options(size, max_steps, true, false) {
                stats.record(&entry);
            }

            assert_eq!(stats.total_programs, exp_total, "size {size} total");
            assert_eq!(stats.halted_programs, exp_halted, "size {size} halted");
            assert_eq!(stats.decided_programs, exp_decided, "size {size} decided");
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
        let mut stats = EnumStats::new(size, max_steps);
        for entry in TnfEnumerator::with_options(size, max_steps, true, false) {
            stats.record(&entry);
        }
        assert_eq!(stats.total_programs, 12_161);
        assert_eq!(stats.halted_programs, 2_517);
        assert_eq!(stats.decided_programs, 9_644);
        assert_eq!(stats.holdout_programs(), 0);
        assert_eq!(stats.max_halting_steps, Some(11));

        // Verify parallel enumeration produces identical stats and champion
        let (par_stats, _) =
            enumerate_parallel(size, max_steps, true, false, false, false, |_| {}, |_| false);
        assert_eq!(par_stats, stats);
    }

    #[test]
    fn test_tnf_enumerator_symmetry_reduction_sizes_1_to_5() {
        let expected = [
            // (size, expected_total, expected_halted, expected_decided, expected_holdouts, expected_max_steps)
            (1, 2u64, 1u64, 1u64, 0u64, 0u64),
            (2, 7, 3, 4, 0, 1),
            (3, 58, 16, 42, 0, 3),
            (4, 469, 114, 355, 0, 6),
            (5, 6084, 1262, 4822, 0, 11),
        ];

        for (size, exp_total, exp_halted, exp_decided, exp_holdouts, exp_max_steps) in expected {
            let max_steps = 50;
            let mut stats = EnumStats::new(size, max_steps);

            for entry in TnfEnumerator::new(size, max_steps) {
                stats.record(&entry);
            }

            assert_eq!(stats.total_programs, exp_total, "size {size} total");
            assert_eq!(stats.halted_programs, exp_halted, "size {size} halted");
            assert_eq!(stats.decided_programs, exp_decided, "size {size} decided");
            assert_eq!(
                stats.holdout_programs(),
                exp_holdouts,
                "size {size} holdouts"
            );
            assert_eq!(stats.max_halting_steps, Some(exp_max_steps));

            // Verify parallel enumeration matches sequential exactly
            let (par_stats, _) =
                enumerate_parallel(size, max_steps, true, true, false, false, |_| {}, |_| false);
            assert_eq!(par_stats, stats, "parallel matches sequential for size {size}");
        }
    }
}
