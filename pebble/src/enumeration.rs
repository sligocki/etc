use crate::deciders::{run_decider_pipeline_sparse, Decider};
use crate::program::{Program, Rule};
use crate::simulation::{SimOutcome, Simulator};

/// Result item produced when enumerating and simulating a TNF program.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EnumEntry {
    pub program: Program,
    pub outcome: SimOutcome,
}

/// Summary statistics accumulated across a TNF enumeration run.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
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
}

impl EnumStats {
    /// Create a fresh statistics accumulator for `size` and `max_steps`.
    pub fn new(size: usize, max_steps: u64) -> Self {
        Self {
            size,
            max_steps,
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
/// When a leaf reaches `max_steps` without halting, optionally runs the decider pipeline
/// (`EdgeGlider` -> `Cycler`/`TranslatedCycler` -> `SeparatedComponents` -> `Bouncer`).
pub struct TnfEnumerator {
    max_steps: u64,
    use_deciders: bool,
    break_symmetry: bool,
    /// DFS stack of `(partial_program, simulator_at_branch_point, is_symmetric)`.
    stack: Vec<(Program, Simulator, bool)>,
    /// Precomputed valid rules for each pebble count `1..=size`.
    rule_table: Vec<Vec<Rule>>,
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
        if size == 0 {
            return Self {
                max_steps,
                use_deciders,
                break_symmetry,
                stack: Vec::new(),
                rule_table: Vec::new(),
            };
        }
        let rule_table: Vec<Vec<Rule>> = (1..=size as u8).map(Rule::all_for_pebbles).collect();
        let initial_prog = Program::empty(size).expect("size > 0");
        let initial_sim = Simulator::new(size);
        Self {
            max_steps,
            use_deciders,
            break_symmetry,
            stack: vec![(initial_prog, initial_sim, break_symmetry)],
            rule_table,
        }
    }

    /// Returns whether left-right symmetry reduction is enabled.
    pub fn break_symmetry(&self) -> bool {
        self.break_symmetry
    }

    fn from_subtree(
        prog: Program,
        sim: Simulator,
        max_steps: u64,
        use_deciders: bool,
        break_symmetry: bool,
        is_symmetric: bool,
        rule_table: Vec<Vec<Rule>>,
    ) -> Self {
        Self {
            max_steps,
            use_deciders,
            break_symmetry,
            stack: vec![(prog, sim, is_symmetric)],
            rule_table,
        }
    }
}

#[inline]
fn resolve_leaf_outcome(
    prog: &Program,
    sim: &Simulator,
    steps: u64,
    max_steps: u64,
    use_deciders: bool,
) -> SimOutcome {
    if use_deciders {
        if let Some(decider) =
            run_decider_pipeline_sparse(prog, Some(sim.sparse_entries()), max_steps)
        {
            SimOutcome::DecidedNonHalting { decider, steps }
        } else {
            SimOutcome::MaxStepsReached { steps }
        }
    } else {
        SimOutcome::MaxStepsReached { steps }
    }
}

impl Iterator for TnfEnumerator {
    type Item = EnumEntry;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some((prog, mut sim, is_symmetric)) = self.stack.pop() {
            match sim.run(&prog, self.max_steps) {
                SimOutcome::MissingRule { pebbles, .. } => {
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
                        let child_sim = sim.clone();
                        self.stack.push((child_prog, child_sim, child_is_symmetric));
                    }
                }
                SimOutcome::Halted { steps } => {
                    return Some(EnumEntry {
                        program: prog,
                        outcome: SimOutcome::Halted { steps },
                    });
                }
                SimOutcome::MaxStepsReached { steps } => {
                    let outcome =
                        resolve_leaf_outcome(&prog, &sim, steps, self.max_steps, self.use_deciders);
                    return Some(EnumEntry {
                        program: prog,
                        outcome,
                    });
                }
                outcome @ SimOutcome::DecidedNonHalting { .. } => {
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
    max_steps: u64,
    use_deciders: bool,
    break_symmetry: bool,
    rule_table: &[Vec<Rule>],
    target_width: usize,
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
                FrontierNode::Branch(prog, mut sim, is_symmetric) => match sim.run(&prog, max_steps) {
                    SimOutcome::MissingRule { pebbles, .. } => {
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
                        next_frontier.push(FrontierNode::Leaf(EnumEntry {
                            program: prog,
                            outcome: SimOutcome::Halted { steps },
                        }));
                    }
                    SimOutcome::MaxStepsReached { steps } => {
                        let outcome =
                            resolve_leaf_outcome(&prog, &sim, steps, max_steps, use_deciders);
                        next_frontier.push(FrontierNode::Leaf(EnumEntry {
                            program: prog,
                            outcome,
                        }));
                    }
                    outcome @ SimOutcome::DecidedNonHalting { .. } => {
                        next_frontier.push(FrontierNode::Leaf(EnumEntry {
                            program: prog,
                            outcome,
                        }));
                    }
                },
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

    let rule_table: Vec<Vec<Rule>> = (1..=size as u8).map(Rule::all_for_pebbles).collect();
    let frontier = build_frontier(
        size,
        max_steps,
        use_deciders,
        break_symmetry,
        &rule_table,
        4096,
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
            let mut local_stats = EnumStats::new(size, max_steps);
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
                    let sub_enum = TnfEnumerator::from_subtree(
                        prog,
                        sim,
                        max_steps,
                        use_deciders,
                        break_symmetry,
                        is_symmetric,
                        rule_table.clone(),
                    );
                    let mut b_tot = 0u64;
                    let mut b_halt = 0u64;
                    let mut b_dec = 0u64;
                    let mut b_max: Option<u64> = None;

                    for entry in sub_enum {
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
                    flush_batch(b_tot, b_halt, b_dec, b_max);
                }
            }
            (local_stats, local_entries)
        })
        .collect();

    let mut final_stats = EnumStats::new(size, max_steps);
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
