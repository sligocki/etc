use crate::deciders::{run_decider_pipeline, Decider};
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
    /// `[EdgeGlider, Cycler, TranslatedCycler, SeparatedComponents, Bouncer]`.
    pub decided_by_kind: [u64; 5],
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
}

/// Tree-Normal-Form (TNF) enumerator that lazily branches on rules for pebble counts `k`
/// only when a cell with `k` pebbles is actually reached during simulation.
///
/// Shares simulation prefixes across branches by snapshotting the `Simulator` at the branch point.
/// When a leaf reaches `max_steps` without halting, optionally runs the decider pipeline
/// (`EdgeGlider` -> `Cycler`/`TranslatedCycler` -> `SeparatedComponents`).
pub struct TnfEnumerator {
    max_steps: u64,
    use_deciders: bool,
    /// DFS stack of `(partial_program, simulator_at_branch_point)`.
    stack: Vec<(Program, Simulator)>,
    /// Precomputed valid rules for each pebble count `1..=size`.
    rule_table: Vec<Vec<Rule>>,
}

impl TnfEnumerator {
    /// Create a new TNF enumerator for programs of `size` running up to `max_steps`,
    /// with the non-halting decider pipeline enabled on holdouts.
    pub fn new(size: usize, max_steps: u64) -> Self {
        Self::with_deciders(size, max_steps, true)
    }

    /// Create a new TNF enumerator with explicit control over whether the decider pipeline is run on holdouts.
    pub fn with_deciders(size: usize, max_steps: u64, use_deciders: bool) -> Self {
        if size == 0 {
            return Self {
                max_steps,
                use_deciders,
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
            stack: vec![(initial_prog, initial_sim)],
            rule_table,
        }
    }
}

impl Iterator for TnfEnumerator {
    type Item = EnumEntry;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some((prog, mut sim)) = self.stack.pop() {
            match sim.run(&prog, self.max_steps) {
                SimOutcome::MissingRule { pebbles, .. } => {
                    let choices = &self.rule_table[pebbles as usize - 1];
                    // Push in reverse so the stack pops in standard lexicographical order.
                    for &rule in choices.iter().rev() {
                        let mut child_prog = prog.clone();
                        child_prog
                            .set_rule(pebbles, Some(rule))
                            .expect("valid rule for pebbles");
                        let child_sim = sim.clone();
                        self.stack.push((child_prog, child_sim));
                    }
                }
                SimOutcome::Halted { steps } => {
                    return Some(EnumEntry {
                        program: prog,
                        outcome: SimOutcome::Halted { steps },
                    });
                }
                SimOutcome::MaxStepsReached { steps } => {
                    let outcome = if self.use_deciders {
                        if let Some(decider) =
                            run_decider_pipeline(&prog, Some(sim.cells()), self.max_steps)
                        {
                            SimOutcome::DecidedNonHalting { decider, steps }
                        } else {
                            SimOutcome::MaxStepsReached { steps }
                        }
                    } else {
                        SimOutcome::MaxStepsReached { steps }
                    };
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
        }
    }

    #[test]
    fn test_tnf_pebble_5_champion_and_zero_holdouts() {
        let size = 5;
        let max_steps = 50;
        let mut stats = EnumStats::new(size, max_steps);
        for entry in TnfEnumerator::new(size, max_steps) {
            stats.record(&entry);
        }
        assert_eq!(stats.total_programs, 12_161);
        assert_eq!(stats.halted_programs, 2_517);
        assert_eq!(stats.decided_programs, 9_644);
        assert_eq!(stats.holdout_programs(), 0);
        assert_eq!(stats.max_halting_steps, Some(11));
    }
}
