use crate::program::{Program, Rule};
use crate::simulation::{simulate, SimOutcome, Simulator};

/// Result item produced when enumerating and simulating a program (or TNF subtree leaf).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EnumEntry {
    pub program: Program,
    pub outcome: SimOutcome,
    /// Number of complete Cartesian programs represented by this program.
    /// For complete programs this is `1`; for TNF leaves with undefined rules,
    /// this is the product of rule choices over all unreached pebble counts.
    pub expansion_factor: u128,
}

/// Summary statistics accumulated across an enumeration run.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct EnumStats {
    pub size: usize,
    pub max_steps: u64,
    /// Number of distinct programs (TNF leaves or Cartesian programs) simulated.
    pub leaves_simulated: u128,
    /// Number of simulated leaves that halted.
    pub leaves_halted: u128,
    /// Total number of complete Cartesian programs represented (`sum(expansion_factor)`).
    pub total_programs: u128,
    /// Total number of complete Cartesian programs that halted.
    pub halted_programs: u128,
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
        self.leaves_simulated += 1;
        self.total_programs += entry.expansion_factor;

        if let SimOutcome::Halted { steps } = entry.outcome {
            self.leaves_halted += 1;
            self.halted_programs += entry.expansion_factor;

            let is_new_max = match self.max_halting_steps {
                None => true,
                Some(prev_max) => steps > prev_max,
            };
            if is_new_max {
                self.max_halting_steps = Some(steps);
                self.champion = Some(entry.program.clone());
            }
        }
    }

    /// Number of non-halting holdout programs in full Cartesian space.
    #[inline]
    pub fn holdout_programs(&self) -> u128 {
        self.total_programs.saturating_sub(self.halted_programs)
    }

    /// Number of non-halting holdout leaves simulated.
    #[inline]
    pub fn holdout_leaves(&self) -> u128 {
        self.leaves_simulated.saturating_sub(self.leaves_halted)
    }

    /// Percentage of full Cartesian programs that halted (`0.0..=100.0`).
    pub fn halted_percentage(&self) -> f64 {
        if self.total_programs == 0 {
            0.0
        } else {
            (self.halted_programs as f64 / self.total_programs as f64) * 100.0
        }
    }

    /// Percentage of simulated TNF leaves that halted (`0.0..=100.0`).
    pub fn leaves_halted_percentage(&self) -> f64 {
        if self.leaves_simulated == 0 {
            0.0
        } else {
            (self.leaves_halted as f64 / self.leaves_simulated as f64) * 100.0
        }
    }
}

/// Tree-Normal-Form (TNF) enumerator that lazily branches on rules for pebble counts `k`
/// only when a cell with `k` pebbles is actually reached during simulation.
///
/// Shares simulation prefixes across branches by snapshotting the `Simulator` at the branch point.
pub struct TnfEnumerator {
    max_steps: u64,
    /// DFS stack of `(partial_program, simulator_at_branch_point)`.
    stack: Vec<(Program, Simulator)>,
    /// Precomputed valid rules for each pebble count `1..=size`.
    rule_table: Vec<Vec<Rule>>,
}

impl TnfEnumerator {
    /// Create a new TNF enumerator for programs of `size` running up to `max_steps`.
    pub fn new(size: usize, max_steps: u64) -> Self {
        if size == 0 {
            return Self {
                max_steps,
                stack: Vec::new(),
                rule_table: Vec::new(),
            };
        }
        let rule_table: Vec<Vec<Rule>> = (1..=size as u8).map(Rule::all_for_pebbles).collect();
        let initial_prog = Program::empty(size).expect("size > 0");
        let initial_sim = Simulator::new(size);
        Self {
            max_steps,
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
                outcome @ (SimOutcome::Halted { .. } | SimOutcome::MaxStepsReached { .. }) => {
                    let expansion_factor = prog.expansion_factor();
                    return Some(EnumEntry {
                        program: prog,
                        outcome,
                        expansion_factor,
                    });
                }
            }
        }
        None
    }
}

/// Complete Cartesian enumerator yielding every fully specified `Program` of a given `size`
/// in lexicographical order.
pub struct CartesianEnumerator {
    size: usize,
    rule_table: Vec<Vec<Rule>>,
    indices: Vec<usize>,
    done: bool,
}

impl CartesianEnumerator {
    /// Create a new Cartesian enumerator over all $\prod_{k=1}^{\text{size}} \frac{(k+1)(k+2)}{2}$ programs.
    pub fn new(size: usize) -> Self {
        if size == 0 {
            return Self {
                size: 0,
                rule_table: Vec::new(),
                indices: Vec::new(),
                done: true,
            };
        }
        let rule_table: Vec<Vec<Rule>> = (1..=size as u8).map(Rule::all_for_pebbles).collect();
        Self {
            size,
            rule_table,
            indices: vec![0; size],
            done: false,
        }
    }

    /// Convert this program iterator into an iterator of `EnumEntry` simulated up to `max_steps`.
    pub fn with_simulation(self, max_steps: u64) -> impl Iterator<Item = EnumEntry> {
        self.map(move |program| {
            let outcome = simulate(&program, max_steps);
            EnumEntry {
                program,
                outcome,
                expansion_factor: 1,
            }
        })
    }
}

impl Iterator for CartesianEnumerator {
    type Item = Program;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }

        let rules: Vec<Option<Rule>> = self
            .indices
            .iter()
            .enumerate()
            .map(|(k_idx, &choice_idx)| Some(self.rule_table[k_idx][choice_idx]))
            .collect();
        let prog = Program::new(rules).expect("valid rules");

        // Advance odometer from right to left (k = size down to 1).
        let mut carry = true;
        for k_idx in (0..self.size).rev() {
            if carry {
                self.indices[k_idx] += 1;
                if self.indices[k_idx] < self.rule_table[k_idx].len() {
                    carry = false;
                    break;
                } else {
                    self.indices[k_idx] = 0;
                }
            }
        }
        if carry {
            self.done = true;
        }

        Some(prog)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cartesian_enumerator_counts() {
        for size in 1..=4 {
            let count = CartesianEnumerator::new(size).count() as u128;
            assert_eq!(count, Program::total_cartesian_programs(size));
        }
    }

    #[test]
    fn test_tnf_matches_cartesian_exactly_for_sizes_1_to_4() {
        let expected_max_steps = [(1, 0u64), (2, 1), (3, 3), (4, 6)];

        for (size, expected_bb) in expected_max_steps {
            let max_steps = 25;

            let mut tnf_stats = EnumStats::new(size, max_steps);
            for entry in TnfEnumerator::new(size, max_steps) {
                // Verify that running the TNF leaf program from scratch at t=0 yields the exact same outcome
                let fresh_outcome = simulate(&entry.program, max_steps);
                assert_eq!(entry.outcome, fresh_outcome);
                tnf_stats.record(&entry);
            }

            let mut cart_stats = EnumStats::new(size, max_steps);
            for entry in CartesianEnumerator::new(size).with_simulation(max_steps) {
                cart_stats.record(&entry);
            }

            assert_eq!(
                tnf_stats.total_programs,
                Program::total_cartesian_programs(size)
            );
            assert_eq!(tnf_stats.total_programs, cart_stats.total_programs);
            assert_eq!(tnf_stats.halted_programs, cart_stats.halted_programs);
            assert_eq!(tnf_stats.holdout_programs(), cart_stats.holdout_programs());
            assert_eq!(tnf_stats.max_halting_steps, Some(expected_bb));
            assert_eq!(cart_stats.max_halting_steps, Some(expected_bb));
            assert!(tnf_stats.leaves_simulated <= cart_stats.leaves_simulated);
        }
    }

    #[test]
    fn test_tnf_pebble_5_champion() {
        let size = 5;
        let max_steps = 50;
        let mut stats = EnumStats::new(size, max_steps);
        for entry in TnfEnumerator::new(size, max_steps) {
            stats.record(&entry);
        }
        assert_eq!(stats.total_programs, 56_700);
        assert_eq!(stats.max_halting_steps, Some(11));
    }
}
