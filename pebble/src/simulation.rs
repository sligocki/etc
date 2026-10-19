use crate::deciders::Decider;
use crate::program::{encode_pebble_digit, Program};
use std::fmt;

/// Result of attempting a single step in a Pebble Automaton simulation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StepResult {
    /// The automaton advanced by 1 generation (`state(t+1) != state(t)`).
    Stepped,
    /// The automaton stabilized (`state(t+1) == state(t)` at the exact same coordinates).
    Halted,
    /// A cell with `k` pebbles was encountered whose rule is undefined (`None`) in the program.
    MissingRule(u8),
}

/// Final outcome of running a Pebble Automaton up to a step limit.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SimOutcome {
    /// The automaton stabilized after `steps` transitions.
    Halted { steps: u64 },
    /// The automaton was proven non-halting by `decider` after simulating `steps` transitions.
    DecidedNonHalting { decider: Decider, steps: u64 },
    /// The automaton did not stabilize within `steps` transitions and was not decided.
    MaxStepsReached { steps: u64 },
    /// Simulation paused at `steps` because rule for `pebbles` is undefined.
    MissingRule { pebbles: u8, steps: u64 },
}

impl SimOutcome {
    /// Returns `true` if the outcome is `SimOutcome::Halted`.
    #[inline]
    pub fn is_halted(&self) -> bool {
        matches!(self, SimOutcome::Halted { .. })
    }

    /// Returns `true` if the outcome is `SimOutcome::DecidedNonHalting`.
    #[inline]
    pub fn is_decided_non_halting(&self) -> bool {
        matches!(self, SimOutcome::DecidedNonHalting { .. })
    }

    /// Returns `true` if the outcome is an undecided holdout (`SimOutcome::MaxStepsReached`).
    #[inline]
    pub fn is_holdout(&self) -> bool {
        matches!(self, SimOutcome::MaxStepsReached { .. })
    }

    /// Returns the step count associated with this outcome.
    #[inline]
    pub fn steps(&self) -> u64 {
        match *self {
            SimOutcome::Halted { steps }
            | SimOutcome::DecidedNonHalting { steps, .. }
            | SimOutcome::MaxStepsReached { steps }
            | SimOutcome::MissingRule { steps, .. } => steps,
        }
    }
}

impl fmt::Display for SimOutcome {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SimOutcome::Halted { steps } => write!(f, "HALT\t{steps}"),
            SimOutcome::DecidedNonHalting { decider, steps } => {
                write!(f, "DECIDED\t{decider}\t{steps}")
            }
            SimOutcome::MaxStepsReached { steps } => write!(f, "MAX_STEPS\t{steps}"),
            SimOutcome::MissingRule { pebbles, steps } => {
                write!(f, "MISSING_RULE\t{pebbles}\t{steps}")
            }
        }
    }
}

/// A snapshot of the active tape at a specific generation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TapeSnapshot {
    pub step: u64,
    pub offset: isize,
    pub cells: Vec<u8>,
}

impl TapeSnapshot {
    /// Minimum active x-coordinate with non-zero pebbles.
    #[inline]
    pub fn min_x(&self) -> isize {
        self.offset
    }

    /// Maximum active x-coordinate with non-zero pebbles.
    #[inline]
    pub fn max_x(&self) -> isize {
        if self.cells.is_empty() {
            self.offset
        } else {
            self.offset + self.cells.len() as isize - 1
        }
    }

    /// Read the pebble count at coordinate `x`.
    #[inline]
    pub fn get(&self, x: isize) -> u8 {
        if x < self.offset {
            return 0;
        }
        let idx = (x - self.offset) as usize;
        self.cells.get(idx).copied().unwrap_or(0)
    }

    /// Render the tape over `[min_x..=max_x]` in wiki style (`.` for `0`, `1-9`/`a-z` for `>0`).
    pub fn format_range(&self, min_x: isize, max_x: isize) -> String {
        let len = (max_x - min_x + 1).max(0) as usize;
        let mut out = String::with_capacity(len);
        for x in min_x..=max_x {
            let v = self.get(x);
            if v == 0 {
                out.push('.');
            } else {
                out.push(encode_pebble_digit(v).unwrap_or('#'));
            }
        }
        out
    }
}

/// Stateful simulator for a 1D Pebble Automaton.
#[derive(Debug, Clone)]
pub struct Simulator {
    offset: isize,
    cells: Vec<u8>,
    steps: u64,
    scratch: Vec<u8>,
}

impl Simulator {
    /// Create a new simulator initialized with `initial_pebbles` at `x = 0`, `t = 0`.
    pub fn new(initial_pebbles: usize) -> Self {
        let p = initial_pebbles as u8;
        let cells = if p > 0 { vec![p] } else { Vec::new() };
        Self {
            offset: 0,
            cells,
            steps: 0,
            scratch: Vec::with_capacity(initial_pebbles + 4),
        }
    }

    /// Current generation / step count `t`.
    #[inline]
    pub fn steps(&self) -> u64 {
        self.steps
    }

    /// Current x-coordinate of `cells()[0]`.
    #[inline]
    pub fn offset(&self) -> isize {
        self.offset
    }

    /// Slice of active cells spanning `[offset .. offset + cells.len() - 1]`.
    #[inline]
    pub fn cells(&self) -> &[u8] {
        &self.cells
    }

    /// Total number of pebbles currently on the tape.
    pub fn total_pebbles(&self) -> usize {
        self.cells.iter().map(|&c| c as usize).sum()
    }

    /// Capture a snapshot of the current tape state.
    pub fn snapshot(&self) -> TapeSnapshot {
        TapeSnapshot {
            step: self.steps,
            offset: self.offset,
            cells: self.cells.clone(),
        }
    }

    /// Attempt to advance the simulation by 1 step.
    ///
    /// - If any non-zero cell `k` on the tape has `program.rule(k) == None`, returns
    ///   `StepResult::MissingRule(k)` without mutating the state.
    /// - If the next state equals the current state at the exact same coordinates, returns
    ///   `StepResult::Halted` without incrementing `steps`.
    /// - Otherwise, updates the tape, increments `steps` by 1, and returns `StepResult::Stepped`.
    pub fn step(&mut self, program: &Program) -> StepResult {
        if self.cells.is_empty() {
            return StepResult::Halted;
        }

        // Check that all pebble counts present in the current configuration have defined rules.
        for &k in &self.cells {
            if k > 0 && program.rule(k).is_none() {
                return StepResult::MissingRule(k);
            }
        }

        let next_len = self.cells.len() + 2;
        self.scratch.clear();
        self.scratch.resize(next_len, 0);

        for (i, &k) in self.cells.iter().enumerate() {
            if k == 0 {
                continue;
            }
            // Safe to unwrap because we verified all non-zero `k` have `Some(rule)` above.
            let rule = program.rule(k).unwrap();
            self.scratch[i] += rule.left;
            self.scratch[i + 1] += rule.stay;
            self.scratch[i + 2] += rule.right;
        }

        // Find non-zero bounding box in `scratch`.
        let Some(first_nz) = self.scratch.iter().position(|&v| v > 0) else {
            self.cells.clear();
            self.offset = 0;
            self.steps += 1;
            return StepResult::Stepped;
        };
        let last_nz = self.scratch.iter().rposition(|&v| v > 0).unwrap();

        let next_offset = self.offset - 1 + first_nz as isize;
        let next_slice = &self.scratch[first_nz..=last_nz];

        if next_offset == self.offset && next_slice == self.cells.as_slice() {
            return StepResult::Halted;
        }

        self.offset = next_offset;
        self.cells.clear();
        self.cells.extend_from_slice(next_slice);
        self.steps += 1;
        StepResult::Stepped
    }

    /// Run the simulator from its current state up to `max_steps` total transitions.
    pub fn run(&mut self, program: &Program, max_steps: u64) -> SimOutcome {
        loop {
            // Before taking a transition past `max_steps`, check if the current state is already stable
            // or missing a rule, and only advance if `self.steps < max_steps`.
            if self.steps >= max_steps {
                // Check if the state at `self.steps` has stabilized or is missing a rule without advancing.
                for &k in &self.cells {
                    if k > 0 && program.rule(k).is_none() {
                        return SimOutcome::MissingRule {
                            pebbles: k,
                            steps: self.steps,
                        };
                    }
                }
                if self.is_current_state_stable(program) {
                    return SimOutcome::Halted { steps: self.steps };
                }
                return SimOutcome::MaxStepsReached { steps: self.steps };
            }

            match self.step(program) {
                StepResult::Stepped => continue,
                StepResult::Halted => return SimOutcome::Halted { steps: self.steps },
                StepResult::MissingRule(k) => {
                    return SimOutcome::MissingRule {
                        pebbles: k,
                        steps: self.steps,
                    }
                }
            }
        }
    }

    /// Run the simulator from its current state up to `max_steps`, checking at each step
    /// whether an edge particle satisfies the light-cone escaping `EdgeGlider` invariant.
    ///
    /// Exits early with `SimOutcome::DecidedNonHalting { decider: Decider::EdgeGlider, steps }`
    /// as soon as an edge glider is detected, or `SimOutcome::Halted` if the tape stabilizes.
    pub fn run_with_edge_glider(&mut self, program: &Program, max_steps: u64) -> SimOutcome {
        loop {
            if let Some(decider) = crate::deciders::check_edge_glider_tape(program, self.cells()) {
                return SimOutcome::DecidedNonHalting {
                    decider,
                    steps: self.steps,
                };
            }
            if self.steps >= max_steps {
                for &k in &self.cells {
                    if k > 0 && program.rule(k).is_none() {
                        return SimOutcome::MissingRule {
                            pebbles: k,
                            steps: self.steps,
                        };
                    }
                }
                if self.is_current_state_stable(program) {
                    return SimOutcome::Halted { steps: self.steps };
                }
                return SimOutcome::MaxStepsReached { steps: self.steps };
            }

            match self.step(program) {
                StepResult::Stepped => continue,
                StepResult::Halted => return SimOutcome::Halted { steps: self.steps },
                StepResult::MissingRule(k) => {
                    return SimOutcome::MissingRule {
                        pebbles: k,
                        steps: self.steps,
                    }
                }
            }
        }
    }

    /// Check if the current state `state(t)` satisfies `state(t+1) == state(t)` without mutating `cells` or `steps`.
    fn is_current_state_stable(&mut self, program: &Program) -> bool {
        if self.cells.is_empty() {
            return true;
        }
        let next_len = self.cells.len() + 2;
        self.scratch.clear();
        self.scratch.resize(next_len, 0);

        for (i, &k) in self.cells.iter().enumerate() {
            if k == 0 {
                continue;
            }
            let Some(rule) = program.rule(k) else {
                return false;
            };
            self.scratch[i] += rule.left;
            self.scratch[i + 1] += rule.stay;
            self.scratch[i + 2] += rule.right;
        }

        let Some(first_nz) = self.scratch.iter().position(|&v| v > 0) else {
            return false;
        };
        let last_nz = self.scratch.iter().rposition(|&v| v > 0).unwrap();
        let next_offset = self.offset - 1 + first_nz as isize;
        let next_slice = &self.scratch[first_nz..=last_nz];

        next_offset == self.offset && next_slice == self.cells.as_slice()
    }
}

/// Convenience function to simulate a `program` from `t = 0` for up to `max_steps`.
pub fn simulate(program: &Program, max_steps: u64) -> SimOutcome {
    let mut sim = Simulator::new(program.size());
    sim.run(program, max_steps)
}

/// Simulate a `program` from `t = 0` up to `max_steps`, early-exiting immediately
/// if an edge particle satisfies the escaping `EdgeGlider` invariant or if the tape halts.
pub fn simulate_with_edge_glider(program: &Program, max_steps: u64) -> SimOutcome {
    let mut sim = Simulator::new(program.size());
    sim.run_with_edge_glider(program, max_steps)
}

/// Simulate a `program` from `t = 0` for up to `max_steps` and record the tape at each generation.
pub fn simulate_with_trace(program: &Program, max_steps: u64) -> (SimOutcome, Vec<TapeSnapshot>) {
    let mut sim = Simulator::new(program.size());
    let mut trace = Vec::new();
    trace.push(sim.snapshot());

    loop {
        if sim.steps() >= max_steps {
            let outcome = sim.run(program, max_steps);
            return (outcome, trace);
        }
        match sim.step(program) {
            StepResult::Stepped => {
                trace.push(sim.snapshot());
            }
            StepResult::Halted => {
                return (SimOutcome::Halted { steps: sim.steps() }, trace);
            }
            StepResult::MissingRule(k) => {
                return (
                    SimOutcome::MissingRule {
                        pebbles: k,
                        steps: sim.steps(),
                    },
                    trace,
                );
            }
        }
    }
}

/// Format a slice of `TapeSnapshot`s aligned to a common `[min_x..=max_x]` bounding box,
/// matching the visual diagram style on the BusyBeaverWiki.
pub fn format_trace_bounds(trace: &[TapeSnapshot]) -> (isize, isize) {
    if trace.is_empty() {
        return (0, 0);
    }
    let min_x = trace.iter().map(TapeSnapshot::min_x).min().unwrap_or(0);
    let max_x = trace.iter().map(TapeSnapshot::max_x).max().unwrap_or(0);
    (min_x, max_x)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_wiki_champions_1_to_9() {
        let champions = [
            ("00", 0u64),
            ("00_01", 1),
            ("00_01_20", 3),
            ("00_01_20_03", 6),
            ("00_11_03_21_04", 11),
            ("00_11_03_21_40_15", 17),
            ("00_11_03_21_10_33_61", 28),
            ("00_11_03_21_50_30_24_70", 63),
            ("00_02_01_40_14_12_00_52_81", 63577),
        ];

        for (code, expected_steps) in champions {
            let prog: Program = code.parse().unwrap();
            let outcome = simulate(&prog, expected_steps + 10);
            assert_eq!(
                outcome,
                SimOutcome::Halted {
                    steps: expected_steps
                },
                "champion {code} did not halt at expected step {expected_steps}"
            );

            // Also test when max_steps equals exact halting step count
            let exact_outcome = simulate(&prog, expected_steps);
            assert_eq!(
                exact_outcome,
                SimOutcome::Halted {
                    steps: expected_steps
                },
                "champion {code} with exact max_steps={expected_steps} failed"
            );

            // And 1 step less than halting should report MaxStepsReached
            if expected_steps > 0 {
                let short_outcome = simulate(&prog, expected_steps - 1);
                assert_eq!(
                    short_outcome,
                    SimOutcome::MaxStepsReached {
                        steps: expected_steps - 1
                    }
                );
            }
        }
    }

    #[test]
    fn test_pebble_5_trace_matches_wiki() {
        let prog: Program = "00_11_03_21_04".parse().unwrap();
        let (outcome, trace) = simulate_with_trace(&prog, 100);
        assert_eq!(outcome, SimOutcome::Halted { steps: 11 });
        assert_eq!(trace.len(), 12); // t = 0..=11

        let (min_x, max_x) = format_trace_bounds(&trace);
        let rendered: Vec<String> = trace
            .iter()
            .map(|snap| snap.format_range(min_x, max_x))
            .collect();

        let expected = vec![
            ".5.....", ".14....", ".311...", "..41...", ".212...", "1.3.1..", "1..31..", "1...4..",
            "1..211.", "1.1.21.", "1.11.2.", "1.111.1",
        ];
        assert_eq!(rendered, expected);
    }

    #[test]
    fn test_glider_does_not_halt() {
        let prog: Program = "01".parse().unwrap();
        let mut sim = Simulator::new(prog.size());
        let outcome = sim.run(&prog, 25);
        assert_eq!(outcome, SimOutcome::MaxStepsReached { steps: 25 });
        assert_eq!(sim.offset(), 25);
        assert_eq!(sim.cells(), &[1]);
        assert_eq!(sim.total_pebbles(), 1);
    }

    #[test]
    fn test_missing_rule_detection() {
        // 5 -> 1 | 0 | 4 (so t=1 has cells [1, 0, 4]), rule 5 defined, rule 4 missing
        let prog: Program = "00_--_--_--_14".parse().unwrap();
        let outcome = simulate(&prog, 10);
        assert_eq!(
            outcome,
            SimOutcome::MissingRule {
                pebbles: 4,
                steps: 1
            }
        );
    }
}
