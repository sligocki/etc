use crate::deciders::Decider;
use crate::program::{decode_pebble_digit, encode_pebble_digit, Program};
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
    /// The automaton was proven non-halting (infinite) by `decider` after simulating `steps` transitions.
    Inf { decider: Decider, steps: u64 },
    /// The automaton did not stabilize within `steps` transitions and was not decided.
    Unknown { steps: u64 },
    /// Simulation paused at `steps` because rule for `pebbles` is undefined.
    MissingRule { pebbles: u8, steps: u64 },
}

impl SimOutcome {
    /// Returns `true` if the outcome is `SimOutcome::Halted`.
    #[inline]
    pub fn is_halted(&self) -> bool {
        matches!(self, SimOutcome::Halted { .. })
    }

    /// Returns `true` if the outcome is `SimOutcome::Inf`.
    #[inline]
    pub fn is_inf(&self) -> bool {
        matches!(self, SimOutcome::Inf { .. })
    }

    /// Backward compatibility alias for `is_inf`.
    #[inline]
    pub fn is_decided_non_halting(&self) -> bool {
        self.is_inf()
    }

    /// Returns `true` if the outcome is unknown (`SimOutcome::Unknown`).
    #[inline]
    pub fn is_unknown(&self) -> bool {
        matches!(self, SimOutcome::Unknown { .. })
    }

    /// Backward compatibility alias for `is_unknown`.
    #[inline]
    pub fn is_holdout(&self) -> bool {
        self.is_unknown()
    }

    /// Returns the step count associated with this outcome.
    #[inline]
    pub fn steps(&self) -> u64 {
        match *self {
            SimOutcome::Halted { steps }
            | SimOutcome::Inf { steps, .. }
            | SimOutcome::Unknown { steps }
            | SimOutcome::MissingRule { steps, .. } => steps,
        }
    }
}

impl fmt::Display for SimOutcome {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SimOutcome::Halted { steps } => write!(f, "HALT\t{steps}"),
            SimOutcome::Inf { decider, steps } => match decider {
                Decider::Ctl(Some(proof)) => {
                    write!(f, "INF\tCTL\t{} # {proof}", proof.num_steps)
                }
                Decider::Cycler(Some(proof)) => {
                    write!(f, "INF\tCycler\t{steps} # {proof}")
                }
                Decider::SeparatedComponents(Some(proof)) => {
                    write!(f, "INF\tSeparatedComponents\t{steps} # {proof}")
                }
                Decider::Bouncer(Some(proof)) => {
                    write!(f, "INF\tBouncer\t{steps} # {proof}")
                }
                _ => write!(f, "INF\t{decider}\t{steps}"),
            },
            SimOutcome::Unknown { steps } => write!(f, "UNKNOWN\t{steps}"),
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

/// Maximum number of non-zero piles supported inline without heap allocation.
///
/// Because total pebble count $N$ is strictly conserved ($L + S + R = k$),
/// the number of non-zero piles can never exceed $N$. This capacity covers all
/// programs up to $N = 32$.
pub const MAX_SPARSE_PEBBLES: usize = 32;

/// Maximum scratch buffer capacity for emitted fragments ($3 \times \text{MAX\_SPARSE\_PEBBLES}$).
pub const MAX_SCRATCH_ENTRIES: usize = MAX_SPARSE_PEBBLES * 3;

/// Error produced when parsing a tape configuration string.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TapeParseError {
    EmptyTape,
    InvalidCharacter(char),
    InvalidCoordinate(String),
    InvalidPebbleCount(String),
    MultipleOriginMarkers,
    UnmatchedBracket,
    TooManyPiles(usize),
    TooManyPebbles(usize),
}

impl fmt::Display for TapeParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TapeParseError::EmptyTape => write!(f, "tape configuration cannot be empty"),
            TapeParseError::InvalidCharacter(c) => {
                write!(f, "invalid character '{c}' in tape configuration")
            }
            TapeParseError::InvalidCoordinate(s) => write!(f, "invalid coordinate '{s}'"),
            TapeParseError::InvalidPebbleCount(s) => write!(f, "invalid pebble count '{s}'"),
            TapeParseError::MultipleOriginMarkers => {
                write!(f, "multiple origin markers '[...]' in tape configuration")
            }
            TapeParseError::UnmatchedBracket => {
                write!(f, "unmatched bracket in tape configuration")
            }
            TapeParseError::TooManyPiles(n) => write!(
                f,
                "number of non-zero piles ({n}) exceeds MAX_SPARSE_PEBBLES ({MAX_SPARSE_PEBBLES})"
            ),
            TapeParseError::TooManyPebbles(n) => write!(
                f,
                "total pebbles ({n}) exceeds MAX_SPARSE_PEBBLES ({MAX_SPARSE_PEBBLES})"
            ),
        }
    }
}

impl std::error::Error for TapeParseError {}

fn parse_pebble_value(part: &str) -> Result<u8, TapeParseError> {
    if let Ok(val) = part.parse::<u8>() {
        if val <= 35 {
            return Ok(val);
        }
    }
    if part.len() == 1 {
        let ch = part.chars().next().unwrap();
        if let Ok(val) = decode_pebble_digit(ch) {
            return Ok(val);
        }
    }
    Err(TapeParseError::InvalidPebbleCount(part.to_string()))
}

/// Compact stack-allocated sparse representation of the active tape.
///
/// Stores non-zero entries `(x, pebbles)` sorted strictly by coordinate `x`.
/// All other cells on the tape are implicitly `0`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SparseTape {
    len: u8,
    entries: [(isize, u8); MAX_SPARSE_PEBBLES],
}

impl SparseTape {
    /// Create a new sparse tape with `p` pebbles at `x = 0`.
    pub fn new(p: u8) -> Self {
        let mut entries = [(0, 0); MAX_SPARSE_PEBBLES];
        if p > 0 {
            entries[0] = (0, p);
            Self { len: 1, entries }
        } else {
            Self { len: 0, entries }
        }
    }

    /// Create a sparse tape directly from non-zero `(x, pebbles)` coordinate entries.
    pub fn from_entries(entries: &[(isize, u8)]) -> Self {
        let mut buf = [(0, 0); MAX_SPARSE_PEBBLES];
        let mut len = 0;
        for &(x, k) in entries {
            if k > 0 {
                assert!(len < MAX_SPARSE_PEBBLES, "exceeded MAX_SPARSE_PEBBLES");
                buf[len] = (x, k);
                len += 1;
            }
        }
        Self {
            len: len as u8,
            entries: buf,
        }
    }

    /// Number of active non-zero piles currently on the tape.
    #[inline]
    pub fn len(&self) -> usize {
        self.len as usize
    }

    /// Returns `true` if there are no non-zero pebbles on the tape.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Slice of active `(coordinate, pebbles)` pairs sorted strictly by coordinate.
    #[inline]
    pub fn entries(&self) -> &[(isize, u8)] {
        &self.entries[..self.len as usize]
    }

    /// Minimum x-coordinate with non-zero pebbles, or `None` if empty.
    #[inline]
    pub fn min_x(&self) -> Option<isize> {
        if self.len > 0 {
            Some(self.entries[0].0)
        } else {
            None
        }
    }

    /// Maximum x-coordinate with non-zero pebbles, or `None` if empty.
    #[inline]
    pub fn max_x(&self) -> Option<isize> {
        if self.len > 0 {
            Some(self.entries[self.len as usize - 1].0)
        } else {
            None
        }
    }

    /// Total number of pebbles on the tape.
    #[inline]
    pub fn total_pebbles(&self) -> usize {
        self.entries().iter().map(|&(_, k)| k as usize).sum()
    }

    /// Read the pebble count at coordinate `x`.
    #[inline]
    pub fn get(&self, x: isize) -> u8 {
        self.entries()
            .binary_search_by_key(&x, |&(pos, _)| pos)
            .map(|idx| self.entries[idx].1)
            .unwrap_or(0)
    }

    /// Reconstruct the dense `(offset, cells)` slice representation from sparse entries.
    pub fn to_dense(&self) -> (isize, Vec<u8>) {
        if self.len == 0 {
            return (0, Vec::new());
        }
        let min_x = self.entries[0].0;
        let max_x = self.entries[self.len as usize - 1].0;
        let width = (max_x - min_x + 1) as usize;
        let mut cells = vec![0u8; width];
        for &(x, k) in self.entries() {
            cells[(x - min_x) as usize] = k;
        }
        (min_x, cells)
    }

    /// Parse a tape configuration string with an explicit coordinate offset.
    ///
    /// Supported formats:
    /// - Dense tape string: `"0230"`, `".23."`, `"102"`, `"23"`
    /// - Origin marker bracket: `"0[2]30"` (cell inside bracket is at x=0)
    /// - Offset prefix: `"-1:0230"`
    /// - Sparse coordinate pairs: `"-1:2, 0:3"`, `"2@-1, 3@0"`, `"(-1, 2), (0, 3)"`
    pub fn parse_with_offset(raw: &str, default_offset: isize) -> Result<Self, TapeParseError> {
        let trimmed = raw.trim();
        if trimmed.is_empty() {
            return Err(TapeParseError::EmptyTape);
        }

        // Check if input represents sparse coordinate pairs
        let is_sparse_pairs = trimmed.contains('@')
            || (trimmed.contains(',') && (trimmed.contains(':') || trimmed.contains('(')))
            || (trimmed.contains(':') && trimmed.matches(':').count() > 1);

        if is_sparse_pairs {
            return Self::parse_sparse_pairs(trimmed, default_offset);
        }

        // Otherwise, treat as dense tape string with optional prefix offset `<offset>:<tape>`
        let (offset, tape_str) = if let Some((prefix, rest)) = trimmed.split_once(':') {
            if let Ok(off) = prefix.trim().parse::<isize>() {
                (off, rest.trim())
            } else {
                (default_offset, trimmed)
            }
        } else {
            (default_offset, trimmed)
        };

        Self::parse_dense_tape(tape_str, offset)
    }

    /// Parse a tape configuration string assuming default coordinate offset 0.
    pub fn parse(raw: &str) -> Result<Self, TapeParseError> {
        Self::parse_with_offset(raw, 0)
    }

    fn parse_sparse_pairs(s: &str, default_offset: isize) -> Result<Self, TapeParseError> {
        let mut raw_pairs = Vec::new();
        if s.contains('(') {
            let mut start = None;
            for (idx, ch) in s.char_indices() {
                if ch == '(' {
                    start = Some(idx + 1);
                } else if ch == ')' {
                    if let Some(st) = start {
                        raw_pairs.push(&s[st..idx]);
                        start = None;
                    }
                }
            }
        } else if s.contains(',') {
            for part in s.split(',') {
                let p = part.trim();
                if !p.is_empty() {
                    raw_pairs.push(p);
                }
            }
        } else {
            for part in s.split_whitespace() {
                raw_pairs.push(part);
            }
        }

        let mut pile_map = std::collections::BTreeMap::<isize, u8>::new();
        for pair in raw_pairs {
            let pair = pair.trim();
            if pair.is_empty() {
                continue;
            }
            let (x, k) = if let Some((k_part, x_part)) = pair.split_once('@') {
                let x: isize = x_part
                    .trim()
                    .parse()
                    .map_err(|_| TapeParseError::InvalidCoordinate(x_part.trim().to_string()))?;
                let k = parse_pebble_value(k_part.trim())?;
                (x, k)
            } else if let Some((x_part, k_part)) = pair.split_once(':') {
                let x: isize = x_part
                    .trim()
                    .parse()
                    .map_err(|_| TapeParseError::InvalidCoordinate(x_part.trim().to_string()))?;
                let k = parse_pebble_value(k_part.trim())?;
                (x, k)
            } else if let Some((x_part, k_part)) = pair.split_once(',') {
                let x: isize = x_part
                    .trim()
                    .parse()
                    .map_err(|_| TapeParseError::InvalidCoordinate(x_part.trim().to_string()))?;
                let k = parse_pebble_value(k_part.trim())?;
                (x, k)
            } else {
                return Err(TapeParseError::InvalidCoordinate(pair.to_string()));
            };

            let coord = x
                .checked_add(default_offset)
                .ok_or_else(|| TapeParseError::InvalidCoordinate(x.to_string()))?;
            let entry = pile_map.entry(coord).or_insert(0);
            *entry = entry
                .checked_add(k)
                .ok_or_else(|| TapeParseError::TooManyPebbles(*entry as usize + k as usize))?;
        }

        let mut entries = Vec::new();
        let mut total_pebbles = 0usize;
        for (x, k) in pile_map {
            if k > 0 {
                total_pebbles += k as usize;
                entries.push((x, k));
            }
        }

        if entries.len() > MAX_SPARSE_PEBBLES {
            return Err(TapeParseError::TooManyPiles(entries.len()));
        }
        if total_pebbles > MAX_SPARSE_PEBBLES {
            return Err(TapeParseError::TooManyPebbles(total_pebbles));
        }

        Ok(Self::from_entries(&entries))
    }

    fn parse_dense_tape(s: &str, offset: isize) -> Result<Self, TapeParseError> {
        let mut chars = Vec::new();
        let mut origin_idx = None;
        let mut in_bracket = false;

        for ch in s.chars() {
            if ch.is_whitespace() {
                continue;
            }
            if ch == '[' {
                if in_bracket || origin_idx.is_some() {
                    return Err(TapeParseError::MultipleOriginMarkers);
                }
                in_bracket = true;
                continue;
            }
            if ch == ']' {
                if !in_bracket {
                    return Err(TapeParseError::UnmatchedBracket);
                }
                in_bracket = false;
                continue;
            }

            let val = match ch {
                '.' | '_' | '0' => 0u8,
                '1'..='9' | 'a'..='z' | 'A'..='Z' => {
                    decode_pebble_digit(ch).map_err(|_| TapeParseError::InvalidCharacter(ch))?
                }
                other => return Err(TapeParseError::InvalidCharacter(other)),
            };

            if in_bracket && origin_idx.is_none() {
                origin_idx = Some(chars.len());
            }
            chars.push(val);
        }

        if in_bracket {
            return Err(TapeParseError::UnmatchedBracket);
        }

        let origin = origin_idx.unwrap_or(0);
        let mut entries = Vec::new();
        let mut total_pebbles = 0usize;

        for (idx, &val) in chars.iter().enumerate() {
            if val > 0 {
                let x = offset + (idx as isize - origin as isize);
                total_pebbles += val as usize;
                entries.push((x, val));
            }
        }

        if entries.len() > MAX_SPARSE_PEBBLES {
            return Err(TapeParseError::TooManyPiles(entries.len()));
        }
        if total_pebbles > MAX_SPARSE_PEBBLES {
            return Err(TapeParseError::TooManyPebbles(total_pebbles));
        }

        Ok(Self::from_entries(&entries))
    }

    /// Advance the sparse tape by 1 generation according to `program`.
    pub fn step(
        &mut self,
        program: &Program,
        scratch: &mut [(isize, u8); MAX_SCRATCH_ENTRIES],
        scratch_len: &mut usize,
    ) -> StepResult {
        if self.len == 0 {
            return StepResult::Halted;
        }

        // Verify all non-zero cells have defined rules and check if any pebbles move
        let mut any_moved = false;
        for i in 0..self.len as usize {
            let k = self.entries[i].1;
            match program.rule(k) {
                None => return StepResult::MissingRule(k),
                Some(rule) => {
                    if rule.left > 0 || rule.right > 0 {
                        any_moved = true;
                    }
                }
            }
        }

        if !any_moved {
            return StepResult::Halted;
        }

        *scratch_len = 0;
        for i in 0..self.len as usize {
            let (x, k) = self.entries[i];
            let rule = program.rule(k).unwrap();
            if rule.left > 0 {
                scratch[*scratch_len] = (x - 1, rule.left);
                *scratch_len += 1;
            }
            if rule.stay > 0 {
                scratch[*scratch_len] = (x, rule.stay);
                *scratch_len += 1;
            }
            if rule.right > 0 {
                scratch[*scratch_len] = (x + 1, rule.right);
                *scratch_len += 1;
            }
        }

        if *scratch_len == 0 {
            self.len = 0;
            return StepResult::Stepped;
        }

        let slice = &mut scratch[..*scratch_len];
        slice.sort_unstable_by_key(|&(x, _)| x);

        let mut next_entries = [(0isize, 0u8); MAX_SPARSE_PEBBLES];
        let mut next_len = 0usize;
        let mut cur_x = slice[0].0;
        let mut cur_k = slice[0].1;

        for i in 1..slice.len() {
            let (x, k) = slice[i];
            if x == cur_x {
                cur_k += k;
            } else {
                if next_len < MAX_SPARSE_PEBBLES {
                    next_entries[next_len] = (cur_x, cur_k);
                    next_len += 1;
                }
                cur_x = x;
                cur_k = k;
            }
        }
        if next_len < MAX_SPARSE_PEBBLES {
            next_entries[next_len] = (cur_x, cur_k);
            next_len += 1;
        }

        self.entries = next_entries;
        self.len = next_len as u8;
        StepResult::Stepped
    }
}

impl std::str::FromStr for SparseTape {
    type Err = TapeParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::parse(s)
    }
}

/// Stateful simulator for a 1D Pebble Automaton using sparse stack-allocated storage.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Simulator {
    tape: SparseTape,
    steps: u64,
}

impl Simulator {
    /// Create a new simulator initialized with `initial_pebbles` at `x = 0`, `t = 0`.
    pub fn new(initial_pebbles: usize) -> Self {
        assert!(
            initial_pebbles <= MAX_SPARSE_PEBBLES,
            "pebble count {} exceeds MAX_SPARSE_PEBBLES {}",
            initial_pebbles,
            MAX_SPARSE_PEBBLES
        );
        Self {
            tape: SparseTape::new(initial_pebbles as u8),
            steps: 0,
        }
    }

    /// Create a simulator initialized from an existing sparse tape.
    pub fn from_tape(tape: SparseTape) -> Self {
        Self { tape, steps: 0 }
    }

    /// Create a simulator initialized from an existing sparse tape with an explicit step count.
    pub fn from_tape_with_steps(tape: SparseTape, steps: u64) -> Self {
        Self { tape, steps }
    }

    /// Create a simulator initialized from a parsed tape configuration string.
    pub fn from_config(s: &str) -> Result<Self, TapeParseError> {
        let tape = SparseTape::parse(s)?;
        Ok(Self::from_tape(tape))
    }

    /// Create a simulator initialized from a parsed tape configuration string with explicit offset.
    pub fn from_config_with_offset(s: &str, offset: isize) -> Result<Self, TapeParseError> {
        let tape = SparseTape::parse_with_offset(s, offset)?;
        Ok(Self::from_tape(tape))
    }

    /// Create a simulator initialized with specific coordinate entries at `t = 0`.
    pub fn from_entries(entries: &[(isize, u8)]) -> Self {
        Self {
            tape: SparseTape::from_entries(entries),
            steps: 0,
        }
    }

    /// Current generation / step count `t`.
    #[inline]
    pub fn steps(&self) -> u64 {
        self.steps
    }

    /// Access the underlying sparse tape.
    #[inline]
    pub fn tape(&self) -> &SparseTape {
        &self.tape
    }

    /// Active sparse entries as `&[(coordinate, pebbles)]`.
    #[inline]
    pub fn sparse_entries(&self) -> &[(isize, u8)] {
        self.tape.entries()
    }

    /// Current x-coordinate of the leftmost non-zero cell, or `0` if empty.
    #[inline]
    pub fn offset(&self) -> isize {
        self.tape.min_x().unwrap_or(0)
    }

    /// Minimum x-coordinate with non-zero pebbles.
    #[inline]
    pub fn min_x(&self) -> isize {
        self.tape.min_x().unwrap_or(0)
    }

    /// Maximum x-coordinate with non-zero pebbles.
    #[inline]
    pub fn max_x(&self) -> isize {
        self.tape.max_x().unwrap_or(0)
    }

    /// Convert current active tape to a dense `cells` vector.
    pub fn cells(&self) -> Vec<u8> {
        self.tape.to_dense().1
    }

    /// Total number of pebbles currently on the tape.
    #[inline]
    pub fn total_pebbles(&self) -> usize {
        self.tape.total_pebbles()
    }

    /// Capture a snapshot of the current tape state.
    pub fn snapshot(&self) -> TapeSnapshot {
        let (offset, cells) = self.tape.to_dense();
        TapeSnapshot {
            step: self.steps,
            offset,
            cells,
        }
    }

    /// Attempt to advance the simulation by 1 step.
    pub fn step(&mut self, program: &Program) -> StepResult {
        let mut scratch = [(0isize, 0u8); MAX_SCRATCH_ENTRIES];
        let mut scratch_len = 0usize;
        let res = self.tape.step(program, &mut scratch, &mut scratch_len);
        if res == StepResult::Stepped {
            self.steps += 1;
        }
        res
    }

    /// Run the simulator from its current state up to `max_steps` total transitions.
    pub fn run(&mut self, program: &Program, max_steps: u64) -> SimOutcome {
        let mut scratch = [(0isize, 0u8); MAX_SCRATCH_ENTRIES];
        let mut scratch_len = 0usize;
        loop {
            if self.steps >= max_steps {
                for &(_, k) in self.tape.entries() {
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
                return SimOutcome::Unknown { steps: self.steps };
            }

            match self.tape.step(program, &mut scratch, &mut scratch_len) {
                StepResult::Stepped => {
                    self.steps += 1;
                    continue;
                }
                StepResult::Halted => return SimOutcome::Halted { steps: self.steps },
                StepResult::MissingRule(k) => {
                    return SimOutcome::MissingRule {
                        pebbles: k,
                        steps: self.steps,
                    };
                }
            }
        }
    }

    /// Run the simulator from its current state up to `max_steps`, checking at each step
    /// whether an edge particle satisfies the light-cone escaping `EdgeGlider` invariant.
    pub fn run_with_edge_glider(&mut self, program: &Program, max_steps: u64) -> SimOutcome {
        let mut scratch = [(0isize, 0u8); MAX_SCRATCH_ENTRIES];
        let mut scratch_len = 0usize;
        loop {
            if let Some(decider) =
                crate::deciders::check_edge_glider_sparse(program, self.tape.entries())
            {
                return SimOutcome::Inf {
                    decider,
                    steps: self.steps,
                };
            }
            if self.steps >= max_steps {
                for &(_, k) in self.tape.entries() {
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
                return SimOutcome::Unknown { steps: self.steps };
            }

            match self.tape.step(program, &mut scratch, &mut scratch_len) {
                StepResult::Stepped => {
                    self.steps += 1;
                    continue;
                }
                StepResult::Halted => return SimOutcome::Halted { steps: self.steps },
                StepResult::MissingRule(k) => {
                    return SimOutcome::MissingRule {
                        pebbles: k,
                        steps: self.steps,
                    };
                }
            }
        }
    }

    /// Check if the current state `state(t)` satisfies `state(t+1) == state(t)`.
    pub fn is_current_state_stable(&mut self, program: &Program) -> bool {
        let mut scratch = [(0isize, 0u8); MAX_SCRATCH_ENTRIES];
        let mut scratch_len = 0usize;
        let mut clone = self.tape;
        clone.step(program, &mut scratch, &mut scratch_len) == StepResult::Halted
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

/// Simulate a `program` starting from an arbitrary `Simulator` state for up to `max_steps`
/// and record the tape at each generation.
pub fn simulate_from_sim_with_trace(
    program: &Program,
    mut sim: Simulator,
    max_steps: u64,
) -> (SimOutcome, Vec<TapeSnapshot>) {
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

/// Simulate a `program` from `t = 0` for up to `max_steps` and record the tape at each generation.
pub fn simulate_with_trace(program: &Program, max_steps: u64) -> (SimOutcome, Vec<TapeSnapshot>) {
    simulate_from_sim_with_trace(program, Simulator::new(program.size()), max_steps)
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

            // And 1 step less than halting should report Unknown
            if expected_steps > 0 {
                let short_outcome = simulate(&prog, expected_steps - 1);
                assert_eq!(
                    short_outcome,
                    SimOutcome::Unknown {
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
        assert_eq!(outcome, SimOutcome::Unknown { steps: 25 });
        assert_eq!(sim.offset(), 25);
        assert_eq!(sim.cells(), vec![1]);
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

    #[test]
    fn test_dynamic_equilibrium_does_not_halt() {
        // 2 -> 0|1|1 (01), 3 -> 1|2|0 (10)
        // Tape with [2, 3] shuttles pebbles back and forth while preserving [2, 3] on tape.
        // Under the new "no pebbles move" halting criteria, this must NOT halt.
        let prog: Program = "00_01_10".parse().unwrap();
        let mut sim = Simulator::from_entries(&[(0, 2), (1, 3)]);
        let res = sim.step(&prog);
        assert_eq!(res, StepResult::Stepped);
        assert_eq!(sim.cells(), vec![2, 3]);
        assert_eq!(sim.steps(), 1);

        // However, a tape with isolated stationary single-pebble piles [1, 0, 1] halts immediately
        let mut sim_stationary = Simulator::from_entries(&[(0, 1), (2, 1)]);
        let res2 = sim_stationary.step(&prog);
        assert_eq!(res2, StepResult::Halted);
        assert_eq!(sim_stationary.steps(), 0);
    }

    struct ReferenceDenseSimulator {
        offset: isize,
        cells: Vec<u8>,
        scratch: Vec<u8>,
    }

    impl ReferenceDenseSimulator {
        fn new(p: usize) -> Self {
            let cells = if p > 0 { vec![p as u8] } else { Vec::new() };
            Self {
                offset: 0,
                cells,
                scratch: Vec::with_capacity(p + 4),
            }
        }

        fn step(&mut self, program: &Program) -> StepResult {
            if self.cells.is_empty() {
                return StepResult::Halted;
            }
            let mut any_moved = false;
            for &k in &self.cells {
                if k > 0 {
                    match program.rule(k) {
                        None => return StepResult::MissingRule(k),
                        Some(rule) => {
                            if rule.left > 0 || rule.right > 0 {
                                any_moved = true;
                            }
                        }
                    }
                }
            }
            if !any_moved {
                return StepResult::Halted;
            }

            let next_len = self.cells.len() + 2;
            self.scratch.clear();
            self.scratch.resize(next_len, 0);

            for (i, &k) in self.cells.iter().enumerate() {
                if k == 0 {
                    continue;
                }
                let rule = program.rule(k).unwrap();
                self.scratch[i] += rule.left;
                self.scratch[i + 1] += rule.stay;
                self.scratch[i + 2] += rule.right;
            }

            let Some(first_nz) = self.scratch.iter().position(|&v| v > 0) else {
                self.cells.clear();
                self.offset = 0;
                return StepResult::Stepped;
            };
            let last_nz = self.scratch.iter().rposition(|&v| v > 0).unwrap();
            let next_offset = self.offset - 1 + first_nz as isize;
            let next_slice = &self.scratch[first_nz..=last_nz];

            self.offset = next_offset;
            self.cells.clear();
            self.cells.extend_from_slice(next_slice);
            StepResult::Stepped
        }
    }

    #[test]
    fn test_sparse_vs_dense_fuzz_equivalence() {
        use crate::enumeration::TnfEnumerator;
        // Test all programs in peBBle(1..=4) across 50 steps
        for size in 1..=4 {
            for entry in TnfEnumerator::new(size, 50, 50) {
                let prog = entry.program;
                let mut dense = ReferenceDenseSimulator::new(size);
                let mut sparse = Simulator::new(size);

                for step in 0..50 {
                    let d_res = dense.step(&prog);
                    let s_res = sparse.step(&prog);
                    assert_eq!(s_res, d_res, "step result mismatch on {prog} at step {step}");
                    if s_res != StepResult::Stepped {
                        break;
                    }
                    assert_eq!(sparse.offset(), dense.offset, "offset mismatch on {prog} at step {step}");
                    assert_eq!(sparse.cells(), dense.cells, "cells mismatch on {prog} at step {step}");
                }
            }
        }
    }

    #[test]
    fn test_parse_tape_config() {
        let t1 = SparseTape::parse("0230").unwrap();
        assert_eq!(t1.entries(), &[(1, 2), (2, 3)]);
        assert_eq!(t1.total_pebbles(), 5);

        let t2 = SparseTape::parse("0[2]30").unwrap();
        assert_eq!(t2.entries(), &[(0, 2), (1, 3)]);
        assert_eq!(t2.total_pebbles(), 5);

        let t3 = SparseTape::parse_with_offset("0230", -1).unwrap();
        assert_eq!(t3.entries(), &[(0, 2), (1, 3)]);

        let t4 = SparseTape::parse("-1:0230").unwrap();
        assert_eq!(t4.entries(), &[(0, 2), (1, 3)]);

        let t5 = SparseTape::parse(".2.3.").unwrap();
        assert_eq!(t5.entries(), &[(1, 2), (3, 3)]);

        let t6 = SparseTape::parse("c").unwrap();
        assert_eq!(t6.entries(), &[(0, 12)]);

        let t7 = SparseTape::parse("2@-1, 3@0").unwrap();
        assert_eq!(t7.entries(), &[((-1), 2), (0, 3)]);

        let t8 = SparseTape::parse("-1:2, 0:3").unwrap();
        assert_eq!(t8.entries(), &[(min_x_val(-1), 2), (0, 3)]);

        let t9 = SparseTape::parse("(-1, 2), (0, 3)").unwrap();
        assert_eq!(t9.entries(), &[(min_x_val(-1), 2), (0, 3)]);

        let empty = SparseTape::parse("...").unwrap();
        assert_eq!(empty.len(), 0);
        assert_eq!(empty.total_pebbles(), 0);

        assert!(SparseTape::parse("").is_err());
        assert!(SparseTape::parse("0[2][3]0").is_err());
        assert!(SparseTape::parse("0[23").is_err());
        assert!(SparseTape::parse("xyz!").is_err());
    }

    fn min_x_val(v: isize) -> isize {
        v
    }
}
