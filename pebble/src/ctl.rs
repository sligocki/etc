use crate::deciders::Decider;
use crate::program::Program;
use crate::simulation::{Simulator, StepResult};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ZeroGap {
    pub rem: usize,
    pub modulus: usize,
}

impl ZeroGap {
    #[inline]
    pub fn new(rem: usize, floor: usize, modulus: usize) -> Self {
        Self {
            rem: if rem >= floor {
                floor + (rem - floor) % modulus
            } else {
                rem
            },
            modulus,
        }
    }

    #[inline]
    pub fn widen(self, floor: usize) -> Self {
        if self.rem >= floor {
            Self {
                rem: floor + (self.rem - floor) % self.modulus,
                modulus: self.modulus,
            }
        } else {
            self
        }
    }

    #[inline]
    pub fn is_subset_of(&self, other: &ZeroGap) -> bool {
        self.rem >= other.rem
            && self.modulus % other.modulus == 0
            && (self.rem - other.rem) % other.modulus == 0
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CtlState {
    pub modulus: usize,
    pub blocks: Vec<Vec<u8>>,
    pub gaps: Vec<ZeroGap>,
}

impl CtlState {
    pub fn is_subset_of(&self, other: &CtlState) -> bool {
        if self.modulus != other.modulus
            || self.blocks != other.blocks
            || self.gaps.len() != other.gaps.len()
        {
            return false;
        }
        self.gaps
            .iter()
            .zip(other.gaps.iter())
            .all(|(g1, g2)| g1.is_subset_of(g2))
    }
}

impl std::fmt::Display for CtlState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, b) in self.blocks.iter().enumerate() {
            if i > 0 && i - 1 < self.gaps.len() {
                let g = self.gaps[i - 1];
                if g.modulus == 1 {
                    write!(f, " (0^{}) ", g.rem)?;
                } else {
                    write!(f, " (0^{}+{}k) ", g.rem, g.modulus)?;
                }
            }
            write!(f, "[")?;
            for (j, &c) in b.iter().enumerate() {
                if j > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{c}")?;
            }
            write!(f, "]")?;
        }
        Ok(())
    }
}

pub fn merge_blocks_with_zeros(b1: &[u8], zeros: usize, b2: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(b1.len() + zeros + b2.len());
    out.extend_from_slice(b1);
    out.resize(b1.len() + zeros, 0);
    out.extend_from_slice(b2);
    out
}

pub fn split_slice_by_threshold(slice: &[u8], split_threshold: usize) -> (Vec<Vec<u8>>, Vec<usize>) {
    let mut blocks = Vec::new();
    let mut gaps = Vec::new();
    let mut last_idx = 0;
    let mut i = 0;
    while i < slice.len() {
        if slice[i] == 0 {
            let z_start = i;
            while i < slice.len() && slice[i] == 0 {
                i += 1;
            }
            let z_len = i - z_start;
            if z_len >= split_threshold {
                blocks.push(slice[last_idx..z_start].to_vec());
                gaps.push(z_len);
                last_idx = i;
            }
        } else {
            i += 1;
        }
    }
    blocks.push(slice[last_idx..].to_vec());
    (blocks, gaps)
}

pub fn unroll_ctl_state(state: &CtlState) -> Result<Vec<CtlState>, ()> {
    if state.gaps.is_empty() {
        return Err(());
    }
    if let Some(idx) = state.gaps.iter().position(|g| g.rem < 2) {
        if state.gaps.len() <= 1 {
            return Err(());
        }
        let g = state.gaps[idx];
        let mut branches = Vec::new();
        let mut cur_rem = g.rem;
        while cur_rem < 2 {
            let merged_block =
                merge_blocks_with_zeros(&state.blocks[idx], cur_rem, &state.blocks[idx + 1]);
            let mut next_blocks = Vec::with_capacity(state.blocks.len() - 1);
            next_blocks.extend_from_slice(&state.blocks[..idx]);
            next_blocks.push(merged_block);
            next_blocks.extend_from_slice(&state.blocks[(idx + 2)..]);

            let mut next_gaps = Vec::with_capacity(state.gaps.len() - 1);
            next_gaps.extend_from_slice(&state.gaps[..idx]);
            next_gaps.extend_from_slice(&state.gaps[(idx + 1)..]);

            let reduced = CtlState {
                modulus: state.modulus,
                blocks: next_blocks,
                gaps: next_gaps,
            };
            branches.extend(unroll_ctl_state(&reduced)?);
            cur_rem += g.modulus;
        }
        let mut tail_gaps = state.gaps.clone();
        tail_gaps[idx] = ZeroGap {
            rem: cur_rem,
            modulus: g.modulus,
        };
        let tail_state = CtlState {
            modulus: state.modulus,
            blocks: state.blocks.clone(),
            gaps: tail_gaps,
        };
        branches.extend(unroll_ctl_state(&tail_state)?);
        Ok(branches)
    } else {
        Ok(vec![state.clone()])
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CtlStepError {
    UndefinedRule { pebbles: u8 },
    HaltingState,
    BlockTooLarge { len: usize, max: usize },
    AllStationary,
    NegativeGap,
    UnrollFailed,
}

pub fn step_isolated_block(
    block: &[u8],
    program: &Program,
) -> Result<(Vec<u8>, isize, isize), CtlStepError> {
    let mut next = vec![0u8; block.len() + 2];
    for (i, &k) in block.iter().enumerate() {
        if k == 0 {
            continue;
        }
        let rule = match program.rule(k) {
            Some(r) => r,
            None => return Err(CtlStepError::UndefinedRule { pebbles: k }),
        };
        next[i] += rule.left;
        next[i + 1] += rule.stay;
        next[i + 2] += rule.right;
    }
    let first_nz = match next.iter().position(|&v| v > 0) {
        Some(idx) => idx,
        None => return Err(CtlStepError::HaltingState),
    };
    let last_nz = next.iter().rposition(|&v| v > 0).unwrap();
    let out = next[first_nz..=last_nz].to_vec();
    if out.len() > 28 {
        return Err(CtlStepError::BlockTooLarge {
            len: out.len(),
            max: 28,
        });
    }
    let delta_left = (first_nz as isize) - 1;
    let delta_right = (last_nz as isize) - (block.len() as isize);
    Ok((out, delta_left, delta_right))
}

pub fn step_ctl_pre_state(
    pre: &CtlState,
    program: &Program,
    split_threshold: usize,
    floor: usize,
) -> Result<CtlState, CtlStepError> {
    let mut stepped_blocks = Vec::with_capacity(pre.blocks.len());
    let mut delta_lefts = Vec::with_capacity(pre.blocks.len());
    let mut delta_rights = Vec::with_capacity(pre.blocks.len());
    let mut any_pebbles_move = false;

    for b in &pre.blocks {
        let (nb, dl, dr) = step_isolated_block(b, program)?;
        for &k in b {
            if k > 0 {
                if let Some(r) = program.rule(k) {
                    if r.left > 0 || r.right > 0 {
                        any_pebbles_move = true;
                    }
                }
            }
        }
        stepped_blocks.push(nb);
        delta_lefts.push(dl);
        delta_rights.push(dr);
    }

    if !any_pebbles_move {
        return Err(CtlStepError::AllStationary);
    }

    let mut inter_gaps = Vec::with_capacity(pre.gaps.len());
    for (i, g) in pre.gaps.iter().enumerate() {
        let dg = delta_lefts[i + 1] - delta_rights[i];
        let next_rem = (g.rem as isize) + dg;
        if next_rem < 0 {
            return Err(CtlStepError::NegativeGap);
        }
        inter_gaps.push(ZeroGap {
            rem: next_rem as usize,
            modulus: g.modulus,
        });
    }

    let mut new_blocks = Vec::with_capacity(stepped_blocks.len() + 1);
    let mut new_gaps = Vec::with_capacity(inter_gaps.len() + 1);

    for (i, nb) in stepped_blocks.into_iter().enumerate() {
        let (sub_blocks, sub_gaps) = split_slice_by_threshold(&nb, split_threshold);
        for (j, sb) in sub_blocks.into_iter().enumerate() {
            new_blocks.push(sb);
            if j < sub_gaps.len() {
                new_gaps.push(ZeroGap {
                    rem: sub_gaps[j],
                    modulus: pre.modulus,
                });
            }
        }
        if i < inter_gaps.len() {
            new_gaps.push(inter_gaps[i]);
        }
    }

    if new_gaps.is_empty() {
        return Err(CtlStepError::UnrollFailed);
    }

    if new_gaps.len() >= 2 {
        for g in &mut new_gaps {
            *g = g.widen(floor);
        }
    } else {
        new_gaps[0] = new_gaps[0].widen(floor + 24);
    }

    Ok(CtlState {
        modulus: pre.modulus,
        blocks: new_blocks,
        gaps: new_gaps,
    })
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CtlFailureDetail {
    HitUndefinedRule {
        pebbles: u8,
        state: CtlState,
    },
    HitHalt {
        state: CtlState,
    },
    PrematureCollapse {
        state: CtlState,
    },
    BlockTooLarge {
        len: usize,
        max: usize,
        state: CtlState,
    },
    NegativeGap {
        state: CtlState,
    },
    ExceededMaxStates {
        limit: usize,
        last_state: CtlState,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CtlFailureDiagnostic {
    pub step: u64,
    pub floor: usize,
    pub modulus: usize,
    pub detail: CtlFailureDetail,
}

impl CtlFailureDiagnostic {
    pub fn format_explanation(&self) -> String {
        let mut out = String::new();
        out.push_str(&format!(
            "  Tested candidate at step {} (mod={}, floor={}):\n",
            self.step, self.modulus, self.floor
        ));
        match &self.detail {
            CtlFailureDetail::PrematureCollapse { state } => {
                out.push_str(&format!("  Failing state: {state}\n"));
                out.push_str("  Problem: Premature block collapse (gap shrank to < 2, leaving 0 separated blocks).\n");
                out.push_str(&format!(
                    "  Explanation: Floor {} allows the gap to shrink too small during symbolic expansion, merging all blocks into one.\n",
                    self.floor
                ));
                out.push_str(&format!(
                    "  Suggestion: Try increasing --floor (e.g. -f {} or -f {}).\n",
                    self.floor + 2, self.floor + 4
                ));
            }
            CtlFailureDetail::HitUndefinedRule { pebbles, state } => {
                out.push_str(&format!("  Failing state: {state}\n"));
                out.push_str(&format!(
                    "  Problem: Transition requires undefined rule for {pebbles} pebbles.\n"
                ));
                out.push_str("  Explanation: Symbolic zero-gap expansion allowed an unconstrained collision phase that hits this rule slot.\n");
                out.push_str("  Suggestion: If concrete simulation never hits this rule, gap parity is likely periodic. Try specifying --modulus (e.g. --mod 2, 3, 4, 6, 12).\n");
            }
            CtlFailureDetail::HitHalt { state } => {
                out.push_str(&format!("  Failing state: {state}\n"));
                out.push_str("  Problem: Symbolic transition generated a halting configuration (empty tape / all stationary pebbles).\n");
            }
            CtlFailureDetail::BlockTooLarge { len, max, state } => {
                out.push_str(&format!("  Failing state: {state}\n"));
                out.push_str(&format!(
                    "  Problem: A block grew to length {len} (maximum supported block size is {max}).\n"
                ));
                out.push_str("  Explanation: The pebbles in this block do not remain tightly localized under the current split threshold.\n");
            }
            CtlFailureDetail::NegativeGap { state } => {
                out.push_str(&format!("  Failing state: {state}\n"));
                out.push_str("  Problem: Gap became negative without merging.\n");
            }
            CtlFailureDetail::ExceededMaxStates { limit, last_state } => {
                out.push_str(&format!("  Last state generated: {last_state}\n"));
                out.push_str(&format!(
                    "  Problem: Language reached limit of {limit} states without closing.\n"
                ));
                out.push_str("  Suggestion: Try increasing --max-states, adjusting --floor, or specifying --modulus.\n");
            }
        }
        out
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CtlVerificationOutcome {
    Closed { num_states: usize },
    ExceededMaxStates { limit: usize, last_state: CtlState },
    HitUndefinedRule { pebbles: u8, state: CtlState },
    HitHalt { state: CtlState },
    StructuralFailure { error: CtlStepError, state: CtlState },
}

pub fn verify_ctl_closure(
    seed: CtlState,
    program: &Program,
    split_threshold: usize,
    floor: usize,
    max_states: usize,
) -> CtlVerificationOutcome {
    let mut language: Vec<CtlState> = vec![seed.clone()];
    let mut queue: std::collections::VecDeque<CtlState> = std::collections::VecDeque::new();
    queue.push_back(seed);

    while let Some(curr) = queue.pop_front() {
        let Ok(pre_branches) = unroll_ctl_state(&curr) else {
            return CtlVerificationOutcome::StructuralFailure {
                error: CtlStepError::UnrollFailed,
                state: curr,
            };
        };
        for pre in pre_branches {
            let next_state = match step_ctl_pre_state(&pre, program, split_threshold, floor) {
                Ok(s) => s,
                Err(CtlStepError::UndefinedRule { pebbles }) => {
                    return CtlVerificationOutcome::HitUndefinedRule { pebbles, state: pre };
                }
                Err(CtlStepError::HaltingState) | Err(CtlStepError::AllStationary) => {
                    return CtlVerificationOutcome::HitHalt { state: pre };
                }
                Err(e) => {
                    return CtlVerificationOutcome::StructuralFailure { error: e, state: pre };
                }
            };
            if !language.iter().any(|existing| next_state.is_subset_of(existing)) {
                if language.len() >= max_states {
                    return CtlVerificationOutcome::ExceededMaxStates {
                        limit: max_states,
                        last_state: next_state,
                    };
                }
                language.retain(|existing| !existing.is_subset_of(&next_state));
                language.push(next_state.clone());
                queue.push_back(next_state);
            }
        }
    }
    CtlVerificationOutcome::Closed {
        num_states: language.len(),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CtlSearchMethod {
    Inferred,
    Exhaustive,
    Manual,
}

impl CtlSearchMethod {
    pub fn as_str(&self) -> &'static str {
        match self {
            CtlSearchMethod::Inferred => "inferred",
            CtlSearchMethod::Exhaustive => "exhaustive",
            CtlSearchMethod::Manual => "manual",
        }
    }
}

impl std::fmt::Display for CtlSearchMethod {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl std::str::FromStr for CtlSearchMethod {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.to_ascii_lowercase().as_str() {
            "inferred" => Ok(CtlSearchMethod::Inferred),
            "exhaustive" | "grid" => Ok(CtlSearchMethod::Exhaustive),
            "manual" => Ok(CtlSearchMethod::Manual),
            other => Err(format!("unknown CTL search method: '{other}'")),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct CtlProof {
    pub num_steps: u64,
    pub num_states: usize,
    pub split_threshold: usize,
    pub floor: usize,
    pub modulus: usize,
    pub method: CtlSearchMethod,
}

impl std::fmt::Display for CtlProof {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "states={} floor={} mod={} method={}",
            self.num_states, self.floor, self.modulus, self.method
        )
    }
}

pub fn gcd(mut a: usize, mut b: usize) -> usize {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

pub fn lcm(a: usize, b: usize) -> usize {
    if a == 0 || b == 0 {
        0
    } else {
        (a / gcd(a, b)) * b
    }
}

pub fn gcd_of_slice(diffs: &[usize]) -> usize {
    let mut g = 0;
    for &d in diffs {
        if d > 0 {
            g = gcd(g, d);
        }
    }
    g
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InferredCtlCandidate {
    pub floor: usize,
    pub modulus: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InferenceAnalysis {
    pub seen_count: usize,
    pub gap_gcds: Vec<usize>,
    pub overall_lcm: usize,
    pub candidate_floors: Vec<usize>,
    pub candidate_moduli: Vec<usize>,
    pub candidates: Vec<InferredCtlCandidate>,
}

pub fn format_blocks_signature(blocks: &[Vec<u8>]) -> String {
    blocks
        .iter()
        .map(|b| {
            let inner = b
                .iter()
                .map(|c| c.to_string())
                .collect::<Vec<_>>()
                .join(", ");
            format!("[{inner}]")
        })
        .collect::<Vec<_>>()
        .join(" ")
}

#[derive(Debug, Clone, Default)]
pub struct CtlTrajectoryTracker {
    pub signatures: std::collections::HashMap<Vec<Vec<u8>>, Vec<(u64, Vec<usize>)>>,
}

impl CtlTrajectoryTracker {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn total_snapshots(&self) -> usize {
        self.signatures.values().map(|v| v.len()).sum()
    }

    pub fn num_signatures(&self) -> usize {
        self.signatures.len()
    }

    pub fn record_snapshot(&mut self, step: u64, blocks: Vec<Vec<u8>>, gaps: Vec<usize>) {
        if gaps.is_empty() {
            return;
        }
        self.signatures.entry(blocks).or_default().push((step, gaps));
    }

    /// Return the top N block patterns by frequency of occurrence in the trajectory.
    pub fn top_signatures(&self, n: usize) -> Vec<(Vec<Vec<u8>>, usize)> {
        let mut list: Vec<(Vec<Vec<u8>>, usize)> = self
            .signatures
            .iter()
            .map(|(blocks, hist)| (blocks.clone(), hist.len()))
            .collect();
        list.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
        list.truncate(n);
        list
    }

    /// Return the rank (1-indexed) and occurrence count of a specific block pattern.
    pub fn signature_rank(&self, blocks: &[Vec<u8>]) -> Option<(usize, usize)> {
        let mut list: Vec<(usize, &Vec<Vec<u8>>)> = self
            .signatures
            .iter()
            .map(|(b, hist)| (hist.len(), b))
            .collect();
        list.sort_by(|a, b| b.0.cmp(&a.0).then_with(|| a.1.cmp(b.1)));
        list.iter()
            .position(|(_, b)| b.as_slice() == blocks)
            .map(|idx| (idx + 1, list[idx].0))
    }

    /// Count how many distinct gap residue combinations (g_i - floor) % modulus
    /// were observed for this pattern in the trajectory.
    pub fn observed_gap_residues(
        &self,
        blocks: &[Vec<u8>],
        floor: usize,
        modulus: usize,
    ) -> (usize, usize) {
        let history = match self.signatures.get(blocks) {
            Some(h) => h,
            None => return (0, 0),
        };
        let num_gaps = history.first().map(|(_, g)| g.len()).unwrap_or(0);
        let max_possible = if modulus <= 1 {
            1
        } else {
            modulus.checked_pow(num_gaps as u32).unwrap_or(usize::MAX)
        };
        let mut distinct = std::collections::HashSet::new();
        for (_, gaps) in history {
            if gaps.iter().all(|&g| g >= floor) {
                let residue_tuple: Vec<usize> = gaps
                    .iter()
                    .map(|&g| (g - floor) % modulus)
                    .collect();
                distinct.insert(residue_tuple);
            }
        }
        (distinct.len(), max_possible)
    }

    /// Analyze recurring block signatures for current blocks and return detailed analysis.
    pub fn analyze_blocks(
        &self,
        current_blocks: &[Vec<u8>],
        current_gaps: &[usize],
        split_threshold: usize,
        candidate_floors: &[usize],
    ) -> Option<InferenceAnalysis> {
        let base_floor = 2 * split_threshold + 2;
        let history = self.signatures.get(current_blocks)?;

        if history.len() < 3 {
            return None;
        }

        let num_gaps = current_gaps.len();
        let mut gap_gcds = Vec::with_capacity(num_gaps);

        for g_idx in 0..num_gaps {
            let values: Vec<usize> = history
                .iter()
                .filter_map(|(_, g)| g.get(g_idx).copied())
                .collect();
            if values.len() < 3 {
                continue;
            }
            let mut diffs = Vec::with_capacity(values.len() - 1);
            for w in values.windows(2) {
                let d = (w[1] as isize - w[0] as isize).unsigned_abs();
                if d > 0 {
                    diffs.push(d);
                }
            }
            let d_i = gcd_of_slice(&diffs);
            if d_i > 0 {
                gap_gcds.push(d_i);
            }
        }

        let floors = if !candidate_floors.is_empty() {
            candidate_floors.to_vec()
        } else {
            vec![base_floor, base_floor + 2, base_floor + 4]
        };

        // Recommend modulus from LCM of observed gap differences
        let overall_lcm = if gap_gcds.is_empty() {
            1
        } else {
            gap_gcds.iter().copied().fold(1, lcm)
        };

        let mut moduli = Vec::new();
        if overall_lcm > 1 && overall_lcm <= 24 {
            moduli.push(overall_lcm);
            for factor in [12, 6, 4, 3, 2] {
                if factor < overall_lcm && overall_lcm % factor == 0 && !moduli.contains(&factor) {
                    moduli.push(factor);
                }
            }
        } else if overall_lcm > 24 {
            for factor in [12, 8, 6, 4, 3, 2] {
                if overall_lcm % factor == 0 && !moduli.contains(&factor) {
                    moduli.push(factor);
                }
            }
        }
        if !moduli.contains(&1) {
            moduli.push(1);
        }

        let mut candidates = Vec::new();
        for &f in &floors {
            for &m in &moduli {
                candidates.push(InferredCtlCandidate {
                    floor: f,
                    modulus: m,
                });
            }
        }

        Some(InferenceAnalysis {
            seen_count: history.len(),
            gap_gcds,
            overall_lcm,
            candidate_floors: floors,
            candidate_moduli: moduli,
            candidates,
        })
    }

    /// Analyze recurring block signatures for current blocks and return inferred candidate parameter pairs.
    pub fn infer_candidates_for_blocks(
        &self,
        current_blocks: &[Vec<u8>],
        current_gaps: &[usize],
        split_threshold: usize,
        candidate_floors: &[usize],
    ) -> Vec<InferredCtlCandidate> {
        self.analyze_blocks(
            current_blocks,
            current_gaps,
            split_threshold,
            candidate_floors,
        )
        .map(|a| a.candidates)
        .unwrap_or_default()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TapeProofResult {
    Proved(CtlProof),
    HitUndefinedRule {
        pebbles: u8,
        diagnostic: Option<CtlFailureDiagnostic>,
    },
    HitHalt {
        diagnostic: Option<CtlFailureDiagnostic>,
    },
    Failed {
        diagnostic: Option<CtlFailureDiagnostic>,
    },
    Inconclusive {
        max_gap: usize,
    },
}

pub fn try_prove_ctl_from_tape(
    program: &Program,
    cells: &[u8],
    step: u64,
    max_states: usize,
) -> TapeProofResult {
    try_prove_ctl_from_tape_with_threshold(program, cells, step, max_states, 2)
}

pub fn try_prove_ctl_from_tape_with_threshold(
    program: &Program,
    cells: &[u8],
    step: u64,
    max_states: usize,
    split_threshold: usize,
) -> TapeProofResult {
    try_prove_ctl_from_tape_with_params(
        program,
        cells,
        step,
        max_states,
        split_threshold,
        2 * split_threshold + 2,
        None,
    )
}

pub fn try_prove_ctl_from_tape_with_params(
    program: &Program,
    cells: &[u8],
    step: u64,
    max_states: usize,
    split_threshold: usize,
    floor: usize,
    forced_modulus: Option<usize>,
) -> TapeProofResult {
    try_prove_ctl_from_tape_with_floors_and_method(
        program,
        cells,
        step,
        max_states,
        split_threshold,
        &[floor],
        forced_modulus.map(|m| vec![m]).as_deref(),
        CtlSearchMethod::Manual,
        false,
        None,
    )
}

pub fn try_prove_ctl_from_tape_with_floors(
    program: &Program,
    cells: &[u8],
    step: u64,
    max_states: usize,
    split_threshold: usize,
    floors: &[usize],
    forced_modulus: Option<usize>,
) -> TapeProofResult {
    try_prove_ctl_from_tape_with_floors_and_method(
        program,
        cells,
        step,
        max_states,
        split_threshold,
        floors,
        forced_modulus.map(|m| vec![m]).as_deref(),
        CtlSearchMethod::Exhaustive,
        false,
        None,
    )
}

pub fn try_prove_ctl_from_tape_with_floors_and_method(
    program: &Program,
    cells: &[u8],
    step: u64,
    max_states: usize,
    split_threshold: usize,
    floors: &[usize],
    custom_moduli: Option<&[usize]>,
    method: CtlSearchMethod,
    show_progress: bool,
    tracker: Option<&CtlTrajectoryTracker>,
) -> TapeProofResult {
    let (blocks, raw_gaps) = split_slice_by_threshold(cells, split_threshold);
    if raw_gaps.is_empty() {
        return TapeProofResult::Inconclusive { max_gap: 0 };
    }
    let max_gap = *raw_gaps.iter().max().unwrap_or(&0);
    let min_floor = *floors.iter().min().unwrap_or(&usize::MAX);
    if max_gap < min_floor {
        return TapeProofResult::Inconclusive { max_gap };
    }
    let default_moduli = [1, 2, 3, 4, 6, 12];
    let moduli: &[usize] = match custom_moduli {
        Some(m) => m,
        None => &default_moduli,
    };
    let mut hit_undef = None;
    let mut hit_halt = None;
    let mut last_failure = None;

    for &floor in floors {
        if max_gap < floor {
            continue;
        }
        let mut skip_remaining_moduli_for_floor = false;
        for &modulus in moduli {
            if skip_remaining_moduli_for_floor {
                break;
            }
            if show_progress {
                use std::io::Write;
                let res_info = if let Some(tr) = tracker {
                    let (obs, max_comb) = tr.observed_gap_residues(&blocks, floor, modulus);
                    if max_comb > 1 {
                        format!(", {obs}/{max_comb} trajectory gap residues")
                    } else {
                        String::new()
                    }
                } else {
                    String::new()
                };
                print!("  Testing floor={floor}, mod={modulus} (method={method}{res_info})... ");
                std::io::stdout().flush().ok();
            }
            let gaps: Vec<ZeroGap> = raw_gaps
                .iter()
                .map(|&g| ZeroGap::new(g, floor, modulus))
                .collect();
            let seed = CtlState {
                modulus,
                blocks: blocks.clone(),
                gaps,
            };
            match verify_ctl_closure(seed, program, split_threshold, floor, max_states) {
                CtlVerificationOutcome::Closed { num_states } => {
                    if show_progress {
                        println!("PROVED! (closed in {num_states} states)");
                    }
                    return TapeProofResult::Proved(CtlProof {
                        num_steps: step,
                        num_states,
                        split_threshold,
                        floor,
                        modulus,
                        method,
                    });
                }
                CtlVerificationOutcome::HitUndefinedRule { pebbles, state } => {
                    if show_progress {
                        println!("failed (requires undefined rule for {pebbles} pebbles)");
                    }
                    let diag = CtlFailureDiagnostic {
                        step,
                        floor,
                        modulus,
                        detail: CtlFailureDetail::HitUndefinedRule { pebbles, state },
                    };
                    hit_undef = Some((pebbles, diag.clone()));
                    last_failure = Some(diag);
                }
                CtlVerificationOutcome::HitHalt { state } => {
                    if show_progress {
                        println!("failed (reached halting state)");
                    }
                    let diag = CtlFailureDiagnostic {
                        step,
                        floor,
                        modulus,
                        detail: CtlFailureDetail::HitHalt { state },
                    };
                    hit_halt = Some(diag.clone());
                    last_failure = Some(diag);
                }
                CtlVerificationOutcome::ExceededMaxStates { limit, last_state } => {
                    if show_progress {
                        println!("failed (exceeded limit of {limit} states)");
                    }
                    last_failure = Some(CtlFailureDiagnostic {
                        step,
                        floor,
                        modulus,
                        detail: CtlFailureDetail::ExceededMaxStates { limit, last_state },
                    });
                }
                CtlVerificationOutcome::StructuralFailure { error, state } => {
                    let is_collapse = matches!(error, CtlStepError::UnrollFailed);
                    if show_progress {
                        match error {
                            CtlStepError::UnrollFailed => {
                                println!("failed (premature block collapse: gap shrank to < 2)");
                            }
                            CtlStepError::BlockTooLarge { len, max } => {
                                println!("failed (block grew to len {len} > {max})");
                            }
                            CtlStepError::NegativeGap => {
                                println!("failed (negative gap)");
                            }
                            CtlStepError::UndefinedRule { pebbles } => {
                                println!("failed (transition requires undefined rule for {pebbles} pebbles)");
                            }
                            CtlStepError::HaltingState | CtlStepError::AllStationary => {
                                println!("failed (reached halting state)");
                            }
                        }
                    }
                    let detail = match error {
                        CtlStepError::BlockTooLarge { len, max } => {
                            CtlFailureDetail::BlockTooLarge { len, max, state }
                        }
                        CtlStepError::NegativeGap => CtlFailureDetail::NegativeGap { state },
                        CtlStepError::UnrollFailed => {
                            CtlFailureDetail::PrematureCollapse { state }
                        }
                        CtlStepError::UndefinedRule { pebbles } => {
                            CtlFailureDetail::HitUndefinedRule { pebbles, state }
                        }
                        CtlStepError::HaltingState | CtlStepError::AllStationary => {
                            CtlFailureDetail::HitHalt { state }
                        }
                    };
                    last_failure = Some(CtlFailureDiagnostic {
                        step,
                        floor,
                        modulus,
                        detail,
                    });
                    if is_collapse {
                        if show_progress {
                            println!("  Skipping remaining moduli for floor {floor} (spatial collapse)");
                        }
                        // Failure-directed pruning: spatial gap collapsed (< 2).
                        // Other moduli at this same floor will also collapse spatially.
                        skip_remaining_moduli_for_floor = true;
                    }
                }
            }
        }
    }

    if let Some((pebbles, diag)) = hit_undef {
        TapeProofResult::HitUndefinedRule {
            pebbles,
            diagnostic: Some(diag),
        }
    } else if let Some(diag) = hit_halt {
        TapeProofResult::HitHalt {
            diagnostic: Some(diag),
        }
    } else if last_failure.is_some() {
        TapeProofResult::Failed {
            diagnostic: last_failure,
        }
    } else {
        TapeProofResult::Inconclusive { max_gap }
    }
}

/// Decider 5: Closed Tape Language (CTL) regular-set non-halting prover.
pub fn decide_ctl(program: &Program, max_steps: u64) -> Option<Decider> {
    let mut sim = Simulator::new(program.size());
    let sample_start = (max_steps / 3).max(max_steps.saturating_sub(68));

    for step in 0..=max_steps {
        if step >= sample_start && (max_steps - step) % 4 == 0 {
            if let TapeProofResult::Proved(proof) =
                try_prove_ctl_from_tape(program, &sim.cells(), step, 1024)
            {
                return Some(Decider::Ctl(Some(proof)));
            }
        }
        if sim.step(program) != StepResult::Stepped {
            return None;
        }
    }
    None
}

#[derive(Debug, Clone)]
pub struct CtlConfig {
    pub min_step: u64,
    pub max_steps: u64,
    pub max_states: usize,
    pub step_interval: u64,
    pub split_threshold: usize,
    pub floor: Option<usize>,
    pub floors: Vec<usize>,
    pub modulus: Option<usize>,
    pub verbose: bool,
    pub show_progress: bool,
}

impl Default for CtlConfig {
    fn default() -> Self {
        Self {
            min_step: 0,
            max_steps: 5000,
            max_states: 10000,
            step_interval: 10,
            split_threshold: 2,
            floor: None,
            floors: Vec::new(),
            modulus: None,
            verbose: false,
            show_progress: false,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CtlSearchOutcome {
    Proved(CtlProof),
    ConcreteHalt {
        step: u64,
    },
    ConcreteMissingRule {
        step: u64,
        pebbles: u8,
    },
    ClosureHitUndefinedRule {
        step: u64,
        pebbles: u8,
        diagnostic: Option<CtlFailureDiagnostic>,
    },
    ClosureHitHalt {
        step: u64,
        diagnostic: Option<CtlFailureDiagnostic>,
    },
    LimitReached {
        max_steps: u64,
        max_states: usize,
        diagnostic: Option<CtlFailureDiagnostic>,
        candidates_tested: usize,
        max_gap_seen: usize,
    },
}

pub fn run_ctl_search(program: &Program, config: &CtlConfig) -> CtlSearchOutcome {
    let mut sim = Simulator::new(program.size());
    let mut tracker = CtlTrajectoryTracker::new();
    let mut last_hit_undef = None;
    let mut last_hit_halt = None;
    let mut best_failure_diag = None;
    let mut candidates_tested = 0;
    let mut max_gap_seen = 0;

    let mut printed_methods: std::collections::HashSet<CtlSearchMethod> =
        std::collections::HashSet::new();
    let mut printed_inferred_signatures: std::collections::HashSet<Vec<Vec<u8>>> =
        std::collections::HashSet::new();

    let is_manual = config.modulus.is_some() || config.floor.is_some();
    let fallback_method = if is_manual {
        CtlSearchMethod::Manual
    } else {
        CtlSearchMethod::Exhaustive
    };

    let floors: Vec<usize> = if !config.floors.is_empty() {
        config.floors.clone()
    } else if let Some(f) = config.floor {
        vec![f]
    } else {
        vec![2 * config.split_threshold + 2]
    };

    #[derive(Debug, Clone)]
    struct SavedSnapshot {
        step: u64,
        blocks: Vec<Vec<u8>>,
        gaps: Vec<usize>,
        cells: Vec<u8>,
    }

    let mut saved_snapshots: Vec<SavedSnapshot> = Vec::new();

    // Phase 1: Fast direct simulation up to max_steps, collecting trajectory snapshots
    for step in 0..=config.max_steps {
        if step >= config.min_step && (step == 0 || step % config.step_interval == 0) {
            let cells = sim.cells();
            if config.verbose {
                eprintln!(
                    "step {step}: span={}, nonzeros={}",
                    cells.len(),
                    sim.sparse_entries().len()
                );
            }
            let (blocks, raw_gaps) = split_slice_by_threshold(&cells, config.split_threshold);
            if !raw_gaps.is_empty() {
                tracker.record_snapshot(step, blocks.clone(), raw_gaps.clone());
                let cur_max = *raw_gaps.iter().max().unwrap_or(&0);
                if cur_max > max_gap_seen {
                    max_gap_seen = cur_max;
                }
                saved_snapshots.push(SavedSnapshot {
                    step,
                    blocks,
                    gaps: raw_gaps,
                    cells,
                });
                if saved_snapshots.len() > 100 {
                    saved_snapshots.remove(0);
                }
            }
        }

        if step < config.max_steps {
            match sim.step(program) {
                StepResult::Halted => return CtlSearchOutcome::ConcreteHalt { step: step + 1 },
                StepResult::MissingRule(pebbles) => {
                    return CtlSearchOutcome::ConcreteMissingRule {
                        step: step + 1,
                        pebbles,
                    }
                }
                StepResult::Stepped => {}
            }
        }
    }

    // Phase 2: Simulation reached max_steps. Perform parameter verification on mature snapshots.
    if saved_snapshots.is_empty() {
        return CtlSearchOutcome::LimitReached {
            max_steps: config.max_steps,
            max_states: config.max_states,
            diagnostic: None,
            candidates_tested: 0,
            max_gap_seen,
        };
    }

    if config.show_progress {
        let total_snaps = tracker.total_snapshots();
        let num_patterns = tracker.num_signatures();
        let recurrent_count = tracker
            .signatures
            .values()
            .filter(|h| h.len() >= 3)
            .count();

        println!();
        println!("=== Trajectory Simulation Summary ===");
        println!("  Simulation steps:    {}", config.max_steps);
        println!(
            "  Snapshots recorded:  {} (sampled every {} steps)",
            total_snaps, config.step_interval
        );
        println!("  Max gap seen:        {}", max_gap_seen);
        println!(
            "  Flattened configs:   {} distinct block patterns ({} recurrent >= 3 times)",
            num_patterns, recurrent_count
        );
        println!("  Top flattened block patterns by frequency:");
        for (rank, (pattern, count)) in tracker.top_signatures(5).into_iter().enumerate() {
            let pct = if total_snaps > 0 {
                (count as f64 / total_snaps as f64) * 100.0
            } else {
                0.0
            };
            println!(
                "    #{}. {} (seen {}x, {:.1}%)",
                rank + 1,
                format_blocks_signature(&pattern),
                count,
                pct
            );
        }
    }

    let min_floor = *floors.iter().min().unwrap_or(&usize::MAX);

    // Select the best candidate snapshot near max_steps:
    // 1. Prefer recurrent block signatures (seen >= 3 times) that have gap >= min_floor, choosing the one with largest gap.
    // 2. Otherwise, pick any snapshot with gap >= min_floor having the largest gap.
    // 3. Otherwise, pick the snapshot with the largest gap overall.
    let target_snapshot = saved_snapshots
        .iter()
        .filter(|s| {
            let gap = *s.gaps.iter().max().unwrap_or(&0);
            gap >= min_floor
                && tracker
                    .signatures
                    .get(&s.blocks)
                    .map(|h| h.len() >= 3)
                    .unwrap_or(false)
        })
        .max_by_key(|s| (*s.gaps.iter().max().unwrap_or(&0), s.step))
        .or_else(|| {
            saved_snapshots
                .iter()
                .filter(|s| *s.gaps.iter().max().unwrap_or(&0) >= min_floor)
                .max_by_key(|s| (*s.gaps.iter().max().unwrap_or(&0), s.step))
        })
        .or_else(|| {
            saved_snapshots
                .iter()
                .max_by_key(|s| (*s.gaps.iter().max().unwrap_or(&0), s.step))
        })
        .cloned();

    let candidate_snapshots: Vec<SavedSnapshot> = target_snapshot.into_iter().collect();

    for snap in &candidate_snapshots {
        let snap_max_gap = *snap.gaps.iter().max().unwrap_or(&0);

        // 1. If not manually constrained, try inferred candidate parameters first
        if !is_manual {
            if let Some(analysis) =
                tracker.analyze_blocks(&snap.blocks, &snap.gaps, config.split_threshold, &floors)
            {
                let inferred_candidates = &analysis.candidates;
                if !inferred_candidates.is_empty() {
                    if config.show_progress && printed_inferred_signatures.insert(snap.blocks.clone()) {
                        printed_methods.insert(CtlSearchMethod::Inferred);
                        println!();
                        println!("Method selected: inferred");
                        let (rank, count) = tracker
                            .signature_rank(&snap.blocks)
                            .unwrap_or((0, analysis.seen_count));
                        let pct = if tracker.total_snapshots() > 0 {
                            (count as f64 / tracker.total_snapshots() as f64) * 100.0
                        } else {
                            0.0
                        };
                        println!(
                            "  Target pattern (step {}): {} (seen {}x, rank #{}, {:.1}% of trajectory)",
                            snap.step,
                            format_blocks_signature(&snap.blocks),
                            count,
                            rank,
                            pct
                        );
                        let num_gaps = snap.gaps.len();
                        println!(
                            "  Gaps in pattern:     {} -> difference GCDs: {:?}, overall LCM modulus: {}",
                            num_gaps, analysis.gap_gcds, analysis.overall_lcm
                        );
                        println!(
                            "  Candidate floors:    {:?}, candidate moduli: {:?}",
                            analysis.candidate_floors, analysis.candidate_moduli
                        );
                    }

                    let mut inferred_floors = Vec::new();
                    for c in inferred_candidates {
                        if !inferred_floors.contains(&c.floor) {
                            inferred_floors.push(c.floor);
                        }
                    }
                    for inf_floor in inferred_floors {
                        if snap_max_gap < inf_floor {
                            continue;
                        }
                        let inf_moduli: Vec<usize> = inferred_candidates
                            .iter()
                            .filter(|c| c.floor == inf_floor)
                            .map(|c| c.modulus)
                            .collect();
                        match try_prove_ctl_from_tape_with_floors_and_method(
                            program,
                            &snap.cells,
                            snap.step,
                            config.max_states,
                            config.split_threshold,
                            &[inf_floor],
                            Some(&inf_moduli),
                            CtlSearchMethod::Inferred,
                            config.show_progress,
                            Some(&tracker),
                        ) {
                            TapeProofResult::Proved(proof) => return CtlSearchOutcome::Proved(proof),
                            TapeProofResult::HitUndefinedRule {
                                pebbles,
                                diagnostic,
                            } => {
                                candidates_tested += 1;
                                if diagnostic.is_some() {
                                    best_failure_diag = diagnostic.clone();
                                }
                                last_hit_undef = Some((snap.step, pebbles, diagnostic));
                            }
                            TapeProofResult::HitHalt { diagnostic } => {
                                candidates_tested += 1;
                                if diagnostic.is_some() {
                                    best_failure_diag = diagnostic.clone();
                                }
                                last_hit_halt = Some((snap.step, diagnostic));
                            }
                            TapeProofResult::Failed { diagnostic } => {
                                candidates_tested += 1;
                                if diagnostic.is_some() {
                                    best_failure_diag = diagnostic;
                                }
                            }
                            TapeProofResult::Inconclusive { max_gap } => {
                                if max_gap > max_gap_seen {
                                    max_gap_seen = max_gap;
                                }
                            }
                        }
                    }
                }
            }
        }

        // 2. Fallback to exhaustive grid scan (or manual search if user constrained)
        if snap_max_gap >= min_floor {
            if config.show_progress
                && printed_methods.insert(fallback_method)
            {
                println!();
                if is_manual {
                    println!("Method selected: manual");
                } else {
                    println!("Method selected: exhaustive (fallback grid)");
                }
                let (rank, count) = tracker
                    .signature_rank(&snap.blocks)
                    .unwrap_or((0, 0));
                let pct = if tracker.total_snapshots() > 0 {
                    (count as f64 / tracker.total_snapshots() as f64) * 100.0
                } else {
                    0.0
                };
                println!(
                    "  Target pattern (step {}): {} (seen {}x, rank #{}, {:.1}% of trajectory)",
                    snap.step,
                    format_blocks_signature(&snap.blocks),
                    count,
                    rank,
                    pct
                );
                if is_manual {
                    println!(
                        "  Candidate parameters: floors={:?}, modulus={:?}",
                        floors, config.modulus
                    );
                } else {
                    let default_moduli = [1, 2, 3, 4, 6, 12];
                    let moduli_to_test = config
                        .modulus
                        .map(|m| vec![m])
                        .unwrap_or_else(|| default_moduli.to_vec());
                    println!(
                        "  Testing grid:        floors={:?}, moduli={:?}",
                        floors, moduli_to_test
                    );
                }
            }

            match try_prove_ctl_from_tape_with_floors_and_method(
                program,
                &snap.cells,
                snap.step,
                config.max_states,
                config.split_threshold,
                &floors,
                config.modulus.map(|m| vec![m]).as_deref(),
                fallback_method,
                config.show_progress,
                Some(&tracker),
            ) {
                TapeProofResult::Proved(proof) => return CtlSearchOutcome::Proved(proof),
                TapeProofResult::HitUndefinedRule {
                    pebbles,
                    diagnostic,
                } => {
                    candidates_tested += 1;
                    if diagnostic.is_some() {
                        best_failure_diag = diagnostic.clone();
                    }
                    last_hit_undef = Some((snap.step, pebbles, diagnostic));
                }
                TapeProofResult::HitHalt { diagnostic } => {
                    candidates_tested += 1;
                    if diagnostic.is_some() {
                        best_failure_diag = diagnostic.clone();
                    }
                    last_hit_halt = Some((snap.step, diagnostic));
                }
                TapeProofResult::Failed { diagnostic } => {
                    candidates_tested += 1;
                    if diagnostic.is_some() {
                        best_failure_diag = diagnostic;
                    }
                }
                TapeProofResult::Inconclusive { max_gap } => {
                    if max_gap > max_gap_seen {
                        max_gap_seen = max_gap;
                    }
                }
            }
        }
    }

    if let Some((step, pebbles, diagnostic)) = last_hit_undef {
        CtlSearchOutcome::ClosureHitUndefinedRule {
            step,
            pebbles,
            diagnostic,
        }
    } else if let Some((step, diagnostic)) = last_hit_halt {
        CtlSearchOutcome::ClosureHitHalt { step, diagnostic }
    } else {
        CtlSearchOutcome::LimitReached {
            max_steps: config.max_steps,
            max_states: config.max_states,
            diagnostic: best_failure_diag,
            candidates_tested,
            max_gap_seen,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ctl_search_user_prog() {
        let prog: Program = "00_00_30_10_11_06_21_03_07_19".parse().unwrap();
        let config = CtlConfig {
            min_step: 100,
            max_steps: 500,
            max_states: 5000,
            step_interval: 50,
            split_threshold: 2,
            floor: None,
            floors: Vec::new(),
            modulus: None,
            verbose: false,
            show_progress: false,
        };
        let outcome = run_ctl_search(&prog, &config);
        match outcome {
            CtlSearchOutcome::Proved(proof) => {
                println!("Proof found at step 100: {:?}", proof);
                assert!(proof.num_steps <= 500);
                assert!(proof.num_states > 0 && proof.num_states <= 5000);
            }
            other => panic!("expected Proved, got {:?}", other),
        }
    }

    #[test]
    fn test_ctl_search_halting_prog() {
        let prog: Program = "00_00_00".parse().unwrap();
        let config = CtlConfig::default();
        let outcome = run_ctl_search(&prog, &config);
        assert_eq!(outcome, CtlSearchOutcome::ConcreteHalt { step: 1 });
    }

    #[test]
    fn test_ctl_search_missing_rule_prog() {
        let prog = Program::new(vec![None]).unwrap();
        let config = CtlConfig::default();
        let outcome = run_ctl_search(&prog, &config);
        assert_eq!(
            outcome,
            CtlSearchOutcome::ConcreteMissingRule {
                step: 1,
                pebbles: 1
            }
        );
    }

    #[test]
    fn test_ctl_search_user_prog_2() {
        let prog: Program = "00_20_10_04_21_21_07_50_17_01".parse().unwrap();
        let config = CtlConfig::default();
        let outcome = run_ctl_search(&prog, &config);
        match outcome {
            CtlSearchOutcome::Proved(proof) => {
                assert!(proof.num_states <= 1000, "proof size too large: {}", proof.num_states);
            }
            other => panic!("expected Proved, got {:?}", other),
        }
    }

    #[test]
    fn test_ctl_user_prog_floor_10() {
        let prog: Program = "01_00_02_03_05_60_23_05_13_19".parse().unwrap();
        let mut sim = Simulator::new(prog.size());
        for _ in 0..240 {
            sim.step(&prog);
        }
        let cells = sim.cells();
        let (blocks, raw_gaps) = split_slice_by_threshold(&cells, 2);
        let floor = 10;
        let gaps: Vec<ZeroGap> = raw_gaps
            .iter()
            .map(|&g| ZeroGap::new(g, floor, 1))
            .collect();
        let seed = CtlState {
            modulus: 1,
            blocks,
            gaps,
        };
        let outcome = verify_ctl_closure(seed, &prog, 2, floor, 500);
        assert_eq!(outcome, CtlVerificationOutcome::Closed { num_states: 63 });
    }

    #[test]
    fn test_ctl_user_prog_modulus_12() {
        let prog: Program = "00_02_21_40_11_--_10_08_43_11".parse().unwrap();
        let mut sim = Simulator::new(prog.size());
        for _ in 0..200 {
            sim.step(&prog);
        }
        let cells = sim.cells();
        let (blocks, raw_gaps) = split_slice_by_threshold(&cells, 2);
        let floor = 6;
        let modulus = 12;
        let gaps: Vec<ZeroGap> = raw_gaps
            .iter()
            .map(|&g| ZeroGap::new(g, floor, modulus))
            .collect();
        let seed = CtlState {
            modulus,
            blocks,
            gaps,
        };
        let outcome = verify_ctl_closure(seed, &prog, 2, floor, 1000);
        assert_eq!(outcome, CtlVerificationOutcome::Closed { num_states: 454 });
    }

    #[test]
    fn test_diagnose_prog_premature_collapse() {
        let prog: Program = "01_00_02_03_05_60_23_05_--_23".parse().unwrap();
        let config = CtlConfig {
            min_step: 0,
            max_steps: 200,
            max_states: 1000,
            step_interval: 10,
            split_threshold: 2,
            floor: Some(6),
            floors: Vec::new(),
            modulus: None,
            verbose: false,
            show_progress: false,
        };
        let outcome = run_ctl_search(&prog, &config);
        match outcome {
            CtlSearchOutcome::LimitReached {
                diagnostic: Some(diag),
                ..
            } => match diag.detail {
                CtlFailureDetail::PrematureCollapse { state } => {
                    assert_eq!(state.blocks.len(), 2);
                }
                other => panic!("expected PrematureCollapse, got {:?}", other),
            },
            other => panic!("expected LimitReached with diagnostic, got {:?}", other),
        }
    }

    #[test]
    fn test_ctl_search_multiple_floors() {
        let prog: Program = "01_00_02_03_05_60_23_05_--_23".parse().unwrap();
        let config = CtlConfig {
            min_step: 0,
            max_steps: 300,
            max_states: 1000,
            step_interval: 10,
            split_threshold: 2,
            floor: None,
            floors: vec![6, 8, 10],
            modulus: None,
            verbose: false,
            show_progress: false,
        };
        let outcome = run_ctl_search(&prog, &config);
        match outcome {
            CtlSearchOutcome::Proved(proof) => {
                assert!(proof.floor >= 8);
                assert!(proof.num_steps >= 200 && proof.num_steps <= 300);
                assert_eq!(proof.method, CtlSearchMethod::Inferred);
            }
            other => panic!("expected Proved with floor >= 8, got {:?}", other),
        }
    }

    #[test]
    fn test_trajectory_tracker_inference() {
        let mut tracker = CtlTrajectoryTracker::new();
        let blocks = vec![vec![1, 2], vec![3]];

        // 3 snapshots: gap 0 has step of 4, gap 1 has step of 6.
        tracker.record_snapshot(10, blocks.clone(), vec![10, 20]);
        tracker.record_snapshot(20, blocks.clone(), vec![14, 26]);
        tracker.record_snapshot(30, blocks.clone(), vec![18, 32]);

        let candidates = tracker.infer_candidates_for_blocks(&blocks, &[18, 32], 2, &[6, 8, 10]);
        assert!(!candidates.is_empty());

        // LCM of diffs 4 and 6 is 12
        let moduli: Vec<usize> = candidates.iter().map(|c| c.modulus).collect();
        assert!(moduli.contains(&12));
        assert!(moduli.contains(&6));
        assert!(moduli.contains(&4));
        assert!(moduli.contains(&1));

        let floors: Vec<usize> = candidates.iter().map(|c| c.floor).collect();
        assert!(floors.contains(&6));
        assert!(floors.contains(&8));
        assert!(floors.contains(&10));
    }
}


