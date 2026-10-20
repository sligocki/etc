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

pub const MAX_CTL_GAPS: usize = 4;

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
    MaxGapsExceeded { count: usize, max: usize },
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
    let mut all_stationary = true;

    for b in &pre.blocks {
        let (nb, dl, dr) = step_isolated_block(b, program)?;
        if dl != 0 || &nb != b {
            all_stationary = false;
        }
        stepped_blocks.push(nb);
        delta_lefts.push(dl);
        delta_rights.push(dr);
    }

    if all_stationary {
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
        return Err(CtlStepError::AllStationary);
    }
    if new_gaps.len() > MAX_CTL_GAPS {
        return Err(CtlStepError::MaxGapsExceeded {
            count: new_gaps.len(),
            max: MAX_CTL_GAPS,
        });
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
pub enum CtlVerificationOutcome {
    Closed { num_states: usize },
    ExceededMaxStates { limit: usize },
    HitUndefinedRule { pebbles: u8 },
    HitHalt,
    StructuralFailure(CtlStepError),
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
            return CtlVerificationOutcome::StructuralFailure(CtlStepError::UnrollFailed);
        };
        for pre in pre_branches {
            let next_state = match step_ctl_pre_state(&pre, program, split_threshold, floor) {
                Ok(s) => s,
                Err(CtlStepError::UndefinedRule { pebbles }) => {
                    return CtlVerificationOutcome::HitUndefinedRule { pebbles };
                }
                Err(CtlStepError::HaltingState) => {
                    return CtlVerificationOutcome::HitHalt;
                }
                Err(e) => {
                    return CtlVerificationOutcome::StructuralFailure(e);
                }
            };
            if !language.iter().any(|existing| next_state.is_subset_of(existing)) {
                if language.len() >= max_states {
                    return CtlVerificationOutcome::ExceededMaxStates { limit: max_states };
                }
                language.push(next_state.clone());
                queue.push_back(next_state);
            }
        }
    }
    CtlVerificationOutcome::Closed {
        num_states: language.len(),
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CtlProof {
    pub num_steps: u64,
    pub num_states: usize,
    pub split_threshold: usize,
    pub floor: usize,
    pub modulus: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TapeProofResult {
    Proved(CtlProof),
    HitUndefinedRule { pebbles: u8 },
    HitHalt,
    Inconclusive,
}

pub fn try_prove_ctl_from_tape(
    program: &Program,
    cells: &[u8],
    step: u64,
    max_states: usize,
) -> TapeProofResult {
    let mut hit_undef = None;
    let mut hit_halt = false;

    for split_threshold in 2..=6 {
        let (blocks, raw_gaps) = split_slice_by_threshold(cells, split_threshold);
        if raw_gaps.is_empty() || raw_gaps.len() > MAX_CTL_GAPS {
            continue;
        }
        let floor = 2 * split_threshold + 2;
        if !raw_gaps.iter().any(|&g| g >= floor) {
            continue;
        }
        for modulus in [1, 2, 3, 4, 6] {
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
                    return TapeProofResult::Proved(CtlProof {
                        num_steps: step,
                        num_states,
                        split_threshold,
                        floor,
                        modulus,
                    });
                }
                CtlVerificationOutcome::HitUndefinedRule { pebbles } => {
                    hit_undef = Some(pebbles);
                }
                CtlVerificationOutcome::HitHalt => {
                    hit_halt = true;
                }
                CtlVerificationOutcome::ExceededMaxStates { .. }
                | CtlVerificationOutcome::StructuralFailure(_) => {}
            }
        }
    }

    if let Some(pebbles) = hit_undef {
        TapeProofResult::HitUndefinedRule { pebbles }
    } else if hit_halt {
        TapeProofResult::HitHalt
    } else {
        TapeProofResult::Inconclusive
    }
}

/// Decider 5: Closed Tape Language (CTL) regular-set non-halting prover.
pub fn decide_ctl(program: &Program, max_steps: u64) -> Option<Decider> {
    let mut sim = Simulator::new(program.size());
    let sample_start = (max_steps / 3).max(max_steps.saturating_sub(68));

    for step in 0..=max_steps {
        if step >= sample_start && (max_steps - step) % 4 == 0 {
            if let TapeProofResult::Proved(_) =
                try_prove_ctl_from_tape(program, &sim.cells(), step, 1024)
            {
                return Some(Decider::Ctl);
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
    pub verbose: bool,
}

impl Default for CtlConfig {
    fn default() -> Self {
        Self {
            min_step: 0,
            max_steps: 5000,
            max_states: 10000,
            step_interval: 10,
            verbose: false,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CtlSearchOutcome {
    Proved(CtlProof),
    ConcreteHalt { step: u64 },
    ConcreteMissingRule { step: u64, pebbles: u8 },
    ClosureHitUndefinedRule { step: u64, pebbles: u8 },
    ClosureHitHalt { step: u64 },
    LimitReached { max_steps: u64, max_states: usize },
}

pub fn run_ctl_search(program: &Program, config: &CtlConfig) -> CtlSearchOutcome {
    let mut sim = Simulator::new(program.size());
    let mut last_hit_undef = None;
    let mut last_hit_halt = None;

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
            match try_prove_ctl_from_tape(program, &cells, step, config.max_states) {
                TapeProofResult::Proved(proof) => return CtlSearchOutcome::Proved(proof),
                TapeProofResult::HitUndefinedRule { pebbles } => {
                    last_hit_undef = Some((step, pebbles));
                }
                TapeProofResult::HitHalt => {
                    last_hit_halt = Some(step);
                }
                TapeProofResult::Inconclusive => {}
            }
        }

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

    if let Some((step, pebbles)) = last_hit_undef {
        CtlSearchOutcome::ClosureHitUndefinedRule { step, pebbles }
    } else if let Some(step) = last_hit_halt {
        CtlSearchOutcome::ClosureHitHalt { step }
    } else {
        CtlSearchOutcome::LimitReached {
            max_steps: config.max_steps,
            max_states: config.max_states,
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
            verbose: false,
        };
        let outcome = run_ctl_search(&prog, &config);
        match outcome {
            CtlSearchOutcome::Proved(proof) => {
                println!("Proof found at step 100: {:?}", proof);
                assert!(proof.num_steps <= 200);
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
}

