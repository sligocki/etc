use crate::program::Program;
use crate::simulation::{Simulator, StepResult};
use std::collections::HashMap;
use std::fmt;
use std::str::FromStr;

/// Non-halting decider classification for Pebble Automata.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Decider {
    /// Leftmost non-zero cell `k` has `L(k) == k`, or rightmost non-zero cell `k` has `R(k) == k`.
    /// By the light-cone invariant (`c = 1` cell/step), this edge particle escapes to infinity.
    EdgeGlider,
    /// Exact tape configuration `(offset, cells)` repeats with period >= 2 (`dx == 0`).
    Cycler,
    /// Normalized tape shape `cells` repeats at a shifted position (`dx != 0`).
    TranslatedCycler,
    /// Tape partitions into 2 causally isolated segments (separated by >= 2 zeros at all steps)
    /// whose shapes both repeat with non-shrinking separation (`dx_left <= dx_right`).
    SeparatedComponents,
    /// A period-1 shuttle bounces back and forth between two stationary walls (`W_L` and `W_R`)
    /// with strictly growing total gap (`g_2 > g_1`), while each wall remains causally isolated
    /// during the opposite bounce.
    Bouncer,
    /// Closed Tape Language (CTL) regular-set proof: a set of symbolic configurations with
    /// modular zero-star gaps `0^r (0^m)*` is entered during simulation, closed under exact
    /// 1-step symbolic transitions, and contains no halting configurations.
    Ctl,
}

impl Decider {
    pub const ALL: [Decider; 6] = [
        Decider::EdgeGlider,
        Decider::Cycler,
        Decider::TranslatedCycler,
        Decider::SeparatedComponents,
        Decider::Bouncer,
        Decider::Ctl,
    ];
}

impl fmt::Display for Decider {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Decider::EdgeGlider => write!(f, "EdgeGlider"),
            Decider::Cycler => write!(f, "Cycler"),
            Decider::TranslatedCycler => write!(f, "TranslatedCycler"),
            Decider::SeparatedComponents => write!(f, "SeparatedComponents"),
            Decider::Bouncer => write!(f, "Bouncer"),
            Decider::Ctl => write!(f, "CTL"),
        }
    }
}

impl FromStr for Decider {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.trim().to_ascii_lowercase().as_str() {
            "edgeglider" | "edge_glider" => Ok(Decider::EdgeGlider),
            "cycler" => Ok(Decider::Cycler),
            "translatedcycler" | "translated_cycler" => Ok(Decider::TranslatedCycler),
            "separatedcomponents" | "separated_components" => Ok(Decider::SeparatedComponents),
            "bouncer" => Ok(Decider::Bouncer),
            "ctl" => Ok(Decider::Ctl),
            other => Err(format!("unknown decider '{other}'")),
        }
    }
}

/// Fast $O(1)$ check on a tape slice `cells` for an escaping light-cone edge glider.
///
/// Since `L(first) == first` and `R(last) == last` are absorbing invariants (once true at step `t`,
/// they remain true at all steps `>= t`), checking the final tape at `max_steps` is equivalent
/// to checking every intermediate step in `0..=max_steps`.
#[inline]
pub fn check_edge_glider_tape(program: &Program, cells: &[u8]) -> Option<Decider> {
    let &first = cells.first()?;
    if first > 0 {
        if let Some(r) = program.rule(first) {
            if r.left == first {
                return Some(Decider::EdgeGlider);
            }
        }
    }
    let &last = cells.last()?;
    if last > 0 {
        if let Some(r) = program.rule(last) {
            if r.right == last {
                return Some(Decider::EdgeGlider);
            }
        }
    }
    None
}

/// Decider 1: Simulate `program` up to `max_steps` and check for an escaping `EdgeGlider`.
pub fn decide_edge_glider(program: &Program, max_steps: u64) -> Option<Decider> {
    let mut sim = Simulator::new(program.size());
    for _ in 0..=max_steps {
        if let Some(d) = check_edge_glider_tape(program, sim.cells()) {
            return Some(d);
        }
        if sim.step(program) != StepResult::Stepped {
            return None;
        }
    }
    None
}

/// Decider 2: Simulate `program` up to `max_steps` and detect `Cycler` (`dx == 0`)
/// or `TranslatedCycler` (`dx != 0`).
pub fn decide_cycler(program: &Program, max_steps: u64) -> Option<Decider> {
    let mut sim = Simulator::new(program.size());
    let mut seen_shapes: HashMap<Vec<u8>, isize> = HashMap::new();

    for _ in 0..=max_steps {
        let cells = sim.cells();
        if let Some(&prev_offset) = seen_shapes.get(cells) {
            // Confirm the state is not a stationary fixed point (halted) before reporting a cycle.
            let prev_off = sim.offset();
            if sim.step(program) != StepResult::Stepped {
                return None;
            }
            if prev_off == prev_offset {
                return Some(Decider::Cycler);
            } else {
                return Some(Decider::TranslatedCycler);
            }
        }
        seen_shapes.insert(cells.to_vec(), sim.offset());

        if sim.step(program) != StepResult::Stepped {
            return None;
        }
    }
    None
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Segment {
    offset: isize,
    cells: Vec<u8>,
}

/// Advance a single isolated segment by 1 step using `program`.
fn step_segment(seg: &Segment, program: &Program) -> Option<Segment> {
    let mut next = vec![0u8; seg.cells.len() + 2];
    for (i, &k) in seg.cells.iter().enumerate() {
        if k == 0 {
            continue;
        }
        let rule = program.rule(k)?;
        next[i] += rule.left;
        next[i + 1] += rule.stay;
        next[i + 2] += rule.right;
    }
    let first_nz = next.iter().position(|&v| v > 0)?;
    let last_nz = next.iter().rposition(|&v| v > 0)?;
    Some(Segment {
        offset: seg.offset - 1 + first_nz as isize,
        cells: next[first_nz..=last_nz].to_vec(),
    })
}

/// Extract all 2-segment causal cuts `[left_seg, right_seg]` separated by at least 2 zeros.
fn extract_bipartitions(offset: isize, cells: &[u8]) -> Vec<[Segment; 2]> {
    let mut nz_indices = Vec::new();
    for (i, &c) in cells.iter().enumerate() {
        if c > 0 {
            nz_indices.push(i);
        }
    }
    let mut cuts = Vec::new();
    for w in nz_indices.windows(2) {
        let left_end_idx = w[0];
        let right_start_idx = w[1];
        let gap = right_start_idx - left_end_idx - 1;
        if gap >= 2 {
            let left_seg = Segment {
                offset,
                cells: cells[0..=left_end_idx].to_vec(),
            };
            let right_seg = Segment {
                offset: offset + right_start_idx as isize,
                cells: cells[right_start_idx..].to_vec(),
            };
            cuts.push([left_seg, right_seg]);
        }
    }
    cuts
}

struct ActiveCut {
    segments: [Segment; 2],
    seen: HashMap<(Vec<u8>, Vec<u8>), (isize, isize)>,
}

/// Decider 3: Simulate `program` up to `max_steps` and detect causally independent
/// `SeparatedComponents` whose shapes repeat with non-shrinking separation (`dx_left <= dx_right`).
pub fn decide_separated_components(program: &Program, max_steps: u64) -> Option<Decider> {
    let mut sim = Simulator::new(program.size());
    let mut active_cuts: Vec<ActiveCut> = Vec::new();

    for _ in 0..=max_steps {
        let cells = sim.cells();
        if !cells.is_empty() {
            let mut next_cuts = Vec::with_capacity(active_cuts.len());
            for mut cut in active_cuts {
                if let (Some(next_l), Some(next_r)) = (
                    step_segment(&cut.segments[0], program),
                    step_segment(&cut.segments[1], program),
                ) {
                    let left_end = next_l.offset + next_l.cells.len() as isize - 1;
                    let right_start = next_r.offset;
                    if right_start - left_end - 1 >= 2 {
                        let key = (next_l.cells.clone(), next_r.cells.clone());
                        if let Some(&(prev_l_off, prev_r_off)) = cut.seen.get(&key) {
                            let dx_l = next_l.offset - prev_l_off;
                            let dx_r = next_r.offset - prev_r_off;
                            if dx_l <= dx_r {
                                // Ensure the full tape is not already halted at this step
                                if sim.step(program) == StepResult::Stepped {
                                    return Some(Decider::SeparatedComponents);
                                } else {
                                    return None;
                                }
                            }
                        } else if cut.seen.len() < 128 {
                            cut.seen.insert(key, (next_l.offset, next_r.offset));
                            cut.segments = [next_l, next_r];
                            next_cuts.push(cut);
                        }
                    }
                }
            }

            for pair in extract_bipartitions(sim.offset(), cells) {
                if !next_cuts.iter().any(|c| c.segments == pair) {
                    let mut seen = HashMap::new();
                    seen.insert(
                        (pair[0].cells.clone(), pair[1].cells.clone()),
                        (pair[0].offset, pair[1].offset),
                    );
                    next_cuts.push(ActiveCut {
                        segments: pair,
                        seen,
                    });
                }
            }
            active_cuts = next_cuts;
        }

        if sim.step(program) != StepResult::Stepped {
            return None;
        }
    }
    None
}

fn is_stationary_slice(program: &Program, slice: &[u8]) -> bool {
    slice.iter().all(|&k| {
        if k == 0 {
            true
        } else if let Some(r) = program.rule(k) {
            r.left == 0 && r.stay == k && r.right == 0
        } else {
            false
        }
    })
}

fn is_right_glider_slice(program: &Program, slice: &[u8]) -> bool {
    slice.iter().all(|&k| {
        if k == 0 {
            true
        } else if let Some(r) = program.rule(k) {
            r.left == 0 && r.stay == 0 && r.right == k
        } else {
            false
        }
    })
}

fn is_left_glider_slice(program: &Program, slice: &[u8]) -> bool {
    slice.iter().all(|&k| {
        if k == 0 {
            true
        } else if let Some(r) = program.rule(k) {
            r.left == k && r.stay == 0 && r.right == 0
        } else {
            false
        }
    })
}

#[derive(Debug, Clone)]
struct Transit {
    w_l: Vec<u8>,
    shuttle: Vec<u8>,
    w_r: Vec<u8>,
    x_l: isize,
    x_r: isize,
    total_gap: usize,
}

fn extract_transits(program: &Program, offset: isize, cells: &[u8]) -> (Vec<Transit>, Vec<Transit>) {
    let mut islands: Vec<(usize, usize)> = Vec::new();
    let mut i = 0;
    while i < cells.len() {
        if cells[i] > 0 {
            let start = i;
            while i + 1 < cells.len() && cells[i + 1] > 0 {
                i += 1;
            }
            islands.push((start, i));
        }
        i += 1;
    }

    let mut right_transits = Vec::new();
    let mut left_transits = Vec::new();
    let m = islands.len();
    if m < 3 {
        return (right_transits, left_transits);
    }

    for left_split in 1..(m - 1) {
        let w_l = &cells[islands[0].0..=islands[left_split - 1].1];
        if !is_stationary_slice(program, w_l) {
            continue;
        }
        for right_split in left_split..(m - 1) {
            let w_r = &cells[islands[right_split + 1].0..=islands[m - 1].1];
            if !is_stationary_slice(program, w_r) {
                continue;
            }
            let shuttle = &cells[islands[left_split].0..=islands[right_split].1];
            let is_right = is_right_glider_slice(program, shuttle);
            let is_left = is_left_glider_slice(program, shuttle);
            if !is_right && !is_left {
                continue;
            }

            let gap_a = islands[left_split].0 - islands[left_split - 1].1 - 1;
            let gap_b = islands[right_split + 1].0 - islands[right_split].1 - 1;
            let tr = Transit {
                w_l: w_l.to_vec(),
                shuttle: shuttle.to_vec(),
                w_r: w_r.to_vec(),
                x_l: offset + islands[0].0 as isize,
                x_r: offset + islands[right_split + 1].0 as isize,
                total_gap: gap_a + gap_b,
            };
            if is_right {
                right_transits.push(tr.clone());
            }
            if is_left {
                left_transits.push(tr);
            }
        }
    }

    (right_transits, left_transits)
}

#[inline]
fn left_wall_isolated(offset: isize, cells: &[u8], w_l: &[u8], x_l: isize) -> bool {
    offset == x_l
        && cells.len() > w_l.len()
        && cells.starts_with(w_l)
        && cells[w_l.len()] == 0
}

#[inline]
fn right_wall_isolated(offset: isize, cells: &[u8], w_r: &[u8], x_r: isize) -> bool {
    offset + (cells.len() as isize) == x_r + (w_r.len() as isize)
        && cells.len() > w_r.len()
        && cells.ends_with(w_r)
        && cells[cells.len() - w_r.len() - 1] == 0
}

#[derive(Debug, Clone)]
struct BounceCandidate {
    started_right: bool,
    w_l: Vec<u8>,
    shuttle_1: Vec<u8>,
    w_r: Vec<u8>,
    fixed_wall_offset: isize,
    g_1: usize,
}

/// Decider 4: Simulate `program` up to `max_steps` and detect a Level-1 `Bouncer`
/// (a period-1 shuttle bouncing between two stationary walls `W_L` and `W_R` with a growing gap
/// while each wall stays causally isolated during the opposite bounce).
pub fn decide_bouncer(program: &Program, max_steps: u64) -> Option<Decider> {
    let mut sim = Simulator::new(program.size());
    let mut waiting_opposite: Vec<BounceCandidate> = Vec::new();
    let mut waiting_return: Vec<BounceCandidate> = Vec::new();

    for _ in 0..=max_steps {
        let offset = sim.offset();
        let cells = sim.cells();
        if !cells.is_empty() {
            let (right_transits, left_transits) = extract_transits(program, offset, cells);

            // 1. Update candidates waiting for the return bounce (t_L -> t_2)
            let mut next_return = Vec::with_capacity(waiting_return.len());
            for cand in waiting_return {
                let intact = if cand.started_right {
                    right_wall_isolated(offset, cells, &cand.w_r, cand.fixed_wall_offset)
                } else {
                    left_wall_isolated(offset, cells, &cand.w_l, cand.fixed_wall_offset)
                };
                if !intact {
                    continue;
                }

                let target_list = if cand.started_right {
                    &right_transits
                } else {
                    &left_transits
                };
                for tr in target_list {
                    let wall_matches = if cand.started_right {
                        tr.x_r == cand.fixed_wall_offset
                    } else {
                        tr.x_l == cand.fixed_wall_offset
                    };
                    if wall_matches
                        && tr.w_l == cand.w_l
                        && tr.shuttle == cand.shuttle_1
                        && tr.w_r == cand.w_r
                        && tr.total_gap > cand.g_1
                    {
                        return Some(Decider::Bouncer);
                    }
                }
                next_return.push(cand);
            }

            // 2. Update candidates waiting for the first (opposite) bounce (t_1 -> t_L)
            let mut next_opposite = Vec::with_capacity(waiting_opposite.len());
            for cand in waiting_opposite {
                let intact = if cand.started_right {
                    left_wall_isolated(offset, cells, &cand.w_l, cand.fixed_wall_offset)
                } else {
                    right_wall_isolated(offset, cells, &cand.w_r, cand.fixed_wall_offset)
                };
                if !intact {
                    continue;
                }

                let opp_list = if cand.started_right {
                    &left_transits
                } else {
                    &right_transits
                };
                for tr in opp_list {
                    let wall_matches = if cand.started_right {
                        tr.x_l == cand.fixed_wall_offset
                    } else {
                        tr.x_r == cand.fixed_wall_offset
                    };
                    if wall_matches && tr.w_l == cand.w_l && tr.w_r == cand.w_r {
                        let new_fixed = if cand.started_right { tr.x_r } else { tr.x_l };
                        let already_tracked = next_return.iter().any(|r| {
                            r.started_right == cand.started_right
                                && r.fixed_wall_offset == new_fixed
                                && r.w_l == cand.w_l
                                && r.shuttle_1 == cand.shuttle_1
                                && r.w_r == cand.w_r
                                && r.g_1 <= cand.g_1
                        });
                        if !already_tracked {
                            next_return.push(BounceCandidate {
                                started_right: cand.started_right,
                                w_l: cand.w_l.clone(),
                                shuttle_1: cand.shuttle_1.clone(),
                                w_r: cand.w_r.clone(),
                                fixed_wall_offset: new_fixed,
                                g_1: cand.g_1,
                            });
                        }
                    }
                }
                next_opposite.push(cand);
            }

            // 3. Register new initial transits at step t
            for (started_right, list) in [(true, &right_transits), (false, &left_transits)] {
                for tr in list {
                    let fixed = if started_right { tr.x_l } else { tr.x_r };
                    let already_tracked = next_opposite.iter().any(|c| {
                        c.started_right == started_right
                            && c.fixed_wall_offset == fixed
                            && c.w_l == tr.w_l
                            && c.shuttle_1 == tr.shuttle
                            && c.w_r == tr.w_r
                            && c.g_1 <= tr.total_gap
                    });
                    if !already_tracked {
                        next_opposite.push(BounceCandidate {
                            started_right,
                            w_l: tr.w_l.clone(),
                            shuttle_1: tr.shuttle.clone(),
                            w_r: tr.w_r.clone(),
                            fixed_wall_offset: fixed,
                            g_1: tr.total_gap,
                        });
                    }
                }
            }

            waiting_opposite = next_opposite;
            waiting_return = next_return;
        }

        if sim.step(program) != StepResult::Stepped {
            return None;
        }
    }
    None
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct ZeroGap {
    rem: usize,
    modulus: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct CtlState {
    modulus: usize,
    blocks: Vec<Vec<u8>>,
    gaps: Vec<ZeroGap>,
}

impl CtlState {
    fn is_subset_of(&self, other: &CtlState) -> bool {
        if self.modulus != other.modulus
            || self.blocks != other.blocks
            || self.gaps.len() != other.gaps.len()
        {
            return false;
        }
        self.gaps.iter().zip(other.gaps.iter()).all(|(g1, g2)| {
            g1.rem >= g2.rem && g1.modulus % g2.modulus == 0 && (g1.rem - g2.rem) % g2.modulus == 0
        })
    }
}

#[inline]
fn widen_rem(rem: usize, floor: usize, modulus: usize) -> usize {
    if rem >= floor {
        floor + (rem - floor) % modulus
    } else {
        rem
    }
}

fn merge_blocks_with_zeros(b1: &[u8], zeros: usize, b2: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(b1.len() + zeros + b2.len());
    out.extend_from_slice(b1);
    out.resize(b1.len() + zeros, 0);
    out.extend_from_slice(b2);
    out
}

fn split_slice_by_threshold(slice: &[u8], split_threshold: usize) -> (Vec<Vec<u8>>, Vec<usize>) {
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

const MAX_CTL_GAPS: usize = 4;

fn unroll_ctl_state(state: &CtlState) -> Result<Vec<CtlState>, ()> {
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

fn step_isolated_block(block: &[u8], program: &Program) -> Result<(Vec<u8>, isize, isize), ()> {
    let mut next = vec![0u8; block.len() + 2];
    for (i, &k) in block.iter().enumerate() {
        if k == 0 {
            continue;
        }
        let rule = program.rule(k).ok_or(())?;
        next[i] += rule.left;
        next[i + 1] += rule.stay;
        next[i + 2] += rule.right;
    }
    let first_nz = next.iter().position(|&v| v > 0).ok_or(())?;
    let last_nz = next.iter().rposition(|&v| v > 0).ok_or(())?;
    let out = next[first_nz..=last_nz].to_vec();
    if out.len() > 28 {
        return Err(());
    }
    let delta_left = (first_nz as isize) - 1;
    let delta_right = (last_nz as isize) - (block.len() as isize);
    Ok((out, delta_left, delta_right))
}

fn step_ctl_pre_state(
    pre: &CtlState,
    program: &Program,
    split_threshold: usize,
    floor: usize,
) -> Result<CtlState, ()> {
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
        return Err(());
    }

    let mut inter_gaps = Vec::with_capacity(pre.gaps.len());
    for (i, g) in pre.gaps.iter().enumerate() {
        let dg = delta_lefts[i + 1] - delta_rights[i];
        let next_rem = (g.rem as isize) + dg;
        if next_rem < 0 {
            return Err(());
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

    if new_gaps.is_empty() || new_gaps.len() > MAX_CTL_GAPS {
        return Err(());
    }

    if new_gaps.len() >= 2 {
        for g in &mut new_gaps {
            g.rem = widen_rem(g.rem, floor, g.modulus);
        }
    } else if new_gaps[0].rem > 36 {
        return Err(());
    }

    Ok(CtlState {
        modulus: pre.modulus,
        blocks: new_blocks,
        gaps: new_gaps,
    })
}

fn verify_ctl_closure(
    seed: CtlState,
    program: &Program,
    split_threshold: usize,
    floor: usize,
    max_states: usize,
) -> bool {
    let mut language: Vec<CtlState> = vec![seed.clone()];
    let mut queue: std::collections::VecDeque<CtlState> = std::collections::VecDeque::new();
    queue.push_back(seed);

    while let Some(curr) = queue.pop_front() {
        let Ok(pre_branches) = unroll_ctl_state(&curr) else {
            return false;
        };
        for pre in pre_branches {
            let Ok(next_state) = step_ctl_pre_state(&pre, program, split_threshold, floor) else {
                return false;
            };
            if !language.iter().any(|existing| next_state.is_subset_of(existing)) {
                if language.len() >= max_states {
                    return false;
                }
                language.push(next_state.clone());
                queue.push_back(next_state);
            }
        }
    }
    true
}

fn try_prove_ctl_from_tape(program: &Program, cells: &[u8]) -> bool {
    for split_threshold in 2..=6 {
        let (blocks, raw_gaps) = split_slice_by_threshold(cells, split_threshold);
        if raw_gaps.len() < 2 || raw_gaps.len() > MAX_CTL_GAPS {
            continue;
        }
        let floor = 2 * split_threshold + 2;
        for modulus in [1, 2, 3, 4, 6] {
            let gaps = raw_gaps
                .iter()
                .map(|&g| ZeroGap {
                    rem: widen_rem(g, floor, modulus),
                    modulus,
                })
                .collect();
            let seed = CtlState {
                modulus,
                blocks: blocks.clone(),
                gaps,
            };
            if verify_ctl_closure(seed, program, split_threshold, floor, 256) {
                return true;
            }
        }
    }
    false
}

/// Decider 5: Closed Tape Language (CTL) regular-set non-halting prover.
///
/// Samples configurations across `(max_steps / 3)..=max_steps`, generalizes the two main
/// zero-gaps into modular star expressions `0^r (0^m)*`, and verifies via exact symbolic
/// forward reachability that the language is closed under `step` and free of halting configurations.
pub fn decide_ctl(program: &Program, max_steps: u64) -> Option<Decider> {
    let mut sim = Simulator::new(program.size());
    let sample_start = (max_steps / 3).max(max_steps.saturating_sub(68));

    for step in 0..=max_steps {
        if step >= sample_start && (max_steps - step) % 4 == 0 {
            if try_prove_ctl_from_tape(program, sim.cells()) {
                return Some(Decider::Ctl);
            }
        }
        if sim.step(program) != StepResult::Stepped {
            return None;
        }
    }
    None
}

/// Run the staged decider pipeline
/// (`EdgeGlider` -> `Cycler`/`TranslatedCycler` -> `SeparatedComponents` -> `Bouncer` -> `Ctl`)
/// on a holdout program.
///
/// If `final_cells` from the simulator is provided, `EdgeGlider` is checked in $O(1)$ time on `final_cells`
/// without re-simulating; otherwise `decide_edge_glider` is run.
pub fn run_decider_pipeline(
    program: &Program,
    final_cells: Option<&[u8]>,
    max_steps: u64,
) -> Option<Decider> {
    let edge_res = match final_cells {
        Some(cells) => check_edge_glider_tape(program, cells),
        None => decide_edge_glider(program, max_steps),
    };
    let res = edge_res
        .or_else(|| decide_cycler(program, max_steps))
        .or_else(|| decide_separated_components(program, max_steps))
        .or_else(|| decide_bouncer(program, max_steps))
        .or_else(|| decide_ctl(program, max_steps));

    if res.is_none() && (50..200).contains(&max_steps) {
        let ext_steps = 200;
        return decide_edge_glider(program, ext_steps)
            .or_else(|| decide_cycler(program, ext_steps))
            .or_else(|| decide_separated_components(program, ext_steps))
            .or_else(|| decide_bouncer(program, ext_steps))
            .or_else(|| decide_ctl(program, ext_steps));
    }
    res
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::simulation::{simulate, SimOutcome};

    #[test]
    fn test_edge_glider_decider() {
        let p1: Program = "01_01".parse().unwrap();
        assert_eq!(decide_edge_glider(&p1, 10), Some(Decider::EdgeGlider));

        let p2: Program = "10_01_02".parse().unwrap();
        assert_eq!(decide_edge_glider(&p2, 10), Some(Decider::EdgeGlider));
    }

    #[test]
    fn test_cycler_and_translated_cycler_decider() {
        // Period-2 stationary cycler: 3 <-> 12
        let cycler: Program = "00_20_02".parse().unwrap();
        assert_eq!(decide_cycler(&cycler, 10), Some(Decider::Cycler));

        // Period-2 translated cycler (speed 1/2): 3 -> 21 -> .3
        let trans_cycler: Program = "00_02_01".parse().unwrap();
        assert_eq!(
            decide_cycler(&trans_cycler, 10),
            Some(Decider::TranslatedCycler)
        );
    }

    #[test]
    fn test_separated_components_decider() {
        // Left component stays `1`, right component `3 -> 21 -> .3` translates right at speed 1/2
        let sep1: Program = "00_02_01_13_04_01".parse().unwrap();
        assert_eq!(
            decide_separated_components(&sep1, 30),
            Some(Decider::SeparatedComponents)
        );

        // Left component stays `1`, right component `5` undergoes an 8-step internal split/merge cycle with dx = +2
        let sep2: Program = "00_11_30_04_22_01".parse().unwrap();
        assert_eq!(
            decide_separated_components(&sep2, 30),
            Some(Decider::SeparatedComponents)
        );
    }

    #[test]
    fn test_bouncer_decider() {
        let n6_bouncers = [
            "00_02_01_40_12_01",
            "00_20_10_04_21_05",
            "00_20_10_04_21_10",
            "00_20_10_04_11_11",
            "00_20_10_04_21_11",
            "00_02_01_40_11_11",
            "00_02_01_40_12_11",
            "00_02_01_40_11_13",
            "00_02_01_40_12_13",
            "00_20_10_04_11_15",
            "00_20_10_04_21_15",
            "00_20_10_04_11_31",
            "00_20_10_04_21_31",
            "00_02_01_40_12_50",
            "00_02_01_40_11_51",
            "00_02_01_40_12_51",
        ];
        for code in n6_bouncers {
            let p: Program = code.parse().unwrap();
            assert_eq!(
                decide_bouncer(&p, 50),
                Some(Decider::Bouncer),
                "expected n=6 bouncer {code} to be decided"
            );
        }

        // n=7 bouncer holdouts
        let n7_bouncers = [
            "00_02_03_01_50_13_01",
            "00_20_30_10_05_31_42",
            "00_02_03_01_50_13_61",
        ];
        for code in n7_bouncers {
            let p: Program = code.parse().unwrap();
            assert_eq!(
                decide_bouncer(&p, 50),
                Some(Decider::Bouncer),
                "expected n=7 bouncer {code} to be decided"
            );
        }
    }

    #[test]
    fn test_ctl_decider() {
        let ctl_programs = [
            // User's period-3 right-wall bouncer with (00)* right gap
            ("00_02_21_40_12_50_16_01", 60),
            // Coupled-parity period-3 walls with internal zeros
            ("10_00_21_13_10_05_--_61", 60),
            // Two-wave shuttle `2 000 2` (3 internal zeros)
            ("00_20_02_04_22_24_61_11", 150),
            // Two-wave shuttle `2 00000 2` (5 internal zeros)
            ("00_20_02_04_23_50_61_35", 160),
            // Multi-glider n=9 bouncer emitting both slow (`3|12`) and fast (`1`) gliders
            ("01_00_02_40_20_21_22_17_34", 100),
            // Escaping left glider + right bouncer (3 gaps)
            ("00_20_10_04_11_33_03_01_01", 100),
        ];
        for (code, steps) in ctl_programs {
            let p: Program = code.parse().unwrap();
            assert_eq!(
                decide_ctl(&p, steps),
                Some(Decider::Ctl),
                "expected program {code} to be decided by CTL"
            );
        }
    }

    #[test]
    fn test_soundness_on_wiki_champions() {
        let champions = [
            "00",
            "00_01",
            "00_01_20",
            "00_01_20_03",
            "00_11_03_21_04",
            "00_11_03_21_40_15",
            "00_11_03_21_10_33_61",
            "00_11_03_21_50_30_24_70",
            "00_02_01_40_14_12_00_52_81",
        ];

        for code in champions {
            let prog: Program = code.parse().unwrap();
            let outcome = simulate(&prog, 70_000);
            assert!(matches!(outcome, SimOutcome::Halted { .. }));
            assert_eq!(
                run_decider_pipeline(&prog, None, 200),
                None,
                "champion {code} must not be decided as non-halting"
            );
        }
    }
}
