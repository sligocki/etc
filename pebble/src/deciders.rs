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
}

impl Decider {
    pub const ALL: [Decider; 4] = [
        Decider::EdgeGlider,
        Decider::Cycler,
        Decider::TranslatedCycler,
        Decider::SeparatedComponents,
    ];
}

impl fmt::Display for Decider {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Decider::EdgeGlider => write!(f, "EdgeGlider"),
            Decider::Cycler => write!(f, "Cycler"),
            Decider::TranslatedCycler => write!(f, "TranslatedCycler"),
            Decider::SeparatedComponents => write!(f, "SeparatedComponents"),
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
                        } else {
                            cut.seen.insert(key, (next_l.offset, next_r.offset));
                        }
                        cut.segments = [next_l, next_r];
                        next_cuts.push(cut);
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

/// Run the staged decider pipeline (`EdgeGlider` -> `Cycler`/`TranslatedCycler` -> `SeparatedComponents`)
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
    edge_res
        .or_else(|| decide_cycler(program, max_steps))
        .or_else(|| decide_separated_components(program, max_steps))
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
