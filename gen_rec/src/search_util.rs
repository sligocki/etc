use crate::grf::Grf;
use crate::io_grl::{self, GrfEntry, Status};
use crate::simulate::{SimOpts, SimResult, SimSteps, simulate_opts};
use rayon::prelude::*;
use std::io::Write;
use std::time::Instant;

/// Tracks the top-K individual halting GRFs by score.
/// Entries are (score, steps, base_steps, raw_expr) sorted ascending; best at end.
pub struct TopK {
    pub k: usize,
    pub entries: Vec<(u64, u64, u64, String)>,
}

impl TopK {
    pub fn new(k: usize) -> Self {
        TopK {
            k,
            entries: Vec::new(),
        }
    }

    pub fn best_score(&self) -> Option<u64> {
        self.entries.last().map(|(s, _, _, _)| s.clone())
    }

    pub fn insert(&mut self, score: u64, steps: u64, base_steps: u64, expr: String) {
        if self.entries.len() >= self.k && score < self.entries[0].0 {
            return;
        }
        let pos = self.entries.partition_point(|(s, _, _, _)| *s < score);
        self.entries.insert(pos, (score, steps, base_steps, expr));
        if self.entries.len() > self.k {
            self.entries.remove(0);
        }
    }

    pub fn merge_from(&mut self, other: TopK) {
        for (score, steps, base_steps, expr) in other.entries {
            self.insert(score, steps, base_steps, expr);
        }
    }

    pub fn iter_desc(&self) -> impl Iterator<Item = &(u64, u64, u64, String)> {
        self.entries.iter().rev()
    }
}

pub struct Accumulator {
    pub top_k: TopK,
    pub total: usize,
    pub holdouts: usize,
    pub diverged: usize,
    pub total_steps: u64,
    pub max_steps_single: u64,
    pub sim_nanos: u64,
}

impl Accumulator {
    pub fn new(k: usize) -> Self {
        Accumulator {
            top_k: TopK::new(k),
            total: 0,
            holdouts: 0,
            diverged: 0,
            total_steps: 0,
            max_steps_single: 0,
            sim_nanos: 0,
        }
    }
}

pub struct BatchResult {
    pub top_k: TopK,
    pub holdouts: Vec<(u64, String, Option<&'static str>)>,
    pub diverged: usize,
    pub total_steps: u64,
    pub max_steps_single: u64,
}

pub fn process_batch(batch: &[Grf], max_steps: u64, k: usize) -> BatchResult {
    let outcomes: Vec<(SimResult, SimSteps)> = batch
        .par_iter()
        .map(|grf| {
            simulate_opts(
                grf,
                &[],
                if max_steps == 0 { None } else { Some(max_steps) },
                SimOpts::default(),
            )
        })
        .collect();

    let mut top_k = TopK::new(k);
    let mut holdouts = Vec::new();
    let mut diverged = 0usize;
    let mut total_steps: u64 = 0;
    let mut max_steps_single: u64 = 0;

    for (idx, (result, sim_steps)) in outcomes.into_iter().enumerate() {
        let steps = sim_steps.sim;
        total_steps += steps;
        match result {
            SimResult::OutOfSteps => {
                holdouts.push((steps, batch[idx].to_string(), Some("OutOfSteps")))
            }
            SimResult::Diverge => diverged += 1,
            SimResult::Value(v) => {
                max_steps_single = max_steps_single.max(steps);
                top_k.insert(v, steps, sim_steps.base_approx, batch[idx].to_string())
            }
            SimResult::ArityMismatch => panic!("arity mismatch in bb_search for {}", batch[idx]),
            SimResult::ValueOverflow => {
                holdouts.push((steps, batch[idx].to_string(), Some("Overflow")))
            }
        }
    }
    BatchResult {
        top_k,
        holdouts,
        diverged,
        total_steps,
        max_steps_single,
    }
}

pub fn flush_batch<W: Write>(
    batch: &mut Vec<Grf>,
    acc: &mut Accumulator,
    holdout_w: &mut W,
    max_steps: u64,
    k: usize,
) {
    if batch.is_empty() {
        return;
    }
    let t0 = Instant::now();
    let br = process_batch(batch, max_steps, k);
    acc.sim_nanos += t0.elapsed().as_nanos() as u64;
    acc.holdouts += br.holdouts.len();
    acc.diverged += br.diverged;
    acc.total_steps += br.total_steps;
    acc.max_steps_single = acc.max_steps_single.max(br.max_steps_single);
    for (steps, expr, reason) in br.holdouts {
        io_grl::write_grf_entry(
            holdout_w,
            &GrfEntry {
                expr,
                status: Some(Status::Unknown),
                steps: Some(steps),
                base_steps: None,
                score: None,
                unknown_reason: reason.map(|r| r.to_string()),
            },
        )
        .unwrap();
    }
    acc.top_k.merge_from(br.top_k);
    batch.clear();
}

pub fn fmt_si(n: u64) -> String {
    if n < 1_000 {
        format!("{}", n)
    } else {
        fmt_si_f64(n as f64)
    }
}

pub fn fmt_si_f64(n: f64) -> String {
    if n < 1_000.0 {
        format!("{:.1}", n)
    } else if n < 1_000_000.0 {
        format!("{:.1}k", n / 1_000.0)
    } else if n < 1_000_000_000.0 {
        format!("{:.1}M", n / 1_000_000.0)
    } else if n < 1_000_000_000_000.0 {
        format!("{:.1}B", n / 1_000_000_000.0)
    } else {
        format!("{:.1}T", n / 1_000_000_000_000.0)
    }
}
