use crate::simulate::{HaltCondition, InfiniteReason, Simulator};
use crate::tag_system::TagSystem;

pub fn check_translation_cycle(sys: &TagSystem, max_steps: usize, max_space: usize, verbose: bool) -> HaltCondition {
    let mut sim = Simulator::new(sys);

    // (step, tape, phase)
    let mut snapshots: Vec<(usize, Vec<u8>, usize)> = Vec::new();
    let mut next_snapshot_step = 1;

    struct PendingCandidate {
        t3: usize,
        expected_tape: Vec<u8>,
        delta_t: usize,
        p: Vec<u8>,
    }
    let mut pending: Vec<PendingCandidate> = Vec::new();

    while sim.true_length >= sys.v && sim.steps < max_steps {
        if sim.tape.len() - sim.head_idx > max_space {
            return HaltCondition::Unknown(crate::simulate::UnknownReason::OverSize, sim.steps);
        }
        if sim.steps == next_snapshot_step {
            snapshots.push((sim.steps, sim.tape[sim.head_idx..].to_vec(), sim.true_length % sys.v));
            next_snapshot_step *= 2;
        }

        let current_tape = &sim.tape[sim.head_idx..];
        let current_phase = sim.true_length % sys.v;

        // Compare with past snapshots
        let mut j = 0;
        while j < pending.len() {
            if sim.steps == pending[j].t3 {
                let cand = &pending[j];
                if current_tape.len() >= cand.expected_tape.len()
                    && current_tape.starts_with(&cand.expected_tape)
                {
                    if verbose {
                        println!(
                            "Translation Cycle rigorously proven (3 data points). Period = {}",
                            cand.delta_t
                        );
                    }
                    return HaltCondition::Infinite(
                        InfiniteReason::TranslationCycle(cand.delta_t, cand.p.clone()),
                        sim.steps,
                    );
                }
                pending.swap_remove(j);
                continue;
            }
            j += 1;
        }

        let mut i = 0;
        while i < snapshots.len() {
            let (saved_step, ref saved_tape, saved_phase) = snapshots[i];

            if current_phase == saved_phase && current_tape.len() > saved_tape.len() && current_tape.starts_with(saved_tape) {
                let delta_t = sim.steps - saved_step;
                let c_consumed = delta_t; // Active tape consumes 1 symbol per step

                if c_consumed <= saved_tape.len() {
                    let p = current_tape[saved_tape.len()..].to_vec();
                    let mut expected_tape = current_tape.to_vec();
                    expected_tape.extend(&p);

                    pending.push(PendingCandidate {
                        t3: sim.steps + delta_t,
                        expected_tape,
                        delta_t,
                        p,
                    });
                }
                
                snapshots.swap_remove(i);
                continue;
            }
            i += 1;
        }

        // Take a standard step
        if let Some(cond) = sim.step(verbose, true) {
            return cond;
        }
    }

    if sim.true_length < sys.v {
        HaltCondition::Halted(sim.steps, sim.max_len)
    } else {
        HaltCondition::Unknown(crate::simulate::UnknownReason::OverSteps, sim.steps)
    }
}
