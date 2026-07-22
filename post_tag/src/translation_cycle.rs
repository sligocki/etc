use crate::simulate::{HaltCondition, InfiniteReason, Simulator};
use crate::tag_system::TagSystem;

pub fn check_translation_cycle(sys: &TagSystem, max_steps: usize, verbose: bool) -> HaltCondition {
    let mut sim = Simulator::new(sys);
    
    // (step, tape, characters_consumed)
    let mut snapshots: Vec<(usize, Vec<u8>, usize)> = Vec::new();
    let mut next_snapshot_step = 1;
    
    while sim.tape.len() - sim.head_idx >= sys.v && sim.steps < max_steps {
        if sim.steps == next_snapshot_step {
            snapshots.push((sim.steps, sim.tape[sim.head_idx..].to_vec(), sim.head_idx));
            next_snapshot_step *= 2;
        }
        
        let current_tape = &sim.tape[sim.head_idx..];
        
        // Compare with past snapshots
        let mut i = 0;
        while i < snapshots.len() {
            let (saved_step, ref saved_tape, saved_head_idx) = snapshots[i];
            
            if current_tape.len() > saved_tape.len() && current_tape.starts_with(saved_tape) {
                let delta_t = sim.steps - saved_step;
                let c_consumed = delta_t * sys.v;
                
                if c_consumed <= saved_tape.len() {
                    let p = current_tape[saved_tape.len()..].to_vec();
                    let a = current_tape[saved_tape.len() - c_consumed..].to_vec();
                    
                    let mut pa = p.clone();
                    pa.extend(&a);
                    
                    let mut ap = a.clone();
                    ap.extend(&p);
                    
                    if pa == ap {
                        if verbose {
                            println!("Translation Cycle strictly proven (C <= |T| and P*A == A*P). Period = {}", delta_t);
                        }
                        return HaltCondition::Infinite(InfiniteReason::TranslationCycle(delta_t, p), sim.steps);
                    }
                }
            }
            i += 1;
        }
        
        // Take a standard step
        if let Some(cond) = sim.step(verbose) {
            return cond;
        }
    }
    
    if sim.tape.len() - sim.head_idx < sys.v {
        HaltCondition::Halted(sim.steps, sim.max_len)
    } else {
        HaltCondition::Unknown
    }
}
