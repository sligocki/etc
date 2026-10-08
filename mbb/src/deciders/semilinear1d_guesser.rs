use crate::program::{Program, Target};
use crate::macro_program::abstract_program;
use crate::deciders::semilinear1d::{Ray, verify_semilinear1d_set};
use crate::deciders::polyhedral_guesser::record_history;

pub fn decide_semilinear1d(prog: &Program, step_limit: u64, verbose: bool) -> crate::deciders::DeciderResult {
    let macros = abstract_program(prog);
    let num_regs = prog.num_regs();

    for (state_idx, m) in macros.iter().enumerate() {
        // Only try to find periods at Dec instructions (start of loops usually)
        if !matches!(m, crate::macro_program::MacroInst::Dec { .. }) {
            continue;
        }

        let history = record_history(prog, state_idx, step_limit);
        if history.len() < 5 {
            continue;
        }

        // Try to find a period between recent history items (limit search to last 50 to avoid hanging)
        let n = history.len();
        let start_idx = n.saturating_sub(50);
        for i in (start_idx..n-1).rev() {
            let v_old = &history[i];
            let v_new = &history[n-1];
            
            // Check if v_new >= v_old
            let mut valid_period = true;
            let mut period = vec![0; num_regs];
            for j in 0..num_regs {
                if v_new[j] < v_old[j] {
                    valid_period = false;
                    break;
                }
                period[j] = (v_new[j] - v_old[j]) as u32;
            }

            if valid_period {
                // To avoid trivial 0-period loops
                if period.iter().all(|&p| p == 0) {
                    continue;
                }

                let base = v_old.iter().map(|&x| x as u32).collect();
                let seed_ray = Ray { base, period };

                if verbose {
                    println!("Semilinear1D: Trying State {} with Ray {:?}", (b'A' + state_idx as u8) as char, seed_ray);
                }

                if verify_semilinear1d_set(&macros, Target::Inst(state_idx), seed_ray.clone(), num_regs, verbose) {
                    let state_char = (b'A' + state_idx as u8) as char;
                    return crate::deciders::DeciderResult::Infinite(crate::deciders::InfiniteReason::Semilinear1D {
                        state: state_char,
                        base: seed_ray.base,
                        period: seed_ray.period,
                    });
                }
            }
        }
    }

    crate::deciders::DeciderResult::Unknown
}
