use crate::deciders::congruence::{verify_congruence_set, Val, CAP};
use crate::deciders::polyhedral_guesser::record_history;
use crate::macro_program::abstract_program;
use crate::program::{Program, Target};

pub fn decide_congruence(
    prog: &Program,
    step_limit: u64,
    verbose: bool,
) -> crate::deciders::DeciderResult {
    let macros = abstract_program(prog);
    let num_regs = prog.num_regs();

    for (state_idx, m) in macros.iter().enumerate() {
        if !matches!(m, crate::macro_program::MacroInst::Dec { .. }) {
            continue;
        }

        let history = record_history(prog, state_idx, step_limit);
        if history.len() < 5 {
            continue;
        }

        let mut moduli = vec![0; num_regs];
        let start_idx = history.len().saturating_sub(50);

        for r in 0..num_regs {
            let mut gcd_val = 0;
            for j in start_idx..history.len() - 1 {
                let diff = history[j + 1][r].abs_diff(history[j][r]) as u32;
                if diff > 0 {
                    gcd_val = gcd(gcd_val, diff);
                }
            }
            if gcd_val == 0 {
                gcd_val = 1;
            }
            moduli[r] = gcd_val;
        }

        let seed = &history[start_idx];
        let mut seed_vals = Vec::new();
        for r in 0..num_regs {
            let v = seed[r] as u32;
            if v < CAP {
                seed_vals.push(Val::Exact(v));
            } else {
                seed_vals.push(Val::Large(v % moduli[r]));
            }
        }

        if verbose {
            println!(
                "Congruence: Trying State {} with Moduli {:?}, Seed {:?}",
                (b'A' + state_idx as u8) as char,
                moduli,
                seed_vals
            );
        }

        if verify_congruence_set(
            &macros,
            Target::Inst(state_idx),
            seed_vals.clone(),
            &moduli,
            verbose,
        ) {
            let state_char = (b'A' + state_idx as u8) as char;
            return crate::deciders::DeciderResult::Infinite(
                crate::deciders::InfiniteReason::Congruence {
                    state: state_char,
                    moduli,
                    seed: seed_vals,
                },
            );
        }
    }

    crate::deciders::DeciderResult::Unknown
}

fn gcd(mut a: u32, mut b: u32) -> u32 {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}
