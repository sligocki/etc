use crate::macro_program::{MacroInst};
use crate::program::Target;
use std::collections::{HashMap, HashSet, VecDeque};

pub const CAP: u32 = 10;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Val {
    Exact(u32),
    Large(u32), // remainder modulo M_i
}

pub fn verify_congruence_set(
    prog: &[MacroInst],
    initial_state: Target,
    seed_regs: Vec<Val>,
    moduli: &[u32],
    verbose: bool,
) -> bool {
    let mut visited: HashMap<Target, HashSet<Vec<Val>>> = HashMap::new();
    let mut queue = VecDeque::new();

    queue.push_back((initial_state, seed_regs.clone()));
    visited.entry(initial_state).or_default().insert(seed_regs);

    while let Some((state, regs)) = queue.pop_front() {
        if verbose {
            println!("State {:?}: {:?}", state, regs);
        }

        let Target::Inst(idx) = state else {
            // Reached Halt or Undef -> this path didn't infinitely loop inside the set
            return false;
        };

        if idx >= prog.len() {
            return false;
        }

        let inst = &prog[idx];

        let mut next_states_to_explore = Vec::new();

        match inst {
            MacroInst::Undef => return false,
            MacroInst::Inc { reg, next } => {
                let mut next_regs = regs.clone();
                let m = moduli[*reg];
                next_regs[*reg] = match regs[*reg] {
                    Val::Exact(v) => {
                        if v + 1 < CAP {
                            Val::Exact(v + 1)
                        } else {
                            Val::Large((v + 1) % m)
                        }
                    }
                    Val::Large(r) => Val::Large((r + 1) % m),
                };
                next_states_to_explore.push((*next, next_regs));
            }
            MacroInst::Dec { reg, next_not_zero, next_zero } => {
                let m = moduli[*reg];
                match regs[*reg] {
                    Val::Exact(0) => {
                        next_states_to_explore.push((*next_zero, regs.clone()));
                    }
                    Val::Exact(v) => {
                        let mut next_regs = regs.clone();
                        next_regs[*reg] = Val::Exact(v - 1);
                        next_states_to_explore.push((*next_not_zero, next_regs));
                    }
                    Val::Large(r) => {
                        // Spawns up to two branches.
                        // 1. Exact(CAP - 1)
                        if CAP % m == r {
                            let mut next_regs1 = regs.clone();
                            next_regs1[*reg] = Val::Exact(CAP - 1);
                            next_states_to_explore.push((*next_not_zero, next_regs1));
                        }
                        // 2. Large((r - 1) % m)
                        let mut next_regs2 = regs.clone();
                        // Handle (r - 1) % m correctly with wrapping
                        let new_r = if r == 0 { m - 1 } else { r - 1 };
                        next_regs2[*reg] = Val::Large(new_r);
                        next_states_to_explore.push((*next_not_zero, next_regs2));
                    }
                }
            }
            MacroInst::Transfer { reg, incs, next } => {
                // If the decremented register is Large, we must check divisibility condition.
                // Transfer acts as if we decrease `reg` by its value V, and for each dest `d`, add `incs[d] * V` to it.
                // But this works exactly only if `reg` has a known Exact value, or if its unknown Large amount
                // respects the modulus of the destination!

                match regs[*reg] {
                    Val::Exact(v) => {
                        let mut next_regs = regs.clone();
                        next_regs[*reg] = Val::Exact(0);
                        
                        let valid = true;
                        for (&d, &inc) in incs {
                            let m_d = moduli[d];
                            let amount_to_add = v * inc;
                            next_regs[d] = match next_regs[d] {
                                Val::Exact(dv) => {
                                    if dv + amount_to_add < CAP {
                                        Val::Exact(dv + amount_to_add)
                                    } else {
                                        Val::Large((dv + amount_to_add) % m_d)
                                    }
                                }
                                Val::Large(dr) => {
                                    Val::Large((dr + amount_to_add) % m_d)
                                }
                            };
                        }
                        if valid {
                            next_states_to_explore.push((*next, next_regs));
                        }
                    }
                    Val::Large(r) => {
                        // The source register has an unknown value V = K * M_s + r (and V >= CAP).
                        // V - r is a multiple of M_s.
                        // For the remainder in the destination to be well-defined for ALL possible V,
                        // `inc * M_s` must be a multiple of `M_d`. 
                        // If it's not, then different values of V (with the same r) will result in different remainders mod M_d.
                        let m_s = moduli[*reg];
                        let mut valid = true;
                        
                        for (&d, &inc) in incs {
                            let m_d = moduli[d];
                            if (inc * m_s) % m_d != 0 {
                                // Invalid transfer, the destination remainder is not invariant under the choice of V.
                                valid = false;
                                break;
                            }
                        }

                        if valid {
                            // What happens to `reg`? It becomes 0.
                            let mut next_regs = regs.clone();
                            next_regs[*reg] = Val::Exact(0);
                            
                            for (&d, &inc) in incs {
                                let m_d = moduli[d];
                                // We add V * inc. V = r mod m_s.
                                // We know (inc * m_s) is 0 mod m_d.
                                // So V * inc = (K * m_s + r) * inc = K * (inc * m_s) + r * inc = 0 + r * inc (mod m_d).
                                // So we effectively just add (r * inc) to the remainder!
                                let amount_to_add = r * inc;
                                next_regs[d] = match next_regs[d] {
                                    Val::Exact(dv) => {
                                        // Since V can be arbitrarily large (V >= CAP), dv + V * inc is definitely >= CAP.
                                        // (Assuming inc > 0, which it always is in our language).
                                        // So the result is always Large!
                                        Val::Large((dv + amount_to_add) % m_d)
                                    }
                                    Val::Large(dr) => {
                                        Val::Large((dr + amount_to_add) % m_d)
                                    }
                                };
                            }
                            
                            next_states_to_explore.push((*next, next_regs));
                        }
                    }
                }
            }
        }

        for (next_state, next_regs) in next_states_to_explore {
            let set = visited.entry(next_state).or_default();
            if set.insert(next_regs.clone()) {
                queue.push_back((next_state, next_regs));
            }
        }
    }

    true // If we explored all paths and didn't hit Halt/Undef, the set is closed (infinite)
}
