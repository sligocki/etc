use crate::macro_program::MacroInst;
use crate::program::Target;
use std::collections::{HashMap, VecDeque};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ray {
    pub base: Vec<u32>,
    pub period: Vec<u32>,
}

impl Ray {
    pub fn is_subset_of(&self, other: &Ray) -> bool {
        if self.base.len() != other.base.len() || self.period.len() != other.period.len() {
            return false;
        }

        let is_point = self.period.iter().all(|&p| p == 0);
        let other_is_point = other.period.iter().all(|&p| p == 0);

        if other_is_point {
            return is_point && self.base == other.base;
        }

        // Check if self.period is a multiple of other.period
        let mut period_mult = None;
        for i in 0..self.period.len() {
            if other.period[i] == 0 {
                if self.period[i] != 0 {
                    return false;
                }
            } else {
                if self.period[i] % other.period[i] != 0 {
                    return false;
                }
                let c = self.period[i] / other.period[i];
                if let Some(prev_c) = period_mult {
                    if prev_c != c {
                        return false;
                    }
                } else {
                    period_mult = Some(c);
                }
            }
        }

        // Check if self.base is on other's ray
        let mut base_mult = None;
        for i in 0..self.base.len() {
            if other.period[i] == 0 {
                if self.base[i] != other.base[i] {
                    return false;
                }
            } else {
                if self.base[i] < other.base[i] {
                    return false;
                }
                let diff = self.base[i] - other.base[i];
                if diff % other.period[i] != 0 {
                    return false;
                }
                let k = diff / other.period[i];
                if let Some(prev_k) = base_mult {
                    if prev_k != k {
                        return false;
                    }
                } else {
                    base_mult = Some(k);
                }
            }
        }

        true
    }
}

pub fn verify_semilinear1d_set(
    prog: &[MacroInst],
    initial_state: Target,
    seed_ray: Ray,
    num_regs: usize,
    verbose: bool,
) -> bool {
    let mut visited: HashMap<Target, Vec<Ray>> = HashMap::new();
    let mut queue = VecDeque::new();

    queue.push_back((initial_state, seed_ray));

    let mut explored_nodes = 0;

    while let Some((pc, mut ray)) = queue.pop_front() {
        explored_nodes += 1;
        if explored_nodes > 1000 {
            if verbose {
                println!("Semilinear1D: Explored nodes limit reached (1000). Bailing out.");
            }
            return false;
        }

        if pc == Target::Halt || pc == Target::Undef {
            if verbose {
                println!(
                    "Semilinear1D: Path failed (reaches {:?}). Ray: {:?}",
                    pc, ray
                );
            }
            return false;
        }

        let state_visited = visited.entry(pc).or_default();
        if state_visited.iter().any(|v| ray.is_subset_of(v)) {
            continue;
        }

        state_visited.retain(|v| !v.is_subset_of(&ray));
        state_visited.push(ray.clone());

        let Target::Inst(pc_idx) = pc else {
            unreachable!()
        };
        let inst = &prog[pc_idx];

        // Ensure ray fits num_regs
        if ray.base.len() < num_regs {
            ray.base.resize(num_regs, 0);
        }
        if ray.period.len() < num_regs {
            ray.period.resize(num_regs, 0);
        }

        match inst.clone() {
            MacroInst::Inc { reg, next } => {
                if reg >= ray.base.len() {
                    ray.base.resize(reg + 1, 0);
                    ray.period.resize(reg + 1, 0);
                }
                ray.base[reg] += 1;
                queue.push_back((next, ray));
            }
            MacroInst::Transfer { reg, incs, next } => {
                if reg >= ray.base.len() {
                    ray.base.resize(reg + 1, 0);
                    ray.period.resize(reg + 1, 0);
                }
                let base_val = ray.base[reg];
                let per_val = ray.period[reg];
                ray.base[reg] = 0;
                ray.period[reg] = 0;

                for (target_reg, count) in incs {
                    if target_reg >= ray.base.len() {
                        ray.base.resize(target_reg + 1, 0);
                        ray.period.resize(target_reg + 1, 0);
                    }
                    ray.base[target_reg] += count * base_val;
                    ray.period[target_reg] += count * per_val;
                }
                queue.push_back((next, ray));
            }
            MacroInst::Dec {
                reg,
                next_not_zero,
                next_zero,
            } => {
                if reg >= ray.base.len() {
                    ray.base.resize(reg + 1, 0);
                    ray.period.resize(reg + 1, 0);
                }
                let b = ray.base[reg];
                let p = ray.period[reg];

                if p == 0 {
                    if b == 0 {
                        queue.push_back((next_zero, ray));
                    } else {
                        ray.base[reg] -= 1;
                        queue.push_back((next_not_zero, ray));
                    }
                } else {
                    if b == 0 {
                        // k = 0 takes next_zero
                        let mut zero_ray = ray.clone();
                        zero_ray.period.fill(0); // It's just a point
                        queue.push_back((next_zero, zero_ray));

                        // k >= 1 takes next_not_zero
                        // Shift ray by 1 period: k' = k - 1
                        let mut nz_ray = ray.clone();
                        for i in 0..nz_ray.base.len() {
                            nz_ray.base[i] += nz_ray.period[i];
                        }
                        nz_ray.base[reg] -= 1;
                        queue.push_back((next_not_zero, nz_ray));
                    } else {
                        // All k >= 0 take next_not_zero
                        ray.base[reg] -= 1;
                        queue.push_back((next_not_zero, ray));
                    }
                }
            }
            MacroInst::Undef => {
                queue.push_back((Target::Halt, ray));
            }
        }
    }

    true
}
