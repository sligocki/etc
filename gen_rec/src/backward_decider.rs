use crate::grf::{Grf, GrfKind};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Constraint {
    Exact(u64),
    Any,
}

impl Constraint {
    pub fn intersect(&self, other: &Constraint) -> Option<Constraint> {
        match (self, other) {
            (Constraint::Exact(a), Constraint::Exact(b)) => {
                if a == b {
                    Some(Constraint::Exact(*a))
                } else {
                    None
                }
            }
            (Constraint::Exact(a), Constraint::Any) => Some(Constraint::Exact(*a)),
            (Constraint::Any, Constraint::Exact(b)) => Some(Constraint::Exact(*b)),
            (Constraint::Any, Constraint::Any) => Some(Constraint::Any),
        }
    }
}

pub type Region = Vec<Constraint>;

pub fn intersect_regions(r1: &[Constraint], r2: &[Constraint]) -> Option<Region> {
    if r1.len() != r2.len() {
        return None;
    }
    let mut result = Vec::with_capacity(r1.len());
    for (c1, c2) in r1.iter().zip(r2.iter()) {
        if let Some(c) = c1.intersect(c2) {
            result.push(c);
        } else {
            return None;
        }
    }
    Some(result)
}

use std::cell::Cell;

pub struct BackwardDecider {
    pub max_depth: usize,
    pub budget: Cell<usize>,
}

impl BackwardDecider {
    pub fn new(max_depth: usize, max_budget: usize) -> Self {
        Self {
            max_depth,
            budget: Cell::new(max_budget),
        }
    }

    /// Evaluates all input configurations that could lead to the target output.
    pub fn backward_eval(&self, grf: &Grf, target: u64, depth: usize) -> Vec<Region> {
        if depth > self.max_depth {
            return vec![vec![Constraint::Any; grf.arity()]];
        }
        if self.budget.get() == 0 {
            return vec![vec![Constraint::Any; grf.arity()]];
        }
        self.budget.set(self.budget.get() - 1);

        match &grf.kind {
            GrfKind::Zero(k) => {
                if target == 0 {
                    vec![vec![Constraint::Any; *k]]
                } else {
                    vec![]
                }
            }
            GrfKind::Succ => {
                if target == 0 {
                    vec![]
                } else {
                    vec![vec![Constraint::Exact(target - 1)]]
                }
            }
            GrfKind::Proj(k, i) => {
                let mut region = vec![Constraint::Any; *k];
                region[*i - 1] = Constraint::Exact(target);
                vec![region]
            }
            GrfKind::Comp(h, gs, _) => {
                let h_regions = self.backward_eval(h, target, depth + 1);
                let mut result = Vec::new();

                for h_reg in h_regions {
                    let mut current_regions = vec![vec![Constraint::Any; grf.arity()]];
                    let mut possible = true;

                    for (j, g_target) in h_reg.iter().enumerate() {
                        if depth >= self.max_depth {
                            return vec![vec![Constraint::Any; grf.arity()]];
                        }

                        let current_budget = self.budget.get();
                        if current_budget == 0 {
                            println!("Degraded due to budget");
                            return vec![vec![Constraint::Any; grf.arity()]];
                        }
                        let g = &gs[j];
                        let g_regions = match g_target {
                            Constraint::Exact(v) => self.backward_eval(g, *v, depth + 1),
                            Constraint::Any => vec![vec![Constraint::Any; grf.arity()]],
                        };

                        if g_regions.is_empty() {
                            possible = false;
                            break;
                        }

                        let mut next_regions = Vec::new();
                        for curr in &current_regions {
                            for g_reg in &g_regions {
                                if let Some(intersected) = intersect_regions(curr, g_reg) {
                                    next_regions.push(intersected);
                                }
                            }
                        }
                        current_regions = next_regions;
                        if current_regions.is_empty() {
                            possible = false;
                            break;
                        }
                        if current_regions.len() > 100 {
                            return vec![vec![Constraint::Any; grf.arity()]];
                        }
                    }
                    if possible {
                        result.extend(current_regions);
                    }
                }
                result
            }
            GrfKind::Rec(g, h) => {
                let mut result = Vec::new();
                let k = g.arity();

                // Base case: n = 0, so g(x) = target
                let g_regions = self.backward_eval(g, target, depth + 1);
                for reg in &g_regions {
                    let mut full_reg = vec![Constraint::Exact(0)];
                    full_reg.extend(reg.clone());
                    result.push(full_reg);
                }

                // Step case: n > 0, so h(n-1, acc, x) = target
                let h_regions = self.backward_eval(h, target, depth + 1);
                for h_reg in h_regions {
                    let req_n_minus_1 = &h_reg[0];
                    let req_acc = &h_reg[1];
                    let req_x = &h_reg[2..];

                    let acc_regions = match req_acc {
                        Constraint::Exact(v) => {
                            if *v == target {
                                // CYCLE DETECTED!
                                // The step case requires the accumulator to be exactly the target.
                                // Instead of recursing infinitely (asking "when is G = target" while computing it),
                                // we mathematically know that any such sequence must ultimately stem from the
                                // base case of G = target. We substitute the base case constraints (g_regions).
                                let mut pseudo_g_regs = Vec::with_capacity(g_regions.len());
                                for base_reg in &g_regions {
                                    let mut r = vec![Constraint::Any];
                                    r.extend(base_reg.clone());
                                    pseudo_g_regs.push(r);
                                }
                                pseudo_g_regs
                            } else {
                                self.backward_eval(grf, *v, depth + 1)
                            }
                        }
                        Constraint::Any => vec![vec![Constraint::Any; k + 1]],
                    };

                    let mut current_reqs = vec![req_n_minus_1.clone()];
                    current_reqs.extend_from_slice(req_x);

                    for acc_reg in acc_regions {
                        if let Some(intersected) = intersect_regions(&current_reqs, &acc_reg) {
                            let n_minus_1 = &intersected[0];
                            let x_reqs = &intersected[1..];
                            let req_n = match n_minus_1 {
                                Constraint::Exact(v) => Constraint::Exact(v + 1),
                                Constraint::Any => Constraint::Any,
                            };
                            let mut full_reg = vec![req_n];
                            full_reg.extend_from_slice(x_reqs);
                            result.push(full_reg);
                        }
                    }
                }
                result
            }
            GrfKind::Min(f) => {
                let f_regions = self.backward_eval(f, 0, depth + 1);
                let mut result = Vec::new();
                for f_reg in f_regions {
                    let req_target = &f_reg[0];
                    let req_args = &f_reg[1..];

                    let possible = match req_target {
                        Constraint::Exact(v) => *v == target,
                        Constraint::Any => true,
                    };

                    if possible {
                        result.push(req_args.to_vec());
                    }
                }
                result
            }
        }
    }

    /// If f(i, args...) = 0 is only possible for specific exact values of i, returns those values.
    /// Returns None if i can be Any (or if depth limit is exceeded, degrading to Any).
    /// If the returned list is empty, then f(i, args...) = 0 is impossible for any i.
    pub fn valid_search_indices(&self, f: &Grf) -> Option<Vec<u64>> {
        let regions = self.backward_eval(f, 0, 0);
        let mut valid = Vec::new();
        for reg in regions {
            match reg[0] {
                Constraint::Exact(v) => {
                    if !valid.contains(&v) {
                        valid.push(v);
                    }
                }
                Constraint::Any => return None,
            }
        }
        Some(valid)
    }

    /// Checks if a M(f) expression is provably divergent.
    pub fn proves_divergence(&self, m_f: &Grf) -> bool {
        if let GrfKind::Min(f) = &m_f.kind {
            if let Some(valid_indices) = self.valid_search_indices(f) {
                // If there are no valid indices at all, it's impossible for f(i) to be 0.
                if valid_indices.is_empty() {
                    return true;
                }

                // If there are finite valid indices, simulate them to see if any yield 0.
                // If all of them halt with a non-zero value, then M(f) diverges!
                for &v in &valid_indices {
                    let (res, _) = crate::simulate::simulate(f, &[v], 10_000);
                    match res {
                        crate::simulate::SimResult::Value(val) => {
                            if val == 0 {
                                return false; // This index halts and yields 0, M(f) halts!
                            }
                        }
                        _ => {
                            // If it diverges or runs out of steps, we can't prove M(f) diverges
                            // since this candidate index might actually yield 0 eventually.
                            return false;
                        }
                    }
                }

                // All candidates halted with non-zero values. M(f) diverges!
                return true;
            }
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::grf;

    #[test]
    fn test_example_1_divergence() {
        let f = grf!("C(R(C(S,Z1),P(3,3)),R(Z0,C(R(P(1,1),P(3,1)),P(2,2),P(2,1))),P(1,1))");
        let decider = BackwardDecider::new(10, 100_000);
        let valid_indices = decider.valid_search_indices(&f).unwrap();
        // The original logic concluded it's only possible at n=0
        assert_eq!(valid_indices, vec![0]);
    }

    #[test]
    fn test_example_2_divergence() {
        let f = grf!("C(R(Z0,C(R(S,R(P(2,2),C(S,P(4,1)))),P(2,2),P(2,1))),S)");
        let decider = BackwardDecider::new(10, 100_000);
        let valid_indices = decider.valid_search_indices(&f).unwrap();
        // The original logic concluded it's only possible at n=0
        assert_eq!(valid_indices, vec![0]);
    }

    #[test]
    fn test_decides_m_f() {
        let decider = BackwardDecider::new(10, 100_000);
        let m_f_1 = grf!("M(C(R(C(S,Z1),P(3,3)),R(Z0,C(R(P(1,1),P(3,1)),P(2,2),P(2,1))),P(1,1)))");

        // Wait, proves_divergence simulates the valid indices. Example 1 has valid_indices = vec![0].
        // It simulates f(0), which evaluates to 1 (not 0). So it proves divergence!
        assert_eq!(decider.proves_divergence(&m_f_1), true);
    }
}
