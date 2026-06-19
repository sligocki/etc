use std::collections::BTreeSet;
use std::sync::OnceLock;

use crate::closed_form::ClosedForm;
use crate::grf::{Bound, Grf, GrfKind, Rewirability, grf_outer_arg_dfs_kind};

#[derive(Clone, Debug)]
pub struct GrfAnalysis {
    pub used_args: OnceLock<BTreeSet<usize>>,
    pub is_never_zero: OnceLock<bool>,
    pub is_always_pos: OnceLock<bool>,
    pub is_always_zero: OnceLock<bool>,
    pub is_prf: bool,
    pub rewirability: Rewirability,
    pub canonical_arg_order: OnceLock<Vec<usize>>,
    pub acc_plus_k: Option<u64>,
    pub closed_form: OnceLock<Option<ClosedForm>>,
}

impl GrfAnalysis {
    pub fn compute(kind: &GrfKind) -> Self {
        let is_prf = Self::compute_is_prf(kind);
        let rewirability = Self::compute_rewirability(kind);
        let acc_plus_k = Self::compute_acc_plus_k(kind);

        GrfAnalysis {
            used_args: OnceLock::new(),
            is_never_zero: OnceLock::new(),
            is_always_pos: OnceLock::new(),
            is_always_zero: OnceLock::new(),
            is_prf,
            rewirability,
            canonical_arg_order: OnceLock::new(),
            acc_plus_k,
            closed_form: OnceLock::new(),
        }
    }

    pub fn compute_used_args(kind: &GrfKind) -> BTreeSet<usize> {
        match kind {
            GrfKind::Zero(_) => BTreeSet::new(),
            GrfKind::Succ => [1].into_iter().collect(),
            GrfKind::Proj(_, i) => [*i].into_iter().collect(),
            GrfKind::Comp(h, gs, _) => {
                let h_used = h.used_args();
                let mut result = BTreeSet::new();
                for (idx, g) in gs.iter().enumerate() {
                    if h_used.contains(&(idx + 1)) {
                        result.extend(g.used_args().iter().copied());
                    }
                }
                result
            }
            GrfKind::Rec(g, h) => {
                let g_used = g.used_args();
                let h_used = h.used_args();
                let mut result = BTreeSet::new();
                result.insert(1);
                for &j in g_used {
                    result.insert(j + 1);
                }
                for &j in h_used {
                    if j >= 3 {
                        result.insert(j - 1);
                    }
                }
                result
            }
            GrfKind::Min(f) => {
                let f_used = f.used_args();
                let mut result = BTreeSet::new();
                for &j in f_used {
                    if j >= 2 {
                        result.insert(j - 1);
                    }
                }
                result
            }
        }
    }

    fn compute_is_prf(kind: &GrfKind) -> bool {
        match kind {
            GrfKind::Zero(_) | GrfKind::Succ | GrfKind::Proj(_, _) => true,
            GrfKind::Comp(h, gs, _) => h.analysis.is_prf && gs.iter().all(|g| g.analysis.is_prf),
            GrfKind::Rec(g, h) => g.analysis.is_prf && h.analysis.is_prf,
            GrfKind::Min(_) => false,
        }
    }

    fn compute_rewirability(kind: &GrfKind) -> Rewirability {
        match kind {
            GrfKind::Zero(_) | GrfKind::Proj(_, _) | GrfKind::Comp(_, _, _) | GrfKind::Min(_) => {
                Rewirability::Full
            }
            GrfKind::Rec(_, _) => Rewirability::CounterLocked,
            GrfKind::Succ => Rewirability::SuccLocked,
        }
    }

    fn compute_acc_plus_k(kind: &GrfKind) -> Option<u64> {
        match kind {
            GrfKind::Proj(_, 2) => Some(0),
            GrfKind::Comp(outer, inners, _) => {
                if let GrfKind::Succ = &outer.kind {
                    if inners.len() == 1 {
                        return inners[0].analysis.acc_plus_k.map(|k| k + 1);
                    }
                }
                None
            }
            _ => None,
        }
    }

    pub fn compute_canonical_arg_order(kind: &GrfKind) -> Vec<usize> {
        let arity = match kind {
            GrfKind::Zero(k) => *k,
            GrfKind::Succ => 1,
            GrfKind::Proj(k, _) => *k,
            GrfKind::Comp(_, _, k) => *k,
            GrfKind::Rec(g, _) => g.arity() + 1,
            GrfKind::Min(func) => func.arity() - 1,
        };
        let identity: Vec<usize> = (1..=arity).collect();
        let mut seen = vec![false; arity + 1];
        let mut order = Vec::new();
        grf_outer_arg_dfs_kind(kind, &identity, &mut seen, &mut order);
        order
    }
}



pub fn compute_is_always_zero(grf: &Grf) -> bool {
    if let Some(Some(cf)) = grf.analysis.closed_form.get() {
        if cf.is_always_zero() {
            return true;
        }
    }
    match &grf.kind {
        GrfKind::Zero(_) => true,
        GrfKind::Comp(h, _, _) => h.is_always_zero(),
        GrfKind::Rec(g, h) => g.is_always_zero() && h.is_always_zero(),
        _ => false,
    }
}

    pub fn min_val(grf: &Grf) -> u64 {
        match &grf.kind {
            GrfKind::Zero(_) => 0,
            GrfKind::Succ => 1,
            GrfKind::Proj(_, _) => 0,
            GrfKind::Comp(h, gs, _) => {
                if let GrfKind::Succ = h.kind {
                    if let Some(g) = gs.first() {
                        return g.min_val() + 1;
                    }
                }
                if grf.is_never_zero() { 1 } else { 0 }
            }
            GrfKind::Rec(_, _) => {
                if grf.is_never_zero() { 1 } else { 0 }
            }
            _ => 0,
        }
    }

    /// Returns the minimum mathematically guaranteed value of `self(args) - other(args)`.
    pub fn guaranteed_diff(grf: &Grf, other: &Grf) -> Option<i64> {
        let cf_self = grf.closed_form()?;
        let cf_other = other.closed_form()?;

        if let (ClosedForm::Affine(aff_s), ClosedForm::Affine(aff_o)) = (cf_self, cf_other) {
            if aff_s.coeffs.len() < aff_o.coeffs.len() {
                return None;
            }
            for i in 1..aff_o.coeffs.len() {
                if aff_s.coeffs[i] < aff_o.coeffs[i] {
                    return None;
                }
            }
            return Some((aff_s.coeffs[0] as i64) - (aff_o.coeffs[0] as i64));
        }
        None
    }



    pub fn compute_lower_bound(grf: &Grf, args_bound: &[Bound], cf: Option<&ClosedForm>) -> Bound {
        let mut bound = 0;

        if let Some(cf) = cf {
            if cf.is_always_pos() {
                bound = 1;
            }
            for (i, arg) in args_bound.iter().enumerate() {
                if let Some(c) = cf.min_diff_from_arg(i) {
                    let mut b = arg.min_value() as i64 + c;
                    if b < 0 {
                        b = 0;
                    }
                    if b as usize > bound {
                        bound = b as usize;
                    }
                }
            }
        }

        let structural_bound = match &grf.kind {
            GrfKind::Zero(_) => Bound::Exact(0),
            GrfKind::Succ => args_bound[0].map_val(|v| v + 1),
            GrfKind::Proj(_, i) => args_bound.get(*i - 1).copied().unwrap_or(Bound::Min(0)),
            GrfKind::Comp(h, gs, _) => {
                let gs_bound: Vec<Bound> = gs.iter().map(|g| g.lower_bound(args_bound)).collect();
                let mut h_bound = h.lower_bound(&gs_bound);
                if h_bound.min_value() == 0 && is_monus_descent_trap(h, gs) {
                    h_bound = Bound::Min(1);
                }
                h_bound
            }
            GrfKind::Rec(g, h) => {
                let c_bound = args_bound[0];
                let rest_bound = &args_bound[1..];

                let mut current_min = g.lower_bound(rest_bound);

                if let Bound::Exact(c) = c_bound {
                    let unroll_limit = std::cmp::min(c, 3);
                    for c_val in 0..unroll_limit {
                        let mut h_args = vec![Bound::Exact(c_val)];
                        h_args.push(current_min);
                        h_args.extend_from_slice(rest_bound);

                        let mut use_sim = false;
                        if rest_bound.is_empty() && current_min.is_exact() {
                            let sim_args: Vec<u64> =
                                h_args.iter().map(|x| x.min_value() as u64).collect();
                            if let crate::simulate::SimResult::Value(v) =
                                crate::simulate::simulate(h, &sim_args, 100).0
                            {
                                current_min = Bound::Exact(v as usize);
                                use_sim = true;
                            }
                        }
                        if !use_sim {
                            current_min = h.lower_bound(&h_args);
                        }
                    }

                    if c <= 3 {
                        current_min
                    } else {
                        let mut global_min = current_min.min_value();
                        let mut possible_acc = current_min.min_value();
                        loop {
                            let mut h_args = vec![Bound::Min(unroll_limit)];
                            h_args.push(Bound::Min(possible_acc));
                            h_args.extend_from_slice(rest_bound);
                            let next_acc = h.lower_bound(&h_args).min_value();

                            if next_acc >= possible_acc {
                                break;
                            }
                            possible_acc = next_acc;
                            global_min = std::cmp::min(global_min, possible_acc);
                        }
                        Bound::Min(global_min)
                    }
                } else {
                    let c_min = c_bound.min_value();
                    let unroll_limit = std::cmp::min(c_min, 3);
                    for c_val in 0..unroll_limit {
                        let mut h_args = vec![Bound::Exact(c_val)];
                        h_args.push(current_min);
                        h_args.extend_from_slice(rest_bound);

                        let mut use_sim = false;
                        if rest_bound.is_empty() && current_min.is_exact() {
                            let sim_args: Vec<u64> =
                                h_args.iter().map(|x| x.min_value() as u64).collect();
                            if let crate::simulate::SimResult::Value(v) =
                                crate::simulate::simulate(h, &sim_args, 100).0
                            {
                                current_min = Bound::Exact(v as usize);
                                use_sim = true;
                            }
                        }
                        if !use_sim {
                            current_min = h.lower_bound(&h_args);
                        }
                    }

                    let mut global_min = current_min.min_value();
                    let mut possible_acc = current_min.min_value();
                    loop {
                        let mut h_args = vec![Bound::Min(std::cmp::max(c_min, unroll_limit))];
                        h_args.push(Bound::Min(possible_acc));
                        h_args.extend_from_slice(rest_bound);
                        let next_acc = h.lower_bound(&h_args).min_value();

                        if next_acc >= possible_acc {
                            break;
                        }
                        possible_acc = next_acc;
                        global_min = std::cmp::min(global_min, possible_acc);
                    }
                    Bound::Min(global_min)
                }
            }
            GrfKind::Min(_) => Bound::Exact(0),
        };

        if structural_bound.min_value() >= bound {
            structural_bound
        } else {
            Bound::Min(bound)
        }
    }

    pub(crate) fn is_monus_descent_trap(h: &Grf, gs: &[Grf]) -> bool {
        let (g_h, h_h) = match &h.kind {
            GrfKind::Rec(g, h2) => (g, h2),
            _ => return false,
        };
        let cf_h = match h_h.closed_form() {
            Some(cf) => cf,
            None => return false,
        };
        let d_h = match cf_h.min_diff_from_arg(1) {
            Some(d) => d,
            None => return false,
        };
        if d_h < -1 {
            return false;
        }
        let cf_g = match g_h.closed_form() {
            Some(cf) => cf,
            None => return false,
        };

        for k in 0..gs.len() {
            let d_g = match cf_g.min_diff_from_arg(k) {
                Some(d) => d,
                None => continue,
            };
            let gs_k = match gs.get(k + 1) {
                Some(g) => g,
                None => continue,
            };
            let diff = match gs_k.guaranteed_diff(&gs[0]) {
                Some(d) => d,
                None => continue,
            };

            if diff + d_g >= 1 {
                return true;
            }
            if diff + d_g == 0 || diff + d_g == -1 {
                if let ClosedForm::Piecewise(pw) = cf_h {
                    if let ClosedForm::Affine(z_aff) = &*pw.zero_branch {
                        if z_aff.coeffs[0] >= 1 {
                            return true;
                        }
                        for (i, &c) in z_aff.coeffs.iter().enumerate().skip(1) {
                            if c > 0 {
                                if let Some(g_arg) = gs.get(i - 1) {
                                    if g_arg.lower_bound(&vec![Bound::Min(0); g_arg.arity()]).min_value() > 0 {
                                        return true;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        false
    }
