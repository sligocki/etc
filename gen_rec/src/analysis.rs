use std::collections::BTreeSet;
use std::sync::OnceLock;

use crate::closed_form::ClosedForm;
use crate::grf::{GrfKind, Rewirability};

#[derive(Clone, Debug)]
pub struct GrfAnalysis {
    pub used_args: BTreeSet<usize>,
    pub is_prf: bool,
    pub rewirability: Rewirability,
    pub canonical_arg_order: Vec<usize>,
    pub acc_plus_k: Option<u64>,
    pub closed_form: OnceLock<Option<ClosedForm>>,
}

impl GrfAnalysis {
    pub fn compute(kind: &GrfKind) -> Self {
        let used_args = Self::compute_used_args(kind);
        let is_prf = Self::compute_is_prf(kind);
        let rewirability = Self::compute_rewirability(kind);
        let canonical_arg_order = Self::compute_canonical_arg_order(kind);
        let acc_plus_k = Self::compute_acc_plus_k(kind);


        GrfAnalysis {
            used_args,
            is_prf,

            rewirability,
            canonical_arg_order,
            acc_plus_k,
            closed_form: OnceLock::new(),
        }
    }

    fn compute_used_args(kind: &GrfKind) -> BTreeSet<usize> {
        match kind {
            GrfKind::Zero(_) => BTreeSet::new(),
            GrfKind::Succ => [1].into_iter().collect(),
            GrfKind::Proj(_, i) => [*i].into_iter().collect(),
            GrfKind::Comp(h, gs, _) => {
                let h_used = &h.analysis.used_args;
                let mut result = BTreeSet::new();
                for (idx, g) in gs.iter().enumerate() {
                    if h_used.contains(&(idx + 1)) {
                        result.extend(g.analysis.used_args.iter().copied());
                    }
                }
                result
            }
            GrfKind::Rec(g, h) => {
                let g_used = &g.analysis.used_args;
                let h_used = &h.analysis.used_args;
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
                let f_used = &f.analysis.used_args;
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

    fn compute_canonical_arg_order(kind: &GrfKind) -> Vec<usize> {
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
        crate::grf::grf_outer_arg_dfs_kind(kind, &identity, &mut seen, &mut order);
        order
    }
}


