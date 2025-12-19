// Structures representing subsets of the Natural numbers (and vector spaces over them).
//
// VecSets are sets of Fractran states.
//
// These could be used as preconditions for rules or building up CTL sets, etc.

use crate::program::SmallInt;

// Represents a subset of the natural numbers (0, 1, 2, ...)
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum NatSet {
    // Fixed(n) = {n} is a set containing only one value, n
    Fixed(SmallInt),
    // Min(n) = [n, inf) is a set containing all integers ≥ n
    Min(SmallInt),
}

#[derive(Debug, PartialEq, Clone)]
pub struct SplitAddResult {
    success: Option<NatSet>,
    failure: Vec<NatSet>,
}

impl NatSet {
    // Is self a subset of other?
    pub fn is_subset(self, other: NatSet) -> bool {
        match (self, other) {
            // {a} subset {b} iff a == b
            (NatSet::Fixed(a), NatSet::Fixed(b)) => a == b,
            // [a, inf) subset {b} is impossible
            (NatSet::Min(_), NatSet::Fixed(_)) => false,
            // {a} subset [b, inf) iff a ≥ b
            (NatSet::Fixed(a), NatSet::Min(b)) => a >= b,
            // [a,inf) subset [b, inf) iff a ≥ b
            (NatSet::Min(a), NatSet::Min(b)) => a >= b,
        }
    }

    // Try adding v (posibly negative) to NatSet X. Returns "success" and "failure" results.
    //      Success: Valid result of addition: {x+v | x in X and x+v >= 0}
    //      Failure: Values from original set that cannot be added to: {x in X | x+v < 0}
    pub fn split_add(self, v: SmallInt) -> SplitAddResult {
        match self {
            NatSet::Fixed(n) => {
                let sum = n + v;
                if sum >= 0 {
                    // Total success: {n} + v -> {n+v}
                    SplitAddResult {
                        success: Some(NatSet::Fixed(sum)),
                        failure: vec![],
                    }
                } else {
                    // Total failure: {n} + v contains no positive values
                    SplitAddResult {
                        success: None,
                        failure: vec![self],
                    }
                }
            }
            NatSet::Min(n) => {
                let sum = n + v;
                if sum >= 0 {
                    // Total success: [n, inf) + v -> [n+v, inf)
                    SplitAddResult {
                        success: Some(NatSet::Min(sum)),
                        failure: vec![],
                    }
                } else {
                    // Mixture of success and failure: [n, inf) = [n, -v) | [-v, inf)
                    //      Success: [-v, inf) + v -> [0, inf)
                    //      Failure: [n, -v) + v contains no positive values
                    SplitAddResult {
                        success: Some(NatSet::Min(0)),
                        // Represent [n, v) as {n} | {n+1} | ... | {v-1}
                        failure: (n..-v).map(|x| NatSet::Fixed(x)).collect(),
                    }
                }
            }
        }
    }
}

// Represents a subset of vectors N^k by the cartesian product of NatSets.
#[derive(Debug, PartialEq, Clone)]
pub struct VecSet(Vec<NatSet>);

#[derive(Debug, PartialEq, Clone)]
pub struct SplitApplyResult {
    success: Option<VecSet>,
    failure: Vec<VecSet>,
}

impl VecSet {
    // Is self a subset of other?
    pub fn is_subset(&self, other: &VecSet) -> bool {
        assert_eq!(self.0.len(), other.0.len());
        self.0
            .iter()
            .zip(other.0.iter())
            .all(|(a, b)| a.is_subset(*b))
    }

    fn update(&self, index: usize, val: NatSet) -> VecSet {
        let mut new = self.clone();
        new.0[index] = val;
        new
    }

    // Attempt to apply an instruction (`vs`). Returns "success" and "failure" results.
    //      Success: New VecSet of all valid states after applying `vs`.
    //      Failure: VecSets that union to cover all cases where `vs` cannot apply.
    pub fn split_apply(&self, vs: &Vec<SmallInt>) -> SplitApplyResult {
        let split_add_res: Vec<SplitAddResult> = self
            .0
            .iter()
            .zip(vs.iter())
            .map(|(x, v)| x.split_add(*v))
            .collect();
        // Collect the combination of all successfull NatSets.
        // Or if any are None, this will be None.
        let success: Option<Vec<NatSet>> = split_add_res.iter().map(|r| r.success).collect();
        let mut failure = Vec::new();
        for (reg_num, res) in split_add_res.iter().enumerate() {
            for nat_set in res.failure.iter() {
                failure.push(self.update(reg_num, *nat_set))
            }
        }
        SplitApplyResult {
            success: success.and_then(|x| Some(VecSet(x))),
            failure,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_subset() {
        let f1 = NatSet::Fixed(1);
        let f13 = NatSet::Fixed(13);
        let m8 = NatSet::Min(8);
        let m276 = NatSet::Min(276);
        assert!(f1.is_subset(f1));
        assert!(!f1.is_subset(f13));
        assert!(!f1.is_subset(m8));
        assert!(!f1.is_subset(m276));

        assert!(!f13.is_subset(f1));
        assert!(f13.is_subset(f13));
        assert!(f13.is_subset(m8));
        assert!(!f13.is_subset(m276));

        assert!(!m8.is_subset(f1));
        assert!(!m8.is_subset(f13));
        assert!(m8.is_subset(m8));
        assert!(!m8.is_subset(m276));

        assert!(!m276.is_subset(f1));
        assert!(!m276.is_subset(f13));
        assert!(m276.is_subset(m8));
        assert!(m276.is_subset(m276));

        let v1 = VecSet(vec![f13, m276]);
        let v2 = VecSet(vec![m8, m8]);
        assert!(v1.is_subset(&v2));
        assert!(!v2.is_subset(&v1));
    }

    #[test]
    fn test_split_add() {
        let f13 = NatSet::Fixed(13);
        assert_eq!(
            f13.split_add(8),
            SplitAddResult {
                success: Some(NatSet::Fixed(21)),
                failure: vec![],
            }
        );
        assert_eq!(
            f13.split_add(-8),
            SplitAddResult {
                success: Some(NatSet::Fixed(5)),
                failure: vec![],
            }
        );
        assert_eq!(
            f13.split_add(-13),
            SplitAddResult {
                success: Some(NatSet::Fixed(0)),
                failure: vec![],
            }
        );
        assert_eq!(
            f13.split_add(-14),
            SplitAddResult {
                success: None,
                failure: vec![f13],
            }
        );

        let m8 = NatSet::Min(8);
        assert_eq!(
            m8.split_add(100),
            SplitAddResult {
                success: Some(NatSet::Min(108)),
                failure: vec![],
            }
        );
        assert_eq!(
            m8.split_add(-8),
            SplitAddResult {
                success: Some(NatSet::Min(0)),
                failure: vec![],
            }
        );
        assert_eq!(
            m8.split_add(-13),
            SplitAddResult {
                // [13, inf) - 13 -> [0, inf)
                success: Some(NatSet::Min(0)),
                // [8, 13) cannot subtract 13
                failure: vec![
                    NatSet::Fixed(8),
                    NatSet::Fixed(9),
                    NatSet::Fixed(10),
                    NatSet::Fixed(11),
                    NatSet::Fixed(12),
                ],
            }
        );
    }

    #[test]
    fn test_split_apply() {
        let v = VecSet(vec![
            NatSet::Fixed(13),
            NatSet::Min(8),
            NatSet::Min(31),
        ]);
        assert_eq!(
            v.split_apply(&vec![100, 200, 300]),
            SplitApplyResult {
                success: Some(VecSet(vec![NatSet::Fixed(113), NatSet::Min(208), NatSet::Min(331)])),
                failure: vec![],
            }
        );
        assert_eq!(
            v.split_apply(&vec![-1, -1, -1]),
            SplitApplyResult {
                success: Some(VecSet(vec![NatSet::Fixed(12), NatSet::Min(7), NatSet::Min(30)])),
                failure: vec![],
            }
        );
        assert_eq!(
            v.split_apply(&vec![-20, 0, 0]),
            SplitApplyResult {
                success: None,
                failure: vec![v.clone()],
            }
        );
        assert_eq!(
            v.split_apply(&vec![0, -10, 0]),
            SplitApplyResult {
                success: Some(VecSet(vec![NatSet::Fixed(13), NatSet::Min(0), NatSet::Min(31)])),
                failure: vec![
                    VecSet(vec![NatSet::Fixed(13), NatSet::Fixed(8), NatSet::Min(31)]),
                    VecSet(vec![NatSet::Fixed(13), NatSet::Fixed(9), NatSet::Min(31)]),
                ],
            }
        );
        assert_eq!(
            v.split_apply(&vec![1, -10, -34]),
            SplitApplyResult {
                success: Some(VecSet(vec![NatSet::Fixed(14), NatSet::Min(0), NatSet::Min(0)])),
                failure: vec![
                    VecSet(vec![NatSet::Fixed(13), NatSet::Fixed(8), NatSet::Min(31)]),
                    VecSet(vec![NatSet::Fixed(13), NatSet::Fixed(9), NatSet::Min(31)]),
                    VecSet(vec![NatSet::Fixed(13), NatSet::Min(8), NatSet::Fixed(31)]),
                    VecSet(vec![NatSet::Fixed(13), NatSet::Min(8), NatSet::Fixed(32)]),
                    VecSet(vec![NatSet::Fixed(13), NatSet::Min(8), NatSet::Fixed(33)]),
                ],
            }
        );
    }
}
