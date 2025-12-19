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

impl NatSet {
    // Is this range a valid subset of the natural numbers (>= 0)?
    fn is_valid(self) -> bool {
        match self {
            NatSet::Fixed(n) => n >= 0,
            NatSet::Min(n) => n >= 0,
        }
    }
    fn validate(self) -> Option<NatSet> {
        if self.is_valid() { Some(self) } else { None }
    }

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

    // X.add(v) = {x+v : x in X}
    fn add(self, v: SmallInt) -> NatSet {
        match self {
            NatSet::Fixed(n) => NatSet::Fixed(n + v),
            NatSet::Min(n) => NatSet::Min(n + v),
        }
    }

    // X.add(v), but return None if result leads to invalid set (set containing negative integers).
    pub fn checked_add(self, v: SmallInt) -> Option<NatSet> {
        self.add(v).validate()
    }
}

// Represents a subset of vectors N^k by the cartesian product of NatSets.
#[derive(Debug, PartialEq, Clone)]
pub struct VecSet(Vec<NatSet>);

impl VecSet {
    // Is self a subset of other?
    pub fn is_subset(&self, other: &VecSet) -> bool {
        assert_eq!(self.0.len(), other.0.len());
        self.0
            .iter()
            .zip(other.0.iter())
            .all(|(a, b)| a.is_subset(*b))
    }

    pub fn checked_add(&self, vs: Vec<SmallInt>) -> Option<VecSet> {
        let vals: Option<Vec<NatSet>> = self
            .0
            .iter()
            .zip(vs.iter())
            .map(|(x, v)| x.checked_add(*v))
            .collect();
        Some(VecSet(vals?))
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
    fn test_checked_add() {
        let f13 = NatSet::Fixed(13);
        assert_eq!(f13.checked_add(8), Some(NatSet::Fixed(21)));
        assert_eq!(f13.checked_add(-8), Some(NatSet::Fixed(5)));
        assert_eq!(f13.checked_add(-13), Some(NatSet::Fixed(0)));
        assert_eq!(f13.checked_add(-14), None);

        let m8 = NatSet::Min(8);
        assert_eq!(m8.checked_add(100), Some(NatSet::Min(108)));
        assert_eq!(m8.checked_add(-2), Some(NatSet::Min(6)));
        assert_eq!(m8.checked_add(-8), Some(NatSet::Min(0)));
        assert_eq!(m8.checked_add(-13), None);

        let v = VecSet(vec![f13, m8]);
        assert_eq!(
            v.checked_add(vec![100, 200]),
            Some(VecSet(vec![NatSet::Fixed(113), NatSet::Min(208)]))
        );
        assert_eq!(
            v.checked_add(vec![-1, -1]),
            Some(VecSet(vec![NatSet::Fixed(12), NatSet::Min(7)]))
        );
        assert_eq!(v.checked_add(vec![-1, -10]), None);
        assert_eq!(v.checked_add(vec![-20, 0]), None);
    }
}
