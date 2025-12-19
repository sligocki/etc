// A class representing an integer range.
// These sets can be used to define CTL sets for Fractran states.

use crate::program::SmallInt;

// Represents a subset of the natural numbers (0, 1, 2, ...)
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum IntRange {
    // Fixed(n) = {n} is a set containing only one value, n
    Fixed(SmallInt),
    // Min(n) = [n, inf) is a set containing all integers ≥ n
    Min(SmallInt),
}

impl IntRange {
    // Is this range a valid subset of the natural numbers (>= 0)?
    fn is_valid(self) -> bool {
        match self {
            IntRange::Fixed(n) => n >= 0,
            IntRange::Min(n) => n >= 0,
        }
    }
    fn validate(self) -> Option<IntRange> {
        if self.is_valid() { Some(self) } else { None }
    }

    // Is self a subset of other?
    pub fn is_subset(self, other: IntRange) -> bool {
        match (self, other) {
            // {a} subset {b} iff a == b
            (IntRange::Fixed(a), IntRange::Fixed(b)) => a == b,
            // [a, inf) subset {b} is impossible
            (IntRange::Min(_), IntRange::Fixed(_)) => false,
            // {a} subset [b, inf) iff a ≥ b
            (IntRange::Fixed(a), IntRange::Min(b)) => a >= b,
            // [a,inf) subset [b, inf) iff a ≥ b
            (IntRange::Min(a), IntRange::Min(b)) => a >= b,
        }
    }

    // X.add(v) = {x+v : x in X}
    fn add(self, v: SmallInt) -> IntRange {
        match self {
            IntRange::Fixed(n) => IntRange::Fixed(n + v),
            IntRange::Min(n) => IntRange::Min(n + v),
        }
    }

    // X.add(v), but return None if result leads to invalid set (set containing negative integers).
    pub fn checked_add(self, v: SmallInt) -> Option<IntRange> {
        self.add(v).validate()
    }
}

// Represents a subset of vectors N^k by the cartesian product of IntRanges.
#[derive(Debug, PartialEq, Clone)]
pub struct VecSet(Vec<IntRange>);

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
        let vals: Option<Vec<IntRange>> = self
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
        let f1 = IntRange::Fixed(1);
        let f13 = IntRange::Fixed(13);
        let m8 = IntRange::Min(8);
        let m276 = IntRange::Min(276);
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
        let f13 = IntRange::Fixed(13);
        assert_eq!(f13.checked_add(8), Some(IntRange::Fixed(21)));
        assert_eq!(f13.checked_add(-8), Some(IntRange::Fixed(5)));
        assert_eq!(f13.checked_add(-13), Some(IntRange::Fixed(0)));
        assert_eq!(f13.checked_add(-14), None);

        let m8 = IntRange::Min(8);
        assert_eq!(m8.checked_add(100), Some(IntRange::Min(108)));
        assert_eq!(m8.checked_add(-2), Some(IntRange::Min(6)));
        assert_eq!(m8.checked_add(-8), Some(IntRange::Min(0)));
        assert_eq!(m8.checked_add(-13), None);

        let v = VecSet(vec![f13, m8]);
        assert_eq!(
            v.checked_add(vec![100, 200]),
            Some(VecSet(vec![IntRange::Fixed(113), IntRange::Min(208)]))
        );
        assert_eq!(
            v.checked_add(vec![-1, -1]),
            Some(VecSet(vec![IntRange::Fixed(12), IntRange::Min(7)]))
        );
        assert_eq!(v.checked_add(vec![-1, -10]), None);
        assert_eq!(v.checked_add(vec![-20, 0]), None);
    }
}
