// A class representing an integer range.
// These sets can be used to define CTL sets for Fractran states.

use crate::program::SmallInt;

// Represents a subset of the natural numbers (0, 1, 2, ...)
#[derive(Debug, PartialEq, Clone)]
pub enum IntRange {
    // Fixed(n) = {n} is a set containing only one value, n
    Fixed(SmallInt),
    // Min(n) = [n, inf) is a set containing all integers ≥ n
    Min(SmallInt),
}

impl IntRange {
    // Is this range a valid subset of the natural numbers (>= 0)?
    fn is_nat(&self) -> bool {
        match self {
            IntRange::Fixed(n) => *n >= 0,
            IntRange::Min(n) => *n >= 0,
        }
    }

    // Is self a subset of other?
    pub fn is_subset(&self, other: &IntRange) -> bool {
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
    // This is only intended for use with non-negative v (in pub uses).
    // For subtraction use checked_sub which ensures the result is a valid range.
    pub fn add(&self, v: SmallInt) -> IntRange {
        match self {
            IntRange::Fixed(n) => IntRange::Fixed(n + v),
            IntRange::Min(n) => IntRange::Min(n + v),
        }
    }

    // X.sub(v) = {x-v : x in X}
    // X.checked_sub(v) = None if X.sub(v) contains any negative values
    pub fn checked_sub(&self, v: SmallInt) -> Option<IntRange> {
        let n = self.add(-v);
        if n.is_nat() { Some(n) } else { None }
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
        assert!(f1.is_subset(&f1));
        assert!(!f1.is_subset(&f13));
        assert!(!f1.is_subset(&m8));
        assert!(!f1.is_subset(&m276));

        assert!(!f13.is_subset(&f1));
        assert!(f13.is_subset(&f13));
        assert!(f13.is_subset(&m8));
        assert!(!f13.is_subset(&m276));

        assert!(!m8.is_subset(&f1));
        assert!(!m8.is_subset(&f13));
        assert!(m8.is_subset(&m8));
        assert!(!m8.is_subset(&m276));

        assert!(!m276.is_subset(&f1));
        assert!(!m276.is_subset(&f13));
        assert!(m276.is_subset(&m8));
        assert!(m276.is_subset(&m276));
    }

    #[test]
    fn test_add() {
        let f13 = IntRange::Fixed(13);
        let m8 = IntRange::Min(8);

        assert_eq!(f13.add(8), IntRange::Fixed(21));
        assert_eq!(m8.add(100), IntRange::Min(108));
    }

    #[test]
    fn test_sub() {
        let f13 = IntRange::Fixed(13);
        let m8 = IntRange::Min(8);

        assert_eq!(f13.checked_sub(8), Some(IntRange::Fixed(5)));
        assert_eq!(f13.checked_sub(13), Some(IntRange::Fixed(0)));
        assert_eq!(f13.checked_sub(14), None);
        assert_eq!(m8.checked_sub(2), Some(IntRange::Min(6)));
        assert_eq!(m8.checked_sub(8), Some(IntRange::Min(0)));
        assert_eq!(m8.checked_sub(13), None);
    }
}
