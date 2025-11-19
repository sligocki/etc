// TODO: Use this in Program to implement Rule/State?

use std::cmp::{self, Ordering};
use std::ops::{Add, AddAssign, Sub};

pub type Int = i64;

// Mathematical vector that can be added to other vectors.
#[derive(Debug, PartialEq, Clone)]
pub struct StateDiff {
    data: Vec<Int>,
}

impl StateDiff {
    pub fn new(data: Vec<Int>) -> Self {
        StateDiff { data }
    }

    pub fn pointwise_max(&self, other: &Self) -> Self {
        self.map_with(other, |(a, b)| cmp::max(a, b).clone())
    }
    pub fn pointwise_min(&self, other: &Self) -> Self {
        self.map_with(other, |(a, b)| cmp::min(a, b).clone())
    }

    // Apply `func` pointwise to all pairs of elements in self and other.
    // Used to define most operations (+,-,min,max)
    fn map_with(&self, other: &Self, func: fn((&Int, &Int)) -> Int) -> Self {
        assert!(self.data.len() == other.data.len());
        let data: Vec<Int> = self.data.iter().zip(other.data.iter()).map(func).collect();
        StateDiff { data }
    }
}

impl AddAssign<&StateDiff> for StateDiff {
    fn add_assign(&mut self, other: &StateDiff) {
        for (val, delta) in self.data.iter_mut().zip(other.data.iter()) {
            *val += delta;
        }
    }
}

impl Add for &StateDiff {
    type Output = StateDiff;

    fn add(self, other: &StateDiff) -> StateDiff {
        self.map_with(other, |(a, b)| a + b)
    }
}

impl Sub for &StateDiff {
    type Output = StateDiff;

    fn sub(self, other: &StateDiff) -> StateDiff {
        self.map_with(other, |(a, b)| a - b)
    }
}

impl PartialOrd for StateDiff {
    // self <= other  iff  all self[i] <= other[i]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let element_ords: Vec<Ordering> = self
            .data
            .iter()
            .zip(other.data.iter())
            .map(|(a, b)| a.cmp(b))
            .collect();
        let min_ord = element_ords.iter().min()?;
        let max_ord = element_ords.iter().max()?;
        match (min_ord, max_ord) {
            (Ordering::Equal, Ordering::Equal) => Some(Ordering::Equal),
            (Ordering::Less, Ordering::Equal) => Some(Ordering::Less),
            (Ordering::Equal, Ordering::Greater) => Some(Ordering::Greater),
            _ => None,
        }
    }
}

// sd![...] = StateDiff::new(vec![...])
#[macro_export]
macro_rules! sd {
    ($($x:expr),* $(,)?) => {
        StateDiff::new(vec![$($x),*])
    };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_add_sub() {
        let mut a = sd![9, -4, 5, 6, -4];
        let b = sd![0, -2, -9, 0, 6];

        let c = sd![9, -6, -4, 6, 2];
        assert_eq!(&a + &b, c);

        let d = sd![9, -2, 14, 6, -10];
        assert_eq!(&a - &b, d);

        a += &b;
        assert_eq!(a, c);
    }

    #[test]
    fn test_min_max() {
        let a = sd![9, -4, 5, -6, -4];
        let b = sd![0, -2, 9, 0, 6];

        let min = sd![0, -4, 5, -6, -4];
        assert_eq!(a.pointwise_min(&b), min);
        assert_eq!(b.pointwise_min(&a), min);

        let max = sd![9, -2, 9, 0, 6];
        assert_eq!(a.pointwise_max(&b), max);
        assert_eq!(b.pointwise_max(&a), max);
    }

    #[test]
    fn test_order() {
        let a = sd![0, 0, 0];
        let b = sd![0, 0, 1];
        let c = sd![0, 1, 0];

        assert!(a <= b);
        assert!(a <= c);
        // b and c are not comparible
        assert!(!(b <= c));
        assert!(!(c <= b));
    }
}
