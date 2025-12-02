// TODO: Use this in Program to implement Rule/State?

use infinitable::{Finite, Infinitable, Infinity, NegativeInfinity};
use std::cmp::{self, Ordering};
use std::ops::{Add, AddAssign, Mul, Sub};

pub type Int = i64;

// Mathematical vector that can be added to other vectors.
#[derive(Debug, PartialEq, Clone)]
pub struct StateDiffBase<T>
where
    T: Add + Sub<Output = T> + Ord + Clone,
{
    pub data: Vec<T>,
}

pub type StateDiff = StateDiffBase<Int>;
// Useful for min/max bounds where default is either +- infinity.
pub type StateDiffBound = StateDiffBase<Infinitable<Int>>;

impl From<&StateDiff> for StateDiffBound {
    fn from(sd: &StateDiff) -> StateDiffBound {
        StateDiffBound {
            data: sd.data.iter().map(|x| Finite(*x)).collect(),
        }
    }
}

impl<T> StateDiffBase<T>
where
    T: Add + Sub<Output = T> + Ord + Clone,
{
    pub fn new(data: Vec<T>) -> Self {
        Self { data }
    }

    pub fn pointwise_max(&self, other: &Self) -> Self {
        self.map_with(other, |(a, b)| cmp::max(a, b).clone())
    }
    pub fn pointwise_min(&self, other: &Self) -> Self {
        self.map_with(other, |(a, b)| cmp::min(a, b).clone())
    }

    // Apply `func` pointwise to all pairs of elements in self and other.
    // Used to define most operations (+,-,min,max)
    fn map_with(&self, other: &Self, func: fn((&T, &T)) -> T) -> Self {
        assert!(self.data.len() == other.data.len());
        let data: Vec<T> = self.data.iter().zip(other.data.iter()).map(func).collect();
        Self { data }
    }
}

impl StateDiffBound {
    pub fn new_max(size: usize) -> Self {
        Self {
            data: vec![Infinity; size],
        }
    }
    pub fn new_min(size: usize) -> Self {
        Self {
            data: vec![NegativeInfinity; size],
        }
    }
}

impl AddAssign for StateDiff {
    fn add_assign(&mut self, other: StateDiff) {
        self.add_assign(&other);
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

impl Add<StateDiff> for &StateDiff {
    type Output = StateDiff;

    fn add(self, other: StateDiff) -> StateDiff {
        self.add(&other)
    }
}

impl<T> Sub for &StateDiffBase<T>
where
    T: Add + Sub<Output = T> + Ord + Clone,
{
    type Output = StateDiffBase<T>;

    fn sub(self, other: Self) -> Self::Output {
        self.map_with(other, |(a, b)| a.clone() - b.clone())
    }
}

impl Mul<Int> for &StateDiff {
    type Output = StateDiff;

    fn mul(self, other: Int) -> StateDiff {
        StateDiff {
            data: self.data.iter().map(|a| a * other).collect(),
        }
    }
}

impl<T> PartialOrd for StateDiffBase<T>
where
    T: Add + Sub<Output = T> + Ord + Clone,
{
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
            // All equal
            (Ordering::Equal, Ordering::Equal) => Some(Ordering::Equal),
            // Some less, some greater -> not comparible
            (Ordering::Less, Ordering::Greater) => None,
            // All ≤
            (Ordering::Less, _) => Some(Ordering::Less),
            // All ≥
            (_, Ordering::Greater) => Some(Ordering::Greater),
            // Impossible, but compiler doesn't know that.
            _ => None,
        }
    }
}

#[macro_export]
macro_rules! sd {
    ($($x:expr),* $(,)?) => {
        StateDiff::new(vec![$($x),*])
    };
}

#[macro_export]
macro_rules! sdb {
    ($($x:expr),* $(,)?) => {
        StateDiffBound::new(vec![$($x),*])
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

        let d = sd![1, 2, 3];
        assert!(a <= d);
        assert!(b <= d);
        assert!(c <= d);
    }

    #[test]
    fn test_order_bound() {
        let min = StateDiffBound::new_min(3);
        let max = StateDiffBound::new_max(3);
        let x = StateDiffBound::from(&sd![10, -20, 0]);
        assert!(min <= max);
        assert!(min <= x);
        assert!(x <= max);
    }
}
