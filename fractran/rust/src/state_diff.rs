// TODO: Use this in Program to implement Rule/State?

use std::cmp::{self, Ordering};
use std::ops::AddAssign;

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

    pub fn add(&self, other: &Self) -> Self {
        self.map_with(other, |(a, b)| a + b)
    }
    pub fn sub(&self, other: &Self) -> Self {
        self.map_with(other, |(a, b)| a - b)
    }

    pub fn pointwise_max(&self, other: &Self) -> Self {
        self.map_with(other, |(a, b)| cmp::max(a, b).clone())
    }
    pub fn pointwise_min(&self, other: &Self) -> Self {
        self.map_with(other, |(a, b)| cmp::min(a, b).clone())
    }

    fn map_with(&self, other: &Self, func: fn((&Int, &Int)) -> Int) -> Self {
        let data: Vec<Int> = self.data.iter().zip(other.data.iter()).map(func).collect();
        StateDiff { data }
    }
}

impl AddAssign for StateDiff {
    fn add_assign(&mut self, other: Self) {
        for (val, delta) in self.data.iter_mut().zip(other.data.iter()) {
            *val += delta;
        }
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

// TODO: Add tests
