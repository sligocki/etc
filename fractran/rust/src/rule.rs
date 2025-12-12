// Abstract base class for all transition rules.

use crate::program::{BigInt, State};

#[derive(Debug, PartialEq)]
pub enum ApplyResult {
    // Rule does not apply at all.
    None,
    // Rule applies a finite number of times.
    Some { num_apps: BigInt, result: State },
    // Rule applies infinitely (proof of non-halting).
    Infinite,
}

pub trait Rule {
    fn is_applicable(&self, state: &State) -> bool;
    fn apply(&self, state: &State) -> ApplyResult;
}
