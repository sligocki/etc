// Objects for expressing constraints on integer values.
// Useful for the pre-conditions for Rules.
// Things like: x >= 4, x == 1, x % 2 == 1

use crate::program::Int;

// A magnitude constraint. Restricts the size of the integer.
pub enum MagnitudeCon {
    // Any value allowed
    Unconstrained,
    // value == constant
    Equals(Int),
    // value >= constant
    Min(Int),
}

// General constraint. Includes
pub struct Constraint {
    pub mag: MagnitudeCon,
    // TODO: Add Modularity constraints like x % 2 == 1, allow multiple
    // TODO: Allow cross register constraints like x > y + 1? That will be hard ...
}

pub enum ConstraintResult {
    // Value successfully passes constraints
    Success,
    // Value failed a constraint, returned is the alternative cosntraint that matches it.
    // This returned cosntraint matches value, but has no overlap with the original constraint.
    // In other words, as long as the new constraint succeeds, we know the original constraint would fail.
    Failure(Constraint),
}

impl MagnitudeCon {
    pub fn eval(&self, val: Int) -> ConstraintResult {
        let success = match self {
            MagnitudeCon::Unconstrained => true,
            MagnitudeCon::Equals(c) => *c == val,
            MagnitudeCon::Min(c) => *c <= val,
        };
        if success {
            ConstraintResult::Success
        } else {
            ConstraintResult::Failure(Constraint {
                mag: MagnitudeCon::Equals(val),
            })
        }
    }
}
