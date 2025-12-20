// CTL using unions of VecSets.
//
// A ClosedVecSet is a collection of VecSets such that from every Fractran state in one
// of those sets, it has a successor state also in one of the sets.
//
// Thus, if the program ever enters this ClosedVecSet, it can never leave and can never halt.

use crate::program::Program;
use crate::vec_set::UnionVecSet;

#[derive(Debug, PartialEq)]
pub enum ClosureResult {
    // The set contains a halting config.
    ContainsHalt,
    // The set is closed under program step.
    Closed(UnionVecSet),
    // Iterated too many times without set closing.
    GaveUp(UnionVecSet),
}

// Extend `set` to all successors iteratively until it:
// Becomes closed, contains a halt, or we give up trying.
pub fn closure(prog: &Program, set: &UnionVecSet, num_iters: usize) -> ClosureResult {
    // Total accumulated closure.
    let mut result = set.clone();
    // Subset added in last iteration.
    let mut frontier = set.clone();
    for _ in 0..num_iters {
        // Load all successors of all configs added in previous iteration.
        match frontier.successors(&prog.instrs) {
            None => {
                return ClosureResult::ContainsHalt;
            }
            Some(succ) => {
                // Subset down to only ones that are actually new.
                let next = succ.minus_covered(&result);
                if next.is_empty() {
                    return ClosureResult::Closed(result);
                }
                result = result.union(frontier);
                frontier = next;
            }
        }
    }
    ClosureResult::GaveUp(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{prog, vec_set};

    #[test]
    fn test_complex() {
        // A complex Collatz-like non-halting program.
        // [2/45, 25/6, 343/2, 9/7, 2/3]
        let p = prog![
             1, -2, -1,  0;
            -1, -1,  2,  0;
            -1,  0,  0,  3;
             0,  2,  0, -1;
             1, -1,  0,  0;
        ];

        let seed = UnionVecSet::new(vec![
            vec_set!["10+", "0+", "0", "0"],
            vec_set!["0+", "0", "0+", "24+"],
            vec_set!["0", "46+", "0", "0+"],
        ]);
        let result = closure(&p, &seed, 100);
        assert!(matches!(result, ClosureResult::Closed(_)));
    }
}
