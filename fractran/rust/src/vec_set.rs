// Structures representing subsets of the Natural numbers (and vector spaces over them).
//
// VecSets are sets of Fractran states.
//
// These could be used as preconditions for rules or building up CTL sets, etc.

use std::str::FromStr;

use crate::program::{Instr, SmallInt};

// Represents a subset of the natural numbers (0, 1, 2, ...)
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum NatSet {
    // Fixed(n) = {n} is a set containing only one value, n
    Fixed(SmallInt),
    // Min(n) = [n, inf) is a set containing all integers ≥ n
    Min(SmallInt),
}

#[derive(Debug, PartialEq, Clone)]
struct SplitAddResult {
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

    // X.add(v) = {x+v | x in X}
    // Does not check if all results are valid (>= 0).
    fn add(self, v: SmallInt) -> NatSet {
        match self {
            // {n} + v = {n+v}
            NatSet::Fixed(n) => NatSet::Fixed(n + v),
            // [n, inf) + v = [n+v, inf)
            NatSet::Min(n) => NatSet::Min(n + v),
        }
    }

    // Partition a NatSet into part above (>=) `thresh` value and part below (<).
    fn partition(self, thresh: SmallInt) -> (Option<NatSet>, Vec<NatSet>) {
        match self {
            // n >= thresh -> all of {n} is above
            NatSet::Fixed(n) if n >= thresh => (Some(self), vec![]),
            // n < thresh -> all of {n} is below
            NatSet::Fixed(_) => (None, vec![self]),
            // n >= thresh -> all of [n, inf) is above
            NatSet::Min(n) if n >= thresh => (Some(self), vec![]),
            // n < thresh -> mixed results:
            //      Above: [thresh, inf)
            //      Below: {n, n+1, ..., thresh-1}
            NatSet::Min(n) => (
                Some(NatSet::Min(thresh)),
                (n..thresh).map(NatSet::Fixed).collect(),
            ),
        }
    }

    // Try adding v (posibly negative) to NatSet X. Returns "success" and "failure" results.
    //      Success: Valid result of addition: {x+v | x in X and x+v >= 0}
    //      Failure: Values from original set that cannot be added to: {x in X | x+v < 0}
    fn split_add(self, v: SmallInt) -> SplitAddResult {
        let (above, below) = self.partition(-v);
        SplitAddResult {
            success: above.map(|ns| ns.add(v)),
            failure: below,
        }
    }
}

impl FromStr for NatSet {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = s.trim();
        if let Some(n_str) = s.strip_suffix('+') {
            // "8+" -> Min(8)
            let n = n_str.parse::<SmallInt>().map_err(|e| e.to_string())?;
            Ok(NatSet::Min(n))
        } else {
            // "13" -> Fixed(13)
            let n = s.parse::<SmallInt>().map_err(|e| e.to_string())?;
            Ok(NatSet::Fixed(n))
        }
    }
}

// Represents a subset of vectors N^k by the cartesian product of NatSets.
#[derive(Debug, PartialEq, Clone)]
pub struct VecSet(Vec<NatSet>);

#[derive(Debug, PartialEq, Clone)]
struct SplitApplyResult {
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
    fn split_apply(&self, instr: &Instr) -> SplitApplyResult {
        let split_add_res: Vec<SplitAddResult> = self
            .0
            .iter()
            .zip(instr.data.iter())
            .map(|(x, v)| x.split_add(*v))
            .collect();
        // Collect the combination of all successfull NatSets.
        // Or if any are None, this will be None.
        let success: Option<Vec<NatSet>> = split_add_res.iter().map(|r| r.success).collect();
        match success {
            None => SplitApplyResult {
                success: None,
                failure: vec![self.clone()],
            },
            Some(success) => {
                let mut failure = Vec::new();
                for (reg_num, res) in split_add_res.iter().enumerate() {
                    for nat_set in res.failure.iter() {
                        failure.push(self.update(reg_num, *nat_set))
                    }
                }
                SplitApplyResult {
                    success: Some(VecSet(success)),
                    failure,
                }
            }
        }
    }

    // Return collection of all successor configs after taking one step using `prog`.
    // If any config in VecSet halts, return None.
    pub fn successors(&self, instrs: &[Instr]) -> Option<Vec<VecSet>> {
        match instrs {
            // If we are trying to apply no instructions that means all configs in `self` will halt.
            [] => None,
            [instr, rest @ ..] => {
                let res = self.split_apply(instr);
                // Recursive call on all failures. If this instr did not apply, try following ones.
                let after = (res.failure.into_iter())
                    .map(|vs| vs.successors(rest))
                    // This collapses Iterator<Option<Vec<VecSet>>> into Option<Vec<Vec<VecSet>>>
                    // which is None if any of the successors were None.
                    // In other words None if any configs in vs are halting.
                    .collect::<Option<Vec<_>>>();
                let mut next: Vec<VecSet> = after?.into_iter().flatten().collect();
                if let Some(vs) = res.success {
                    next.push(vs);
                }
                Some(next)
            }
        }
    }
}

// Light syntax for writing VecSets
// vec_set!["1", "2+"] = VecSet(vec![NatSet::Fixed(1), NatSet::Min(2)])
#[macro_export]
macro_rules! vec_set {
    ($($val:expr),* $(,)?) => {{
        use std::str::FromStr;
        $crate::vec_set::VecSet(vec![
            $( $crate::vec_set::NatSet::from_str($val).expect("Invalid NatSet format") ),*
        ])
    }};
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::program::Program;
    use crate::{prog, rule};

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
        let v = vec_set!["13", "8+", "31+"];
        assert_eq!(
            v.clone().split_apply(&rule![100, 200, 300]),
            SplitApplyResult {
                success: Some(vec_set!["113", "208+", "331+"]),
                failure: vec![],
            }
        );
        assert_eq!(
            v.clone().split_apply(&rule![-1, -1, -1]),
            SplitApplyResult {
                success: Some(vec_set!["12", "7+", "30+"]),
                failure: vec![],
            }
        );
        assert_eq!(
            v.clone().split_apply(&rule![-20, 0, 0]),
            SplitApplyResult {
                success: None,
                failure: vec![v.clone()],
            }
        );
        assert_eq!(
            v.clone().split_apply(&rule![0, -10, 0]),
            SplitApplyResult {
                success: Some(vec_set!["13", "0+", "31+"]),
                failure: vec![vec_set!["13", "8", "31+"], vec_set!["13", "9", "31+"],],
            }
        );
        assert_eq!(
            v.clone().split_apply(&rule![1, -10, -34]),
            SplitApplyResult {
                success: Some(vec_set!["14", "0+", "0+"]),
                failure: vec![
                    vec_set!["13", "8", "31+"],
                    vec_set!["13", "9", "31+"],
                    // TODO: Remove overlaps here? Switch the 8+ below to 10+?
                    vec_set!["13", "8+", "31"],
                    vec_set!["13", "8+", "32"],
                    vec_set!["13", "8+", "33"],
                ],
            }
        );
    }

    #[test]
    fn test_successors() {
        // A complex Collatz-like non-halting program.
        // [2/45, 25/6, 343/2, 9/7, 2/3]
        let p = prog![
             1, -2, -1,  0;
            -1, -1,  2,  0;
            -1,  0,  0,  3;
             0,  2,  0, -1;
             1, -1,  0,  0;
        ];
        let instrs = &p.instrs;

        // [0 46+ 0 0] -> [1 45+ 0 0] -> [0 44+ 2 0]
        let a = vec_set!["0", "46+", "0", "0"];
        let b = vec_set!["1", "45+", "0", "0"];
        let c = vec_set!["0", "44+", "2", "0"];
        assert_eq!(a.successors(&instrs), Some(vec![b.clone()]));
        assert_eq!(b.successors(&instrs), Some(vec![c]));

        // [10+ 0+ 0 0]:
        //      [10+ 0 0 0] -> [9+ 0 0 3]
        //      [10+ 1+ 0 0] -> [9+ 0+ 2 0]
        let a = vec_set!["10+", "0+", "0", "0"];
        let b = vec_set!["9+", "0", "0", "3"];
        let c = vec_set!["9+", "0+", "2", "0"];
        assert_eq!(a.successors(&instrs), Some(vec![b, c]));

        // [9+ 0+ 2 0]:
        //      [9+ 0 2 0] -> [8+ 0 2 3]
        //      [9+ 1 2 0] -> [8+ 0 4 0]
        //      [9+ 2+ 2 0] -> [10+ 0+ 1 0]
        let a = vec_set!["9+", "0+", "2", "0"];
        let b = vec_set!["8+", "0", "2", "3"];
        let c = vec_set!["8+", "0", "4", "0"];
        let d = vec_set!["10+", "0+", "1", "0"];
        assert_eq!(a.successors(&instrs), Some(vec![b, c, d]));
    }
}
