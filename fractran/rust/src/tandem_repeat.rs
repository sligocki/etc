// Library for identifying and compressing "tandem repeats" or sections of a message that repeat back-to-back.

use std::cmp;
use std::fmt;

const MIN_REPEATS: usize = 2;
const MAX_WINDOW: usize = 100;

// pub trait DisplayVec: Sized {
//     fn fmt_one(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result;
//     fn fmt_vec(xs: &Vec::<Self>, f: &mut fmt::Formatter<'_>) -> fmt::Result;
// }

#[derive(Debug, PartialEq, Clone)]
pub struct RepBlock<T: PartialEq + Clone> {
    pub block: Vec<T>,
    pub rep: usize,
}

// impl fmt::Display for RepBlock<T> {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         write!(f, "{}", self.block)?;
//         if self.rep != 1 {
//             write!(f, "^{}", self.rep)?;
//         }
//         Ok(())
//     }
// }

// Find repeated blocks and parse into RepBlock format.
pub fn as_rep_blocks<T: PartialEq + Clone>(data: &[T]) -> Vec<RepBlock<T>> {
    let repeats = find_repeat_info(data);

    let mut ret = Vec::new();
    let mut n = 0;
    for repeat in repeats.iter() {
        if repeat.start > n {
            ret.push(RepBlock {
                block: data[n..repeat.start].to_vec(),
                rep: 1,
            });
        }
        ret.push(RepBlock {
            block: data[repeat.start..repeat.start + repeat.period].to_vec(),
            rep: repeat.count,
        });
        n = repeat.start + repeat.period * repeat.count;
    }
    if n < data.len() {
        ret.push(RepBlock {
            block: data[n..].to_vec(),
            rep: 1,
        });
    }
    ret
}

// Encodes a repeat such that data[i] = data[i + n * period] for start ≤ i < start + period and 0 ≤ n < count.
#[derive(Debug, PartialEq)]
pub struct RepeatInfo {
    pub start: usize,
    pub period: usize,
    pub count: usize,
}

pub fn find_repeat_info<T: PartialEq>(data: &[T]) -> Vec<RepeatInfo> {
    let mut repeats = Vec::new();
    let mut start = 0;
    while start < data.len() {
        if let Some(repeat) = find_repeat_info_prefix(&data[start..]) {
            repeats.push(RepeatInfo { start, ..repeat });
            start += repeat.period * repeat.count;
        } else {
            start += 1;
        }
    }
    repeats
}

fn find_repeat_info_prefix<T: PartialEq>(data: &[T]) -> Option<RepeatInfo> {
    let mut best: Option<RepeatInfo> = None;
    let mut max_coverage = 0;
    let p_max = cmp::min(MAX_WINDOW, data.len() / MIN_REPEATS);
    for period in 1..=p_max {
        let mut count = 1;
        let mut offset = period;
        while offset + period <= data.len() && data[..period] == data[offset..offset + period] {
            count += 1;
            offset += period;
        }
        let coverage = count * period;
        if count >= MIN_REPEATS && coverage > max_coverage {
            max_coverage = coverage;
            best = Some(RepeatInfo {
                start: 0,
                period,
                count,
            });
        }
    }
    best
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple() {
        let message = vec![13; 6];
        let result = find_repeat_info(&message);
        let expected = vec![RepeatInfo {
            start: 0,
            period: 1,
            count: 6,
        }];
        assert_eq!(result, expected);
    }

    #[test]
    fn test_offset() {
        let message = vec![1, 2, 3, 4, 3, 4, 3, 4, 1];
        let result = find_repeat_info(&message);
        let expected = vec![RepeatInfo {
            start: 2,
            period: 2,
            count: 3,
        }];
        assert_eq!(result, expected);
    }

    // #[test]
    // fn test_complex() {
    //     let message: Vec<Symbol> =  // TODO
    //     let result = find_repeats(&message);
    //     let expected = vec![RepeatInfo { start: 2, period: 2, count: 3 }];
    //     assert_eq!(result, expected);
    // }
}
