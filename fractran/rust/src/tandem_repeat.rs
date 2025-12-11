// Library for identifying and compressing "tandem repeats" or sections of a message that repeat back-to-back.

use std::cmp;

use itertools::Itertools;

const MIN_REPEATS: usize = 2;
const MAX_WINDOW: usize = 100;

pub trait ToStringVec: Sized {
    fn to_string_one(&self) -> String;
    fn to_string_vec(xs: &Vec<Self>) -> String;
}

#[derive(Debug, PartialEq, Clone)]
pub struct RepBlock<T: PartialEq + Clone + ToStringVec> {
    pub block: Vec<T>,
    pub rep: usize,
}

impl<T: PartialEq + Clone + ToStringVec> ToStringVec for RepBlock<T> {
    fn to_string_one(&self) -> String {
        let mut ret = T::to_string_vec(&self.block);
        if self.rep != 1 {
            ret.push_str(&format!("^{}", self.rep));
        }
        ret
    }

    fn to_string_vec(xs: &Vec<Self>) -> String {
        xs.iter().map(|x| x.to_string_one()).join(" ")
    }
}

// Find repeated blocks and parse into RepBlock format.
pub fn find_rep_blocks<T: PartialEq + Clone + ToStringVec>(data: &[T]) -> Vec<RepBlock<T>> {
    let repeats = find_repeat_info(data);
    as_rep_blocks(data, repeats)
}

pub fn as_rep_blocks<T: PartialEq + Clone + ToStringVec>(
    data: &[T],
    repeats: Vec<RepeatInfo>,
) -> Vec<RepBlock<T>> {
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
#[derive(Debug, PartialEq, Clone)]
pub struct RepeatInfo {
    pub start: usize,
    pub period: usize,
    pub count: usize,
}

impl RepeatInfo {
    pub fn size(&self) -> usize {
        self.period * self.count
    }
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

/// Summary statistics about repeats from a Vec<RepeatInfo>
#[derive(Debug, PartialEq, Clone)]
pub struct RepBlockStats {
    /// Number of repeated blocks (with rep >= 2)
    pub num_blocks: usize,
    /// Maximum tandom repeat of across all blocks
    pub max_rep: usize,
    /// Fraction of message that is part of a block (with rep >= 2)
    pub frac_in_reps: f32,
    /// Fraction of message that is part of largest block
    pub frac_in_max_block: f32,
}

pub fn rep_stats(rep_info: &Vec<RepeatInfo>, data_size: usize) -> RepBlockStats {
    let size_in_reps: usize = rep_info.iter().map(|x| x.size()).sum();

    let max_block = rep_info.iter().max_by_key(|x| x.count);
    let max_rep = max_block.map_or(0, |x| x.count);
    let size_in_max_block = max_block.map_or(0, |x| x.size());

    RepBlockStats {
        num_blocks: rep_info.len(),
        max_rep,
        frac_in_reps: (size_in_reps as f32) / (data_size as f32),
        frac_in_max_block: (size_in_max_block as f32) / (data_size as f32),
    }
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
