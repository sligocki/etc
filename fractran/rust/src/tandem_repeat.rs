// Library for identifying and compressing "tandem repeats" or sections of a message that repeat back-to-back.

use std::cmp;

// Basic symbol set of the message
pub type Symbol = u32;

const MIN_REPEATS: usize = 3;
const MAX_WINDOW: usize = 100;

// Encodes a repeat such that data[i] = data[i + n * period] for start ≤ i < start + period and 0 ≤ n < count.
#[derive(Debug, PartialEq)]
pub struct RepeatInfo {
    pub start: usize,
    pub period: usize,
    pub count: usize,
}

pub fn find_repeats(data: &[Symbol]) -> Vec<RepeatInfo> {
    let mut repeats = Vec::new();
    let mut start = 0;
    while start < data.len() {
        if let Some(repeat) = find_repeat_prefix(&data[start..]) {
            repeats.push(RepeatInfo { start, ..repeat });
            start += repeat.period * repeat.count;
        } else {
            start += 1;
        }
    }
    repeats
}

pub fn find_repeat_prefix(data: &[Symbol]) -> Option<RepeatInfo> {
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
        let message: Vec<Symbol> = vec![13; 6];
        let result = find_repeats(&message);
        let expected = vec![RepeatInfo {
            start: 0,
            period: 1,
            count: 6,
        }];
        assert_eq!(result, expected);
    }

    #[test]
    fn test_offset() {
        let message: Vec<Symbol> = vec![1, 2, 3, 4, 3, 4, 3, 4, 1];
        let result = find_repeats(&message);
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
