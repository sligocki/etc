use crate::tag_system::TagSystem;

fn enum_lengths(
    n: usize,
    remaining: usize,
    current: &mut [usize],
    index: usize,
    callback: &mut impl FnMut(&[usize]),
) {
    if index == n - 1 {
        current[index] = remaining;
        callback(current);
        return;
    }
    for i in 0..=remaining {
        current[index] = i;
        enum_lengths(n, remaining - i, current, index + 1, callback);
    }
}

fn enum_strings(
    n: usize,
    lens: &[usize],
    current: &mut [u8],
    index: usize,
    max_seen: u8,
    callback: &mut impl FnMut(&[u8]),
) {
    if index == lens[0] && max_seen == 0 {
        // Prune! If w_0 does not contain '1', then since the initial tape is purely '0's,
        // no other symbol will ever be reached. 
        // Such systems either halt in 1 step (if |w_0| < v) or loop forever (if |w_0| >= v).
        return;
    }

    if index == current.len() {
        callback(current);
        return;
    }

    let limit = std::cmp::min(n as u8 - 1, max_seen + 1);
    for c in 0..=limit {
        current[index] = c;
        let next_max = std::cmp::max(max_seen, c);
        enum_strings(n, lens, current, index + 1, next_max, callback);
    }
}

pub fn enumerate_systems(v: usize, s: usize, callback: &mut impl FnMut(TagSystem)) {
    for n in 1..=s {
        let mut lengths = vec![0; n];
        let remaining = s - n;
        enum_lengths(n, remaining, &mut lengths, 0, &mut |lens| {
            let mut string_buf = vec![0u8; remaining];
            enum_strings(n, lens, &mut string_buf, 0, 0, &mut |chars| {
                let mut rules = vec![vec![]; n];
                let mut char_idx = 0;
                for r in 0..n {
                    for _ in 0..lens[r] {
                        rules[r].push(chars[char_idx]);
                        char_idx += 1;
                    }
                }
                callback(TagSystem { v, rules });
            });
        });
    }
}
