use crate::simulate::{simulate, HaltCondition, InfiniteReason};
use crate::tag_system::TagSystem;

fn enum_lengths(
    n: usize,
    remaining: usize,
    current: &mut [usize],
    index: usize,
    v: usize,
    callback: &mut impl FnMut(&[usize]),
) {
    if index == n - 1 {
        current[index] = remaining;
        if current.iter().any(|&l| l < v) {
            callback(current);
        }
        return;
    }
    for i in 0..=remaining {
        current[index] = i;
        enum_lengths(n, remaining - i, current, index + 1, v, callback);
    }
}

fn enum_strings_adaptive(
    n: usize,
    len: usize,
    current: &mut [u8],
    index: usize,
    max_seen: u8,
    callback: &mut impl FnMut(&[u8], u8),
) {
    if index == len {
        callback(current, max_seen);
        return;
    }

    let limit = std::cmp::min(n as u8 - 1, max_seen + 1);
    for c in 0..=limit {
        current[index] = c;
        let next_max = std::cmp::max(max_seen, c);
        enum_strings_adaptive(n, len, current, index + 1, next_max, callback);
    }
}

fn is_valid_reachability(sys: &TagSystem) -> bool {
    let mut reachable = vec![false; sys.rules.len()];
    let mut queue = vec![0];
    reachable[0] = true;

    while let Some(r) = queue.pop() {
        if let Some(w) = &sys.rules[r as usize] {
            for &c in w {
                if !reachable[c as usize] {
                    reachable[c as usize] = true;
                    queue.push(c);
                }
            }
        } else {
            // Reached an undefined rule. The closure is open.
            return true;
        }
    }

    // Closure is fully defined. It is only valid if ALL n symbols are reachable.
    // If not, it's equivalent to a smaller program (padding).
    reachable.iter().all(|&b| b)
}

fn explore_adaptive(
    sys: &mut TagSystem,
    lens: &[usize],
    max_steps: usize,
    max_seen: u8,
    callback: &mut impl FnMut(&TagSystem, HaltCondition),
) {
    if let Some(w) = sys.has_immortal_substring() {
        callback(sys, HaltCondition::Infinite(InfiniteReason::ImmortalSubstring(w.clone()), 0));
        return;
    }

    match simulate(sys, max_steps, false) {
        HaltCondition::UndefinedRule(c) => {
            let l = lens[c as usize];
            let mut string_buf = vec![0u8; l];
            enum_strings_adaptive(sys.rules.len(), l, &mut string_buf, 0, max_seen, &mut |chars, new_max_seen| {
                // Prune w_0 must contain '1' if n > 1
                if c == 0 && new_max_seen == 0 && sys.rules.len() > 1 {
                    return;
                }

                sys.rules[c as usize] = Some(chars.to_vec());
                if is_valid_reachability(sys) {
                    explore_adaptive(sys, lens, max_steps, new_max_seen, callback);
                }
                sys.rules[c as usize] = None; // Backtrack
            });
        }
        condition => {
            callback(sys, condition);
        }
    }
}

pub fn enumerate_systems(
    v: usize,
    s: usize,
    max_steps: usize,
    callback: &mut impl FnMut(&TagSystem, HaltCondition),
) {
    for n in 1..=s {
        let mut lengths = vec![0; n];
        let remaining = s - n;
        enum_lengths(n, remaining, &mut lengths, 0, v, &mut |lens| {
            let mut sys = TagSystem {
                v,
                rules: vec![None; n],
            };
            explore_adaptive(&mut sys, lens, max_steps, 0, callback);
        });
    }
}
