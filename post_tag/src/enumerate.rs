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

pub fn enumerate_systems(v: usize, s: usize, callback: &mut impl FnMut(TagSystem)) {
    for n in 1..=s {
        let mut lengths = vec![0; n];
        let remaining = s - n;
        enum_lengths(n, remaining, &mut lengths, 0, &mut |lens| {
            let total_chars = remaining as u32;
            let num_assignments = (n as u64).pow(total_chars);
            for mut i in 0..num_assignments {
                let mut rules = vec![vec![]; n];
                for r in 0..n {
                    for _ in 0..lens[r] {
                        let c = (i % (n as u64)) as u8;
                        rules[r].push(c);
                        i /= n as u64;
                    }
                }
                callback(TagSystem { v, rules });
            }
        });
    }
}
