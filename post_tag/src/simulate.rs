use crate::tag_system::TagSystem;

#[derive(Debug, Clone, Copy)]
pub enum InfiniteReason {
    Cycle(usize), // period
    ImmortalSubstring,
    NonDecreasingSymbol(u8),
}

#[derive(Debug, Clone, Copy)]
pub enum HaltCondition {
    Halted(usize, usize), // steps, max_length
    Infinite(InfiniteReason, usize), // reason, steps taken to detect
    Unknown,
    UndefinedRule(u8),
}

impl TagSystem {
    pub fn simulate_fast(&self, max_steps: usize) -> HaltCondition {
        let mut tape = vec![0u8; self.v];
        let mut head_idx = 0;
        let mut steps = 0;
        let mut max_len = self.v;

        let mut saved_tape = Vec::with_capacity(64);
        saved_tape.extend_from_slice(&tape);
        let mut power = 1;
        let mut lam = 0;

        while tape.len() - head_idx >= self.v {
            if steps >= max_steps {
                return HaltCondition::Unknown;
            }
            steps += 1;
            lam += 1;
            
            let head = tape[head_idx];
            head_idx += self.v;

            let rule = match &self.rules[head as usize] {
                Some(r) => r,
                None => return HaltCondition::UndefinedRule(head),
            };

            for &c in rule {
                tape.push(c);
            }

            let current_len = tape.len() - head_idx;
            if current_len > max_len {
                max_len = current_len;
            }

            if current_len == saved_tape.len() && tape[head_idx..] == saved_tape[..] {
                return HaltCondition::Infinite(InfiniteReason::Cycle(lam), steps);
            }

            if lam == power {
                power *= 2;
                lam = 0;
                // Only take snapshots if the tape is reasonably sized to prevent slow O(N) memcpys
                if current_len < 10_000 {
                    saved_tape.clear();
                    saved_tape.extend_from_slice(&tape[head_idx..]);
                }
            }

            // Keep memory bounded
            if head_idx > 1_000_000 {
                tape.drain(0..head_idx);
                head_idx = 0;
            }
        }

        HaltCondition::Halted(steps, max_len)
    }

    pub fn simulate_verbose(&self, max_steps: usize) -> HaltCondition {
        let mut tape = vec![0u8; self.v];
        let mut head_idx = 0;
        let mut steps = 0;
        let mut max_len = self.v;

        let mut saved_tape = Vec::with_capacity(64);
        saved_tape.extend_from_slice(&tape);
        let mut power = 1;
        let mut lam = 0;

        while tape.len() - head_idx >= self.v {
            if steps >= max_steps {
                return HaltCondition::Unknown;
            }
            
            print!("Step {}: Tape ", steps);
            if tape.len() == head_idx {
                println!("eps");
            } else {
                for i in head_idx..tape.len() {
                    print!("{}", tape[i]);
                }
                println!();
            }

            steps += 1;
            lam += 1;
            
            let head = tape[head_idx];
            head_idx += self.v;

            let rule = match &self.rules[head as usize] {
                Some(r) => r,
                None => return HaltCondition::UndefinedRule(head),
            };

            for &c in rule {
                tape.push(c);
            }

            let current_len = tape.len() - head_idx;
            if current_len > max_len {
                max_len = current_len;
            }

            if current_len == saved_tape.len() && tape[head_idx..] == saved_tape[..] {
                println!("Exact cycle of period {} detected!", lam);
                return HaltCondition::Infinite(InfiniteReason::Cycle(lam), steps);
            }

            if lam == power {
                power *= 2;
                lam = 0;
                if current_len < 10_000 {
                    saved_tape.clear();
                    saved_tape.extend_from_slice(&tape[head_idx..]);
                }
            }

            // Keep memory bounded
            if head_idx > 1_000_000 {
                tape.drain(0..head_idx);
                head_idx = 0;
            }
        }
        
        print!("Step {}: Tape ", steps);
        if tape.len() == head_idx {
            println!("eps");
        } else {
            for i in head_idx..tape.len() {
                print!("{}", tape[i]);
            }
            println!();
        }

        HaltCondition::Halted(steps, max_len)
    }

    pub fn is_immortal_substring(v: usize, rules: &[Option<Vec<u8>>], w: &[u8]) -> Option<bool> {
        if w.len() < v {
            return Some(false);
        }
        for k in 0..v {
            let p = (v - ((k + w.len()) % v)) % v;
            let l = k + w.len() + p;
            let n = rules.len();
            let num_left = n.pow(k as u32);
            let num_right = n.pow(p as u32);
            
            for left_val in 0..num_left {
                for right_val in 0..num_right {
                    let mut s = Vec::with_capacity(l);
                    
                    let mut lv = left_val;
                    for _ in 0..k {
                        s.push((lv % n) as u8);
                        lv /= n;
                    }
                    
                    s.extend_from_slice(w);
                    
                    let mut rv = right_val;
                    for _ in 0..p {
                        s.push((rv % n) as u8);
                        rv /= n;
                    }
                    
                    let mut w_out = Vec::new();
                    // Initial minimum guaranteed tape length is the unread part of w and left padding
                    let mut current_len = k + w.len(); 
                    
                    for i in (0..l).step_by(v) {
                        let c = s[i];
                        if let Some(rule) = &rules[c as usize] {
                            // Tape dips by v, grows by rule.len()
                            // If current_len < v before we read, it would halt!
                            // But wait, the blocks we are reading MUST be on the tape.
                            // The real question is: after reading this block, does the tape length
                            // dip below v, which would prevent reading the NEXT block (if there is one)?
                            // Or if this is the last block, does it dip below v preventing future steps?
                            if current_len < v {
                                return Some(false); // Dips and halts
                            }
                            current_len = current_len - v + rule.len();
                            w_out.extend_from_slice(rule);
                        } else {
                            return None;
                        }
                    }
                    
                    // After processing all blocks, net length must not decrease
                    if w_out.len() < l {
                        return Some(false);
                    }
                    
                    // The length of the tape after processing all blocks is at least w_out.len() - p
                    // Wait, current_len already tracks this exactly!
                    // current_len at the end is exactly the guaranteed length after processing.
                    if current_len < v {
                        return Some(false);
                    }
                    
                    let slice_to_check = if p <= w_out.len() {
                        &w_out[p..]
                    } else {
                        &[]
                    };
                    
                    if slice_to_check.windows(w.len()).all(|window| window != w) {
                        return Some(false);
                    }
                }
            }
        }
        Some(true)
    }

    pub fn has_immortal_substring(&self) -> bool {
        for rule_opt in &self.rules {
            if let Some(rule) = rule_opt {
                if rule.len() < self.v {
                    continue;
                }
                for len in self.v..=rule.len() {
                    for i in 0..=(rule.len() - len) {
                        let w = &rule[i..i+len];
                        if Self::is_immortal_substring(self.v, &self.rules, w) == Some(true) {
                            return true;
                        }
                    }
                }
            }
        }
        false
    }

    pub fn has_non_decreasing_symbol(&self) -> Option<u8> {
        let n = self.rules.len();
        for c in 0..n {
            let mut is_non_decreasing = true;
            for h in 0..n {
                if let Some(rule) = &self.rules[h] {
                    let count = rule.iter().filter(|&&x| x == c as u8).count();
                    let required = if h == c { self.v } else { self.v.saturating_sub(1) };
                    if count < required {
                        is_non_decreasing = false;
                        break;
                    }
                } else {
                    is_non_decreasing = false;
                    break;
                }
            }
            if is_non_decreasing {
                if c == 0 {
                    return Some(c as u8);
                }
            }
        }
        None
    }
}
