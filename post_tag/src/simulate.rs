use crate::tag_system::TagSystem;

#[derive(Debug, Clone, Copy)]
pub enum InfiniteReason {
    Cycle(usize), // period
}

#[derive(Debug, Clone, Copy)]
pub enum HaltCondition {
    Halted(usize, usize), // steps, max_length
    Infinite(InfiniteReason, usize), // reason, steps taken to detect
    Unknown,
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

            for &c in &self.rules[head as usize] {
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

            for &c in &self.rules[head as usize] {
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
}
