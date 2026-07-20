use crate::tag_system::TagSystem;

#[derive(Debug, Clone, Copy)]
pub enum HaltCondition {
    Halted(usize, usize), // steps, max_length
    Infinite,
}

impl TagSystem {
    pub fn simulate_fast(&self, max_steps: usize) -> HaltCondition {
        let mut tape = vec![0u8; self.v];
        let mut head_idx = 0;
        let mut steps = 0;
        let mut max_len = self.v;

        while tape.len() - head_idx >= self.v {
            if steps >= max_steps {
                return HaltCondition::Infinite;
            }
            steps += 1;
            let head = tape[head_idx];
            head_idx += self.v;

            for &c in &self.rules[head as usize] {
                tape.push(c);
            }

            let current_len = tape.len() - head_idx;
            if current_len > max_len {
                max_len = current_len;
            }

            // Keep memory bounded
            if head_idx > 1_000_000 {
                tape.drain(0..head_idx);
                head_idx = 0;
            }
        }

        HaltCondition::Halted(steps, max_len)
    }
}
