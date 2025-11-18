pub type Int = i64;

#[derive(Debug)]
pub struct PVAS {
    // Flattened rule matrix: [r1_v1, r1_v2, ..., r2_v1, r2_v2, ...]
    // Made public for debugging if needed, though typically internal.
    pub rules: Vec<Int>,
    // Number of registers (columns)
    pub dims: usize,
    // Number of rules (rows)
    pub num_rules: usize,
}

#[derive(Debug)]
pub struct SimResult {
    pub halted: bool,
    pub total_steps: Int,
}

impl PVAS {
    pub fn new(rules: Vec<Int>, dims: usize, num_rules: usize) -> Self {
        PVAS {
            rules,
            dims,
            num_rules,
        }
    }

    // The hot loop.
    // Returns true if a rule was applied, false if halted.
    #[inline(always)]
    pub fn step(&self, state: &mut [Int]) -> bool {
        // Iterate through rules (rows)
        'rule_loop: for r in 0..self.num_rules {
            let offset = r * self.dims;

            // 1. Check Phase: Can this rule apply?
            // We manually iterate to avoid bounds checks and iterator overhead
            for c in 0..self.dims {
                let val = unsafe { *state.get_unchecked(c) };
                let delta = unsafe { *self.rules.get_unchecked(offset + c) };

                if val + delta < 0 {
                    continue 'rule_loop; // Rule failed, try next rule
                }
            }

            // 2. Apply Phase: Update state
            // If we are here, the rule is valid.
            for c in 0..self.dims {
                let delta = unsafe { *self.rules.get_unchecked(offset + c) };
                // Unsafe access for speed, we know state and rules match dims
                unsafe {
                    *state.get_unchecked_mut(c) += delta;
                }
            }

            return true; // Rule applied, restart from top (handled by caller)
        }

        false // No rules applied -> HALT
    }

    // Returns Some(steps) if halted in steps or None if not halted after num_steps.
    #[inline(always)]
    pub fn run(&self, state: &mut [Int], num_steps: Int) -> SimResult {
        for step_num in 0..num_steps {
            if !self.step(state) {
                return SimResult {
                    halted: true,
                    total_steps: step_num,
                };
            }
        }

        SimResult {
            halted: false,
            total_steps: num_steps,
        }
    }
}
