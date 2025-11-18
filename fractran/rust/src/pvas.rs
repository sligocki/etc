pub type Int = i64;

// Fractran/pVAS configuration state
#[derive(Debug)]
pub struct State {
    data: Vec<Int>,
}

// Fractran/pVAS rule ()
#[derive(Debug)]
pub struct Rule {
    data: Vec<Int>,
}

#[derive(Debug)]
pub struct Program {
    pub rules: Vec<Rule>,
}

#[derive(Debug)]
pub struct SimResult {
    pub halted: bool,
    pub total_steps: Int,
}

impl State {
    // Initial state (scaled to number of registers of program).
    pub fn start(prog: &Program) -> State {
        let num_regs = prog.num_registers();
        let mut state = vec![0 as Int; num_regs];
        state[0] = 1;
        State { data: state }
    }
}

impl Rule {
    pub fn new(data: Vec<Int>) -> Rule {
        Rule {data}
    }

    pub fn num_registers(&self) -> usize {
        self.data.len()
    }

    pub fn can_apply(&self, state: &State) -> Result<(), usize> {
        for (i, (val, delta)) in state.data.iter().zip(self.data.iter()).enumerate() {
            if val + delta < 0 {
                return Err(i);
            }
        }
        return Ok(());
    }
    pub fn apply(&self, state: &mut State) {
        for (val, delta) in state.data.iter_mut().zip(self.data.iter()) {
            *val += delta;
        }
    }
}

impl Program {
    pub fn num_rules(&self) -> usize {
        self.rules.len()
    }
    pub fn num_registers(&self) -> usize {
        self.rules.first().expect("Program has rules").num_registers()
    }

    // Returns true if a rule was applied, false if halted.
    #[inline(always)]
    pub fn step(&self, state: &mut State) -> bool {
        for rule in self.rules.iter() {
            if rule.can_apply(state).is_ok() {
                rule.apply(state);
                return true;
            }
        }
        false // No rules applied -> HALT
    }

    // Returns Some(steps) if halted in steps or None if not halted after num_steps.
    #[inline(always)]
    pub fn run(&self, state: &mut State, num_steps: Int) -> SimResult {
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
