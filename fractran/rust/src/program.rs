use rug;

// Small int and big int
pub type SmallInt = i32;
pub type BigInt = rug::Integer;

// Fractran/pVAS configuration state
#[derive(Debug, Clone, PartialEq)]
pub struct State {
    pub data: Vec<BigInt>,
}

// Fractran/pVAS instruction
#[derive(Debug, Clone, PartialEq)]
pub struct Instr {
    pub data: Vec<SmallInt>,
}

#[derive(Debug)]
pub struct Program {
    pub instrs: Vec<Instr>,
}

#[derive(Debug)]
pub struct SimResult {
    pub halted: bool,
    pub total_steps: usize,
}

impl State {
    pub fn new(data: Vec<BigInt>) -> State {
        State { data }
    }

    // Initial state (scaled to number of registers of program).
    pub fn start(prog: &Program) -> State {
        let num_regs = prog.num_registers();
        let mut state = vec![0.into(); num_regs];
        state[0] = 1.into();
        State { data: state }
    }
}

impl Instr {
    pub fn new(data: Vec<SmallInt>) -> Instr {
        Instr { data }
    }

    pub fn num_registers(&self) -> usize {
        self.data.len()
    }

    // Evaluate if it is possible to apply this rule to a state.
    // If not, returns the first register index that fails (would go negative).
    // This is useful for inductive deciders to understand which register condition failed.
    pub fn can_apply(&self, state: &State) -> Result<(), usize> {
        for (i, (val, delta)) in state.data.iter().zip(self.data.iter()).enumerate() {
            if *val < -delta {
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
    pub fn num_instrs(&self) -> usize {
        self.instrs.len()
    }
    pub fn num_registers(&self) -> usize {
        self.instrs
            .first()
            .expect("Program has instrs")
            .num_registers()
    }

    // Returns true if a instruction was applied, false if halted.
    #[inline(always)]
    pub fn step(&self, state: &mut State) -> bool {
        for rule in self.instrs.iter() {
            if rule.can_apply(state).is_ok() {
                rule.apply(state);
                return true;
            }
        }
        false // No instrs applied -> HALT
    }

    #[inline(always)]
    pub fn run(&self, state: &mut State, num_steps: usize) -> SimResult {
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

#[macro_export]
macro_rules! state {
    ($($x:expr),* $(,)?) => {
        $crate::program::State::new(vec![$($x.into()),*])
    };
}

#[macro_export]
macro_rules! rule {
    ($($x:expr),* $(,)?) => {
        $crate::program::Instr::new(vec![$($x),*])
    };
}

// let p = prog![ 1, -1, -1;
//               -1,  2,  0;
//                0,  1, -2];
#[macro_export]
macro_rules! prog {
    // The pattern matches rows separated by semicolons (;).
    // Inside each row, expressions are separated by commas (,).
    // $(;)? allows for an optional trailing semicolon.
    ( $( $( $x:expr ),* );* ) => {
        $crate::program::Program { instrs: vec![
            $(
                $crate::program::Instr::new(vec![ $( $x ),* ])
            ),*
        ] }
    }
}

// TODO: Add tests
// #[cfg(test)]
// mod tests {
//     use super::*;

//     #[test]
//     fn test_foo() {}
// }
