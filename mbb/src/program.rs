#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Target {
    Halt,
    Inst(usize),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Instruction {
    Inc {
        reg: usize,
        next: Target,
    },
    Dec {
        reg: usize,
        next_not_zero: Target,
        next_zero: Target,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Program {
    pub instructions: Vec<Instruction>,
}

impl Target {
    pub fn to_char(self) -> char {
        match self {
            Target::Halt => '*',
            Target::Inst(idx) => (b'A' + idx as u8) as char,
        }
    }
}

impl std::fmt::Display for Instruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Instruction::Inc { reg, next } => {
                write!(f, "{}+{}", reg, next.to_char())
            }
            Instruction::Dec { reg, next_not_zero, next_zero } => {
                write!(f, "{}-{}{}", reg, next_not_zero.to_char(), next_zero.to_char())
            }
        }
    }
}

impl std::fmt::Display for Program {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, inst) in self.instructions.iter().enumerate() {
            if i > 0 {
                write!(f, "_")?;
            }
            write!(f, "{}", inst)?;
        }
        Ok(())
    }
}
