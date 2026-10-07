#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Target {
    Halt,
    Inst(usize),
    Undef,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Instruction {
    Undef,
    Inc {
        reg: usize,
        next: Target,
    },
    Dec {
        reg: usize,
        next_not_zero: Target,
        next_zero: Target,
    },
    NoOp {
        next: Target,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Program {
    pub instructions: Vec<Instruction>,
}

impl Program {
    pub fn num_regs(&self) -> usize {
        self.instructions.iter().map(|inst| match inst {
            Instruction::Inc { reg, .. } => *reg,
            Instruction::Dec { reg, .. } => *reg,
            Instruction::Undef => 0,
            Instruction::NoOp { .. } => 0,
        }).max().map_or(0, |max_reg| max_reg + 1)
    }

    pub fn to_string_format(&self, max_reg_referenced: i32) -> String {
        let dummy_reg = (max_reg_referenced.max(-1) + 1) as usize;
        let mut s = String::new();
        for (i, inst) in self.instructions.iter().enumerate() {
            if i > 0 {
                s.push('_');
            }
            match inst {
                Instruction::Undef => s.push('?'),
                Instruction::Inc { reg, next } => {
                    s.push_str(&format!("{}+{}", reg, next.to_char()));
                }
                Instruction::Dec { reg, next_not_zero, next_zero } => {
                    s.push_str(&format!("{}-{}{}", reg, next_not_zero.to_char(), next_zero.to_char()));
                }
                Instruction::NoOp { next } => {
                    s.push_str(&format!("{}+{}", dummy_reg, next.to_char()));
                }
            }
        }
        s
    }

    pub fn get_missing_requirements(&self, max_reg_referenced: i32) -> (usize, Vec<bool>, Vec<bool>) {
        let mut undef_count = 0;
        let mut has_inc = vec![false; (max_reg_referenced.max(-1) + 1) as usize];
        let mut has_dec = vec![false; (max_reg_referenced.max(-1) + 1) as usize];

        for inst in &self.instructions {
            match inst {
                Instruction::Undef => undef_count += 1,
                Instruction::Inc { reg, .. } => {
                    if *reg < has_inc.len() {
                        has_inc[*reg] = true;
                    }
                }
                Instruction::Dec { reg, .. } => {
                    if *reg < has_dec.len() {
                        has_dec[*reg] = true;
                    }
                }
                Instruction::NoOp { .. } => {}
            }
        }

        (undef_count, has_inc, has_dec)
    }
}

impl Target {
    pub fn to_char(self) -> char {
        match self {
            Target::Halt => '*',
            Target::Inst(idx) => (b'A' + idx as u8) as char,
            Target::Undef => '?',
        }
    }
}

impl std::fmt::Display for Target {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_char())
    }
}

impl std::fmt::Display for Instruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Instruction::Undef => write!(f, "?"),
            Instruction::Inc { reg, next } => {
                write!(f, "{}+{}", reg, next.to_char())
            }
            Instruction::Dec { reg, next_not_zero, next_zero } => {
                write!(f, "{}-{}{}", reg, next_not_zero.to_char(), next_zero.to_char())
            }
            Instruction::NoOp { next } => {
                write!(f, "NoOp({})", next.to_char()) // Internal representation
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
