use crate::program::{Instruction, Program, Target};
use std::collections::HashMap;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MacroInst {
    Inc {
        reg: usize,
        next: Target,
    },
    Dec {
        reg: usize,
        next_not_zero: Target,
        next_zero: Target,
    },
    Transfer {
        reg: usize,
        incs: HashMap<usize, u32>,
        next: Target,
    },
    Undef,
}

pub fn abstract_program(prog: &Program) -> Vec<MacroInst> {
    let mut macros = Vec::new();

    for (i, inst) in prog.instructions.iter().enumerate() {
        match inst {
            Instruction::Undef => {
                macros.push(MacroInst::Undef);
            }
            Instruction::NoOp { .. } => {
                macros.push(MacroInst::Undef); // or panic, this isn't expected. let's just make it Undef
            }
            Instruction::Inc { reg, next } => {
                macros.push(MacroInst::Inc {
                    reg: *reg,
                    next: *next,
                });
            }
            Instruction::Dec {
                reg,
                next_not_zero,
                next_zero,
            } => {
                // Check if this forms a transfer loop
                if let Some(incs) = detect_transfer_loop(prog, i, *reg, *next_not_zero) {
                    macros.push(MacroInst::Transfer {
                        reg: *reg,
                        incs,
                        next: *next_zero,
                    });
                } else {
                    macros.push(MacroInst::Dec {
                        reg: *reg,
                        next_not_zero: *next_not_zero,
                        next_zero: *next_zero,
                    });
                }
            }
        }
    }

    macros
}

fn detect_transfer_loop(
    prog: &Program,
    start_idx: usize,
    dec_reg: usize,
    mut current_target: Target,
) -> Option<HashMap<usize, u32>> {
    let mut incs: HashMap<usize, u32> = HashMap::new();
    let mut visited = vec![false; prog.instructions.len()];

    loop {
        match current_target {
            Target::Halt => return None,
            Target::Undef => return None,
            Target::Inst(idx) => {
                if idx == start_idx {
                    // Loop completed successfully
                    return Some(incs);
                }

                if visited[idx] {
                    // Infinite loop or complex graph, not a simple transfer
                    return None;
                }
                visited[idx] = true;

                match &prog.instructions[idx] {
                    Instruction::Undef => return None,
                    Instruction::NoOp { .. } => return None,
                    Instruction::Inc { reg, next } => {
                        if *reg == dec_reg {
                            // Modifying the decrement register breaks the simple transfer property
                            return None;
                        }
                        *incs.entry(*reg).or_insert(0) += 1;
                        current_target = *next;
                    }
                    Instruction::Dec { .. } => {
                        // Any other dec instruction breaks the simple transfer property
                        return None;
                    }
                }
            }
        }
    }
}
use crate::deciders::symbolic::AffineExpr;

impl MacroInst {
    pub fn to_string_with_state(&self, state_idx: usize, num_regs: usize) -> String {
        let state_char = (b'A' + state_idx as u8) as char;

        match self {
            MacroInst::Undef => {
                format!("{}: ?", state_char)
            }
            MacroInst::Inc { reg, next } => {
                format!("{}: {}+{}", state_char, reg, next.to_char())
            }
            MacroInst::Dec {
                reg,
                next_not_zero,
                next_zero,
            } => {
                format!(
                    "{}: {}-{}{}",
                    state_char,
                    reg,
                    next_not_zero.to_char(),
                    next_zero.to_char()
                )
            }
            MacroInst::Transfer { reg, incs, next } => {
                let mut in_regs = Vec::new();
                let mut out_regs = Vec::new();
                for i in 0..num_regs {
                    in_regs.push(AffineExpr::var(i));
                    let mut out_expr = AffineExpr::var(i);
                    if i == *reg {
                        out_expr = AffineExpr::new(0);
                    } else if let Some(&c) = incs.get(&i) {
                        out_expr.mul_add(c as i64, &AffineExpr::var(*reg));
                    }
                    out_regs.push(out_expr);
                }

                let format_regs = |regs: &[AffineExpr]| -> String {
                    let mut s = String::new();
                    s.push('[');
                    for (i, r) in regs.iter().enumerate() {
                        if i > 0 {
                            s.push_str(", ");
                        }
                        s.push_str(&r.to_string());
                    }
                    s.push(']');
                    s
                };

                format!(
                    "{}:{} -> {}:{}",
                    state_char,
                    format_regs(&in_regs),
                    next.to_char(),
                    format_regs(&out_regs)
                )
            }
        }
    }
}

impl std::fmt::Display for MacroInst {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MacroInst::Undef => write!(f, "?"),
            MacroInst::Inc { reg, next } => {
                write!(f, "{}+{}", reg, next.to_char())
            }
            MacroInst::Dec {
                reg,
                next_not_zero,
                next_zero,
            } => {
                write!(
                    f,
                    "{}-{}{}",
                    reg,
                    next_not_zero.to_char(),
                    next_zero.to_char()
                )
            }
            MacroInst::Transfer { reg, incs, next } => {
                write!(f, "{}-[", reg)?;
                let mut first = true;
                for (r, inc) in incs {
                    if !first {
                        write!(f, ",")?;
                    }
                    write!(f, "{}+{}", r, inc)?;
                    first = false;
                }
                write!(f, "]{}", next.to_char())
            }
        }
    }
}
