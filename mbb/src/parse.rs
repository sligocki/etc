use crate::program::{Instruction, Program, Target};

pub fn parse_target(c: char) -> Option<Target> {
    if c == '*' || c == '?' {
        Some(Target::Halt)
    } else if c >= 'A' && c <= 'Z' {
        Some(Target::Inst((c as u8 - b'A') as usize))
    } else {
        None
    }
}

pub fn parse_program(s: &str) -> Option<Program> {
    let mut instructions = Vec::new();
    let parts = s.split('_');
    for part in parts {
        let part = part.trim();
        if part.is_empty() {
            return None;
        }
        if part == "?" {
            instructions.push(Instruction::Undef);
            continue;
        }
        let plus_idx = part.find('+');
        let minus_idx = part.find('-');
        
        if let Some(idx) = plus_idx {
            let reg_str = &part[..idx];
            let reg: usize = reg_str.parse().ok()?;
            let next_char = part.chars().nth(idx + 1)?;
            let next = parse_target(next_char)?;
            if part.len() != idx + 2 {
                return None;
            }
            instructions.push(Instruction::Inc { reg, next });
        } else if let Some(idx) = minus_idx {
            let reg_str = &part[..idx];
            let reg: usize = reg_str.parse().ok()?;
            let next_not_zero_char = part.chars().nth(idx + 1)?;
            let next_not_zero = parse_target(next_not_zero_char)?;
            let next_zero_char = part.chars().nth(idx + 2)?;
            let next_zero = parse_target(next_zero_char)?;
            if part.len() != idx + 3 {
                return None;
            }
            instructions.push(Instruction::Dec { reg, next_not_zero, next_zero });
        } else {
            return None;
        }
    }
    Some(Program { instructions })
}
