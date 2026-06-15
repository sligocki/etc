#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Instr {
    Inc(usize),
    Dec(usize),
    While(usize, Vec<Instr>),
}

pub fn var_name(v: usize) -> String {
    if v < 26 {
        ((b'A' + v as u8) as char).to_string()
    } else {
        format!("V{}", v)
    }
}

pub fn format_program(program: &[Instr]) -> String {
    let mut parts = Vec::new();
    for instr in program {
        match instr {
            Instr::Inc(v) => parts.push(format!("{}++;", var_name(*v))),
            Instr::Dec(v) => parts.push(format!("{}--;", var_name(*v))),
            Instr::While(v, body) => {
                parts.push(format!(
                    "while {} {{ {} }}",
                    var_name(*v),
                    format_program(body)
                ));
            }
        }
    }
    parts.join(" ")
}
