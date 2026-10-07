use std::io::Write;

pub enum ProgramResult<'a> {
    Halt { steps: u64, registers: &'a [u64] },
    Unknown,
    Polyhedral { state: char, conditions: &'a str },
}

pub fn write_result<W: Write>(
    writer: &mut W,
    prog_str: &str,
    result: ProgramResult,
) -> std::io::Result<()> {
    match result {
        ProgramResult::Halt { steps, registers } => {
            let regs_str = registers.iter().map(|r| r.to_string()).collect::<Vec<_>>().join(",");
            writeln!(writer, "{}\tHalt\t{}\t[{}]", prog_str, steps, regs_str)
        }
        ProgramResult::Unknown => {
            writeln!(writer, "{}\tUnknown\t", prog_str)
        }
        ProgramResult::Polyhedral { state, conditions } => {
            writeln!(writer, "{}\tInfinite\tState: {}, Conditions: [{}]", prog_str, state, conditions)
        }
    }
}
