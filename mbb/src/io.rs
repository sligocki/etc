use std::io::Write;

pub enum InfiniteReason<'a> {
    Cycle { start_by: u64, period: u64 },
    Polyhedral { state: char, conditions: &'a str },
}

pub enum ProgramResult<'a> {
    Halt { steps: u64, registers: &'a [u64] },
    Infinite(InfiniteReason<'a>),
    Unknown,
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
        ProgramResult::Infinite(reason) => match reason {
            InfiniteReason::Cycle { start_by, period } => {
                writeln!(writer, "{}\tInfinite\tCycle(start_by: {}, period: {})", prog_str, start_by, period)
            }
            InfiniteReason::Polyhedral { state, conditions } => {
                writeln!(writer, "{}\tInfinite\tPolyhedral(State: {}, Conditions: [{}])", prog_str, state, conditions)
            }
        }
    }
}
