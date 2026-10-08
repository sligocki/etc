use std::io::Write;
use crate::deciders::{DeciderResult, InfiniteReason};

pub fn write_result<W: Write>(
    writer: &mut W,
    prog_str: &str,
    result: &DeciderResult,
) -> std::io::Result<()> {
    match result {
        DeciderResult::Halt { steps, registers, hit_undef } => {
            if hit_undef.is_none() {
                let regs_str = registers.iter().map(|r| r.to_string()).collect::<Vec<_>>().join(",");
                writeln!(writer, "{}\tHalt\t{}\t[{}]", prog_str, steps, regs_str)
            } else {
                Ok(())
            }
        }
        DeciderResult::Unknown => {
            writeln!(writer, "{}\tUnknown\t", prog_str)
        }
        DeciderResult::Error(msg) => {
            writeln!(writer, "{}\tError\t{}", prog_str, msg)
        }
        DeciderResult::Infinite(reason) => match reason {
            InfiniteReason::Cycle { start_by, period, is_min_start } => {
                writeln!(writer, "{}\tInfinite\tCycle(start_by: {}, period: {}, is_min_start: {})", prog_str, start_by, period, is_min_start)
            }
            InfiniteReason::TranslatedCycler { start_by, period, is_min_start } => {
                writeln!(writer, "{}\tInfinite\tTranslatedCycler(start_by: {}, period: {}, is_min_start: {})", prog_str, start_by, period, is_min_start)
            }
            InfiniteReason::Polyhedral { state, conditions } => {
                writeln!(writer, "{}\tInfinite\tPolyhedral(State: {}, Conditions: [{}])", prog_str, state, conditions)
            }
            InfiniteReason::Bouncer { start_by, period, is_min_start } => {
                writeln!(writer, "{}\tInfinite\tBouncer(start_by: {}, period: {}, is_min_start: {})", prog_str, start_by, period, is_min_start)
            }
            InfiniteReason::Semilinear1D { state, base, period } => {
                writeln!(writer, "{}\tInfinite\tSemilinear1D(State: {}, Base: {:?}, Period: {:?})", prog_str, state, base, period)
            }
            InfiniteReason::Congruence { state, moduli, seed } => {
                writeln!(writer, "{}\tInfinite\tCongruence(State: {}, Moduli: {:?}, Seed: {:?})", prog_str, state, moduli, seed)
            }
            InfiniteReason::BackwardsUnreachable => {
                writeln!(writer, "{}\tInfinite\tBackwardsUnreachable()", prog_str)
            }
        }
    }
}
