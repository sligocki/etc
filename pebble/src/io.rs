use crate::program::{Program, ProgramError};
use crate::simulation::SimOutcome;
use std::fmt;
use std::fs::File;
use std::io::{self, BufRead, BufReader, BufWriter, Write};
use std::path::Path;

/// Error type for reading or writing program and simulation record files.
#[derive(Debug)]
pub enum IoError {
    Io(io::Error),
    ParseProgram { line: usize, source: ProgramError },
    ParseOutcome { line: usize, detail: String },
}

impl fmt::Display for IoError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IoError::Io(e) => write!(f, "I/O error: {e}"),
            IoError::ParseProgram { line, source } => {
                write!(f, "line {line}: failed to parse program: {source}")
            }
            IoError::ParseOutcome { line, detail } => {
                write!(f, "line {line}: failed to parse simulation outcome: {detail}")
            }
        }
    }
}

impl std::error::Error for IoError {}

impl From<io::Error> for IoError {
    fn from(e: io::Error) -> Self {
        IoError::Io(e)
    }
}

/// A program alongside an optional simulation outcome, corresponding to a single line in a results file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProgramRecord {
    pub program: Program,
    pub outcome: Option<SimOutcome>,
}

impl ProgramRecord {
    pub fn new(program: Program, outcome: Option<SimOutcome>) -> Self {
        Self { program, outcome }
    }
}

impl fmt::Display for ProgramRecord {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.outcome {
            Some(outcome) => write!(f, "{}\t{}", self.program, outcome),
            None => write!(f, "{}", self.program),
        }
    }
}

/// Parse a single non-empty, comment-stripped line into a `ProgramRecord`.
///
/// Supported formats:
/// - `<program>`
/// - `<program>\tHALT\t<steps>`
/// - `<program>\t<steps>` (shorthand for `Halted { steps }`)
/// - `<program>\tMAX_STEPS\t<steps>` (or `HOLD` / `TIMEOUT`)
/// - `<program>\tMISSING_RULE\t<pebbles>\t<steps>`
pub fn parse_record_line(line: &str, line_num: usize) -> Result<ProgramRecord, IoError> {
    let (code_part, comment_part) = match line.split_once('#') {
        Some((code, comment)) => (code.trim(), Some(comment.trim())),
        None => (line.trim(), None),
    };

    let mut fields = code_part.split_whitespace();
    let prog_str = fields.next().ok_or_else(|| IoError::ParseOutcome {
        line: line_num,
        detail: "unexpected empty line".to_string(),
    })?;

    let program: Program = prog_str
        .parse()
        .map_err(|source| IoError::ParseProgram {
            line: line_num,
            source,
        })?;

    let Some(status_or_steps) = fields.next() else {
        return Ok(ProgramRecord {
            program,
            outcome: None,
        });
    };

    let outcome = match status_or_steps.to_ascii_uppercase().as_str() {
        "HALT" | "HALTED" => {
            let steps_str = fields.next().ok_or_else(|| IoError::ParseOutcome {
                line: line_num,
                detail: "missing step count after HALT".to_string(),
            })?;
            let steps: u64 = steps_str.parse().map_err(|_| IoError::ParseOutcome {
                line: line_num,
                detail: format!("invalid step count '{steps_str}'"),
            })?;
            SimOutcome::Halted { steps }
        }
        "DECIDED" => {
            let decider_str = fields.next().ok_or_else(|| IoError::ParseOutcome {
                line: line_num,
                detail: "missing decider name after DECIDED".to_string(),
            })?;
            let mut decider: crate::deciders::Decider = decider_str
                .parse()
                .map_err(|detail| IoError::ParseOutcome {
                    line: line_num,
                    detail,
                })?;
            let steps_str = fields.next().ok_or_else(|| IoError::ParseOutcome {
                line: line_num,
                detail: "missing step count after DECIDED decider name".to_string(),
            })?;
            let steps: u64 = steps_str.parse().map_err(|_| IoError::ParseOutcome {
                line: line_num,
                detail: format!("invalid step count '{steps_str}'"),
            })?;
            if matches!(decider, crate::deciders::Decider::Ctl(_)) {
                if let Some(comment) = comment_part {
                    if let Some(proof) = parse_ctl_proof_comment(steps, comment) {
                        decider = crate::deciders::Decider::Ctl(Some(proof));
                    }
                }
            }
            SimOutcome::DecidedNonHalting { decider, steps }
        }
        "MAX_STEPS" | "HOLD" | "HOLDOUT" | "TIMEOUT" => {
            let steps_str = fields.next().ok_or_else(|| IoError::ParseOutcome {
                line: line_num,
                detail: format!("missing step count after {status_or_steps}"),
            })?;
            let steps: u64 = steps_str.parse().map_err(|_| IoError::ParseOutcome {
                line: line_num,
                detail: format!("invalid step count '{steps_str}'"),
            })?;
            SimOutcome::MaxStepsReached { steps }
        }
        "MISSING_RULE" => {
            let pebbles_str = fields.next().ok_or_else(|| IoError::ParseOutcome {
                line: line_num,
                detail: "missing pebble count after MISSING_RULE".to_string(),
            })?;
            let steps_str = fields.next().ok_or_else(|| IoError::ParseOutcome {
                line: line_num,
                detail: "missing step count after MISSING_RULE pebble count".to_string(),
            })?;
            let pebbles: u8 = pebbles_str.parse().map_err(|_| IoError::ParseOutcome {
                line: line_num,
                detail: format!("invalid pebble count '{pebbles_str}'"),
            })?;
            let steps: u64 = steps_str.parse().map_err(|_| IoError::ParseOutcome {
                line: line_num,
                detail: format!("invalid step count '{steps_str}'"),
            })?;
            SimOutcome::MissingRule { pebbles, steps }
        }
        _ => {
            // Allow shorthand `<program> <steps>` for halted step count
            if let Ok(steps) = status_or_steps.parse::<u64>() {
                SimOutcome::Halted { steps }
            } else {
                return Err(IoError::ParseOutcome {
                    line: line_num,
                    detail: format!("unrecognized outcome token '{status_or_steps}'"),
                });
            }
        }
    };

    if let Some(extra) = fields.next() {
        return Err(IoError::ParseOutcome {
            line: line_num,
            detail: format!("unexpected trailing token '{extra}'"),
        });
    }

    Ok(ProgramRecord {
        program,
        outcome: Some(outcome),
    })
}

fn parse_ctl_proof_comment(num_steps: u64, comment: &str) -> Option<crate::ctl::CtlProof> {
    let mut num_states = None;
    let mut split_threshold = None;
    let mut floor = None;
    let mut modulus = None;
    for part in comment.split_whitespace() {
        let part = part.trim_start_matches('#');
        if let Some(v) = part.strip_prefix("states=") {
            num_states = v.parse().ok();
        } else if let Some(v) = part.strip_prefix("thresh=") {
            split_threshold = v.parse().ok();
        } else if let Some(v) = part.strip_prefix("floor=") {
            floor = v.parse().ok();
        } else if let Some(v) = part.strip_prefix("mod=") {
            modulus = v.parse().ok();
        }
    }
    let split_threshold = split_threshold.unwrap_or(2);
    let floor = floor.unwrap_or(2 * split_threshold + 2);
    Some(crate::ctl::CtlProof {
        num_steps,
        num_states: num_states?,
        split_threshold,
        floor,
        modulus: modulus?,
    })
}

/// Read `ProgramRecord`s from any `BufRead` source, ignoring comment-only and blank lines.
pub fn read_records<R: BufRead>(reader: R) -> Result<Vec<ProgramRecord>, IoError> {
    let mut records = Vec::new();
    for (idx, line_res) in reader.lines().enumerate() {
        let line_num = idx + 1;
        let raw_line = line_res?;
        let trimmed = raw_line.trim();
        if trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }
        records.push(parse_record_line(trimmed, line_num)?);
    }
    Ok(records)
}

/// Read `ProgramRecord`s from a file path.
pub fn read_records_from_file<P: AsRef<Path>>(path: P) -> Result<Vec<ProgramRecord>, IoError> {
    let file = File::open(path)?;
    read_records(BufReader::new(file))
}

/// Write `ProgramRecord`s to any `Write` sink, one per line.
pub fn write_records<W: Write>(mut writer: W, records: &[ProgramRecord]) -> Result<(), IoError> {
    for record in records {
        writeln!(writer, "{record}")?;
    }
    Ok(())
}

/// Write `ProgramRecord`s to a file path.
pub fn write_records_to_file<P: AsRef<Path>>(
    path: P,
    records: &[ProgramRecord],
) -> Result<(), IoError> {
    let file = File::create(path)?;
    let mut writer = BufWriter::new(file);
    write_records(&mut writer, records)?;
    writer.flush()?;
    Ok(())
}

/// Read a list of `Program`s from any `BufRead` source (ignoring any trailing outcome columns and `#` comments).
pub fn read_programs<R: BufRead>(reader: R) -> Result<Vec<Program>, IoError> {
    let records = read_records(reader)?;
    Ok(records.into_iter().map(|r| r.program).collect())
}

/// Read a list of `Program`s from a file path.
pub fn read_programs_from_file<P: AsRef<Path>>(path: P) -> Result<Vec<Program>, IoError> {
    let file = File::open(path)?;
    read_programs(BufReader::new(file))
}

/// Write a slice of `Program`s to any `Write` sink in wiki short format, one per line.
pub fn write_programs<W: Write>(mut writer: W, programs: &[Program]) -> Result<(), IoError> {
    for prog in programs {
        writeln!(writer, "{prog}")?;
    }
    Ok(())
}

/// Write a slice of `Program`s to a file path.
pub fn write_programs_to_file<P: AsRef<Path>>(
    path: P,
    programs: &[Program],
) -> Result<(), IoError> {
    let file = File::create(path)?;
    let mut writer = BufWriter::new(file);
    write_programs(&mut writer, programs)?;
    writer.flush()?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::deciders::Decider;
    use std::io::Cursor;

    #[test]
    fn test_read_and_write_records_roundtrip() {
        let records = vec![
            ProgramRecord::new(
                "00_11_03_21_04".parse().unwrap(),
                Some(SimOutcome::Halted { steps: 11 }),
            ),
            ProgramRecord::new(
                "01_01".parse().unwrap(),
                Some(SimOutcome::DecidedNonHalting {
                    decider: Decider::EdgeGlider,
                    steps: 50,
                }),
            ),
            ProgramRecord::new(
                "01_11_03_21_04".parse().unwrap(),
                Some(SimOutcome::MaxStepsReached { steps: 100 }),
            ),
            ProgramRecord::new(
                "00_--_--_--_14".parse().unwrap(),
                Some(SimOutcome::MissingRule {
                    pebbles: 4,
                    steps: 1,
                }),
            ),
            ProgramRecord::new(
                "00_20_10_04_21_21_07_50_17_01".parse().unwrap(),
                Some(SimOutcome::DecidedNonHalting {
                    decider: Decider::Ctl(Some(crate::ctl::CtlProof {
                        num_steps: 60,
                        num_states: 4757,
                        split_threshold: 2,
                        floor: 6,
                        modulus: 1,
                    })),
                    steps: 60,
                }),
            ),
            ProgramRecord::new(
                "01_00_02_03_05_60_23_05_13_19".parse().unwrap(),
                Some(SimOutcome::DecidedNonHalting {
                    decider: Decider::Ctl(Some(crate::ctl::CtlProof {
                        num_steps: 240,
                        num_states: 63,
                        split_threshold: 2,
                        floor: 10,
                        modulus: 1,
                    })),
                    steps: 240,
                }),
            ),
            ProgramRecord::new("00_01_20_03".parse().unwrap(), None),
        ];

        let mut buf = Vec::new();
        write_records(&mut buf, &records).unwrap();

        let parsed = read_records(Cursor::new(buf)).unwrap();
        assert_eq!(parsed, records);
    }

    #[test]
    fn test_comments_blank_lines_and_shorthand() {
        let input = "\
            # Pebble Automaton test file\n\
            \n\
            00_11_03_21_04\t11 # peBBle(5) champion\n\
            00_01_20_03\tHALT\t6\n\
            01_00_00_00\tHOLD\t50\n\
            00_01\n\
        ";

        let records = read_records(Cursor::new(input)).unwrap();
        assert_eq!(records.len(), 4);
        assert_eq!(records[0].outcome, Some(SimOutcome::Halted { steps: 11 }));
        assert_eq!(records[1].outcome, Some(SimOutcome::Halted { steps: 6 }));
        assert_eq!(
            records[2].outcome,
            Some(SimOutcome::MaxStepsReached { steps: 50 })
        );
        assert_eq!(records[3].outcome, None);

        let programs = read_programs(Cursor::new(input)).unwrap();
        assert_eq!(programs.len(), 4);
        assert_eq!(programs[0].to_string(), "00_11_03_21_04");
    }

    #[test]
    fn test_invalid_record_errors() {
        let bad_prog = "99_00\n";
        assert!(read_records(Cursor::new(bad_prog)).is_err());

        let bad_outcome = "00_01\tUNKNOWN_STATUS\t5\n";
        assert!(read_records(Cursor::new(bad_outcome)).is_err());
    }
}
