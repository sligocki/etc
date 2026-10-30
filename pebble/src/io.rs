use crate::program::{Program, ProgramError};
use crate::simulation::{SimOutcome, UnknownReason};
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

/// Format an integer count with comma thousands separators (e.g. `23,884,622`).
pub fn format_count(n: u64) -> String {
    let s = n.to_string();
    let mut out = String::with_capacity(s.len() + s.len() / 3);
    let bytes = s.as_bytes();
    let len = bytes.len();
    for (i, &b) in bytes.iter().enumerate() {
        if i > 0 && (len - i) % 3 == 0 {
            out.push(',');
        }
        out.push(b as char);
    }
    out
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
/// - `<program>\tINF\t<decider>\t<steps>` (or `DECIDED`)
/// - `<program>\tUNKNOWN\t<reason>\t<steps>` (or `MAX_STEPS` / `HOLD` / `TIMEOUT` / `UNK`, or legacy `UNKNOWN\t<steps>`)
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
        "INF" | "DECIDED" => {
            let decider_str = fields.next().ok_or_else(|| IoError::ParseOutcome {
                line: line_num,
                detail: format!("missing decider name after {status_or_steps}"),
            })?;
            let mut decider: crate::deciders::Decider = decider_str
                .parse()
                .map_err(|detail| IoError::ParseOutcome {
                    line: line_num,
                    detail,
                })?;
            let steps_str = fields.next().ok_or_else(|| IoError::ParseOutcome {
                line: line_num,
                detail: format!("missing step count after {status_or_steps} decider name"),
            })?;
            let steps: u64 = steps_str.parse().map_err(|_| IoError::ParseOutcome {
                line: line_num,
                detail: format!("invalid step count '{steps_str}'"),
            })?;
            if let Some(comment) = comment_part {
                match decider {
                    crate::deciders::Decider::Ctl(_) => {
                        if let Some(proof) = parse_ctl_proof_comment(steps, comment) {
                            decider = crate::deciders::Decider::Ctl(Some(proof));
                        }
                    }
                    crate::deciders::Decider::Cycler(_) => {
                        if let Some(proof) = parse_cycler_proof_comment(comment) {
                            decider = crate::deciders::Decider::Cycler(Some(proof));
                        }
                    }
                    crate::deciders::Decider::SeparatedComponents(_) => {
                        if let Some(proof) = parse_separated_components_proof_comment(comment) {
                            decider = crate::deciders::Decider::SeparatedComponents(Some(proof));
                        }
                    }
                    crate::deciders::Decider::Bouncer(_) => {
                        if let Some(proof) = parse_bouncer_proof_comment(comment) {
                            decider = crate::deciders::Decider::Bouncer(Some(proof));
                        }
                    }
                    crate::deciders::Decider::AcceleratedInfinite(_) => {
                        if let Some(proof) = parse_accelerated_infinite_proof_comment(comment) {
                            decider = crate::deciders::Decider::AcceleratedInfinite(Some(proof));
                        }
                    }
                    _ => {}
                }
            }
            SimOutcome::Inf { decider, steps }
        }
        "OVERFLOW" | "COORD_OVERFLOW" => {
            let steps_str = fields.next().ok_or_else(|| IoError::ParseOutcome {
                line: line_num,
                detail: format!("missing step count after {status_or_steps}"),
            })?;
            let steps: u64 = steps_str.parse().map_err(|_| IoError::ParseOutcome {
                line: line_num,
                detail: format!("invalid step count '{steps_str}'"),
            })?;
            SimOutcome::Unknown {
                steps,
                reason: UnknownReason::CoordOverflow,
            }
        }
        "UNKNOWN" | "MAX_STEPS" | "HOLD" | "HOLDOUT" | "TIMEOUT" | "UNK" => {
            let token2 = fields.next().ok_or_else(|| IoError::ParseOutcome {
                line: line_num,
                detail: format!("missing step count or reason after {status_or_steps}"),
            })?;
            if let Ok(steps) = token2.parse::<u64>() {
                // Legacy format: UNKNOWN <steps> [optional reason]
                let reason = match fields.next() {
                    Some(r) => r.parse::<UnknownReason>().map_err(|detail| IoError::ParseOutcome {
                        line: line_num,
                        detail,
                    })?,
                    None => UnknownReason::StepLimit,
                };
                SimOutcome::Unknown { steps, reason }
            } else {
                // Canonical format: UNKNOWN <reason> <steps>
                let reason = token2.parse::<UnknownReason>().map_err(|detail| IoError::ParseOutcome {
                    line: line_num,
                    detail,
                })?;
                let steps_str = fields.next().ok_or_else(|| IoError::ParseOutcome {
                    line: line_num,
                    detail: format!("missing step count after UNKNOWN {token2}"),
                })?;
                let steps: u64 = steps_str.parse().map_err(|_| IoError::ParseOutcome {
                    line: line_num,
                    detail: format!("invalid step count '{steps_str}'"),
                })?;
                SimOutcome::Unknown { steps, reason }
            }
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
    let mut method = None;
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
        } else if let Some(v) = part.strip_prefix("method=").or_else(|| part.strip_prefix("alg=")) {
            method = v.parse().ok();
        }
    }
    let split_threshold = split_threshold.unwrap_or(2);
    let floor = floor.unwrap_or(2 * split_threshold + 2);
    let method = method.unwrap_or(crate::ctl::CtlSearchMethod::Manual);
    Some(crate::ctl::CtlProof {
        num_steps,
        num_states: num_states?,
        split_threshold,
        floor,
        modulus: modulus?,
        method,
    })
}

fn parse_cycler_proof_comment(comment: &str) -> Option<crate::deciders::CyclerProof> {
    let mut period = None;
    let mut dx = None;
    for part in comment.split_whitespace() {
        let part = part.trim_start_matches('#');
        if let Some(v) = part.strip_prefix("period=").or_else(|| part.strip_prefix("p=")) {
            period = v.parse().ok();
        } else if let Some(v) = part.strip_prefix("dx=") {
            dx = v.parse().ok();
        }
    }
    Some(crate::deciders::CyclerProof {
        period: period?,
        dx: dx.unwrap_or(0),
    })
}

fn parse_separated_components_proof_comment(
    comment: &str,
) -> Option<crate::deciders::SeparatedComponentsProof> {
    let mut period = None;
    let mut dx_left = None;
    let mut dx_right = None;
    for part in comment.split_whitespace() {
        let part = part.trim_start_matches('#');
        if let Some(v) = part.strip_prefix("period=").or_else(|| part.strip_prefix("p=")) {
            period = v.parse().ok();
        } else if let Some(v) = part.strip_prefix("dx_l=").or_else(|| part.strip_prefix("dx_left=")) {
            dx_left = v.parse().ok();
        } else if let Some(v) = part.strip_prefix("dx_r=").or_else(|| part.strip_prefix("dx_right=")) {
            dx_right = v.parse().ok();
        }
    }
    Some(crate::deciders::SeparatedComponentsProof {
        period: period?,
        dx_left: dx_left.unwrap_or(0),
        dx_right: dx_right.unwrap_or(0),
    })
}

fn parse_bouncer_proof_comment(comment: &str) -> Option<crate::deciders::BouncerProof> {
    let mut bounce_steps = None;
    let mut gap_growth = None;
    for part in comment.split_whitespace() {
        let part = part.trim_start_matches('#');
        if let Some(v) = part
            .strip_prefix("bounce_steps=")
            .or_else(|| part.strip_prefix("bounce="))
            .or_else(|| part.strip_prefix("period="))
            .or_else(|| part.strip_prefix("p="))
        {
            bounce_steps = v.parse().ok();
        } else if let Some(v) = part
            .strip_prefix("gap_growth=")
            .or_else(|| part.strip_prefix("growth="))
            .or_else(|| part.strip_prefix("dg="))
        {
            gap_growth = v.parse().ok();
        }
    }
    Some(crate::deciders::BouncerProof {
        bounce_steps: bounce_steps?,
        gap_growth: gap_growth.unwrap_or(1),
    })
}

fn parse_accelerated_infinite_proof_comment(
    comment: &str,
) -> Option<crate::deciders::AcceleratedInfiniteProof> {
    let mut period = None;
    let mut dxs = Vec::new();
    let mut periods = Vec::new();
    let mut dx_left = None;
    let mut dx_right = None;

    for part in comment.split_whitespace() {
        let part = part.trim_start_matches('#');
        if let Some(v) = part.strip_prefix("period=").or_else(|| part.strip_prefix("p=")) {
            period = v.parse().ok();
        } else if let Some(v) = part.strip_prefix("dxs=").or_else(|| part.strip_prefix("dx=")) {
            let v = v.trim_matches(|c| c == '[' || c == ']');
            for item in v.split(',') {
                if let Ok(d) = item.trim().parse::<i64>() {
                    dxs.push(d);
                }
            }
        } else if let Some(v) = part.strip_prefix("periods=") {
            let v = v.trim_matches(|c| c == '[' || c == ']');
            for item in v.split(',') {
                if let Ok(p) = item.trim().parse::<u32>() {
                    periods.push(p);
                }
            }
        } else if let Some(v) = part.strip_prefix("dx_l=").or_else(|| part.strip_prefix("dx_left=")) {
            dx_left = v.parse().ok();
        } else if let Some(v) = part.strip_prefix("dx_r=").or_else(|| part.strip_prefix("dx_right=")) {
            dx_right = v.parse().ok();
        }
    }

    if dxs.is_empty() {
        if let (Some(l), Some(r)) = (dx_left, dx_right) {
            dxs.push(l);
            dxs.push(r);
        }
    }

    let p = period.unwrap_or(1);
    if periods.is_empty() {
        periods = vec![p as u32; dxs.len()];
    }

    Some(crate::deciders::AcceleratedInfiniteProof::new(
        p,
        &dxs,
        &periods,
    ))
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

/// Write `ProgramRecord`s to a file path atomically via a temporary file.
pub fn write_records_to_file<P: AsRef<Path>>(
    path: P,
    records: &[ProgramRecord],
) -> Result<(), IoError> {
    let path = path.as_ref();
    let mut tmp_name = path.file_name().unwrap_or_default().to_os_string();
    tmp_name.push(".tmp");
    let tmp_path = path.with_file_name(tmp_name);
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent)?;
    }
    let file = File::create(&tmp_path)?;
    let mut writer = BufWriter::new(file);
    write_records(&mut writer, records)?;
    writer.flush()?;
    drop(writer);
    std::fs::rename(&tmp_path, path)?;
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
                Some(SimOutcome::Inf {
                    decider: Decider::EdgeGlider,
                    steps: 50,
                }),
            ),
            ProgramRecord::new(
                "01_11_03_21_04".parse().unwrap(),
                Some(SimOutcome::unknown_step_limit(100)),
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
                Some(SimOutcome::Inf {
                    decider: Decider::Ctl(Some(crate::ctl::CtlProof {
                        num_steps: 60,
                        num_states: 4757,
                        split_threshold: 2,
                        floor: 6,
                        modulus: 1,
                        method: crate::ctl::CtlSearchMethod::Manual,
                    })),
                    steps: 60,
                }),
            ),
            ProgramRecord::new(
                "01_00_02_03_05_60_23_05_13_19".parse().unwrap(),
                Some(SimOutcome::Inf {
                    decider: Decider::Ctl(Some(crate::ctl::CtlProof {
                        num_steps: 240,
                        num_states: 63,
                        split_threshold: 2,
                        floor: 10,
                        modulus: 1,
                        method: crate::ctl::CtlSearchMethod::Inferred,
                    })),
                    steps: 240,
                }),
            ),
            ProgramRecord::new(
                "00_02_21_40_11_--_10_08_43_11".parse().unwrap(),
                Some(SimOutcome::Inf {
                    decider: Decider::Ctl(Some(crate::ctl::CtlProof {
                        num_steps: 40,
                        num_states: 300,
                        split_threshold: 2,
                        floor: 6,
                        modulus: 12,
                        method: crate::ctl::CtlSearchMethod::Exhaustive,
                    })),
                    steps: 40,
                }),
            ),
            ProgramRecord::new(
                "00_20_02".parse().unwrap(),
                Some(SimOutcome::Inf {
                    decider: Decider::Cycler(Some(crate::deciders::CyclerProof { period: 2, dx: 0 })),
                    steps: 3,
                }),
            ),
            ProgramRecord::new(
                "00_02_01".parse().unwrap(),
                Some(SimOutcome::Inf {
                    decider: Decider::Cycler(Some(
                        crate::deciders::CyclerProof { period: 2, dx: 1 },
                    )),
                    steps: 2,
                }),
            ),
            ProgramRecord::new(
                "00_02_01_40_12_01".parse().unwrap(),
                Some(SimOutcome::Inf {
                    decider: Decider::Bouncer(Some(crate::deciders::BouncerProof {
                        bounce_steps: 18,
                        gap_growth: 2,
                    })),
                    steps: 18,
                }),
            ),
            ProgramRecord::new(
                "00_02_01_13_04_01".parse().unwrap(),
                Some(SimOutcome::Inf {
                    decider: Decider::SeparatedComponents(Some(
                        crate::deciders::SeparatedComponentsProof {
                            period: 4,
                            dx_left: -1,
                            dx_right: 1,
                        },
                    )),
                    steps: 4,
                }),
            ),
            ProgramRecord::new(
                "00_00_00_04_41_11_33_80_22_12_56".parse().unwrap(),
                Some(SimOutcome::Inf {
                    decider: Decider::AcceleratedInfinite(Some(
                        crate::deciders::AcceleratedInfiniteProof::new(
                            1,
                            &[-1, 1],
                            &[1, 1],
                        ),
                    )),
                    steps: 25,
                }),
            ),
            ProgramRecord::new(
                "00_01_20_03".parse().unwrap(),
                Some(SimOutcome::unknown_coord_overflow(9_223_372_036_854_776_075)),
            ),
            ProgramRecord::new("00_01_20_03".parse().unwrap(), None),
        ];

        let mut buf = Vec::new();
        write_records(&mut buf, &records).unwrap();

        let parsed = read_records(Cursor::new(buf)).unwrap();
        assert_eq!(parsed, records);
    }

    #[test]
    fn test_ctl_proof_comment_backward_compatibility_and_algorithms() {
        let input = "\
            # Legacy format without method= or alg=
            00_20_10_04_21_21_07_50_17_01\tDECIDED\tCTL\t60 # states=4757 floor=6 mod=1
            # Inferred format with method=
            01_00_02_03_05_60_23_05_13_19\tDECIDED\tCTL\t240 # states=63 floor=10 mod=1 method=inferred
            # Legacy format with alg=
            00_02_21_40_11_--_10_08_43_11\tDECIDED\tCTL\t40 # states=300 floor=6 mod=12 alg=exhaustive
        ";

        let records = read_records(Cursor::new(input)).unwrap();
        assert_eq!(records.len(), 3);

        match &records[0].outcome {
            Some(SimOutcome::Inf {
                decider: Decider::Ctl(Some(proof)),
                ..
            }) => {
                assert_eq!(proof.method, crate::ctl::CtlSearchMethod::Manual);
                assert_eq!(proof.floor, 6);
                assert_eq!(proof.modulus, 1);
            }
            other => panic!("expected legacy CTL proof, got {:?}", other),
        }

        match &records[1].outcome {
            Some(SimOutcome::Inf {
                decider: Decider::Ctl(Some(proof)),
                ..
            }) => {
                assert_eq!(proof.method, crate::ctl::CtlSearchMethod::Inferred);
                assert_eq!(proof.floor, 10);
            }
            other => panic!("expected inferred CTL proof, got {:?}", other),
        }

        match &records[2].outcome {
            Some(SimOutcome::Inf {
                decider: Decider::Ctl(Some(proof)),
                ..
            }) => {
                assert_eq!(proof.method, crate::ctl::CtlSearchMethod::Exhaustive);
                assert_eq!(proof.modulus, 12);
            }
            other => panic!("expected exhaustive CTL proof, got {:?}", other),
        }
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
            Some(SimOutcome::unknown_step_limit(50))
        );
        assert_eq!(records[3].outcome, None);

        let programs = read_programs(Cursor::new(input)).unwrap();
        assert_eq!(programs.len(), 4);
        assert_eq!(programs[0].to_string(), "00_11_03_21_04");
    }

    #[test]
    fn test_format_count() {
        assert_eq!(format_count(0), "0");
        assert_eq!(format_count(9), "9");
        assert_eq!(format_count(999), "999");
        assert_eq!(format_count(1000), "1,000");
        assert_eq!(format_count(23884622), "23,884,622");
    }

    #[test]
    fn test_accelerated_infinite_differing_periods_roundtrip() {
        let proof = crate::deciders::AcceleratedInfiniteProof::new(
            4,
            &[-4, 0, 2],
            &[1, 2, 4],
        );
        let outcome = SimOutcome::Inf {
            decider: Decider::AcceleratedInfinite(Some(proof)),
            steps: 40,
        };
        assert_eq!(
            outcome.to_string(),
            "INF\tAcceleratedInfinite\t40 # period=4 dxs=[-4,0,2] periods=[1,2,4]"
        );

        let input = "00_01\tINF\tAcceleratedInfinite\t40 # period=4 dxs=[-4,0,2] periods=[1,2,4]\n";
        let records = read_records(Cursor::new(input)).unwrap();
        assert_eq!(records.len(), 1);
        assert_eq!(records[0].outcome, Some(outcome));
    }

    #[test]
    fn test_unknown_reason_io_formats() {
        let step_lim = SimOutcome::unknown_step_limit(1000);
        let overflow = SimOutcome::unknown_coord_overflow(2000);

        assert_eq!(step_lim.to_string(), "UNKNOWN\tSTEP_LIMIT\t1000");
        assert_eq!(overflow.to_string(), "UNKNOWN\tOVERFLOW\t2000");

        let input = "\
            00_01\tUNKNOWN\tSTEP_LIMIT\t1000\n\
            00_02\tUNKNOWN\tOVERFLOW\t2000\n\
            00_11\tUNKNOWN\t3000\n\
            00_20\tOVERFLOW\t4000\n\
        ";

        let records = read_records(Cursor::new(input)).unwrap();
        assert_eq!(records.len(), 4);
        assert_eq!(records[0].outcome, Some(SimOutcome::unknown_step_limit(1000)));
        assert_eq!(records[1].outcome, Some(SimOutcome::unknown_coord_overflow(2000)));
        assert_eq!(records[2].outcome, Some(SimOutcome::unknown_step_limit(3000)));
        assert_eq!(records[3].outcome, Some(SimOutcome::unknown_coord_overflow(4000)));
    }

    #[test]
    fn test_invalid_record_errors() {
        let bad_prog = "99_00\n";
        assert!(read_records(Cursor::new(bad_prog)).is_err());

        let bad_outcome = "00_01\tUNKNOWN_STATUS\t5\n";
        assert!(read_records(Cursor::new(bad_outcome)).is_err());
    }
}
