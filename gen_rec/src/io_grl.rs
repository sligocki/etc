//! Read and write `.grl` (GRF Results List) files.
//!
//! **Line format** (one GRF per line):
//!   `grf=EXPR [status=Halt|Diverge|Unknown] [steps=N] [score=N]`
//!
//! Comment/blank lines are skipped.  Unknown keys are ignored, so the format
//! is forward-compatible with new fields added in the future.
//!
//! **Backward-compatible old formats** are also parsed:
//!   `STEPS  EXPR`   — leading step count (holdout files from bb_search)
//!   `EXPR`          — plain expression per line

use crate::base::Num;
use std::fmt;
use std::io::{self, Write};

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Status {
    Halt,
    Diverge,
    Unknown,
}

impl fmt::Display for Status {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Status::Halt    => write!(f, "Halt"),
            Status::Diverge => write!(f, "Diverge"),
            Status::Unknown => write!(f, "Unknown"),
        }
    }
}

impl std::str::FromStr for Status {
    type Err = ();
    fn from_str(s: &str) -> Result<Self, ()> {
        match s {
            "Halt"    => Ok(Status::Halt),
            "Diverge" => Ok(Status::Diverge),
            "Unknown" => Ok(Status::Unknown),
            _         => Err(()),
        }
    }
}

#[derive(Clone, Debug)]
pub struct GrfEntry {
    pub expr:           String,
    pub status:         Option<Status>,
    pub steps:          Option<Num>,
    pub base_steps:     Option<Num>,
    pub score:          Option<Num>,
    pub unknown_reason: Option<String>,
}

// ---------------------------------------------------------------------------
// Reading
// ---------------------------------------------------------------------------

/// Parse all GRF entries from the text content of a file.
///
/// Handles both the `.grl` key=value format and the two legacy formats
/// (`STEPS  EXPR` and plain `EXPR`).  Blank lines and `#` comments are
/// skipped.
pub fn parse_grf_entries(content: &str) -> Vec<GrfEntry> {
    let mut out = Vec::new();
    for raw in content.lines() {
        let line = raw.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        out.push(parse_line(line));
    }
    out
}

fn parse_line(line: &str) -> GrfEntry {
    // New format: at least one token is "key=value" where key is a known field.
    if line.contains("grf=") {
        return parse_kv_line(line);
    }
    // Legacy format: "STEPS  EXPR" or plain "EXPR".
    let mut parts = line.splitn(2, |c: char| c.is_whitespace());
    let first = parts.next().unwrap_or("").trim();
    if let Ok(steps) = first.parse::<Num>() {
        let expr = parts.next().map(str::trim).unwrap_or("").to_string();
        GrfEntry { expr, status: None, steps: Some(steps), base_steps: None, score: None, unknown_reason: None }
    } else {
        GrfEntry { expr: line.to_string(), status: None, steps: None, base_steps: None, score: None, unknown_reason: None }
    }
}

fn parse_kv_line(line: &str) -> GrfEntry {
    let mut expr           = String::new();
    let mut status         = None;
    let mut steps          = None;
    let mut base_steps     = None;
    let mut score          = None;
    let mut unknown_reason = None;

    for token in line.split_whitespace() {
        if let Some(v) = token.strip_prefix("grf=") {
            expr = v.to_string();
        } else if let Some(v) = token.strip_prefix("status=") {
            status = v.parse::<Status>().ok();
        } else if let Some(v) = token.strip_prefix("steps=") {
            steps = v.parse::<Num>().ok();
        } else if let Some(v) = token.strip_prefix("base_steps=") {
            base_steps = v.parse::<Num>().ok();
        } else if let Some(v) = token.strip_prefix("score=") {
            score = v.parse::<Num>().ok();
        } else if let Some(v) = token.strip_prefix("unknown_reason=") {
            unknown_reason = Some(v.to_string());
        }
        // other unknown keys are ignored
    }

    GrfEntry { expr, status, steps, base_steps, score, unknown_reason }
}

// ---------------------------------------------------------------------------
// Writing
// ---------------------------------------------------------------------------

/// Write `# format: grl/1.0\n# <comment>\n` to any writer.
pub fn write_grl_header(w: &mut dyn Write, comment: &str) -> io::Result<()> {
    writeln!(w, "# format: grl/1.0")?;
    if !comment.is_empty() {
        writeln!(w, "# {}", comment)?;
    }
    Ok(())
}

/// Write one `GrfEntry` as a `key=value` line.  `grf=` is always first.
///
/// Spaces are stripped from the expression (`", "` → `","`) so the `grf=`
/// token remains a single whitespace-delimited token on the line.
pub fn write_grf_entry(w: &mut dyn Write, entry: &GrfEntry) -> io::Result<()> {
    let compact = entry.expr.replace(", ", ",");
    assert!(!compact.contains(' '), "grl expr still has spaces after replace: {compact}");
    write!(w, "grf={}", compact)?;
    if let Some(s) = entry.status            { write!(w, " status={}", s)?; }
    if let Some(r) = &entry.unknown_reason   { write!(w, " unknown_reason={}", r)?; }
    if let Some(n) = entry.steps             { write!(w, " steps={}", n)?; }
    if let Some(n) = entry.base_steps        { write!(w, " base_steps={}", n)?; }
    if let Some(v) = entry.score             { write!(w, " score={}", v)?; }
    writeln!(w)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_kv_all_fields() {
        let entries = parse_grf_entries("grf=R(Z0,S) status=Halt steps=42 score=7");
        assert_eq!(entries.len(), 1);
        let e = &entries[0];
        assert_eq!(e.expr, "R(Z0,S)");
        assert_eq!(e.status, Some(Status::Halt));
        assert_eq!(e.steps, Some(42));
        assert_eq!(e.score, Some(7));
    }

    #[test]
    fn parse_kv_unknown_keys_ignored() {
        let entries = parse_grf_entries("grf=Z0 status=Unknown future_field=xyz steps=1");
        assert_eq!(entries[0].expr, "Z0");
        assert_eq!(entries[0].status, Some(Status::Unknown));
        assert_eq!(entries[0].steps, Some(1));
    }

    #[test]
    fn parse_kv_grf_only() {
        let entries = parse_grf_entries("grf=M(S)");
        assert_eq!(entries[0].expr, "M(S)");
        assert_eq!(entries[0].status, None);
        assert_eq!(entries[0].steps, None);
    }

    #[test]
    fn parse_legacy_steps_expr() {
        let entries = parse_grf_entries("100000  M(C(R(Z0,P(2,1)),S))");
        assert_eq!(entries[0].expr, "M(C(R(Z0,P(2,1)),S))");
        assert_eq!(entries[0].steps, Some(100000));
        assert_eq!(entries[0].status, None);
    }

    #[test]
    fn parse_legacy_plain_expr() {
        let entries = parse_grf_entries("M(S)");
        assert_eq!(entries[0].expr, "M(S)");
        assert_eq!(entries[0].steps, None);
    }

    #[test]
    fn parse_skips_blanks_and_comments() {
        let content = "\n# a comment\n\ngrf=Z0\n# another\ngrf=S\n";
        let entries = parse_grf_entries(content);
        assert_eq!(entries.len(), 2);
        assert_eq!(entries[0].expr, "Z0");
        assert_eq!(entries[1].expr, "S");
    }

    #[test]
    fn roundtrip_write_parse() {
        let entry = GrfEntry {
            expr:           "R(Z0,P(2,1))".to_string(),
            status:         Some(Status::Unknown),
            steps:          Some(99999),
            base_steps:     None,
            score:          None,
            unknown_reason: None,
        };
        let mut buf = Vec::new();
        write_grf_entry(&mut buf, &entry).unwrap();
        let s = String::from_utf8(buf).unwrap();
        let back = parse_grf_entries(&s);
        assert_eq!(back.len(), 1);
        assert_eq!(back[0].expr, entry.expr);
        assert_eq!(back[0].status, entry.status);
        assert_eq!(back[0].steps, entry.steps);
        assert_eq!(back[0].base_steps, entry.base_steps);
        assert_eq!(back[0].score, entry.score);
    }

    #[test]
    fn roundtrip_base_steps() {
        let entry = GrfEntry {
            expr:           "M(R(P(1,1),S))".to_string(),
            status:         Some(Status::Halt),
            steps:          Some(42),
            base_steps:     Some(113),
            score:          Some(7),
            unknown_reason: None,
        };
        let mut buf = Vec::new();
        write_grf_entry(&mut buf, &entry).unwrap();
        let s = String::from_utf8(buf).unwrap();
        assert!(s.contains("base_steps=113"), "line: {s}");
        let back = parse_grf_entries(&s);
        assert_eq!(back[0].base_steps, Some(113));
        assert_eq!(back[0].steps, Some(42));
        assert_eq!(back[0].score, Some(7));
        // non-Halt entry: base_steps absent → parses as None
        let non_halt = "grf=Z0 status=Unknown steps=5";
        assert_eq!(parse_grf_entries(non_halt)[0].base_steps, None);
    }

    #[test]
    fn roundtrip_nested_grf_with_spaces() {
        // write_grf_entry strips spaces so the grf= token is whitespace-free,
        // matching what Grf::Display produces (e.g. "R(Z0, P(2,1))").
        let entry = GrfEntry {
            expr:           "M(C(R(Z1, P(3,2)), S))".to_string(),
            status:         Some(Status::Unknown),
            steps:          Some(100000),
            base_steps:     None,
            score:          None,
            unknown_reason: None,
        };
        let mut buf = Vec::new();
        write_grf_entry(&mut buf, &entry).unwrap();
        let line = String::from_utf8(buf).unwrap();
        let grf_token = line.split_whitespace().find(|t| t.starts_with("grf=")).unwrap();
        assert_eq!(grf_token, "grf=M(C(R(Z1,P(3,2)),S))");
        let back = parse_grf_entries(&line);
        assert_eq!(back[0].expr, "M(C(R(Z1,P(3,2)),S))");
        assert_eq!(back[0].status, entry.status);
        assert_eq!(back[0].steps, entry.steps);
    }
}
