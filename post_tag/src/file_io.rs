use crate::simulate::{HaltCondition, InfiniteReason};
use crate::tag_system::TagSystem;
use std::fs::File;
use std::io::{BufRead, BufReader, Write};
use std::path::Path;

pub fn resolve_program_string(input: &str) -> String {
    if let Some((file_path, line_idx_str)) = input.rsplit_once(':') {
        if let Ok(line_idx) = line_idx_str.parse::<usize>() {
            let path = Path::new(file_path);
            if path.exists() && path.is_file() {
                if let Ok(file) = File::open(path) {
                    let reader = BufReader::new(file);
                    if let Some(Ok(line)) = reader.lines().nth(line_idx) {
                        if let Some(prog_str) = line.split_whitespace().find(|p| p.starts_with("prog=")) {
                            if let Some(prog) = prog_str.strip_prefix("prog=") {
                                return prog.to_string();
                            }
                        }
                        return line.trim().to_string();
                    }
                }
            }
        }
    }
    input.to_string()
}

pub fn write_result<W: Write>(w: &mut W, sys: &TagSystem, condition: &HaltCondition) -> std::io::Result<()> {
    let dense = sys.dense_string();
    match condition {
        HaltCondition::Halted(steps, space) => {
            writeln!(w, "prog={} status=Halt steps={} space={}", dense, steps, space)
        }
        HaltCondition::Infinite(reason, _steps) => {
            let reason_str = match reason {
                InfiniteReason::Cycle(period) => format!("Cycle period={}", period),
                InfiniteReason::ImmortalSubstring(w) => {
                    let mut s = String::new();
                    for &c in w {
                        s.push_str(&c.to_string());
                    }
                    format!("ImmortalSubstring substring={}", s)
                }
                InfiniteReason::NonDecreasingSymbol(c) => format!("NonDecreasingSymbol symbol={}", c),
                InfiniteReason::ClosedSymbol(c) => format!("ClosedSymbol symbol={}", c),
                InfiniteReason::TranslationCycle(period, _) => format!("TranslationCycle period={}", period),
            };
            writeln!(w, "prog={} status=Infinite reason={}", dense, reason_str)
        }
        HaltCondition::Unknown => {
            writeln!(w, "prog={} status=Unknown", dense)
        }
        HaltCondition::UndefinedRule(_) => Ok(()),
    }
}

pub fn read_unknowns(path: &Path) -> std::io::Result<Vec<String>> {
    let file = File::open(path)?;
    let reader = BufReader::new(file);
    let mut unknowns = Vec::new();

    for line in reader.lines() {
        let line = line?;
        if line.contains("status=Unknown") {
            if let Some(prog_str) = line.split_whitespace().find(|p| p.starts_with("prog=")) {
                let prog = prog_str.strip_prefix("prog=").unwrap();
                unknowns.push(prog.to_string());
            }
        }
    }
    
    Ok(unknowns)
}
