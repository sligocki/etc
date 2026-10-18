use std::fmt;
use std::str::FromStr;

/// Error type for constructing or parsing a Pebble Automaton rule or program.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProgramError {
    EmptyProgram,
    InvalidRuleSum {
        pebbles: u8,
        left: u8,
        right: u8,
    },
    InvalidRuleStay {
        pebbles: u8,
        left: u8,
        stay: u8,
        right: u8,
    },
    InvalidRuleFormat(String),
    InvalidDigit(char),
    DigitOutOfRange(u8),
    InvalidPebbleIndex {
        pebbles: u8,
        size: usize,
    },
}

impl fmt::Display for ProgramError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ProgramError::EmptyProgram => write!(f, "program must have at least 1 rule"),
            ProgramError::InvalidRuleSum {
                pebbles,
                left,
                right,
            } => write!(
                f,
                "invalid rule for {pebbles} pebbles: L({left}) + R({right}) > {pebbles}"
            ),
            ProgramError::InvalidRuleStay {
                pebbles,
                left,
                stay,
                right,
            } => write!(
                f,
                "invalid rule for {pebbles} pebbles: L({left}) + S({stay}) + R({right}) != {pebbles}"
            ),
            ProgramError::InvalidRuleFormat(s) => write!(f, "invalid rule format: '{s}'"),
            ProgramError::InvalidDigit(c) => write!(f, "invalid pebble digit character: '{c}'"),
            ProgramError::DigitOutOfRange(v) => {
                write!(f, "pebble count {v} exceeds base-36 digit limit (35)")
            }
            ProgramError::InvalidPebbleIndex { pebbles, size } => write!(
                f,
                "pebble index {pebbles} is out of bounds for program of size {size}"
            ),
        }
    }
}

impl std::error::Error for ProgramError {}

/// Encode a pebble count (`0..=35`) as a single character (`'0'..='9'`, `'a'..='z'`).
pub fn encode_pebble_digit(value: u8) -> Result<char, ProgramError> {
    match value {
        0..=9 => Ok((b'0' + value) as char),
        10..=35 => Ok((b'a' + (value - 10)) as char),
        _ => Err(ProgramError::DigitOutOfRange(value)),
    }
}

/// Decode a single character (`'0'..='9'`, `'a'..='z'`, `'A'..='Z'`) into a pebble count (`0..=35`).
pub fn decode_pebble_digit(ch: char) -> Result<u8, ProgramError> {
    match ch {
        '0'..='9' => Ok(ch as u8 - b'0'),
        'a'..='z' => Ok(ch as u8 - b'a' + 10),
        'A'..='Z' => Ok(ch as u8 - b'A' + 10),
        _ => Err(ProgramError::InvalidDigit(ch)),
    }
}

/// A transition rule for a cell containing `k = left + stay + right` pebbles.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Rule {
    pub left: u8,
    pub stay: u8,
    pub right: u8,
}

impl Rule {
    /// Create a rule for `pebbles` total pebbles, pushing `left` left and `right` right.
    /// The remaining `stay = pebbles - left - right` pebbles stay in the current cell.
    pub fn new(pebbles: u8, left: u8, right: u8) -> Result<Self, ProgramError> {
        if left.saturating_add(right) > pebbles {
            return Err(ProgramError::InvalidRuleSum {
                pebbles,
                left,
                right,
            });
        }
        let stay = pebbles - left - right;
        Ok(Self { left, stay, right })
    }

    /// Create a rule from explicit `(left, stay, right)` components for `pebbles`.
    pub fn from_lsr(pebbles: u8, left: u8, stay: u8, right: u8) -> Result<Self, ProgramError> {
        if left.saturating_add(stay).saturating_add(right) != pebbles {
            return Err(ProgramError::InvalidRuleStay {
                pebbles,
                left,
                stay,
                right,
            });
        }
        Ok(Self { left, stay, right })
    }

    /// Total number of pebbles this rule applies to (`left + stay + right`).
    #[inline]
    pub fn pebbles(&self) -> u8 {
        self.left + self.stay + self.right
    }

    /// Returns true if no pebbles move to neighboring cells (`left == 0 && right == 0`).
    #[inline]
    pub fn is_stationary(&self) -> bool {
        self.left == 0 && self.right == 0
    }

    /// Number of valid `(left, right)` rule choices for `k` pebbles: `(k + 1) * (k + 2) / 2`.
    #[inline]
    pub fn num_choices(pebbles: u8) -> u128 {
        let k = pebbles as u128;
        ((k + 1) * (k + 2)) / 2
    }

    /// Generate all `(k + 1) * (k + 2) / 2` valid rules for `pebbles` in lexicographical order of `(left, right)`.
    pub fn all_for_pebbles(pebbles: u8) -> Vec<Rule> {
        let mut rules = Vec::with_capacity(Self::num_choices(pebbles) as usize);
        for left in 0..=pebbles {
            for right in 0..=(pebbles - left) {
                let stay = pebbles - left - right;
                rules.push(Rule { left, stay, right });
            }
        }
        rules
    }

    /// Format rule in 2-character short notation (`LR`).
    pub fn to_short_string(&self) -> String {
        let l = encode_pebble_digit(self.left).unwrap_or('?');
        let r = encode_pebble_digit(self.right).unwrap_or('?');
        format!("{l}{r}")
    }
}

/// A 1D Pebble Automaton program of size `n`.
///
/// Rules are indexed for pebble counts `1..=n` (stored at `rules[k - 1]`).
/// A rule slot may be `None` to represent an undefined transition in Tree-Normal-Form (TNF).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Program {
    rules: Vec<Option<Rule>>,
}

impl Program {
    /// Construct a program from a list of optional rules for `k = 1..=rules.len()`.
    pub fn new(rules: Vec<Option<Rule>>) -> Result<Self, ProgramError> {
        if rules.is_empty() {
            return Err(ProgramError::EmptyProgram);
        }
        for (idx, rule_opt) in rules.iter().enumerate() {
            let k = (idx + 1) as u8;
            if let Some(rule) = rule_opt {
                if rule.left.saturating_add(rule.stay).saturating_add(rule.right) != k {
                    return Err(ProgramError::InvalidRuleStay {
                        pebbles: k,
                        left: rule.left,
                        stay: rule.stay,
                        right: rule.right,
                    });
                }
            }
        }
        Ok(Self { rules })
    }

    /// Construct an empty program of `size` where all rules `1..=size` are `None` (undefined).
    pub fn empty(size: usize) -> Result<Self, ProgramError> {
        if size == 0 {
            return Err(ProgramError::EmptyProgram);
        }
        Ok(Self {
            rules: vec![None; size],
        })
    }

    /// Return the size `n` of the program (which is also the initial number of pebbles at `x = 0`).
    #[inline]
    pub fn size(&self) -> usize {
        self.rules.len()
    }

    /// Return the slice of optional rules for `k = 1..=size`.
    #[inline]
    pub fn rules(&self) -> &[Option<Rule>] {
        &self.rules
    }

    /// Look up the rule for `pebbles` (`0..=size`).
    /// For `0` pebbles, always returns `Some(Rule { left: 0, stay: 0, right: 0 })`.
    #[inline]
    pub fn rule(&self, pebbles: u8) -> Option<Rule> {
        if pebbles == 0 {
            return Some(Rule {
                left: 0,
                stay: 0,
                right: 0,
            });
        }
        let idx = (pebbles as usize).checked_sub(1)?;
        self.rules.get(idx).copied().flatten()
    }

    /// Set or clear the rule for `pebbles` (`1..=size`).
    pub fn set_rule(&mut self, pebbles: u8, rule: Option<Rule>) -> Result<(), ProgramError> {
        let size = self.size();
        if pebbles == 0 || (pebbles as usize) > size {
            return Err(ProgramError::InvalidPebbleIndex { pebbles, size });
        }
        if let Some(r) = rule {
            if r.left.saturating_add(r.stay).saturating_add(r.right) != pebbles {
                return Err(ProgramError::InvalidRuleStay {
                    pebbles,
                    left: r.left,
                    stay: r.stay,
                    right: r.right,
                });
            }
        }
        self.rules[pebbles as usize - 1] = rule;
        Ok(())
    }

    /// Returns true if all rules `1..=size` are defined (`Some`).
    pub fn is_complete(&self) -> bool {
        self.rules.iter().all(Option::is_some)
    }

    /// Total number of complete Cartesian programs of a given `size`:
    /// $\prod_{k=1}^{\text{size}} \frac{(k+1)(k+2)}{2}$.
    pub fn total_cartesian_programs(size: usize) -> u128 {
        if size == 0 {
            return 0;
        }
        (1..=size as u8).map(Rule::num_choices).product()
    }

    /// Number of complete Cartesian programs represented by this (possibly partial TNF) program,
    /// equal to the product of `Rule::num_choices(k)` over all undefined (`None`) rules `k`.
    pub fn expansion_factor(&self) -> u128 {
        self.rules
            .iter()
            .enumerate()
            .filter(|(_, r)| r.is_none())
            .map(|(idx, _)| Rule::num_choices((idx + 1) as u8))
            .product()
    }

    /// Format the program in the wiki's multi-line long notation (`k --> L | S | R`).
    pub fn to_long_string(&self) -> String {
        let mut lines = Vec::with_capacity(self.rules.len());
        for (idx, rule_opt) in self.rules.iter().enumerate() {
            let k = idx + 1;
            match rule_opt {
                Some(r) => lines.push(format!("{k} --> {} | {} | {}", r.left, r.stay, r.right)),
                None => lines.push(format!("{k} --> - | - | -")),
            }
        }
        lines.join("\n")
    }

    /// Parse a program from the wiki's multi-line long notation (`k --> L | S | R`).
    /// Unmentioned pebble counts below the maximum `k` remain `None`.
    pub fn from_long_str(s: &str) -> Result<Self, ProgramError> {
        let mut parsed_entries: Vec<(u8, Option<Rule>)> = Vec::new();
        let mut max_k: u8 = 0;

        for raw_line in s.lines() {
            let line = raw_line.split('#').next().unwrap_or("").trim();
            if line.is_empty() {
                continue;
            }
            let (lhs, rhs) = line
                .split_once("-->")
                .ok_or_else(|| ProgramError::InvalidRuleFormat(line.to_string()))?;
            let k: u8 = lhs
                .trim()
                .parse()
                .map_err(|_| ProgramError::InvalidRuleFormat(line.to_string()))?;
            if k == 0 {
                continue;
            }
            let parts: Vec<&str> = rhs.split('|').map(str::trim).collect();
            if parts.len() != 3 {
                return Err(ProgramError::InvalidRuleFormat(line.to_string()));
            }
            let rule_opt = if parts[0] == "-" && parts[1] == "-" && parts[2] == "-" {
                None
            } else {
                let left: u8 = parts[0]
                    .parse()
                    .map_err(|_| ProgramError::InvalidRuleFormat(line.to_string()))?;
                let stay: u8 = parts[1]
                    .parse()
                    .map_err(|_| ProgramError::InvalidRuleFormat(line.to_string()))?;
                let right: u8 = parts[2]
                    .parse()
                    .map_err(|_| ProgramError::InvalidRuleFormat(line.to_string()))?;
                Some(Rule::from_lsr(k, left, stay, right)?)
            };
            if k > max_k {
                max_k = k;
            }
            parsed_entries.push((k, rule_opt));
        }

        if max_k == 0 {
            return Err(ProgramError::EmptyProgram);
        }

        let mut prog = Program::empty(max_k as usize)?;
        for (k, rule_opt) in parsed_entries {
            prog.set_rule(k, rule_opt)?;
        }
        Ok(prog)
    }
}

impl fmt::Display for Program {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (idx, rule_opt) in self.rules.iter().enumerate() {
            if idx > 0 {
                write!(f, "_")?;
            }
            match rule_opt {
                Some(rule) => {
                    let l = encode_pebble_digit(rule.left).map_err(|_| fmt::Error)?;
                    let r = encode_pebble_digit(rule.right).map_err(|_| fmt::Error)?;
                    write!(f, "{l}{r}")?;
                }
                None => write!(f, "--")?,
            }
        }
        Ok(())
    }
}

impl FromStr for Program {
    type Err = ProgramError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let trimmed = s.trim();
        if trimmed.is_empty() {
            return Err(ProgramError::EmptyProgram);
        }
        let tokens: Vec<&str> = trimmed.split('_').collect();
        let mut rules = Vec::with_capacity(tokens.len());

        for (idx, token) in tokens.iter().enumerate() {
            let k = (idx + 1) as u8;
            if *token == "--" || *token == ".." {
                rules.push(None);
                continue;
            }
            let mut chars = token.chars();
            let l_ch = chars
                .next()
                .ok_or_else(|| ProgramError::InvalidRuleFormat((*token).to_string()))?;
            let r_ch = chars
                .next()
                .ok_or_else(|| ProgramError::InvalidRuleFormat((*token).to_string()))?;
            if chars.next().is_some() {
                return Err(ProgramError::InvalidRuleFormat((*token).to_string()));
            }
            let left = decode_pebble_digit(l_ch)?;
            let right = decode_pebble_digit(r_ch)?;
            rules.push(Some(Rule::new(k, left, right)?));
        }

        Program::new(rules)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rule_creation_and_choices() {
        let r = Rule::new(5, 2, 1).unwrap();
        assert_eq!(r.left, 2);
        assert_eq!(r.stay, 2);
        assert_eq!(r.right, 1);
        assert_eq!(r.pebbles(), 5);
        assert!(!r.is_stationary());

        let stationary = Rule::new(3, 0, 0).unwrap();
        assert!(stationary.is_stationary());

        assert!(Rule::new(4, 3, 2).is_err());

        for k in 1..=6 {
            let all = Rule::all_for_pebbles(k);
            assert_eq!(all.len() as u128, Rule::num_choices(k));
        }
    }

    #[test]
    fn test_short_format_roundtrip() {
        let champ5 = "00_11_03_21_04";
        let prog: Program = champ5.parse().unwrap();
        assert_eq!(prog.size(), 5);
        assert!(prog.is_complete());
        assert_eq!(prog.to_string(), champ5);
        assert_eq!(prog.expansion_factor(), 1);

        let r4 = prog.rule(4).unwrap();
        assert_eq!(
            r4,
            Rule {
                left: 2,
                stay: 1,
                right: 1
            }
        );
    }

    #[test]
    fn test_partial_tnf_program_and_expansion_factor() {
        let tnf_str = "--_11_--_21_04";
        let prog: Program = tnf_str.parse().unwrap();
        assert_eq!(prog.size(), 5);
        assert!(!prog.is_complete());
        assert_eq!(prog.rule(1), None);
        assert_eq!(prog.rule(3), None);
        assert_eq!(prog.to_string(), tnf_str);
        // k=1 has 3 choices, k=3 has 10 choices -> expansion factor = 30
        assert_eq!(prog.expansion_factor(), 3 * 10);
    }

    #[test]
    fn test_base36_digits_and_large_program() {
        // Test size 11 with 'a' (10) and 'b' (11)
        let s = "00_00_00_00_00_00_00_00_00_a0_0b";
        let prog: Program = s.parse().unwrap();
        assert_eq!(prog.size(), 11);
        assert_eq!(
            prog.rule(10).unwrap(),
            Rule {
                left: 10,
                stay: 0,
                right: 0
            }
        );
        assert_eq!(
            prog.rule(11).unwrap(),
            Rule {
                left: 0,
                stay: 0,
                right: 11
            }
        );
        assert_eq!(prog.to_string(), s);
    }

    #[test]
    fn test_long_format_roundtrip() {
        let prog: Program = "00_11_03_21_04".parse().unwrap();
        let long_str = prog.to_long_string();
        let parsed = Program::from_long_str(&long_str).unwrap();
        assert_eq!(prog, parsed);
    }

    #[test]
    fn test_cartesian_program_counts() {
        assert_eq!(Program::total_cartesian_programs(1), 3);
        assert_eq!(Program::total_cartesian_programs(2), 18);
        assert_eq!(Program::total_cartesian_programs(3), 180);
        assert_eq!(Program::total_cartesian_programs(4), 2_700);
        assert_eq!(Program::total_cartesian_programs(5), 56_700);
        assert_eq!(Program::total_cartesian_programs(6), 1_587_600);
    }
}
