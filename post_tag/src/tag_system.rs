#[derive(Clone, Debug)]
pub struct TagSystem {
    pub v: usize,
    pub rules: Vec<Option<Vec<u8>>>,
}

impl TagSystem {
    pub fn format_rules(&self) -> String {
        let mut parts = vec![];
        for (i, r) in self.rules.iter().enumerate() {
            match r {
                Some(w) if w.is_empty() => parts.push(format!("{}->eps", i)),
                Some(w) => {
                    let mut s = format!("{}->", i);
                    for &c in w {
                        s.push_str(&c.to_string());
                    }
                    parts.push(s);
                }
                None => parts.push(format!("{}->?", i)),
            }
        }
        parts.join(", ")
    }

    pub fn dense_string(&self) -> String {
        let mut parts = vec![];
        for r in &self.rules {
            match r {
                Some(w) if w.is_empty() => parts.push(String::new()),
                Some(w) => {
                    let mut s = String::new();
                    for &c in w {
                        s.push_str(&c.to_string());
                    }
                    parts.push(s);
                }
                None => parts.push("?".to_string()),
            }
        }
        parts.join("_")
    }

    pub fn parse(v: usize, s: &str) -> Self {
        if !s.contains("->") {
            let mut rules = Vec::new();
            for part in s.split('_') {
                if part == "?" {
                    rules.push(None);
                } else if part.is_empty() {
                    rules.push(Some(vec![]));
                } else {
                    let mut rv = vec![];
                    for c in part.chars() {
                        rv.push(c.to_digit(10).unwrap() as u8);
                    }
                    rules.push(Some(rv));
                }
            }
            return TagSystem { v, rules };
        }

        let mut rules = Vec::new();
        for part in s.split(',') {
            let part = part.trim();
            if part.is_empty() {
                continue;
            }
            if let Some((lhs, rhs)) = part.split_once("->") {
                let lhs: usize = lhs.trim().parse().unwrap();
                while rules.len() <= lhs {
                    rules.push(None);
                }
                let rhs = rhs.trim();
                if rhs == "?" {
                    rules[lhs] = None;
                } else if rhs == "eps" {
                    rules[lhs] = Some(vec![]);
                } else {
                    let mut rv = vec![];
                    for c in rhs.chars() {
                        rv.push(c.to_digit(10).unwrap() as u8);
                    }
                    rules[lhs] = Some(rv);
                }
            }
        }
        TagSystem { v, rules }
    }
}
