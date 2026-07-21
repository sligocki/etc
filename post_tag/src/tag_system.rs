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
}
