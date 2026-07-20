#[derive(Clone, Debug)]
pub struct TagSystem {
    pub v: usize,
    pub rules: Vec<Vec<u8>>,
}

impl TagSystem {
    pub fn format_rules(&self) -> String {
        let mut parts = vec![];
        for (i, r) in self.rules.iter().enumerate() {
            let mut s = format!("{}->", i);
            if r.is_empty() {
                s.push_str("eps");
            } else {
                for &c in r {
                    s.push_str(&c.to_string());
                }
            }
            parts.push(s);
        }
        parts.join(", ")
    }
}
