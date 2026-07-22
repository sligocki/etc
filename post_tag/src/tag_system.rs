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

    pub fn is_immortal_substring(v: usize, rules: &[Option<Vec<u8>>], w: &[u8]) -> Option<bool> {
        if w.len() < v {
            return Some(false);
        }
        for k in 0..v {
            let p = (v - ((k + w.len()) % v)) % v;
            let l = k + w.len() + p;
            let n = rules.len();
            let num_left = n.pow(k as u32);
            let num_right = n.pow(p as u32);

            for left_val in 0..num_left {
                for right_val in 0..num_right {
                    let mut s = Vec::with_capacity(l);

                    let mut lv = left_val;
                    for _ in 0..k {
                        s.push((lv % n) as u8);
                        lv /= n;
                    }

                    s.extend_from_slice(w);

                    let mut rv = right_val;
                    for _ in 0..p {
                        s.push((rv % n) as u8);
                        rv /= n;
                    }

                    let mut w_out = Vec::new();
                    let mut current_len = k + w.len();

                    for i in (0..l).step_by(v) {
                        let c = s[i];
                        if let Some(rule) = &rules[c as usize] {
                            if current_len < v {
                                return Some(false);
                            }
                            current_len = current_len - v + rule.len();
                            w_out.extend_from_slice(rule);
                        } else {
                            return None;
                        }
                    }

                    if w_out.len() < l {
                        return Some(false);
                    }

                    if current_len < v {
                        return Some(false);
                    }

                    let slice_to_check = if p <= w_out.len() { &w_out[p..] } else { &[] };

                    if slice_to_check.windows(w.len()).all(|window| window != w) {
                        return Some(false);
                    }
                }
            }
        }
        Some(true)
    }

    pub fn has_immortal_substring(&self) -> Option<Vec<u8>> {
        for rule_opt in &self.rules {
            if let Some(rule) = rule_opt {
                if rule.len() < self.v {
                    continue;
                }
                for len in self.v..=rule.len() {
                    for i in 0..=(rule.len() - len) {
                        let w = &rule[i..i + len];
                        if Self::is_immortal_substring(self.v, &self.rules, w) == Some(true) {
                            return Some(w.to_vec());
                        }
                    }
                }
            }
        }
        None
    }

    pub fn non_decreasing_symbols(&self) -> Vec<u8> {
        let n = self.rules.len();
        let mut res = Vec::new();
        for c in 0..n {
            let mut is_non_decreasing = true;
            for h in 0..n {
                if let Some(rule) = &self.rules[h] {
                    let count = rule.iter().filter(|&&x| x == c as u8).count();
                    let required = if h == c {
                        self.v
                    } else {
                        self.v.saturating_sub(1)
                    };
                    if count < required {
                        is_non_decreasing = false;
                        break;
                    }
                } else {
                    is_non_decreasing = false;
                    break;
                }
            }
            if is_non_decreasing {
                res.push(c as u8);
            }
        }
        res
    }

    pub fn closed_symbols(&self) -> Vec<u8> {
        let n = self.rules.len();
        let mut res = Vec::new();
        for c in 0..n {
            if let Some(rule) = &self.rules[c] {
                if rule.len() >= self.v && rule.len() % self.v == 0 {
                    let mut all_match = true;
                    for i in (0..rule.len()).step_by(self.v) {
                        if rule[i] != c as u8 {
                            all_match = false;
                            break;
                        }
                    }
                    if all_match {
                        res.push(c as u8);
                    }
                }
            }
        }
        res
    }
}
