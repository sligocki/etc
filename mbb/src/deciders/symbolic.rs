use std::collections::HashMap;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConditionType {
    GreaterEqualZero,
    EqualZero,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AffineExpr {
    pub constant: i64,
    pub coeffs: HashMap<usize, i64>,
}

impl AffineExpr {
    pub fn new(constant: i64) -> Self {
        AffineExpr {
            constant,
            coeffs: HashMap::new(),
        }
    }

    pub fn var(idx: usize) -> Self {
        let mut expr = AffineExpr::new(0);
        expr.coeffs.insert(idx, 1);
        expr
    }

    pub fn add(&mut self, other: &AffineExpr) {
        self.constant += other.constant;
        for (&k, &v) in &other.coeffs {
            *self.coeffs.entry(k).or_insert(0) += v;
        }
    }

    pub fn add_const(&mut self, c: i64) {
        self.constant += c;
    }

    pub fn mul_add(&mut self, mult: i64, other: &AffineExpr) {
        if mult == 0 { return; }
        self.constant += mult * other.constant;
        for (&k, &v) in &other.coeffs {
            *self.coeffs.entry(k).or_insert(0) += mult * v;
        }
    }

    pub fn sub(&mut self, other: &AffineExpr) {
        self.constant -= other.constant;
        for (&k, &v) in &other.coeffs {
            *self.coeffs.entry(k).or_insert(0) -= v;
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Condition {
    pub expr: AffineExpr,
    pub cond_type: ConditionType,
}

impl Condition {
    pub fn geq_zero(expr: AffineExpr) -> Self {
        Condition {
            expr,
            cond_type: ConditionType::GreaterEqualZero,
        }
    }

    pub fn eq_zero(expr: AffineExpr) -> Self {
        Condition {
            expr,
            cond_type: ConditionType::EqualZero,
        }
    }
}

impl std::fmt::Display for AffineExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut first = true;
        let mut sorted_coeffs: Vec<_> = self.coeffs.iter().collect();
        sorted_coeffs.sort_by_key(|&(k, _)| k);
        for (&k, &v) in sorted_coeffs {
            if v == 0 { continue; }
            if !first {
                if v > 0 { write!(f, " + ")?; }
                else { write!(f, " - ")?; }
            } else if v < 0 {
                write!(f, "-")?;
            }
            first = false;
            let abs_v = v.abs();
            if abs_v != 1 { write!(f, "{}", abs_v)?; }
            write!(f, "{}", (b'a' + k as u8) as char)?;
        }
        if self.constant != 0 || first {
            if !first {
                if self.constant > 0 { write!(f, " + ")?; }
                else { write!(f, " - ")?; }
                write!(f, "{}", self.constant.abs())?;
            } else {
                write!(f, "{}", self.constant)?;
            }
        }
        Ok(())
    }
}

impl std::fmt::Display for Condition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.cond_type {
            ConditionType::GreaterEqualZero => write!(f, "{} >= 0", self.expr),
            ConditionType::EqualZero => write!(f, "{} == 0", self.expr),
        }
    }
}
