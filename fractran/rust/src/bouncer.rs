use crate::diff_rule::DiffRule;
use crate::program::{BigInt, Program, State, SmallInt};
use crate::transcript::{StrippedBlock, Trans};
use infinitable::{Finite, Infinitable, Infinity};
use crate::rule::Rule;

#[derive(Debug, Clone, PartialEq)]
pub struct AffineExpr {
    pub coeffs: Vec<i64>,
    pub constant: i64,
}

impl AffineExpr {
    pub fn new(num_vars: usize) -> Self {
        AffineExpr {
            coeffs: vec![0; num_vars],
            constant: 0,
        }
    }

    pub fn from_var(num_vars: usize, var_idx: usize) -> Self {
        let mut expr = Self::new(num_vars);
        expr.coeffs[var_idx] = 1;
        expr
    }

    pub fn add(&self, other: &Self) -> Self {
        let mut expr = self.clone();
        for (i, c) in other.coeffs.iter().enumerate() {
            expr.coeffs[i] += c;
        }
        expr.constant += other.constant;
        expr
    }

    pub fn scale(&self, factor: i64) -> Self {
        let mut expr = self.clone();
        for c in expr.coeffs.iter_mut() {
            *c *= factor;
        }
        expr.constant *= factor;
        expr
    }

    pub fn sub(&self, other: &Self) -> Self {
        let mut expr = self.clone();
        for (i, c) in other.coeffs.iter().enumerate() {
            expr.coeffs[i] -= c;
        }
        expr.constant -= other.constant;
        expr
    }

    pub fn evaluate(&self, vals: &[BigInt]) -> BigInt {
        let mut sum = BigInt::from(self.constant);
        for (c, v) in self.coeffs.iter().zip(vals.iter()) {
            sum += BigInt::from(*c) * v.clone();
        }
        sum
    }
}

#[derive(Debug, Clone)]
pub struct AffineState {
    pub vars: Vec<AffineExpr>,
}

impl AffineState {
    pub fn new(num_vars: usize) -> Self {
        let mut vars = Vec::new();
        for i in 0..num_vars {
            vars.push(AffineExpr::from_var(num_vars, i));
        }
        AffineState { vars }
    }

    pub fn evaluate(&self, vals: &[BigInt]) -> Vec<BigInt> {
        self.vars.iter().map(|e| e.evaluate(vals)).collect()
    }
}

#[derive(Debug)]
pub enum BouncerError {
    NonUnitDecrement,
    NotInfinite,
    ExponentialGrowth, // Or non-polynomial
    SimulationHalted,
    UnboundedMax, // when trying to apply a rule but max is finite and we can't represent it (shouldn't happen often for FRACTRAN but good to have)
}

#[derive(Debug, Clone)]
pub struct Condition {
    pub expr: AffineExpr, // expr >= 0
}

pub fn build_bouncer_transform(
    prog: &Program,
    mut concrete_state: State,
    pattern: &[StrippedBlock]
) -> Result<(AffineState, Vec<Condition>), BouncerError> {
    let num_regs = prog.num_registers();
    let mut affine = AffineState::new(num_regs);
    let mut conditions = Vec::new();

    for block in pattern {
        let rule = DiffRule::from_trans_vec(prog, &block.block).ok_or(BouncerError::SimulationHalted)?;
        
        if !rule.is_applicable(&concrete_state) {
            return Err(BouncerError::SimulationHalted);
        }

        if !block.is_rep {
            // Apply once
            // 1. Add conditions: affine >= min, affine <= max
            for i in 0..num_regs {
                // v_i >= min_i  => v_i - min_i >= 0
                let mut cond_expr = affine.vars[i].clone();
                cond_expr.constant -= rule.min.data[i] as i64;
                conditions.push(Condition { expr: cond_expr });

                if let Finite(max_val) = rule.max.data[i] {
                    // v_i <= max_i  => max_i - v_i >= 0
                    let mut cond_expr = affine.vars[i].scale(-1);
                    cond_expr.constant += max_val as i64;
                    conditions.push(Condition { expr: cond_expr });
                }
            }
            
            // 2. Update affine
            for i in 0..num_regs {
                affine.vars[i].constant += rule.delta.data[i] as i64;
            }

            // 3. Update concrete
            let mut next_data = concrete_state.data.clone();
            for i in 0..num_regs {
                next_data[i] += BigInt::from(rule.delta.data[i]);
            }
            concrete_state = State::new(next_data);

        } else {
            // Apply as many times as possible
            // 1. Find the bounding register from the concrete state
            let mut min_apps: Option<BigInt> = None;
            let mut bound_reg = None;
            for i in 0..num_regs {
                let del = rule.delta.data[i];
                let val = &concrete_state.data[i];
                let min_val = rule.min.data[i];
                let max_val = &rule.max.data[i];

                if del < 0 {
                    let apps = (val.clone() - BigInt::from(min_val)) / -del + 1;
                    if min_apps.is_none() || apps < *min_apps.as_ref().unwrap() {
                        min_apps = Some(apps);
                        bound_reg = Some(i);
                    }
                } else if del > 0 {
                    if let Finite(max_f) = max_val {
                        let apps = (BigInt::from(*max_f) - val.clone()) / del + 1;
                        if min_apps.is_none() || apps < *min_apps.as_ref().unwrap() {
                            min_apps = Some(apps);
                            bound_reg = Some(i);
                        }
                    }
                }
            }

            let apps = min_apps.ok_or(BouncerError::NotInfinite)?;
            let k = bound_reg.unwrap();

            // 2. Check if it's a unit decrement
            let del_k = rule.delta.data[k];
            if del_k != -1 {
                return Err(BouncerError::NonUnitDecrement);
            }

            // 3. Symbolic N = v_k - min_k + 1
            // N >= 1 => N - 1 >= 0 => v_k - min_k >= 0
            let mut expr_n = affine.vars[k].clone();
            expr_n.constant += (-rule.min.data[k] + 1) as i64;

            let mut cond_n = expr_n.clone();
            cond_n.constant -= 1;
            conditions.push(Condition { expr: cond_n });

            // 4. Conditions for other registers
            // N_j >= N
            for j in 0..num_regs {
                if j == k { continue; }
                let del = rule.delta.data[j];
                if del < 0 {
                    // v_j - min_j >= (-del) * (N - 1)
                    // v_j - min_j + del * (N - 1) >= 0
                    let mut cond = affine.vars[j].clone();
                    cond.constant -= rule.min.data[j] as i64;
                    let mut n_minus_1 = expr_n.clone();
                    n_minus_1.constant -= 1;
                    let term = n_minus_1.scale(del as i64);
                    cond = cond.add(&term);
                    conditions.push(Condition { expr: cond });
                } else if del > 0 {
                    if let Finite(max_val) = rule.max.data[j] {
                        // v_j + N * del <= max_j
                        // max_j - v_j - N * del >= 0
                        let mut cond = affine.vars[j].scale(-1);
                        cond.constant += max_val as i64;
                        let term = expr_n.scale(-del as i64);
                        cond = cond.add(&term);
                        conditions.push(Condition { expr: cond });
                    }
                }
            }

            // 5. Update affine state
            for j in 0..num_regs {
                if rule.delta.data[j] != 0 {
                    let term = expr_n.scale(rule.delta.data[j] as i64);
                    affine.vars[j] = affine.vars[j].add(&term);
                }
            }

            // 6. Update concrete state
            let mut next_data = concrete_state.data.clone();
            for j in 0..num_regs {
                next_data[j] += apps.clone() * BigInt::from(rule.delta.data[j]);
            }
            concrete_state = State::new(next_data);
        }
    }

    Ok((affine, conditions))
}

pub fn prove_condition(mut y: Vec<BigInt>, max_degree: usize) -> Result<bool, BouncerError> {
    // We compute the difference table up to max_degree + 1
    // y has length max_degree + 2
    let mut table = vec![y.clone()];
    for k in 1..=max_degree+1 {
        let mut next_row = Vec::new();
        let prev = &table[k-1];
        for i in 0..prev.len()-1 {
            next_row.push(prev[i+1].clone() - prev[i].clone());
        }
        table.push(next_row);
    }

    // Check if the max_degree + 1 differences are all zero
    let last_row = table.last().unwrap();
    for v in last_row.iter() {
        if *v != BigInt::from(0) {
            return Err(BouncerError::ExponentialGrowth);
        }
    }

    // Find the actual degree d <= max_degree
    let mut d = max_degree;
    while d > 0 {
        let row = &table[d];
        let mut all_zero = true;
        for v in row.iter() {
            if *v != BigInt::from(0) {
                all_zero = false;
                break;
            }
        }
        if !all_zero {
            break;
        }
        d -= 1;
    }

    // Now d is the degree, and table[d] is constant.
    let leading_coef = table[d][0].clone();
    if leading_coef < BigInt::from(0) {
        // Goes to negative infinity
        return Ok(false);
    }

    // We generate elements and check if they ever go negative.
    // If all forward differences at some n are >= 0, it stays >= 0 forever.
    // We have table[k][0] for k=0..=d.
    let mut current_diag: Vec<BigInt> = (0..=d).map(|k| table[k][0].clone()).collect();

    // In the worst case, a polynomial of degree d with positive leading coefficient 
    // will have all positive differences after a finite number of steps.
    // But we don't want to loop forever just in case. 1000 steps should be plenty for FRACTRAN.
    for _step in 0..10000 {
        if current_diag[0] < BigInt::from(0) {
            return Ok(false);
        }

        let mut all_non_negative = true;
        for v in current_diag.iter() {
            if *v < BigInt::from(0) {
                all_non_negative = false;
                break;
            }
        }
        if all_non_negative {
            return Ok(true); // Proven!
        }

        // Advance the diagonal by 1 step:
        // E(n+1) = E(n) + \Delta E(n)
        // \Delta^k E(n+1) = \Delta^k E(n) + \Delta^{k+1} E(n)
        for k in 0..d {
            let next_val = current_diag[k].clone() + current_diag[k+1].clone();
            current_diag[k] = next_val;
        }
    }

    // If we didn't resolve it in 10000 steps, something is weird.
    // It could be a very deep dip. But let's just say we couldn't prove it.
    Ok(false)
}

pub fn decide_bouncer(
    prog: &Program,
    start_state: State,
    pattern: &[StrippedBlock]
) -> Result<bool, BouncerError> {
    let num_regs = prog.num_registers();
    let (affine, conditions) = build_bouncer_transform(prog, start_state.clone(), pattern)?;

    // We need v_0, v_1, ..., v_{R+1}
    let max_degree = num_regs;
    let mut states = vec![start_state.clone()];
    let mut current = start_state.clone();
    for _ in 0..=max_degree {
        let next_data = affine.evaluate(&current.data);
        current = State::new(next_data);
        states.push(current.clone());
    }

    // Evaluate each condition on the sequence of states
    for cond in conditions {
        let mut y = Vec::new();
        for s in states.iter() {
            y.push(cond.expr.evaluate(&s.data));
        }

        let holds = prove_condition(y, max_degree)?;
        if !holds {
            return Ok(false);
        }
    }

    Ok(true)
}
