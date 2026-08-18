#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Instr {
    Inc(usize),
    Dec(usize),
    While(usize, Vec<Instr>),
}

pub fn var_name(v: usize) -> String {
    if v < 26 {
        ((b'A' + v as u8) as char).to_string()
    } else {
        format!("V{}", v)
    }
}

pub fn format_program(program: &[Instr]) -> String {
    let mut parts = Vec::new();
    for instr in program {
        match instr {
            Instr::Inc(v) => parts.push(format!("{}++;", var_name(*v))),
            Instr::Dec(v) => parts.push(format!("{}--;", var_name(*v))),
            Instr::While(v, body) => {
                parts.push(format!(
                    "while {} {{ {} }}",
                    var_name(*v),
                    format_program(body)
                ));
            }
        }
    }
    parts.join(" ")
}

impl Instr {
    pub fn get_rw(&self) -> u32 {
        match self {
            Instr::Inc(v) | Instr::Dec(v) => 1 << v,
            Instr::While(v, body) => {
                let mut mask = 1 << v;
                for stmt in body {
                    mask |= stmt.get_rw();
                }
                mask
            }
        }
    }
}

pub struct CanonCtx {
    pub in_degree: Vec<usize>,
    pub edges: Vec<Vec<usize>>,
    pub result: Vec<Instr>,
    pub used: Vec<bool>,
}

impl CanonCtx {
    pub fn new() -> Self {
        Self {
            in_degree: Vec::new(),
            edges: Vec::new(),
            result: Vec::new(),
            used: Vec::new(),
        }
    }
}

#[inline(never)]
pub fn canonicalize_block(block: &mut [Instr]) {
    let mut ctx = CanonCtx::new();
    canonicalize_block_with_ctx(block, &mut ctx);
}

pub fn canonicalize_block_with_ctx(block: &mut [Instr], ctx: &mut CanonCtx) {
    for instr in block.iter_mut() {
        if let Instr::While(_, body) = instr {
            canonicalize_block_with_ctx(body, ctx);
        }
    }
    
    let n = block.len();
    if n <= 1 {
        return;
    }
    
    ctx.in_degree.clear();
    ctx.in_degree.resize(n, 0);
    ctx.edges.clear();
    ctx.edges.resize(n, Vec::new());
    
    for i in 0..n {
        let rw_i = block[i].get_rw();
        for j in i+1..n {
            let rw_j = block[j].get_rw();
            if (rw_i & rw_j) != 0 {
                ctx.edges[i].push(j);
                ctx.in_degree[j] += 1;
            }
        }
    }
    
    ctx.result.clear();
    ctx.used.clear();
    ctx.used.resize(n, false);
    
    for _ in 0..n {
        let mut best_idx = None;
        for i in 0..n {
            if !ctx.used[i] && ctx.in_degree[i] == 0 {
                if let Some(best) = best_idx {
                    if block[i] < block[best] {
                        best_idx = Some(i);
                    }
                } else {
                    best_idx = Some(i);
                }
            }
        }
        
        if let Some(chosen) = best_idx {
            ctx.used[chosen] = true;
            ctx.result.push(block[chosen].clone());
            for next in &ctx.edges[chosen] {
                ctx.in_degree[*next] -= 1;
            }
        }
    }
    
    block.clone_from_slice(&ctx.result);
}

#[inline(never)]
fn min_net_change(instr: &Instr, target_var: usize, known_gt_0: &mut u32) -> i32 {
    match instr {
        Instr::Inc(v) => {
            *known_gt_0 |= 1 << *v;
            if *v == target_var { 1 } else { 0 }
        }
        Instr::Dec(v) => {
            *known_gt_0 &= !(1 << *v);
            if *v == target_var { -1 } else { 0 }
        }
        Instr::While(v, body) => {
            let guaranteed = (*known_gt_0 & (1 << *v)) != 0;
            let mut inner_known = *known_gt_0 | (1 << *v);
            let mut body_change = 0;
            for stmt in body {
                let c = min_net_change(stmt, target_var, &mut inner_known);
                if c == -1000 { body_change = -1000; break; }
                body_change += c;
            }
            
            *known_gt_0 &= !instr.get_rw();
            
            if body_change < 0 {
                -1000
            } else if body_change > 0 {
                if guaranteed { body_change } else { 0 }
            } else {
                0
            }
        }
    }
}

#[inline(never)]
pub fn prune_infinite_loops(program: &[Instr], mut known_gt_0: u32) -> bool {
    for instr in program {
        match instr {
            Instr::Inc(v) => { known_gt_0 |= 1 << *v; }
            Instr::Dec(v) => { known_gt_0 &= !(1 << *v); }
            Instr::While(v, body) => {
                let mut inner_known = known_gt_0 | (1 << *v);
                let mut body_change = 0;
                for stmt in body {
                    let c = min_net_change(stmt, *v, &mut inner_known);
                    if c == -1000 { body_change = -1000; break; }
                    body_change += c;
                }
                if body_change >= 0 {
                    return true; // Infinite loop!
                }
                
                known_gt_0 &= !instr.get_rw();
                if prune_infinite_loops(body, known_gt_0 | (1 << *v)) { return true; }
            }
        }
    }
    false
}
