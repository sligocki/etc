

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PartialTarget {
    Halt,
    Inst(usize),
    Undef,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PartialInstruction {
    Undef,
    Inc {
        reg: usize,
        next: PartialTarget,
    },
    Dec {
        reg: usize,
        next_not_zero: PartialTarget,
        next_zero: PartialTarget,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PartialProgram {
    pub instructions: Vec<PartialInstruction>,
    pub max_state_referenced: i32,
    pub max_reg_referenced: i32,
}

pub enum PartialSimResult {
    Halted { steps: u64, registers: Vec<u64> },
    LimitReached,
    HitUndefInst(usize),
    HitUndefTarget { pc: usize, branch: Branch },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Branch {
    Next,
    NextNotZero,
    NextZero,
}

impl PartialProgram {
    pub fn new(num_states: usize) -> Self {
        PartialProgram {
            instructions: vec![PartialInstruction::Undef; num_states],
            max_state_referenced: 0,
            max_reg_referenced: -1,
        }
    }
}

impl std::fmt::Display for PartialTarget {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PartialTarget::Halt => write!(f, "*"),
            PartialTarget::Inst(idx) => write!(f, "{}", (b'A' + *idx as u8) as char),
            PartialTarget::Undef => write!(f, "?"),
        }
    }
}

impl std::fmt::Display for PartialInstruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PartialInstruction::Undef => write!(f, "?"),
            PartialInstruction::Inc { reg, next } => {
                write!(f, "{}+{}", reg, next)
            }
            PartialInstruction::Dec { reg, next_not_zero, next_zero } => {
                write!(f, "{}-{}{}", reg, next_not_zero, next_zero)
            }
        }
    }
}

impl std::fmt::Display for PartialProgram {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, inst) in self.instructions.iter().enumerate() {
            if i > 0 {
                write!(f, "_")?;
            }
            write!(f, "{}", inst)?;
        }
        Ok(())
    }
}

pub fn simulate(prog: &PartialProgram, step_limit: u64) -> PartialSimResult {
    let mut pc = 0;
    let mut registers = Vec::new();
    let mut steps = 0;

    let get_reg = |regs: &[u64], r: usize| -> u64 {
        if r < regs.len() { regs[r] } else { 0 }
    };

    let set_reg = |regs: &mut Vec<u64>, r: usize, val: u64| {
        if r >= regs.len() {
            regs.resize(r + 1, 0);
        }
        regs[r] = val;
    };

    loop {
        if steps >= step_limit {
            return PartialSimResult::LimitReached;
        }

        if pc >= prog.instructions.len() {
            return PartialSimResult::Halted { steps, registers };
        }

        let inst = &prog.instructions[pc];

        match inst {
            PartialInstruction::Undef => {
                return PartialSimResult::HitUndefInst(pc);
            }
            PartialInstruction::Inc { reg, next } => {
                steps += 1;
                let val = get_reg(&registers, *reg);
                set_reg(&mut registers, *reg, val.wrapping_add(1));
                match next {
                    PartialTarget::Undef => return PartialSimResult::HitUndefTarget { pc, branch: Branch::Next },
                    PartialTarget::Halt => return PartialSimResult::Halted { steps, registers },
                    PartialTarget::Inst(i) => pc = *i,
                }
            }
            PartialInstruction::Dec { reg, next_not_zero, next_zero } => {
                steps += 1;
                let val = get_reg(&registers, *reg);
                if val == 0 {
                    match next_zero {
                        PartialTarget::Undef => return PartialSimResult::HitUndefTarget { pc, branch: Branch::NextZero },
                        PartialTarget::Halt => return PartialSimResult::Halted { steps, registers },
                        PartialTarget::Inst(i) => pc = *i,
                    }
                } else {
                    set_reg(&mut registers, *reg, val - 1);
                    match next_not_zero {
                        PartialTarget::Undef => return PartialSimResult::HitUndefTarget { pc, branch: Branch::NextNotZero },
                        PartialTarget::Halt => return PartialSimResult::Halted { steps, registers },
                        PartialTarget::Inst(i) => pc = *i,
                    }
                }
            }
        }
    }
}

pub fn enumerate(num_states: usize, step_limit: u64, max_regs: Option<usize>, out_file: &str) {
    use std::fs::File;
    use std::io::BufWriter;

    let file = File::create(out_file).unwrap();
    let mut writer = BufWriter::new(file);

    // TODO: Dynamically restrict the number of registers as we enumerate and keep track of needed
    // instructions (anti-pairs to existing instructions). Ensure all registers eventually have both
    // incr and decr. When the number of remaining instructions gets down to the size of the needed
    // ones, we should only choose from those.
    let max_regs = max_regs.unwrap_or(num_states / 2 + 1); // User's requested default

    let mut stack = vec![PartialProgram::new(num_states)];

    let mut total_explored = 0u64;
    let mut num_halted = 0u64;
    let mut num_unknown = 0u64;
    let mut max_steps = 0u64;
    let mut max_program = String::new();
    let mut last_print_time = std::time::Instant::now();

    while let Some(prog) = stack.pop() {
        total_explored += 1;
        if total_explored % 100_000 == 0 {
            if last_print_time.elapsed().as_secs() >= 5 {
                let total_leaves = num_halted + num_unknown;
                let unknown_pct = if total_leaves > 0 {
                    (num_unknown as f64 / total_leaves as f64) * 100.0
                } else {
                    0.0
                };
                println!("Progress: {} nodes explored | {} programs found ({} unknown, {:.2}%) | Max steps: {}", 
                         total_explored, total_leaves, num_unknown, unknown_pct, max_steps);
                last_print_time = std::time::Instant::now();
            }
        }

        match simulate(&prog, step_limit) {
            PartialSimResult::Halted { steps, registers } => {
                num_halted += 1;
                if steps > max_steps {
                    max_steps = steps;
                    max_program = prog.to_string();
                }
                crate::io::write_result(
                    &mut writer,
                    &prog.to_string(),
                    crate::io::ProgramResult::Halt { steps, registers: &registers }
                ).unwrap();
            }
            PartialSimResult::LimitReached => {
                num_unknown += 1;
                crate::io::write_result(
                    &mut writer,
                    &prog.to_string(),
                    crate::io::ProgramResult::Unknown
                ).unwrap();
            }
            PartialSimResult::HitUndefInst(pc) => {
                let mut max_r = prog.max_reg_referenced;
                if max_r + 1 < max_regs as i32 {
                    max_r += 1;
                }
                
                // Inc instructions
                for r in 0..=max_r {
                    let mut child = prog.clone();
                    child.instructions[pc] = PartialInstruction::Inc {
                        reg: r as usize,
                        next: PartialTarget::Undef,
                    };
                    if r > child.max_reg_referenced {
                        child.max_reg_referenced = r;
                    }
                    stack.push(child);
                }

                // Dec instructions
                // The user requested: "Maybe the first instruction should not be a Decr"
                if pc != 0 {
                    for r in 0..=max_r {
                        let mut child = prog.clone();
                        child.instructions[pc] = PartialInstruction::Dec {
                            reg: r as usize,
                            next_not_zero: PartialTarget::Undef,
                            next_zero: PartialTarget::Undef,
                        };
                        if r > child.max_reg_referenced {
                            child.max_reg_referenced = r;
                        }
                        stack.push(child);
                    }
                }
            }
            PartialSimResult::HitUndefTarget { pc, branch } => {
                let mut max_s = prog.max_state_referenced;
                if max_s + 1 < num_states as i32 {
                    max_s += 1;
                }

                let mut targets = vec![PartialTarget::Halt];
                for s in 0..=max_s {
                    targets.push(PartialTarget::Inst(s as usize));
                }

                for target in targets {
                    let mut child = prog.clone();
                    
                    if let PartialTarget::Inst(s) = target {
                        if s as i32 > child.max_state_referenced {
                            child.max_state_referenced = s as i32;
                        }
                    }

                    match &mut child.instructions[pc] {
                        PartialInstruction::Inc { next, .. } => {
                            if branch == Branch::Next {
                                *next = target;
                            }
                        }
                        PartialInstruction::Dec { next_not_zero, next_zero, .. } => {
                            if branch == Branch::NextNotZero {
                                *next_not_zero = target;
                            } else if branch == Branch::NextZero {
                                *next_zero = target;
                            }
                        }
                        _ => {}
                    }
                    
                    stack.push(child);
                }
            }
        }
    }
    
    let total_leaves = num_halted + num_unknown;
    let unknown_pct = if total_leaves > 0 {
        (num_unknown as f64 / total_leaves as f64) * 100.0
    } else {
        0.0
    };
    println!("Enumeration complete! Explored {} total nodes.", total_explored);
    println!("Total programs found: {}", total_leaves);
    println!("Unknown: {} ({:.2}%)", num_unknown, unknown_pct);
    println!("Max Halting Program: {} ({} steps)", max_program, max_steps);
}
