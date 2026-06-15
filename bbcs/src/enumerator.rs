use crate::ast::Instr;

#[derive(Clone)]
enum FlatInstr {
    Inc(usize),
    Dec(usize),
    WhileStart(usize),
    WhileEnd,
}

pub fn enumerate_programs(length: usize) -> Vec<Vec<Instr>> {
    let mut flat_results = Vec::new();
    let mut current_flat = Vec::new();
    generate_flat(length, None, 0, &mut current_flat, &mut flat_results);

    flat_results.into_iter().map(|flat| parse_flat(&flat)).collect()
}

fn generate_flat(
    remaining_length: usize,
    max_var: Option<usize>,
    open_loops: usize,
    current_flat: &mut Vec<FlatInstr>,
    results: &mut Vec<Vec<FlatInstr>>,
) {
    if remaining_length == 0 {
        // Close all open loops
        for _ in 0..open_loops {
            current_flat.push(FlatInstr::WhileEnd);
        }
        results.push(current_flat.clone());
        for _ in 0..open_loops {
            current_flat.pop();
        }
        return;
    }

    // Option 1: Close a loop (costs 0 length)
    if open_loops > 0 {
        current_flat.push(FlatInstr::WhileEnd);
        generate_flat(remaining_length, max_var, open_loops - 1, current_flat, results);
        current_flat.pop();
    }

    // Option 2: Generate an instruction (costs 1 length)
    let next_allowed = match max_var {
        Some(v) => v + 1,
        None => 0,
    };

    for v in 0..=next_allowed {
        let next_max_var = Some(max_var.unwrap_or(0).max(v));

        // Inc
        current_flat.push(FlatInstr::Inc(v));
        generate_flat(remaining_length - 1, next_max_var, open_loops, current_flat, results);
        current_flat.pop();

        // Dec
        current_flat.push(FlatInstr::Dec(v));
        generate_flat(remaining_length - 1, next_max_var, open_loops, current_flat, results);
        current_flat.pop();

        // WhileStart
        current_flat.push(FlatInstr::WhileStart(v));
        generate_flat(remaining_length - 1, next_max_var, open_loops + 1, current_flat, results);
        current_flat.pop();
    }
}

fn parse_flat(flat: &[FlatInstr]) -> Vec<Instr> {
    let mut ast_stack: Vec<Vec<Instr>> = vec![Vec::new()];
    let mut var_stack: Vec<usize> = Vec::new();

    for instr in flat {
        match instr {
            FlatInstr::Inc(v) => ast_stack.last_mut().unwrap().push(Instr::Inc(*v)),
            FlatInstr::Dec(v) => ast_stack.last_mut().unwrap().push(Instr::Dec(*v)),
            FlatInstr::WhileStart(v) => {
                ast_stack.push(Vec::new());
                var_stack.push(*v);
            }
            FlatInstr::WhileEnd => {
                let body = ast_stack.pop().unwrap();
                let v = var_stack.pop().unwrap();
                ast_stack.last_mut().unwrap().push(Instr::While(v, body));
            }
        }
    }
    ast_stack.pop().unwrap()
}
