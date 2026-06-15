use bbcs::ast::Instr;
use bbcs::simulator::{Simulator, RunResult};
use clap::Parser;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// The program string to simulate
    #[arg(short, long)]
    program: String,

    /// Maximum steps for the simulator
    #[arg(short, long, default_value_t = 100000)]
    max_steps: usize,
}

pub fn parse_program(input: &str) -> Result<Vec<Instr>, String> {
    let mut tokens = Vec::new();
    let mut current_token = String::new();
    
    for c in input.chars() {
        if c.is_whitespace() {
            if !current_token.is_empty() {
                tokens.push(current_token.clone());
                current_token.clear();
            }
        } else if c == '{' || c == '}' || c == ';' {
            if !current_token.is_empty() {
                tokens.push(current_token.clone());
                current_token.clear();
            }
            tokens.push(c.to_string());
        } else {
            current_token.push(c);
        }
    }
    if !current_token.is_empty() {
        tokens.push(current_token);
    }
    
    let mut ast_stack: Vec<Vec<Instr>> = vec![Vec::new()];
    let mut var_stack: Vec<usize> = Vec::new();
    
    let mut i = 0;
    while i < tokens.len() {
        let token = &tokens[i];
        if token == "while" {
            i += 1;
            if i >= tokens.len() {
                return Err("Expected variable after while".to_string());
            }
            let var_str = &tokens[i];
            let v = var_str.chars().next().unwrap() as usize - 'A' as usize;
            i += 1;
            if i >= tokens.len() || tokens[i] != "{" {
                return Err("Expected { after while".to_string());
            }
            ast_stack.push(Vec::new());
            var_stack.push(v);
        } else if token.ends_with("++") {
            let v = token.chars().next().unwrap() as usize - 'A' as usize;
            ast_stack.last_mut().unwrap().push(Instr::Inc(v));
            if i + 1 < tokens.len() && tokens[i + 1] == ";" {
                i += 1;
            }
        } else if token.ends_with("--") {
            let v = token.chars().next().unwrap() as usize - 'A' as usize;
            ast_stack.last_mut().unwrap().push(Instr::Dec(v));
            if i + 1 < tokens.len() && tokens[i + 1] == ";" {
                i += 1;
            }
        } else if token == "}" {
            if ast_stack.len() <= 1 {
                return Err("Unmatched }".to_string());
            }
            let body = ast_stack.pop().unwrap();
            let v = var_stack.pop().unwrap();
            ast_stack.last_mut().unwrap().push(Instr::While(v, body));
        } else if token == ";" {
            // ignore empty semicolons
        } else {
            return Err(format!("Unknown token: {}", token));
        }
        i += 1;
    }
    
    if ast_stack.len() > 1 {
        return Err("Unmatched while".to_string());
    }
    
    Ok(ast_stack.pop().unwrap())
}

fn main() {
    let args = Args::parse();
    
    match parse_program(&args.program) {
        Ok(program) => {
            println!("Parsed program: {}", bbcs::ast::format_program(&program));
            let mut sim = Simulator::new();
            match sim.run(&program, args.max_steps) {
                RunResult::Halted { score, steps } => {
                    println!("Result: Halted");
                    println!("Score: {}", score);
                    println!("Steps: {}", steps);
                    
                    let mut vars = Vec::new();
                    for (i, &v) in sim.counters.iter().enumerate() {
                        if v > 0 {
                            vars.push(format!("{}={}", (b'A' + i as u8) as char, v));
                        }
                    }
                    println!("Final State: {}", vars.join(", "));
                }
                RunResult::Infinite(reason) => {
                    println!("Result: Infinite Loop");
                    println!("Reason: {:?}", reason);
                }
                RunResult::Unknown => {
                    println!("Result: Unknown (Timeout after {} steps)", args.max_steps);
                }
            }
        }
        Err(e) => {
            eprintln!("Parse error: {}", e);
            std::process::exit(1);
        }
    }
}
