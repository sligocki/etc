use clap::Parser;
use post_tag::simulate::Simulator;
use post_tag::tag_system::TagSystem;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// The tag system rules (e.g. 00110_)
    rules: String,

    /// Maximum number of steps to simulate
    #[arg(short, long, default_value_t = 1_000_000)]
    max_steps: usize,
}

fn format_tape(tape: &[u8]) -> String {
    tape.iter()
        .map(|&c| c.to_string())
        .collect::<Vec<_>>()
        .join("")
}

fn main() {
    let args = Args::parse();
    
    let sys = TagSystem::parse(2, &args.rules);
    
    println!("Analyzing for Translation Cycles: {}", sys.format_rules());
    
    let mut sim = Simulator::new(&sys);
    
    // (step, tape, characters_consumed)
    let mut snapshots: Vec<(usize, Vec<u8>, usize)> = Vec::new();
    let mut next_snapshot_step = 1;
    
    while sim.tape.len() - sim.head_idx >= sys.v && sim.steps < args.max_steps {
        if sim.steps == next_snapshot_step {
            snapshots.push((sim.steps, sim.tape[sim.head_idx..].to_vec(), sim.head_idx));
            next_snapshot_step *= 2;
        }
        
        let current_tape = &sim.tape[sim.head_idx..];
        
        let mut i = 0;
        while i < snapshots.len() {
            let (saved_step, ref saved_tape, saved_head_idx) = snapshots[i];
            
            if current_tape.len() > saved_tape.len() && current_tape.starts_with(saved_tape) {
                let delta_t = sim.steps - saved_step;
                let c_consumed = delta_t * sys.v;
                
                if c_consumed <= saved_tape.len() {
                    let p = current_tape[saved_tape.len()..].to_vec();
                    let a = current_tape[saved_tape.len() - c_consumed..].to_vec();
                    
                    let mut pa = p.clone();
                    pa.extend(&a);
                    
                    let mut ap = a.clone();
                    ap.extend(&p);
                    
                    if pa == ap {
                        println!("\n=============================================");
                        println!("--- Translation Cycle Strictly Proven! ---");
                        println!("t1 = {}, tape T = {}", saved_step, format_tape(saved_tape));
                        println!("t2 = {}, tape T*P = {}", sim.steps, format_tape(current_tape));
                        println!("delta_t = {}", delta_t);
                        println!("characters consumed C = {}", c_consumed);
                        println!("|T| = {}", saved_tape.len());
                        println!("P = {}", format_tape(&p));
                        println!("A = {}", format_tape(&a));
                        println!("---------------------------------------------");
                        println!("Proof Part 1: |T| >= C is SATISFIED! ({} >= {})", saved_tape.len(), c_consumed);
                        println!("Because the evaluation of T consumes at most |T| characters,");
                        println!("it NEVER reads past its own boundary.");
                        println!("Proof Part 2: Commutativity (P*A == A*P) is SATISFIED!");
                        println!("Because P and A commute, the evaluation of T*P perfectly aligns to yield T*P*P.");
                        println!("Therefore, T*P evaluates mathematically precisely to T*P*P.");
                        println!("The cycle will continue indefinitely!");
                        println!("=============================================\n");
                        return;
                    } else {
                        println!("--- Translation Cycle Candidate Found but REJECTED! ---");
                        println!("P and A do not commute (P*A != A*P)!");
                        println!("P = {}", format_tape(&p));
                        println!("A = {}", format_tape(&a));
                        println!("This is a false positive cycle pattern and will break on the next iteration.");
                    }
                }
            }
            i += 1;
        }
        
        sim.steps += 1;
        sim.lam += 1;
        let head = sim.tape[sim.head_idx];
        sim.head_idx += sys.v;
        
        let rule = match &sys.rules[head as usize] {
            Some(r) => r,
            None => {
                println!("Halted at step {}: Undefined rule for symbol {}", sim.steps, head);
                return;
            }
        };
        for &c in rule {
            sim.tape.push(c);
        }
        
        if sim.head_idx > 1_000_000 {
            sim.tape.drain(0..sim.head_idx);
            sim.head_idx = 0;
        }
    }
    
    if sim.tape.len() - sim.head_idx < sys.v {
        println!("Halted in {} steps.", sim.steps);
    } else {
        println!("Hit step limit of {} without detecting a translation cycle.", args.max_steps);
    }
}
