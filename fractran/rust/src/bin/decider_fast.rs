use clap::Parser;
use fractran::parse::{load_lines, parse_program};
use fractran::program::Program;
use std::fs;
use std::process::{Command, Stdio};
use std::thread;
use std::time::{Duration, Instant};

/// FAST-based halting decider for FRACTRAN programs
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// File containing FRACTRAN programs (one per line)
    #[arg(value_name = "FILE")]
    filename: String,

    /// Analysis strategy: 'forward' (post*) or 'backward' (pre*)
    #[arg(long, default_value = "forward")]
    strategy: String,

    /// Timeout in seconds for the FAST solver process
    #[arg(long, default_value_t = 10)]
    timeout: u64,

    /// Maximum size of loops to accelerate.
    #[arg(long, default_value_t = 2)]
    max_loop_size: usize,

    /// Internal limit for FAST's state/acceleration steps
    #[arg(long, default_value_t = 200)]
    limit: usize,

    #[arg(long)]
    ignore_priority: bool,
}

fn main() {
    let args = Args::parse();

    let programs = load_lines(&args.filename);
    println!(
        "Loaded {} programs. Strategy: {}. Timeout: {}s. Limit: {}",
        programs.len(),
        args.strategy,
        args.timeout,
        args.limit
    );

    for (i, prog_str) in programs.iter().enumerate() {
        let prog = parse_program(prog_str);

        // 1. Generate FAST input file
        let fst_filename = format!("temp_prog_{}.fst", i);
        let fst_content = generate_fast_source(
            &prog,
            &args.strategy,
            i,
            args.max_loop_size,
            args.limit,
            args.ignore_priority,
        );

        if let Err(e) = fs::write(&fst_filename, &fst_content) {
            eprintln!("Failed to write .fst file: {}", e);
            continue;
        }

        // 2. Run FAST with Timeout
        let start = Instant::now();

        let process_result = run_with_timeout(
            "fast",
            &["--plugin=mona", &fst_filename],
            Duration::from_secs(args.timeout),
        );
        let decision = analyze_output(process_result, args.ignore_priority);
        if decision != DeciderResult::Unknown {
            println!(
                "{}\t{:?}\t[{:.2}s]",
                prog_str,
                decision,
                start.elapsed().as_secs_f64()
            );
        }

        // Cleanup
        let _ = fs::remove_file(fst_filename);
    }
}

fn run_with_timeout(cmd: &str, args: &[&str], timeout: Duration) -> Result<String, String> {
    let mut child = Command::new(cmd)
        .args(args)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| format!("Failed to spawn process: {}", e))?;

    let start = Instant::now();

    loop {
        // Check if child has exited
        match child.try_wait() {
            Ok(Some(status)) => {
                // Process finished
                let output = child.wait_with_output().map_err(|e| e.to_string())?;

                if !status.success() {
                    let stderr = String::from_utf8_lossy(&output.stderr);
                    return Err(format!(
                        "Process failed (Exit code {:?}): {}",
                        status.code(),
                        stderr
                    ));
                }
                return Ok(String::from_utf8_lossy(&output.stdout).to_string());
            }
            Ok(None) => {
                // Still running
                if start.elapsed() >= timeout {
                    let _ = child.kill(); // Kill it
                    return Err("Timeout reached".to_string());
                }
                thread::sleep(Duration::from_millis(50)); // Polling interval
            }
            Err(e) => return Err(format!("Error waiting on child: {}", e)),
        }
    }
}

#[derive(Debug, PartialEq)]
enum DeciderResult {
    Halt,
    Infinite,
    Unknown,
}

fn analyze_output(process_result: Result<String, String>, ignore_priority: bool) -> DeciderResult {
    match process_result {
        Err(_) => DeciderResult::Unknown,
        Ok(output_str) => {
            if output_str.contains("DEADLOCK: FALSE") {
                DeciderResult::Infinite
            } else if output_str.contains("DEADLOCK: TRUE") {
                if ignore_priority {
                    // If we ignore priority rules, then DEADLOCK does not imply halting. It could have reached
                    // deadlock via an incorrect trajectory.
                    DeciderResult::Unknown
                } else {
                    // If we used all correct priority rules and DEADLOCK: TRUE, then we know it actually halted.
                    DeciderResult::Halt
                }
            } else {
                DeciderResult::Unknown
            }
        }
    }
}

fn generate_fast_source(
    prog: &Program,
    strategy: &str,
    id: usize,
    max_loop_size: usize,
    limit: usize,
    ignore_priority: bool,
) -> String {
    let num_vars = prog.num_registers();
    let mut vars = Vec::new();
    for i in 0..num_vars {
        vars.push(format!("x{}", i));
    }

    let mut sb = String::new();
    sb.push_str(&format!("model m{} {{\n", id));
    sb.push_str(&format!("  var {};\n", vars.join(", ")));
    sb.push_str("  states q;\n\n");

    let mut transition_names = Vec::new();
    let mut prio_str = "true".to_string();

    for (r_idx, instr) in prog.instrs.iter().enumerate() {
        let t_name = format!("t{}", r_idx);
        transition_names.push(t_name.clone());

        sb.push_str(&format!("  transition {} := {{\n", t_name));
        sb.push_str("    from := q; to := q;\n");

        // --- GUARD GENERATION ---
        // 1. Resources Check (Must have enough tokens)
        let mut resources_guards = Vec::new();
        for (v_idx, &delta) in instr.data.iter().enumerate() {
            if delta < 0 {
                let req = -delta; // e.g., requires 2
                resources_guards.push(format!("x{} >= {}", v_idx, req));
            }
        }
        if resources_guards.is_empty() {
            resources_guards.push("true".to_string());
        }
        let res_str = resources_guards.join(" && ");
        sb.push_str(&format!("    guard := ({})", res_str));
        if !ignore_priority {
            sb.push_str(&format!(" && {}", prio_str));
        }
        sb.push_str(";\n");
        prio_str.push_str(&format!(" && !({})", res_str));

        // --- ACTION GENERATION ---
        let mut actions = Vec::new();
        for (v_idx, &delta) in instr.data.iter().enumerate() {
            if delta != 0 {
                let op = if delta > 0 { "+" } else { "-" };
                actions.push(format!("x{}' = x{} {} {}", v_idx, v_idx, op, delta.abs()));
            }
        }
        if !actions.is_empty() {
            sb.push_str(&format!("    action := {};\n", actions.join(", ")));
        }

        sb.push_str("  };\n\n");
    }
    sb.push_str("}\n\n");

    // --- STRATEGY GENERATION ---
    sb.push_str("strategy s1 {\n");

    // Inject Limits
    sb.push_str(&format!("  setMaxState({});\n", limit));
    sb.push_str(&format!("  setMaxAcc({});\n", limit));

    // Define compound transition
    sb.push_str(&format!(
        "  Transitions all := {{ {} }};\n",
        transition_names.join(", ")
    ));

    // Initial state: x0=1 (2^1), others 0.
    let mut init_eqs = Vec::new();
    for i in 0..num_vars {
        let val = if i == 0 { 1 } else { 0 };
        init_eqs.push(format!("x{}={}", i, val));
    }
    sb.push_str(&format!(
        "  Region init := {{ state = q && {} }};\n",
        init_eqs.join(" && ")
    ));

    sb.push_str(&format!(
        "  Region halted := {{ state = q && {} }};\n",
        prio_str
    ));

    if strategy == "backward" {
        sb.push_str(&format!(
            "  Region bad_pre := pre*(halted, all, {});\n",
            max_loop_size
        ));
        sb.push_str("  Region overlap := bad_pre && init;\n");
    } else {
        sb.push_str(&format!(
            "  Region reachable := post*(init, all, {});\n",
            max_loop_size
        ));
        sb.push_str("  Region overlap := reachable && halted;\n");
    }
    sb.push_str("  if (isEmpty(overlap)) then\n");
    sb.push_str("    print(\"DEADLOCK: FALSE\");\n");
    sb.push_str("  else\n");
    sb.push_str("    print(\"DEADLOCK: TRUE\");\n");
    sb.push_str("  endif\n");

    sb.push_str("}\n");
    sb
}
