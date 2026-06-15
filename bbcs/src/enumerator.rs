use crate::ast::{Instr, format_program};
use crate::simulator::{Simulator, RunResult};
use rayon::prelude::*;
use std::sync::{Arc, Mutex, Condvar};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Duration;
use std::sync::mpsc::{sync_channel, SyncSender};
use std::io::{Write, BufWriter};
use std::fs::File;

#[derive(Clone, PartialEq, Eq)]
pub enum FlatInstr {
    Inc(usize),
    Dec(usize),
    WhileStart(usize),
    WhileEnd,
}

#[derive(Clone)]
struct PrefixState {
    remaining_length: usize,
    max_var: Option<usize>,
    open_loops: Vec<(usize, bool, bool)>, // (var, has_dec, has_top_level_inc_at_end)
    flat: Vec<FlatInstr>,
}

pub struct SearchResult {
    pub total: usize,
    pub halted: usize,
    pub timeouts: usize,
    pub max_score: usize,
    pub champion: Option<Vec<Instr>>,
}

impl SearchResult {
    fn new() -> Self {
        Self { total: 0, halted: 0, timeouts: 0, max_score: 0, champion: None }
    }
    
    fn merge(mut self, other: Self) -> Self {
        self.total += other.total;
        self.halted += other.halted;
        self.timeouts += other.timeouts;
        if other.max_score > self.max_score || self.champion.is_none() {
            self.max_score = other.max_score;
            self.champion = other.champion;
        }
        self
    }
}

pub struct SharedProgress {
    pub total: AtomicUsize,
    pub halted: AtomicUsize,
    pub timeouts: AtomicUsize,
    pub max_score: Mutex<usize>,
    pub champion: Mutex<Option<Vec<Instr>>>,
    pub done_mutex: Mutex<bool>,
    pub done_cvar: Condvar,
}

impl SharedProgress {
    pub fn new() -> Arc<Self> {
        Arc::new(Self {
            total: AtomicUsize::new(0),
            halted: AtomicUsize::new(0),
            timeouts: AtomicUsize::new(0),
            max_score: Mutex::new(0),
            champion: Mutex::new(None),
            done_mutex: Mutex::new(false),
            done_cvar: Condvar::new(),
        })
    }
}

pub fn search_programs(length: usize, max_steps: usize, output_file: Option<String>) -> SearchResult {
    if length == 0 {
        return SearchResult::new();
    }

    let prefix_len = std::cmp::min(length, 6); 
    
    let mut prefixes = Vec::new();
    let mut initial_flat = Vec::new();
    let mut initial_open_loops = Vec::new();
    
    initial_flat.push(FlatInstr::Inc(0));
    generate_prefixes(
        length - 1,
        Some(0),
        &mut initial_open_loops,
        prefix_len - 1,
        &mut initial_flat,
        &mut prefixes,
    );

    let progress = SharedProgress::new();
    let prog_clone = progress.clone();

    let progress_thread = std::thread::spawn(move || {
        let mut done = prog_clone.done_mutex.lock().unwrap();
        while !*done {
            let (new_done, timeout_res) = prog_clone.done_cvar.wait_timeout(done, Duration::from_secs(10)).unwrap();
            done = new_done;
            if *done {
                break;
            }
            
            if timeout_res.timed_out() {
                let total = prog_clone.total.load(Ordering::Relaxed);
                let halted = prog_clone.halted.load(Ordering::Relaxed);
                let score = *prog_clone.max_score.lock().unwrap();
                let champ = prog_clone.champion.lock().unwrap().clone();
                
                let pct = if total > 0 { (halted as f64 / total as f64) * 100.0 } else { 0.0 };
                let timestamp = chrono::Local::now().format("%Y-%m-%d %H:%M:%S");
                
                println!("[{}] Progress: {} total, {} halted ({:.2}%), max score: {}", 
                         timestamp, total, halted, pct, score);
                if let Some(c) = champ {
                    println!("  Champion: {}", format_program(&c));
                }
            }
        }
    });

    let mut tx_opt = None;
    let mut writer_thread = None;
    if let Some(file_path) = output_file {
        let (tx, rx) = sync_channel::<Vec<String>>(1024);
        tx_opt = Some(tx);
        writer_thread = Some(std::thread::spawn(move || {
            let file = File::create(file_path).expect("Failed to create output file");
            let mut writer = BufWriter::new(file);
            while let Ok(batch) = rx.recv() {
                for line in batch {
                    writeln!(writer, "{}", line).unwrap();
                }
            }
        }));
    }

    let result = prefixes.into_par_iter().map_with(tx_opt, |tx, prefix| {
        let mut local_res = SearchResult::new();
        let mut sim = Simulator::new();
        let mut current_flat = prefix.flat.clone();
        let mut open_loops = prefix.open_loops.clone();
        let mut local_buffer = Vec::with_capacity(10_000);
        
        generate_and_sim(
            prefix.remaining_length,
            prefix.max_var,
            &mut open_loops,
            &mut current_flat,
            &mut local_res,
            &mut sim,
            max_steps,
            tx,
            &mut local_buffer,
        );
        
        if let Some(tx_sender) = tx {
            if !local_buffer.is_empty() {
                let _ = tx_sender.send(local_buffer);
            }
        }
        
        progress.total.fetch_add(local_res.total, Ordering::Relaxed);
        progress.halted.fetch_add(local_res.halted, Ordering::Relaxed);
        progress.timeouts.fetch_add(local_res.timeouts, Ordering::Relaxed);
        
        let mut score_lock = progress.max_score.lock().unwrap();
        let mut champ_lock = progress.champion.lock().unwrap();
        if local_res.max_score > *score_lock || champ_lock.is_none() {
            *score_lock = local_res.max_score;
            *champ_lock = local_res.champion.clone();
        }
        drop(score_lock);
        drop(champ_lock);

        local_res
    }).reduce(|| SearchResult::new(), |a, b| a.merge(b));

    *progress.done_mutex.lock().unwrap() = true;
    progress.done_cvar.notify_all();
    let _ = progress_thread.join();
    
    if let Some(wt) = writer_thread {
        let _ = wt.join();
    }

    result
}

fn is_valid_primitive(last_instr: Option<&FlatInstr>, current_var: usize, is_inc: bool) -> bool {
    match last_instr {
        Some(FlatInstr::Inc(p)) => {
            if current_var < *p { return false; }
            if current_var == *p && !is_inc { return false; } 
            true
        }
        Some(FlatInstr::Dec(p)) => {
            if current_var < *p { return false; }
            true
        }
        _ => true
    }
}

fn generate_prefixes(
    remaining_length: usize,
    max_var: Option<usize>,
    open_loops: &mut Vec<(usize, bool, bool)>,
    steps_left: usize,
    current_flat: &mut Vec<FlatInstr>,
    prefixes: &mut Vec<PrefixState>,
) {
    if steps_left == 0 || remaining_length == 0 {
        if remaining_length == 0 {
            for loop_state in open_loops.iter() {
                if !loop_state.1 || loop_state.2 { return; }
            }
        }
        prefixes.push(PrefixState {
            remaining_length,
            max_var,
            open_loops: open_loops.clone(),
            flat: current_flat.clone(),
        });
        return;
    }

    if !open_loops.is_empty() {
        let last_loop = open_loops.last().unwrap();
        if last_loop.1 && !last_loop.2 {
            current_flat.push(FlatInstr::WhileEnd);
            let popped = open_loops.pop().unwrap();
            generate_prefixes(remaining_length, max_var, open_loops, steps_left, current_flat, prefixes);
            open_loops.push(popped);
            current_flat.pop();
        }
    }

    let next_allowed = match max_var {
        Some(v) => v + 1,
        None => 0,
    };

    let last_instr = current_flat.last().cloned();

    for v in 0..=next_allowed {
        let next_max_var = Some(max_var.unwrap_or(0).max(v));

        if is_valid_primitive(last_instr.as_ref(), v, true) {
            current_flat.push(FlatInstr::Inc(v));
            let mut changed_inc = false;
            if let Some(last_loop) = open_loops.last_mut() {
                if last_loop.0 == v && !last_loop.2 {
                    last_loop.2 = true;
                    changed_inc = true;
                }
            }
            generate_prefixes(remaining_length - 1, next_max_var, open_loops, steps_left - 1, current_flat, prefixes);
            if changed_inc {
                open_loops.last_mut().unwrap().2 = false;
            }
            current_flat.pop();
        }

        if is_valid_primitive(last_instr.as_ref(), v, false) {
            current_flat.push(FlatInstr::Dec(v));
            let mut changed_state = Vec::new();
            for (i, loop_state) in open_loops.iter_mut().enumerate() {
                if loop_state.0 == v {
                    changed_state.push((i, loop_state.1, loop_state.2));
                    loop_state.1 = true;
                    loop_state.2 = false;
                }
            }
            generate_prefixes(remaining_length - 1, next_max_var, open_loops, steps_left - 1, current_flat, prefixes);
            for (i, old_dec, old_inc) in changed_state {
                open_loops[i].1 = old_dec;
                open_loops[i].2 = old_inc;
            }
            current_flat.pop();
        }

        current_flat.push(FlatInstr::WhileStart(v));
        open_loops.push((v, false, false));
        generate_prefixes(remaining_length - 1, next_max_var, open_loops, steps_left - 1, current_flat, prefixes);
        open_loops.pop();
        current_flat.pop();
    }
}

fn generate_and_sim(
    remaining_length: usize,
    max_var: Option<usize>,
    open_loops: &mut Vec<(usize, bool, bool)>,
    current_flat: &mut Vec<FlatInstr>,
    local_res: &mut SearchResult,
    sim: &mut Simulator,
    max_steps: usize,
    tx: &mut Option<SyncSender<Vec<String>>>,
    local_buffer: &mut Vec<String>,
) {
    if remaining_length == 0 {
        for loop_state in open_loops.iter() {
            if !loop_state.1 || loop_state.2 { return; }
        }

        for _ in 0..open_loops.len() {
            current_flat.push(FlatInstr::WhileEnd);
        }
        
        let ast = parse_flat(current_flat);
        local_res.total += 1;
        match sim.run(&ast, max_steps) {
            RunResult::Halted { score } => {
                if tx.is_some() {
                    local_buffer.push(format!("{} Halt {}", format_program(&ast), score));
                }
                local_res.halted += 1;
                if score > local_res.max_score || local_res.champion.is_none() {
                    local_res.max_score = score;
                    local_res.champion = Some(ast);
                }
            }
            RunResult::Timeout => {
                if tx.is_some() {
                    local_buffer.push(format!("{} Unknown >{}", format_program(&ast), max_steps));
                }
                local_res.timeouts += 1;
            }
        }
        
        if local_buffer.len() >= 10_000 {
            if let Some(tx_sender) = tx {
                let chunk = std::mem::replace(local_buffer, Vec::with_capacity(10_000));
                let _ = tx_sender.send(chunk);
            }
        }

        for _ in 0..open_loops.len() {
            current_flat.pop();
        }
        return;
    }

    if !open_loops.is_empty() {
        let last_loop = open_loops.last().unwrap();
        if last_loop.1 && !last_loop.2 {
            current_flat.push(FlatInstr::WhileEnd);
            let popped = open_loops.pop().unwrap();
            generate_and_sim(remaining_length, max_var, open_loops, current_flat, local_res, sim, max_steps, tx, local_buffer);
            open_loops.push(popped);
            current_flat.pop();
        }
    }

    let next_allowed = match max_var {
        Some(v) => v + 1,
        None => 0,
    };

    let last_instr = current_flat.last().cloned();

    for v in 0..=next_allowed {
        let next_max_var = Some(max_var.unwrap_or(0).max(v));

        if is_valid_primitive(last_instr.as_ref(), v, true) {
            current_flat.push(FlatInstr::Inc(v));
            let mut changed_inc = false;
            if let Some(last_loop) = open_loops.last_mut() {
                if last_loop.0 == v && !last_loop.2 {
                    last_loop.2 = true;
                    changed_inc = true;
                }
            }
            generate_and_sim(remaining_length - 1, next_max_var, open_loops, current_flat, local_res, sim, max_steps, tx, local_buffer);
            if changed_inc {
                open_loops.last_mut().unwrap().2 = false;
            }
            current_flat.pop();
        }

        if is_valid_primitive(last_instr.as_ref(), v, false) {
            current_flat.push(FlatInstr::Dec(v));
            let mut changed_state = Vec::new();
            for (i, loop_state) in open_loops.iter_mut().enumerate() {
                if loop_state.0 == v {
                    changed_state.push((i, loop_state.1, loop_state.2));
                    loop_state.1 = true;
                    loop_state.2 = false;
                }
            }
            generate_and_sim(remaining_length - 1, next_max_var, open_loops, current_flat, local_res, sim, max_steps, tx, local_buffer);
            for (i, old_dec, old_inc) in changed_state {
                open_loops[i].1 = old_dec;
                open_loops[i].2 = old_inc;
            }
            current_flat.pop();
        }

        current_flat.push(FlatInstr::WhileStart(v));
        open_loops.push((v, false, false));
        generate_and_sim(remaining_length - 1, next_max_var, open_loops, current_flat, local_res, sim, max_steps, tx, local_buffer);
        open_loops.pop();
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
