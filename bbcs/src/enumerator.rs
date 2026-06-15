use crate::ast::{Instr, format_program};
use crate::simulator::{Simulator, RunResult, InfiniteReason};
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
    inc_mask: u32,
    unresolved_mask: u32,
}

pub struct SearchResult {
    pub total: usize,
    pub halted: usize,
    pub timeouts: usize,
    pub infinites_stationary: usize,
    pub infinites_translated: usize,
    pub infinites_summonotonic: usize,
    pub max_score: usize,
    pub champion_code: String,
}

impl SearchResult {
    fn new() -> Self {
        Self {
            total: 0,
            halted: 0,
            timeouts: 0,
            infinites_stationary: 0,
            infinites_translated: 0,
            infinites_summonotonic: 0,
            max_score: 0,
            champion_code: String::new(),
        }
    }

    fn merge(&mut self, other: &Self) {
        self.total += other.total;
        self.halted += other.halted;
        self.timeouts += other.timeouts;
        self.infinites_stationary += other.infinites_stationary;
        self.infinites_translated += other.infinites_translated;
        self.infinites_summonotonic += other.infinites_summonotonic;
        if other.max_score > self.max_score {
            self.max_score = other.max_score;
            self.champion_code = other.champion_code.clone();
        }
    }
}

pub struct SharedProgress {
    pub total: AtomicUsize,
    pub halted: AtomicUsize,
    pub timeouts: AtomicUsize,
    pub infinites_stationary: AtomicUsize,
    pub infinites_translated: AtomicUsize,
    pub infinites_summonotonic: AtomicUsize,
    pub max_score: Mutex<usize>,
    pub champion_code: Mutex<String>,
    pub done_mutex: Mutex<bool>,
    pub done_cvar: Condvar,
}

impl SharedProgress {
    pub fn new() -> Arc<Self> {
        Arc::new(Self {
            total: AtomicUsize::new(0),
            halted: AtomicUsize::new(0),
            timeouts: AtomicUsize::new(0),
            infinites_stationary: AtomicUsize::new(0),
            infinites_translated: AtomicUsize::new(0),
            infinites_summonotonic: AtomicUsize::new(0),
            max_score: Mutex::new(0),
            champion_code: Mutex::new(String::new()),
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
        1,
        0,
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
                let champ = prog_clone.champion_code.lock().unwrap().clone();
                
                let pct = if total > 0 { (halted as f64 / total as f64) * 100.0 } else { 0.0 };
                let timestamp = chrono::Local::now().format("%Y-%m-%d %H:%M:%S");
                
                println!("[{}] Progress: {} total, {} halted ({:.2}%), max score: {}", 
                         timestamp, total, halted, pct, score);
                if !champ.is_empty() {
                    println!("  Champion: {}", champ);
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
            prefix.inc_mask,
            prefix.unresolved_mask,
        );
        
        if let Some(tx_sender) = tx {
            if !local_buffer.is_empty() {
                let _ = tx_sender.send(local_buffer);
            }
        }
        
        progress.total.fetch_add(local_res.total, Ordering::Relaxed);
        progress.halted.fetch_add(local_res.halted, Ordering::Relaxed);
        progress.timeouts.fetch_add(local_res.timeouts, Ordering::Relaxed);
        progress.infinites_stationary.fetch_add(local_res.infinites_stationary, Ordering::Relaxed);
        progress.infinites_translated.fetch_add(local_res.infinites_translated, Ordering::Relaxed);
        progress.infinites_summonotonic.fetch_add(local_res.infinites_summonotonic, Ordering::Relaxed);
        
        let mut score_lock = progress.max_score.lock().unwrap();
        let mut champ_lock = progress.champion_code.lock().unwrap();
        if local_res.max_score > *score_lock {
            *score_lock = local_res.max_score;
            *champ_lock = local_res.champion_code.clone();
        }
        drop(score_lock);
        drop(champ_lock);

        local_res
    }).reduce(|| SearchResult::new(), |mut a, b| { a.merge(&b); a });

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

fn instr_rank(instr: &FlatInstr) -> usize {
    match instr {
        FlatInstr::WhileEnd => 0,
        FlatInstr::Inc(v) => 1 + v * 3,
        FlatInstr::Dec(v) => 1 + v * 3 + 1,
        FlatInstr::WhileStart(v) => 1 + v * 3 + 2,
    }
}

fn check_permutation(prefix: &[FlatInstr], perm: &[usize]) -> bool {
    let mut mapped = prefix.to_vec();
    
    for instr in mapped.iter_mut() {
        match instr {
            FlatInstr::Inc(v) => *v = perm[*v],
            FlatInstr::Dec(v) => *v = perm[*v],
            FlatInstr::WhileStart(v) => *v = perm[*v],
            FlatInstr::WhileEnd => {}
        }
    }
    
    let mut start = 0;
    while start < mapped.len() {
        if matches!(mapped[start], FlatInstr::Inc(_) | FlatInstr::Dec(_)) {
            let mut end = start + 1;
            while end < mapped.len() && matches!(mapped[end], FlatInstr::Inc(_) | FlatInstr::Dec(_)) {
                end += 1;
            }
            mapped[start..end].sort_by_key(|instr| match instr {
                FlatInstr::Inc(v) => *v,
                FlatInstr::Dec(v) => *v,
                _ => unreachable!(),
            });
            start = end;
        } else {
            start += 1;
        }
    }
    
    for (m, p) in mapped.iter().zip(prefix.iter()) {
        let rank_m = instr_rank(m);
        let rank_p = instr_rank(p);
        if rank_m < rank_p {
            return false;
        } else if rank_m > rank_p {
            return true;
        }
    }
    
    true
}

fn is_canonical(prefix: &[FlatInstr], max_var: usize) -> bool {
    if max_var == 0 { return true; }
    
    let mut perm: Vec<usize> = (0..=max_var).collect();
    let mut c = vec![0; max_var + 1];
    let mut i = 1;
    
    if !check_permutation(prefix, &perm) { return false; }
    
    while i <= max_var {
        if c[i] < i {
            if i % 2 == 0 {
                perm.swap(0, i);
            } else {
                perm.swap(c[i], i);
            }
            
            if !check_permutation(prefix, &perm) {
                return false;
            }
            
            c[i] += 1;
            i = 1;
        } else {
            c[i] = 0;
            i += 1;
        }
    }
    
    true
}

fn generate_prefixes(
    remaining_length: usize,
    max_var: Option<usize>,
    open_loops: &mut Vec<(usize, bool, bool)>,
    steps_left: usize,
    current_flat: &mut Vec<FlatInstr>,
    prefixes: &mut Vec<PrefixState>,
    inc_mask: u32,
    unresolved_mask: u32,
) {
    let num_vars = max_var.map_or(0, |v| v + 1);
    let missing_incs = num_vars as u32 - inc_mask.count_ones();
    if remaining_length < missing_incs as usize {
        return;
    }

    if steps_left == 0 || remaining_length == 0 {
        if remaining_length == 0 {
            for loop_state in open_loops.iter() {
                if !loop_state.1 || loop_state.2 { return; }
            }
            if !is_canonical(current_flat, max_var.unwrap_or(0)) {
                return;
            }
        }
        prefixes.push(PrefixState {
            remaining_length,
            max_var,
            open_loops: open_loops.clone(),
            flat: current_flat.clone(),
            inc_mask,
            unresolved_mask,
        });
        return;
    }

    if !open_loops.is_empty() {
        let last_loop = open_loops.last().unwrap();
        if last_loop.1 && !last_loop.2 {
            if open_loops.len() == 1 && unresolved_mask != 0 {
                // Reject: outer loop closes before inner variables are resolved with an increment
            } else {
                current_flat.push(FlatInstr::WhileEnd);
                let popped = open_loops.pop().unwrap();
                generate_prefixes(remaining_length, max_var, open_loops, steps_left, current_flat, prefixes, inc_mask, unresolved_mask);
                open_loops.push(popped);
                current_flat.pop();
            }
        }
    }

    let next_allowed = match max_var {
        Some(v) => v + 1,
        None => 0,
    };

    let last_instr = current_flat.last().cloned();

    for v in 0..=next_allowed {
        let next_max_var = Some(max_var.unwrap_or(0).max(v));
        let is_new_var = v == next_allowed;
        let is_top_level = open_loops.is_empty();

        if is_valid_primitive(last_instr.as_ref(), v, true) {
            current_flat.push(FlatInstr::Inc(v));
            let mut changed_inc = false;
            if let Some(last_loop) = open_loops.last_mut() {
                if last_loop.0 == v && !last_loop.2 {
                    last_loop.2 = true;
                    changed_inc = true;
                }
            }
            generate_prefixes(remaining_length - 1, next_max_var, open_loops, steps_left - 1, current_flat, prefixes, inc_mask | (1 << v), unresolved_mask & !(1 << v));
            if changed_inc {
                open_loops.last_mut().unwrap().2 = false;
            }
            current_flat.pop();
        }

        if !(is_new_var && is_top_level) {
            let next_unresolved = if is_new_var { unresolved_mask | (1 << v) } else { unresolved_mask };

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
                generate_prefixes(remaining_length - 1, next_max_var, open_loops, steps_left - 1, current_flat, prefixes, inc_mask, next_unresolved);
                for (i, old_dec, old_inc) in changed_state {
                    open_loops[i].1 = old_dec;
                    open_loops[i].2 = old_inc;
                }
                current_flat.pop();
            }

            current_flat.push(FlatInstr::WhileStart(v));
            open_loops.push((v, false, false));
            generate_prefixes(remaining_length - 1, next_max_var, open_loops, steps_left - 1, current_flat, prefixes, inc_mask, next_unresolved);
            open_loops.pop();
            current_flat.pop();
        }
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
    inc_mask: u32,
    unresolved_mask: u32,
) {
    let num_vars = max_var.map_or(0, |v| v + 1);
    let missing_incs = num_vars as u32 - inc_mask.count_ones();
    if remaining_length < missing_incs as usize {
        return;
    }

    if remaining_length == 0 {
        for loop_state in open_loops.iter() {
            if !loop_state.1 || loop_state.2 { return; }
        }

        if !is_canonical(current_flat, max_var.unwrap_or(0)) {
            return;
        }

        for _ in 0..open_loops.len() {
            current_flat.push(FlatInstr::WhileEnd);
        }
        
        let ast = parse_flat(current_flat);
        local_res.total += 1;
        match sim.run(&ast, max_steps) {
            RunResult::Halted { score } => {
                local_res.halted += 1;
                if score > local_res.max_score {
                    local_res.max_score = score;
                    local_res.champion_code = format_program(&ast);
                }
                if tx.is_some() {
                    local_buffer.push(format!("{} Halt {}", format_program(&ast), score));
                }
            }
            RunResult::Infinite(reason) => {
                match reason {
                    InfiniteReason::StationaryCycle => local_res.infinites_stationary += 1,
                    InfiniteReason::TranslatedCycle => local_res.infinites_translated += 1,
                    InfiniteReason::SumMonotonic => local_res.infinites_summonotonic += 1,
                }
                if tx.is_some() {
                    local_buffer.push(format!("{} Infinite({:?})", format_program(&ast), reason));
                }
            }
            RunResult::Unknown => {
                local_res.timeouts += 1;
                if tx.is_some() {
                    local_buffer.push(format!("{} Unknown >{}", format_program(&ast), max_steps));
                }
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
            if open_loops.len() == 1 && unresolved_mask != 0 {
                // Reject
            } else {
                current_flat.push(FlatInstr::WhileEnd);
                let popped = open_loops.pop().unwrap();
                generate_and_sim(remaining_length, max_var, open_loops, current_flat, local_res, sim, max_steps, tx, local_buffer, inc_mask, unresolved_mask);
                open_loops.push(popped);
                current_flat.pop();
            }
        }
    }

    let next_allowed = match max_var {
        Some(v) => v + 1,
        None => 0,
    };

    let last_instr = current_flat.last().cloned();

    for v in 0..=next_allowed {
        let next_max_var = Some(max_var.unwrap_or(0).max(v));
        let is_new_var = v == next_allowed;
        let is_top_level = open_loops.is_empty();

        if is_valid_primitive(last_instr.as_ref(), v, true) {
            current_flat.push(FlatInstr::Inc(v));
            let mut changed_inc = false;
            if let Some(last_loop) = open_loops.last_mut() {
                if last_loop.0 == v && !last_loop.2 {
                    last_loop.2 = true;
                    changed_inc = true;
                }
            }
            generate_and_sim(remaining_length - 1, next_max_var, open_loops, current_flat, local_res, sim, max_steps, tx, local_buffer, inc_mask | (1 << v), unresolved_mask & !(1 << v));
            if changed_inc {
                open_loops.last_mut().unwrap().2 = false;
            }
            current_flat.pop();
        }

        if !(is_new_var && is_top_level) {
            let next_unresolved = if is_new_var { unresolved_mask | (1 << v) } else { unresolved_mask };

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
                generate_and_sim(remaining_length - 1, next_max_var, open_loops, current_flat, local_res, sim, max_steps, tx, local_buffer, inc_mask, next_unresolved);
                for (i, old_dec, old_inc) in changed_state {
                    open_loops[i].1 = old_dec;
                    open_loops[i].2 = old_inc;
                }
                current_flat.pop();
            }

            current_flat.push(FlatInstr::WhileStart(v));
            open_loops.push((v, false, false));
            generate_and_sim(remaining_length - 1, next_max_var, open_loops, current_flat, local_res, sim, max_steps, tx, local_buffer, inc_mask, next_unresolved);
            open_loops.pop();
            current_flat.pop();
        }
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
