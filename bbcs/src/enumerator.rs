use crate::ast::{Instr, format_program};
use crate::simulator::{InfiniteReason, RunResult, Simulator};
use rayon::prelude::*;
use std::fs::File;
use std::io::{BufWriter, Write};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::mpsc::SyncSender;
use std::sync::{Arc, Condvar, Mutex};
use std::time::Duration;

#[derive(Clone, PartialEq, Eq)]
#[derive(Debug)]
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
    open_loops: Vec<(usize, u32, u32, bool, u32)>, // (var, dec_mask, inc_mask, is_guaranteed, known_gt_0_before)
    flat: Vec<FlatInstr>,
    inc_mask: u32,
    unresolved_mask: u32,
    pub known_gt_0: u32,
    pub has_while: u32,
    pub has_external_inc: u32,
    pub last_dec_was_gt_0: bool,
}

#[derive(Eq, PartialEq, Clone)]
pub struct TopProgram {
    pub score: usize,
    pub steps: usize,
    pub code: String,
}

impl std::cmp::Ord for TopProgram {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        other.score.cmp(&self.score)
            .then_with(|| self.steps.cmp(&other.steps))
            .then_with(|| self.code.cmp(&other.code))
    }
}
impl std::cmp::PartialOrd for TopProgram {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Clone)]
pub struct SearchResult {
    pub top_halted: std::collections::BinaryHeap<TopProgram>,
    pub total: usize,
    pub halted: usize,
    pub holdouts: usize,
    pub infinites_stationary: usize,
    pub infinites_translated: usize,
    pub infinites_symbolic: usize,
    pub infinites_sum: usize,
    pub max_score: usize,
    pub max_halting_steps: usize,
    pub champion_code: String,
}

impl SearchResult {
    fn new() -> Self {
        Self {
            total: 0,
            halted: 0,
            holdouts: 0,
            infinites_stationary: 0,
            infinites_translated: 0,
            infinites_symbolic: 0,
            infinites_sum: 0,
            max_score: 0,
            max_halting_steps: 0,
            champion_code: String::new(),
            top_halted: std::collections::BinaryHeap::new(),
        }
    }

    fn merge(&mut self, other: &Self) {
        self.total += other.total;
        self.halted += other.halted;
        self.holdouts += other.holdouts;
        self.infinites_stationary += other.infinites_stationary;
        self.infinites_translated += other.infinites_translated;
        self.infinites_symbolic += other.infinites_symbolic;
        self.infinites_sum += other.infinites_sum;
        if other.max_score > self.max_score {
            self.max_score = other.max_score;
            self.champion_code = other.champion_code.clone();
        }
        for p in other.top_halted.iter() {
            self.top_halted.push(p.clone());
            if self.top_halted.len() > 1000 { self.top_halted.pop(); }
        }
        if other.max_halting_steps > self.max_halting_steps {
            self.max_halting_steps = other.max_halting_steps;
        }
    }
}

pub struct SharedProgress {
    pub total: AtomicUsize,
    pub halted: AtomicUsize,
    pub holdouts: AtomicUsize,
    pub infinites_stationary: AtomicUsize,
    pub infinites_translated: AtomicUsize,
    pub infinites_symbolic: AtomicUsize,
    pub max_score: Mutex<usize>,
    pub max_halting_steps: AtomicUsize,
    pub champion_code: Mutex<String>,
    pub top_halted: Mutex<std::collections::BinaryHeap<TopProgram>>,
    pub done_mutex: Mutex<bool>,
    pub done_cvar: Condvar,
}

impl SharedProgress {
    pub fn new() -> Arc<Self> {
        Arc::new(Self {
            total: AtomicUsize::new(0),
            halted: AtomicUsize::new(0),
            holdouts: AtomicUsize::new(0),
            infinites_stationary: AtomicUsize::new(0),
            infinites_translated: AtomicUsize::new(0),
            infinites_symbolic: AtomicUsize::new(0),
            max_score: Mutex::new(0),
            max_halting_steps: AtomicUsize::new(0),
            champion_code: Mutex::new(String::new()),
            top_halted: Mutex::new(std::collections::BinaryHeap::new()),
            done_mutex: Mutex::new(false),
            done_cvar: Condvar::new(),
        })
    }
}

pub fn search_programs(
    length: usize,
    max_steps: usize,
    out_dir: Option<String>,
    progress_secs: u64,
    write_holdouts: bool,
) -> SearchResult {
    rayon::ThreadPoolBuilder::new()
        .stack_size(50_000)
        .build_global()
        .unwrap_or(());
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
        1,
        0,
        1,
        false,
    );


    let mut completed_indices = std::collections::HashSet::new();
    let mut initial_result = SearchResult::new();

    if let Some(dir_path) = &out_dir {
        let checkpoint_path = format!("{}/checkpoint.txt", dir_path);
        if std::path::Path::new(&checkpoint_path).exists() {
            println!("Loading checkpoint from {}...", checkpoint_path);
            let file = std::fs::File::open(&checkpoint_path).unwrap();
            let reader = std::io::BufReader::new(file);
            use std::io::BufRead;
            
            let mut lines = reader.lines();
            while let Some(Ok(line)) = lines.next() {
                if line.starts_with("PREFIX ") {
                    let parts: Vec<&str> = line.splitn(12, ' ').collect();
                    if parts.len() == 12 {
                        let idx: usize = parts[1].parse().unwrap();
                        let mut res = SearchResult::new();
                        res.total = parts[2].parse().unwrap();
                        res.halted = parts[3].parse().unwrap();
                        res.holdouts = parts[4].parse().unwrap();
                        res.infinites_stationary = parts[5].parse().unwrap();
                        res.infinites_translated = parts[6].parse().unwrap();
                        res.infinites_symbolic = parts[7].parse().unwrap();
                        res.infinites_sum = parts[8].parse().unwrap();
                        res.max_score = parts[9].parse().unwrap();
                        res.max_halting_steps = parts[10].parse().unwrap();
                        let champ = parts[11];
                        if champ != "-" {
                            res.champion_code = champ.to_string();
                        }
                        
                        while let Some(Ok(inner_line)) = lines.next() {
                            if inner_line == "END_PREFIX" {
                                break;
                            }
                            if inner_line.starts_with("TOP ") {
                                let top_parts: Vec<&str> = inner_line.splitn(4, ' ').collect();
                                if top_parts.len() == 4 {
                                    res.top_halted.push(TopProgram {
                                        score: top_parts[1].parse().unwrap(),
                                        steps: top_parts[2].parse().unwrap(),
                                        code: top_parts[3].to_string(),
                                    });
                                }
                            }
                        }
                        
                        completed_indices.insert(idx);
                        initial_result.merge(&res);
                    }
                }
            }
            println!("Loaded {} completed prefixes.", completed_indices.len());
        }
    }

    let progress = SharedProgress::new();
    progress.total.store(initial_result.total, Ordering::Relaxed);
    progress.halted.store(initial_result.halted, Ordering::Relaxed);
    progress.holdouts.store(initial_result.holdouts, Ordering::Relaxed);
    progress.infinites_stationary.store(initial_result.infinites_stationary, Ordering::Relaxed);
    progress.infinites_translated.store(initial_result.infinites_translated, Ordering::Relaxed);
    progress.infinites_symbolic.store(initial_result.infinites_symbolic, Ordering::Relaxed);
    *progress.max_score.lock().unwrap() = initial_result.max_score;
    *progress.champion_code.lock().unwrap() = initial_result.champion_code.clone();
    progress.max_halting_steps.store(initial_result.max_halting_steps, Ordering::Relaxed);
    for p in initial_result.top_halted.iter() {
        progress.top_halted.lock().unwrap().push(p.clone());
    }
    let prog_clone = progress.clone();

    let progress_thread = std::thread::spawn(move || {
        let mut done = prog_clone.done_mutex.lock().unwrap();
        while !*done {
            let (new_done, timeout_res) = prog_clone
                .done_cvar
                .wait_timeout(done, Duration::from_secs(progress_secs))
                .unwrap();
            done = new_done;
            if *done {
                break;
            }

            if timeout_res.timed_out() {
                let total = prog_clone.total.load(Ordering::Relaxed);
                let unknown = prog_clone.holdouts.load(Ordering::Relaxed);
                let score = *prog_clone.max_score.lock().unwrap();
                let max_steps = prog_clone.max_halting_steps.load(Ordering::Relaxed);
                let champ = prog_clone.champion_code.lock().unwrap().clone();

                let pct = if total > 0 {
                    (unknown as f64 / total as f64) * 100.0
                } else {
                    0.0
                };
                let timestamp = chrono::Local::now().format("%Y-%m-%d %H:%M:%S");

                println!(
                    "[{}] Progress: {} total, {} Unknown ({:.2}%), max score: {}, max steps: {}",
                    timestamp, total, unknown, pct, score, max_steps
                );
                if !champ.is_empty() {
                    println!("  Champion: {}", champ);
                }
            }
        }
    });

    let mut tx_opt = None;
    let mut writer_thread = None;
    let mut checkpoint_tx_opt = None;
    let mut checkpoint_writer_thread = None;

    if let Some(dir_path) = &out_dir {
        std::fs::create_dir_all(dir_path).unwrap();
        
        if write_holdouts {
            let holdouts_path = format!("{}/holdouts.txt", dir_path);
            let (tx, rx) = std::sync::mpsc::sync_channel::<Vec<String>>(1000);
            tx_opt = Some(tx);
            writer_thread = Some(std::thread::spawn(move || {
                let file = std::fs::OpenOptions::new().create(true).append(true).open(holdouts_path).expect("Failed to open holdouts file");
                let mut writer = BufWriter::new(file);
                while let Ok(batch) = rx.recv() {
                    for line in batch {
                        writeln!(writer, "{}", line).unwrap();
                    }
                }
            }));
        }

        let checkpoint_path = format!("{}/checkpoint.txt", dir_path);
        let (ctx, crx) = std::sync::mpsc::sync_channel::<(usize, SearchResult)>(1000);
        checkpoint_tx_opt = Some(ctx);
        checkpoint_writer_thread = Some(std::thread::spawn(move || {
            let file = std::fs::OpenOptions::new().create(true).append(true).open(checkpoint_path).expect("Failed to open checkpoint file");
            let mut writer = BufWriter::new(file);
            while let Ok((idx, res)) = crx.recv() {
                writeln!(writer, "PREFIX {} {} {} {} {} {} {} {} {} {} {}", 
                    idx, res.total, res.halted, res.holdouts, 
                    res.infinites_stationary, res.infinites_translated, 
                    res.infinites_symbolic, res.infinites_sum, 
                    res.max_score, res.max_halting_steps, 
                    if res.champion_code.is_empty() { "-" } else { &res.champion_code }
                ).unwrap();
                for p in &res.top_halted {
                    writeln!(writer, "TOP {} {} {}", p.score, p.steps, p.code).unwrap();
                }
                writeln!(writer, "END_PREFIX").unwrap();
                writer.flush().unwrap();
            }
        }));
    }
    let reduced_result = prefixes
        .into_par_iter()
        .enumerate()
        .filter(|(idx, _)| !completed_indices.contains(idx))
        .map_with((tx_opt, checkpoint_tx_opt), |(tx_opt, ctx_opt), (idx, prefix)| {
            let mut tx = tx_opt.as_ref().cloned();
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
                &mut tx,
                &mut local_buffer,
                prefix.inc_mask,
                prefix.unresolved_mask,
                prefix.known_gt_0,
                prefix.has_while,
                prefix.has_external_inc,
                prefix.last_dec_was_gt_0,
                Some(&progress),
            );

            if let Some(tx_sender) = tx {
                if !local_buffer.is_empty() {
                    let _ = tx_sender.send(local_buffer);
                }
            }

            if !local_res.top_halted.is_empty() {
                let mut global_heap = progress.top_halted.lock().unwrap();
                for prog in local_res.top_halted.iter() {
                    global_heap.push(prog.clone());
                    if global_heap.len() > 1000 {
                        global_heap.pop();
                    }
                }
            }
progress.total.fetch_add(local_res.total, Ordering::Relaxed);
            progress
                .halted
                .fetch_add(local_res.halted, Ordering::Relaxed);
            progress
                .holdouts
                .fetch_add(local_res.holdouts, Ordering::Relaxed);
            progress
                .infinites_stationary
                .fetch_add(local_res.infinites_stationary, Ordering::Relaxed);
            progress
                .infinites_translated
                .fetch_add(local_res.infinites_translated, Ordering::Relaxed);
            progress
                .infinites_symbolic
                .fetch_add(local_res.infinites_symbolic, Ordering::Relaxed);

            let mut score_lock = progress.max_score.lock().unwrap();
            let mut champ_lock = progress.champion_code.lock().unwrap();
            if local_res.max_score > *score_lock {
                *score_lock = local_res.max_score;
                *champ_lock = local_res.champion_code.clone();
            }
            drop(score_lock);
            drop(champ_lock);
            progress.max_halting_steps.fetch_max(local_res.max_halting_steps, Ordering::Relaxed);

            if let Some(ctx_sender) = ctx_opt {
                let _ = ctx_sender.send((idx, local_res.clone()));
            }

            local_res
        })
        .reduce(
            || SearchResult::new(),
            |mut a, b| {
                a.merge(&b);
                a
            },
        );

    *progress.done_mutex.lock().unwrap() = true;
    progress.done_cvar.notify_all();
    let _ = progress_thread.join();

    if let Some(wt) = writer_thread {
        let _ = wt.join();
    }
    
    if let Some(cwt) = checkpoint_writer_thread {
        let _ = cwt.join();
    }

    let mut result = initial_result;
    result.merge(&reduced_result);

    if let Some(dir_path) = out_dir {
        let halt_path = format!("{}/halt.top.txt", dir_path);
        let mut file = File::create(halt_path).expect("Failed to create halt.top.txt");
        let sorted = result.top_halted.clone().into_sorted_vec();
        for p in sorted {
            writeln!(file, "{} Halt {} {}", p.code, p.score, p.steps).unwrap();
        }
    }

    result
}

fn is_valid_primitive(last_instr: Option<&FlatInstr>, current_var: usize, is_inc: bool) -> bool {
    match last_instr {
        Some(FlatInstr::Inc(p)) => {
            if current_var < *p {
                return false;
            }
            if current_var == *p && !is_inc {
                return false;
            }
            true
        }
        Some(FlatInstr::Dec(p)) => {
            if current_var < *p {
                return false;
            }
            true
        }
        _ => true,
    }
}


fn map_in_place(ast: &mut [crate::ast::Instr], p: &[usize]) {
    for instr in ast {
        match instr {
            crate::ast::Instr::Inc(v) => *v = p[*v],
            crate::ast::Instr::Dec(v) => *v = p[*v],
            crate::ast::Instr::While(v, body) => {
                *v = p[*v];
                map_in_place(body, p);
            }
        }
    }
}

thread_local! {
    static CANON_CTX: std::cell::RefCell<crate::ast::CanonCtx> = std::cell::RefCell::new(crate::ast::CanonCtx::new());
}

#[inline(never)]
fn is_canonical(prefix: &[FlatInstr], max_var: usize) -> bool {
    if max_var == 0 {
        return true;
    }

    let mut orig_ast = parse_flat(prefix);
    CANON_CTX.with(|ctx| {
        crate::ast::canonicalize_block_with_ctx(&mut orig_ast, &mut *ctx.borrow_mut());
    });

    if orig_ast.is_empty() {
        return true;
    }

    let n = orig_ast.len();
    let mut in_degree = vec![0; n];
    for i in 0..n {
        let rw_i = orig_ast[i].get_rw();
        for j in i+1..n {
            let rw_j = orig_ast[j].get_rw();
            if (rw_i & rw_j) != 0 {
                in_degree[j] += 1;
            }
        }
    }
    
    let mut orig_roots = Vec::new();
    for i in 0..n {
        if in_degree[i] == 0 {
            orig_roots.push(orig_ast[i].clone());
        }
    }
    
    let orig_first = orig_ast[0].clone();
    let mut mapped_roots = orig_roots.clone();

    let mut perm: Vec<usize> = (0..=max_var).collect();
    let mut c = vec![0; max_var + 1];
    let mut i = 1;

    let mut mapped_ast = orig_ast.clone();
    
    let mut check_perm = |p: &[usize]| -> bool {
        let mut min_idx: Option<usize> = None;
        for (idx, r) in orig_roots.iter().enumerate() {
            mapped_roots[idx].clone_from(r);
            map_in_place(std::slice::from_mut(&mut mapped_roots[idx]), p);
            if min_idx.is_none() || mapped_roots[idx] < mapped_roots[min_idx.unwrap()] {
                min_idx = Some(idx);
            }
        }
        
        if let Some(idx) = min_idx {
            if mapped_roots[idx] > orig_first {
                return true;
            }
            if mapped_roots[idx] < orig_first {
                return false;
            }
        }

        mapped_ast.clone_from(&orig_ast);
        map_in_place(&mut mapped_ast, p);
        CANON_CTX.with(|ctx| {
            crate::ast::canonicalize_block_with_ctx(&mut mapped_ast, &mut *ctx.borrow_mut());
        });
        mapped_ast >= orig_ast
    };

    if !check_perm(&perm) {
        return false;
    }

    while i <= max_var {
        if c[i] < i {
            if i % 2 == 0 {
                perm.swap(0, i);
            } else {
                perm.swap(c[i], i);
            }

            if !check_perm(&perm) {
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

#[inline(never)]
fn generate_prefixes(
    remaining_length: usize,
    max_var: Option<usize>,
    open_loops: &mut Vec<(usize, u32, u32, bool, u32)>,
    steps_left: usize,
    current_flat: &mut Vec<FlatInstr>,
    prefixes: &mut Vec<PrefixState>,
    inc_mask: u32,
    unresolved_mask: u32,
    known_gt_0: u32,
    has_while: u32,
    has_external_inc: u32,
    last_dec_was_gt_0: bool,
) {
    let num_vars = max_var.map_or(0, |v| v + 1);
    let missing_incs = num_vars as u32 - inc_mask.count_ones();
    if remaining_length < missing_incs as usize {
        return;
    }

    if steps_left == 0 || remaining_length == 0 {
        if remaining_length == 0 {
            if (has_while & !has_external_inc) != 0 {
                return;
            }
            if open_loops.is_empty() {
                if let Some(FlatInstr::Dec(_)) = current_flat.last() {
                    return;
                }
            }
            let mut prop_dec = 0;
            let mut prop_inc = 0;
            for loop_state in open_loops.iter().rev() {
                let mut my_dec = loop_state.1;
                let mut my_inc = loop_state.2;
                my_dec |= prop_dec;
                my_inc &= !prop_dec;
                if loop_state.3 {
                    my_inc |= prop_inc;
                    my_dec &= !prop_inc;
                }
                if (my_dec & (1 << loop_state.0)) == 0 {
                    return;
                }
                prop_dec = my_dec;
                prop_inc = my_inc;
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
            known_gt_0,
            has_while,
            has_external_inc,
            last_dec_was_gt_0,
        });
        return;
    }

    if !open_loops.is_empty() {
        let last_loop = open_loops.last().unwrap();
        if (last_loop.1 & (1 << last_loop.0)) != 0 {
            if open_loops.len() == 1 && unresolved_mask != 0 {
                // Reject
            } else {
                current_flat.push(FlatInstr::WhileEnd);
                let popped = open_loops.pop().unwrap();
                let mut old_parent_dec = 0;
                let mut old_parent_inc = 0;
                if let Some(parent) = open_loops.last_mut() {
                    old_parent_dec = parent.1;
                    old_parent_inc = parent.2;
                    parent.1 |= popped.1;
                    parent.2 &= !popped.1;
                    if popped.3 {
                        parent.2 |= popped.2;
                        parent.1 &= !popped.2;
                    }
                }
                let new_known = (popped.4 & !popped.1) & !(1 << popped.0);
                generate_prefixes(
                    remaining_length,
                    max_var,
                    open_loops,
                    steps_left - 1,
                    current_flat,
                    prefixes,
                    inc_mask,
                    unresolved_mask,
                    new_known,
                    has_while,
                    has_external_inc,
                    false,
                );
                if let Some(parent) = open_loops.last_mut() {
                    parent.1 = old_parent_dec;
                    parent.2 = old_parent_inc;
                }
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
            let mut skip = false;
            if last_dec_was_gt_0 {
                if let Some(FlatInstr::Dec(p)) = last_instr {
                    if p == v {
                        skip = true;
                    }
                }
            }
            if !skip {
                let mut is_inside_v = false;
                for loop_state in open_loops.iter() {
                    if loop_state.0 == v {
                        is_inside_v = true;
                        break;
                    }
                }
                let next_external_inc = if !is_inside_v {
                    has_external_inc | (1 << v)
                } else {
                    has_external_inc
                };

                current_flat.push(FlatInstr::Inc(v));
                let mut old_dec = 0;
                let mut old_inc = 0;
                if let Some(last_loop) = open_loops.last_mut() {
                    old_dec = last_loop.1;
                    old_inc = last_loop.2;
                    last_loop.1 &= !(1 << v);
                    last_loop.2 |= 1 << v ;
                }
                generate_prefixes(
                    remaining_length - 1,
                    next_max_var,
                    open_loops,
                    steps_left - 1,
                    current_flat,
                    prefixes,
                    inc_mask | (1 << v),
                    unresolved_mask & !(1 << v),
                    known_gt_0 | (1 << v),
                    has_while,
                    next_external_inc,
                    false,
                );
                if let Some(last_loop) = open_loops.last_mut() {
                    last_loop.1 = old_dec;
                    last_loop.2 = old_inc;
                }
                current_flat.pop();
            }
        }

        if !(is_new_var && is_top_level) {
            let next_unresolved = if is_new_var {
                unresolved_mask | (1 << v)
            } else {
                unresolved_mask
            };

            if is_valid_primitive(last_instr.as_ref(), v, false) {
                let ends_program_in_dec = remaining_length == 1 && open_loops.is_empty();
                if !ends_program_in_dec {
                    let is_gt_0 = (known_gt_0 & (1 << v)) != 0;
                    current_flat.push(FlatInstr::Dec(v));
                    let mut old_dec = 0;
                    let mut old_inc = 0;
                    if let Some(last_loop) = open_loops.last_mut() {
                        old_dec = last_loop.1;
                        old_inc = last_loop.2;
                        last_loop.1 |= 1 << v ;
                        last_loop.2 &= !(1 << v);
                    }
                    generate_prefixes(
                        remaining_length - 1,
                        next_max_var,
                        open_loops,
                        steps_left - 1,
                        current_flat,
                        prefixes,
                        inc_mask,
                        next_unresolved,
                        known_gt_0 & !(1 << v),
                        has_while,
                        has_external_inc,
                        is_gt_0,
                    );
                    if let Some(last_loop) = open_loops.last_mut() {
                        last_loop.1 = old_dec;
                        last_loop.2 = old_inc;
                    }
                    current_flat.pop();
                }
            }

            if open_loops.is_empty() && (known_gt_0 & (1 << v)) == 0 {
                // Top-level dead loop, perfectly prune!
            } else {
                current_flat.push(FlatInstr::WhileStart(v));
                let is_guar = (known_gt_0 & (1 << v)) != 0;
                open_loops.push((v, 0, 0, is_guar, known_gt_0));
                generate_prefixes(
                    remaining_length - 1,
                    next_max_var,
                    open_loops,
                    steps_left - 1,
                    current_flat,
                    prefixes,
                    inc_mask,
                    next_unresolved,
                    known_gt_0 | (1 << v),
                    has_while | (1 << v),
                    has_external_inc,
                    false,
                );
                open_loops.pop();
                current_flat.pop();
            }
        }
    }
}

#[inline(never)]
fn generate_and_sim(
    remaining_length: usize,
    max_var: Option<usize>,
    open_loops: &mut Vec<(usize, u32, u32, bool, u32)>,
    current_flat: &mut Vec<FlatInstr>,
    local_res: &mut SearchResult,
    sim: &mut Simulator,
    max_steps: usize,
    tx: &mut Option<SyncSender<Vec<String>>>,
    local_buffer: &mut Vec<String>,
    inc_mask: u32,
    unresolved_mask: u32,
    known_gt_0: u32,
    has_while: u32,
    has_external_inc: u32,
    last_dec_was_gt_0: bool,
    progress: Option<&SharedProgress>,
) {
    let num_vars = max_var.map_or(0, |v| v + 1);
    let missing_incs = num_vars as u32 - inc_mask.count_ones();
    if remaining_length < missing_incs as usize {
        return;
    }

    if remaining_length == 0 {
        if (has_while & !has_external_inc) != 0 {
            return;
        }
        if open_loops.is_empty() {
            if let Some(FlatInstr::Dec(_)) = current_flat.last() {
                return;
            }
        }

        let mut prop_dec = 0;
        let mut prop_inc = 0;
        for loop_state in open_loops.iter().rev() {
            let mut my_dec = loop_state.1;
            let mut my_inc = loop_state.2;
            my_dec |= prop_dec;
            my_inc &= !prop_dec;
            if loop_state.3 {
                my_inc |= prop_inc;
                my_dec &= !prop_inc;
            }
            if (my_dec & (1 << loop_state.0)) == 0 {
                return;
            }
            prop_dec = my_dec;
            prop_inc = my_inc;
        }

        if !is_canonical(current_flat, max_var.unwrap_or(0)) {
            return;
        }

        for _ in 0..open_loops.len() {
            current_flat.push(FlatInstr::WhileEnd);
        }

        let ast = parse_flat(current_flat);
        if crate::ast::prune_infinite_loops(&ast, 0) {
            for _ in 0..open_loops.len() {
                current_flat.pop();
            }
            return;
        }
        local_res.total += 1;
        match sim.run(&ast, max_steps) {
            RunResult::Halted { score, steps } => {
                local_res.halted += 1;
                if score > local_res.max_score {
                    local_res.max_score = score;
                    local_res.champion_code = format_program(&ast);
                }
                if steps > local_res.max_halting_steps {
                    local_res.max_halting_steps = steps;
                }
                local_res.top_halted.push(TopProgram { score, steps, code: format_program(&ast) });
                if local_res.top_halted.len() > 1000 {
                    local_res.top_halted.pop();
                }
            }
            RunResult::Infinite(reason) => {
                match reason {
                    InfiniteReason::StationaryCycle => local_res.infinites_stationary += 1,
                    InfiniteReason::TranslatedCycle => local_res.infinites_translated += 1,
                    InfiniteReason::SymbolicMonotonic => local_res.infinites_symbolic += 1,
                    InfiniteReason::SumMonotonic => local_res.infinites_sum += 1,
                }
            }
            RunResult::Unknown => {
                local_res.holdouts += 1;
                if tx.is_some() {
                    local_buffer.push(format!("{} Holdout", format_program(&ast)));
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
        if (last_loop.1 & (1 << last_loop.0)) != 0 {
            if open_loops.len() == 1 && unresolved_mask != 0 {
                // Reject
            } else {
                current_flat.push(FlatInstr::WhileEnd);
                let popped = open_loops.pop().unwrap();
                let mut old_parent_dec = 0;
                let mut old_parent_inc = 0;
                if let Some(parent) = open_loops.last_mut() {
                    old_parent_dec = parent.1;
                    old_parent_inc = parent.2;
                    parent.1 |= popped.1;
                    parent.2 &= !popped.1;
                    if popped.3 {
                        parent.2 |= popped.2;
                        parent.1 &= !popped.2;
                    }
                }
                let new_known = (popped.4 & !popped.1) & !(1 << popped.0);
                generate_and_sim(
                    remaining_length,
                    max_var,
                    open_loops,
                    current_flat,
                    local_res,
                    sim,
                    max_steps,
                    tx,
                    local_buffer,
                    inc_mask,
                    unresolved_mask,
                    new_known,
                    has_while,
                    has_external_inc,
                    false,
                    progress,
                );
                if let Some(parent) = open_loops.last_mut() {
                    parent.1 = old_parent_dec;
                    parent.2 = old_parent_inc;
                }
                open_loops.push(popped);
                current_flat.pop();
            }
        }
    }

    let next_allowed = match max_var {
        Some(v) => std::cmp::min(v + 1, 9),
        None => 0,
    };
    let last_instr = current_flat.last().cloned();

    for v in 0..=next_allowed {
        let next_max_var = Some(max_var.unwrap_or(0).max(v));
        let is_new_var = v == next_allowed;
        let is_top_level = open_loops.is_empty();

        if is_valid_primitive(last_instr.as_ref(), v, true) {
            let mut skip = false;
            if last_dec_was_gt_0 {
                if let Some(FlatInstr::Dec(p)) = last_instr {
                    if p == v {
                        skip = true;
                    }
                }
            }
            if !skip {
                let mut is_inside_v = false;
                for loop_state in open_loops.iter() {
                    if loop_state.0 == v {
                        is_inside_v = true;
                        break;
                    }
                }
                let next_external_inc = if !is_inside_v {
                    has_external_inc | (1 << v)
                } else {
                    has_external_inc
                };

                current_flat.push(FlatInstr::Inc(v));
                let mut old_dec = 0;
                let mut old_inc = 0;
                if let Some(last_loop) = open_loops.last_mut() {
                    old_dec = last_loop.1;
                    old_inc = last_loop.2;
                    last_loop.1 &= !(1 << v);
                    last_loop.2 |= 1 << v ;
                }
                generate_and_sim(
                    remaining_length - 1,
                    next_max_var,
                    open_loops,
                    current_flat,
                    local_res,
                    sim,
                    max_steps,
                    tx,
                    local_buffer,
                    inc_mask | (1 << v),
                    unresolved_mask & !(1 << v),
                    known_gt_0 | (1 << v),
                    has_while,
                    next_external_inc,
                    false,
                    progress,
                );
                if let Some(last_loop) = open_loops.last_mut() {
                    last_loop.1 = old_dec;
                    last_loop.2 = old_inc;
                }
                current_flat.pop();
            }
        }

        if !(is_new_var && is_top_level) {
            let next_unresolved = if is_new_var {
                unresolved_mask | (1 << v)
            } else {
                unresolved_mask
            };

            if is_valid_primitive(last_instr.as_ref(), v, false) {
                let ends_program_in_dec = remaining_length == 1 && open_loops.is_empty();
                if !ends_program_in_dec {
                    let is_gt_0 = (known_gt_0 & (1 << v)) != 0;
                    current_flat.push(FlatInstr::Dec(v));
                    let mut old_dec = 0;
                    let mut old_inc = 0;
                    if let Some(last_loop) = open_loops.last_mut() {
                        old_dec = last_loop.1;
                        old_inc = last_loop.2;
                        last_loop.1 |= 1 << v ;
                        last_loop.2 &= !(1 << v);
                    }
                    generate_and_sim(
                        remaining_length - 1,
                        next_max_var,
                        open_loops,
                        current_flat,
                        local_res,
                        sim,
                        max_steps,
                        tx,
                        local_buffer,
                        inc_mask,
                        next_unresolved,
                        known_gt_0 & !(1 << v),
                        has_while,
                        has_external_inc,
                        is_gt_0,
                        progress,
                    );
                    if let Some(last_loop) = open_loops.last_mut() {
                        last_loop.1 = old_dec;
                        last_loop.2 = old_inc;
                    }
                    current_flat.pop();
                }
            }

            if open_loops.is_empty() && (known_gt_0 & (1 << v)) == 0 {
                // Top-level dead loop, perfectly prune!
            } else {
                current_flat.push(FlatInstr::WhileStart(v));
                let is_guar = (known_gt_0 & (1 << v)) != 0;
                open_loops.push((v, 0, 0, is_guar, known_gt_0));
                generate_and_sim(
                    remaining_length - 1,
                    next_max_var,
                    open_loops,
                    current_flat,
                    local_res,
                    sim,
                    max_steps,
                    tx,
                    local_buffer,
                    inc_mask,
                    next_unresolved,
                    known_gt_0 | (1 << v),
                    has_while | (1 << v),
                    has_external_inc,
                    false,
                    progress,
                );
                open_loops.pop();
                current_flat.pop();
            }
        }
    }
}

#[inline(never)]
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
                let v = match var_stack.pop() {
    Some(val) => val,
    None => {
        println!("PANIC! flat={:?}", flat);
        std::process::exit(1);
    }
};
                ast_stack.last_mut().unwrap().push(Instr::While(v, body));
            }
        }
    }
    while ast_stack.len() > 1 {
        let body = ast_stack.pop().unwrap();
        let v = match var_stack.pop() {
    Some(val) => val,
    None => {
        println!("PANIC! flat={:?}", flat);
        std::process::exit(1);
    }
};
        ast_stack.last_mut().unwrap().push(Instr::While(v, body));
    }
    ast_stack.pop().unwrap()
}
