use crate::grf::Grf;
use crate::simulate::{simulate_with_fallback, SimResult, Num};

fn eval(grf: &Grf, template: &[Option<Num>], sweep: &[(usize, Num)], max_steps: Num) -> String {
    let mut args: Vec<Num> = template.iter().map(|v| v.unwrap_or(0)).collect();
    for &(idx, val) in sweep {
        args[idx] = val;
    }
    match simulate_with_fallback(grf, &args, max_steps).0 {
        SimResult::Value(v) => v.to_string(),
        SimResult::Diverge  => "∞".to_string(),
        _                   => "?".to_string(),
    }
}

pub fn fmt_val(v: Option<Num>) -> String {
    match v {
        Some(n) => n.to_string(),
        None => "?".to_string(),
    }
}

fn print_1d(grf: &Grf, template: &[Option<Num>], sweep_idx: usize, grid: Num, max_steps: Num) {
    let axis = format!("x{}", sweep_idx + 1);
    let f_hdr = format!("f(x{})", sweep_idx + 1);
    let vals: Vec<String> = (0..=grid)
        .map(|v| eval(grf, template, &[(sweep_idx, v)], max_steps))
        .collect();
    let val_w = vals.iter().map(|v| v.len()).max().unwrap_or(1).max(f_hdr.len());
    let n_w = grid.to_string().len().max(axis.len());

    println!("{:>n_w$}  |  {:>val_w$}", axis, f_hdr);
    println!("{}--+--{}", "-".repeat(n_w), "-".repeat(val_w));
    for (a, v) in vals.iter().enumerate() {
        println!("{:>n_w$}  |  {:>val_w$}", a, v);
    }
}

fn print_2d(grf: &Grf, template: &[Option<Num>], row_idx: usize, col_idx: usize, grid: Num, max_steps: Num) {
    let vals: Vec<Vec<String>> = (0..=grid)
        .map(|a| (0..=grid)
            .map(|b| eval(grf, template, &[(row_idx, a), (col_idx, b)], max_steps))
            .collect())
        .collect();

    let cell_w = vals.iter().flatten()
        .map(|v| v.len())
        .chain((0..=grid).map(|b| b.to_string().len()))
        .max().unwrap_or(1);

    let row_label = format!("x{}↓", row_idx + 1);
    let row_w = grid.to_string().len().max(row_label.chars().count());

    let header: String = (0..=grid).map(|b| format!("{:>cell_w$}", b)).collect::<Vec<_>>().join("  ");
    let pad = " ".repeat(row_w);
    println!("{}  |  x{} →", pad, col_idx + 1);
    let corner_pad = " ".repeat(row_w - row_label.chars().count());
    println!("{}{}  |  {}", corner_pad, row_label, header);
    println!("{}--+--{}", "-".repeat(row_w), "-".repeat(header.len()));

    for (a, row) in vals.iter().enumerate() {
        let cells: String = row.iter()
            .map(|v| format!("{:>cell_w$}", v))
            .collect::<Vec<_>>().join("  ");
        println!("{:>row_w$}  |  {}", a, cells);
    }
}

fn print_3d_slices(grf: &Grf, template: &[Option<Num>], sweep_indices: &[usize], grid: Num, max_steps: Num) {
    debug_assert_eq!(sweep_indices.len(), 3);
    let (slice_idx, row_idx, col_idx) = (sweep_indices[0], sweep_indices[1], sweep_indices[2]);
    for s in 0..=grid {
        println!("x{}={}:", slice_idx + 1, s);
        let mut tpl = template.to_vec();
        tpl[slice_idx] = Some(s);
        print_2d(grf, &tpl, row_idx, col_idx, grid, max_steps);
        if s < grid {
            println!();
        }
    }
}

fn print_flat(grf: &Grf, template: &[Option<Num>], sweep_indices: &[usize], grid: Num, max_steps: Num) {
    let sc = sweep_indices.len();
    let mut all_sweep_vals: Vec<Vec<Num>> = Vec::new();
    let mut tuple = vec![0 as Num; sc];
    loop {
        all_sweep_vals.push(tuple.clone());
        let mut pos = sc - 1;
        loop {
            tuple[pos] += 1;
            if tuple[pos] <= grid { break; }
            tuple[pos] = 0;
            if pos == 0 { break; }
            pos -= 1;
        }
        if tuple.iter().all(|&x| x == 0) { break; }
    }

    let results: Vec<String> = all_sweep_vals.iter()
        .map(|sv| {
            let sweep: Vec<(usize, Num)> = sweep_indices.iter().copied().zip(sv.iter().copied()).collect();
            eval(grf, template, &sweep, max_steps)
        })
        .collect();

    let arg_w = grid.to_string().len().max(2);
    let val_w = results.iter().map(|v| v.len()).max().unwrap_or(1).max(6);

    let arg_headers: String = sweep_indices.iter()
        .map(|i| format!("{:>arg_w$}", format!("x{}", i + 1)))
        .collect::<Vec<_>>().join("  ");
    println!("{}  |  {:>val_w$}", arg_headers, "result");
    println!("{}--+--{}", "-".repeat(arg_w * sc + 2 * (sc - 1)), "-".repeat(val_w));

    for (sv, v) in all_sweep_vals.iter().zip(results.iter()) {
        let args_str: String = sv.iter().map(|x| format!("{:>arg_w$}", x)).collect::<Vec<_>>().join("  ");
        println!("{}  |  {:>val_w$}", args_str, v);
    }
}

/// Print an I/O table sweeping over `sweep_indices` (0-based arg positions).
///
/// `template[i] = Some(v)` fixes arg i at v; `None` means that arg is swept.
/// `sweep_indices` must list exactly the None positions of `template`.
/// Dispatch: 0 sweeps → single value, 1 → row, 2 → 2D grid,
///           3 → 2D slices (first sweep dim is the slice axis), 4+ → flat list.
pub fn print_sweep_table(
    grf: &Grf,
    template: &[Option<Num>],
    sweep_indices: &[usize],
    grid: Num,
    max_steps: Num,
) {
    match sweep_indices.len() {
        0 => {
            let v = eval(grf, template, &[], max_steps);
            println!("  = {}", v);
        }
        1 => print_1d(grf, template, sweep_indices[0], grid, max_steps),
        2 => print_2d(grf, template, sweep_indices[0], sweep_indices[1], grid, max_steps),
        3 => print_3d_slices(grf, template, sweep_indices, grid, max_steps),
        _ => print_flat(grf, template, sweep_indices, grid, max_steps),
    }
}

/// Print an I/O table for `grf`, sweeping only the args reported by `used_args()`.
/// Unused args are held at 0. Arity-0 or all-unused → prints a single value.
pub fn print_io_table(grf: &Grf, grid: Num, max_steps: Num) {
    let used: Vec<usize> = grf.used_args().into_iter().map(|j| j - 1).collect();
    let template: Vec<Option<Num>> = (0..grf.arity())
        .map(|i| if used.contains(&i) { None } else { Some(0) })
        .collect();

    if used.is_empty() {
        let v = eval(grf, &template, &[], max_steps);
        println!("  = {}", v);
    } else {
        print_sweep_table(grf, &template, &used, grid, max_steps);
    }
}
