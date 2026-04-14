use crate::grf::Grf;
use crate::pruning::PruningOpts;
use std::cell::RefCell;
use std::collections::HashMap;

// ---------------------------------------------------------------------------
// GRF streaming enumeration
// ---------------------------------------------------------------------------

/// Call `callback` once for each GRF of exactly `size` with exactly `arity` inputs.
///
/// - `allow_min`: include the Minimization combinator (GRF); exclude for PRF-only.
/// - `opts`: structural pruning options (see [`PruningOpts`]).
///
/// No `Vec<Grf>` is ever materialised — memory use is O(size) at any point.
pub fn stream_grf<F: FnMut(&Grf)>(
    size: usize,
    arity: usize,
    allow_min: bool,
    opts: PruningOpts,
    callback: &mut F,
) {
    for_each_grf(size, arity, allow_min, opts, callback);
}

/// Internal recursive generator.  Uses `&mut dyn FnMut` so nested closures can
/// each capture and call through the same `callback` reference without the
/// borrow checker rejecting two simultaneous `&mut F` borrows.
fn for_each_grf(
    size: usize,
    arity: usize,
    allow_min: bool,
    opts: PruningOpts,
    callback: &mut dyn FnMut(&Grf),
) {
    if size == 0 {
        return;
    }
    if size == 1 {
        callback(&Grf::Zero(arity));
        for i in 1..=arity {
            callback(&Grf::Proj(arity, i));
        }
        if arity == 1 {
            callback(&Grf::Succ);
        }
        return;
    }
    let n = size - 1;

    // C(h, g1..gm): stream h's; for each h, stream all argument tuples
    for hsize in 1..=n {
        let gs_total = n - hsize;
        for m in 1..=gs_total {
            for_each_grf(hsize, m, allow_min, opts, &mut |h: &Grf| {
                // Prune C(Z,...) and C(P,...)
                if opts.skip_comp_zero && matches!(h, Grf::Zero(_)) {
                    return
                }
                if opts.skip_comp_proj && matches!(h, Grf::Proj(_, _)) {
                    return;
                }
                // Prune C(C(f,g), k)
                if opts.comp_assoc {
                    if let Grf::Comp(_, inner_gs, _) = h {
                        if inner_gs.len() == 1 {
                            return;
                        }
                    }
                }

                let h_box = Box::new(h.clone());
                let h_is_rec = matches!(h, Grf::Rec(_, _));
                let mut args = Vec::with_capacity(m);
                for_each_args(
                    gs_total,
                    m,
                    arity,
                    allow_min,
                    opts,
                    &mut args,
                    &mut |gs: &[Grf]| {
                        // skip_rec_zero_arg: C(R(g,h), Z(p), f2,...) ≡ C(g, f2,...)
                        // The first arg being Zero forces n=0, so only the base case
                        // fires. The strictly-smaller C(g, f2,...) is generated separately.
                        if opts.skip_rec_zero_arg
                            && h_is_rec
                            && matches!(gs.first(), Some(Grf::Zero(_)))
                        {
                            return;
                        }
                        callback(&Grf::Comp(h_box.clone(), gs.to_vec(), arity));
                    },
                );
            });
        }
    }

    // R(g, h): stream g's; for each g, stream h's
    if arity >= 1 {
        for gsize in 1..n {
            let hsize = n - gsize;
            for_each_grf(gsize, arity - 1, allow_min, opts, &mut |g: &Grf| {
                let g_box = Box::new(g.clone());
                let g_is_zero = matches!(g, Grf::Zero(_));
                for_each_grf(hsize, arity + 1, allow_min, opts, &mut |h: &Grf| {
                    // skip_rec_zero_base: R(Z(k), Z(k+2)) ≡ Z(k+1) (step always 0)
                    //                    R(Z(k), P(k+2,2)) ≡ Z(k+1) (acc starts 0, stays 0)
                    if opts.skip_rec_zero_base
                        && g_is_zero
                        && matches!(h, Grf::Zero(_) | Grf::Proj(_, 2))
                    {
                        return;
                    }
                    callback(&Grf::Rec(g_box.clone(), Box::new(h.clone())));
                });
            });
        }
    }

    // M(f): f ∈ GRF_{arity+1}, |f| = n
    if allow_min {
        for_each_grf(n, arity + 1, allow_min, opts, &mut |f: &Grf| {
            callback(&Grf::Min(Box::new(f.clone())));
        });
    }
}

/// Generate all ordered `remaining_count`-tuples of `arity`-GRFs whose sizes
/// sum to `remaining_size`, appending each element to `current` in turn.
fn for_each_args(
    remaining_size: usize,
    remaining_count: usize,
    arity: usize,
    allow_min: bool,
    opts: PruningOpts,
    current: &mut Vec<Grf>,
    callback: &mut dyn FnMut(&[Grf]),
) {
    if remaining_count == 0 {
        if remaining_size == 0 {
            callback(current);
        }
        return;
    }
    let max_first = remaining_size.saturating_sub(remaining_count - 1);
    for x in 1..=max_first {
        for_each_grf(x, arity, allow_min, opts, &mut |g: &Grf| {
            current.push(g.clone());
            for_each_args(
                remaining_size - x,
                remaining_count - 1,
                arity,
                allow_min,
                opts,
                current,
                callback,
            );
            current.pop();
        });
    }
}

// ---------------------------------------------------------------------------
// GRF seek-streaming enumeration
// ---------------------------------------------------------------------------

/// Stream GRFs at ordinal positions `[start, start + count)` in the same order
/// as [`stream_grf`], without generating any skipped GRFs.
///
/// Uses [`count_grf`] to jump over sub-trees in O(1) per level, so the seek
/// cost is O(size²) rather than O(start).
pub fn seek_stream_grf<F: FnMut(&Grf)>(
    size: usize,
    arity: usize,
    allow_min: bool,
    opts: PruningOpts,
    start: usize,
    count: usize,
    callback: &mut F,
) {
    if count == 0 {
        return;
    }
    let mut skip = start;
    let mut rem = count;
    seek_grfs(size, arity, allow_min, opts, &mut skip, &mut rem, callback);
}

/// Emit up to `*rem` GRFs of (size, arity), starting after skipping `*skip`.
/// Updates both counters as atoms are emitted or blocks are bypassed.
fn seek_grfs(
    size: usize,
    arity: usize,
    allow_min: bool,
    opts: PruningOpts,
    skip: &mut usize,
    rem: &mut usize,
    callback: &mut dyn FnMut(&Grf),
) {
    if *rem == 0 {
        return;
    }
    // Fast-skip the entire (size, arity) block if skip covers it all.
    let total = count_grf(size, arity, allow_min, opts);
    if *skip >= total {
        *skip -= total;
        return;
    }

    if size == 0 {
        return;
    }

    // Size-1 atoms: Zero(arity), Proj(arity,1..=arity), Succ (if arity==1).
    if size == 1 {
        emit_atom(skip, rem, &Grf::Zero(arity), callback);
        for i in 1..=arity {
            if *rem == 0 {
                return;
            }
            emit_atom(skip, rem, &Grf::Proj(arity, i), callback);
        }
        if arity == 1 {
            emit_atom(skip, rem, &Grf::Succ, callback);
        }
        return;
    }

    let n = size - 1;

    // ---- Comp section ----
    'comp: for hsize in 1..=n {
        let gs_total = n - hsize;
        for m in 1..=gs_total {
            if *rem == 0 {
                break 'comp;
            }

            let args_all = count_many_fast(gs_total, m, arity, allow_min, opts);
            let n_heads = count_as_head(hsize, m, allow_min, opts);
            if n_heads == 0 || args_all == 0 {
                continue;
            }

            // When skip_rec_zero_arg: Rec heads have fewer valid arg tuples.
            let args_rec = if opts.skip_rec_zero_arg && gs_total >= 1 {
                args_all
                    .saturating_sub(count_many_fast(gs_total - 1, m - 1, arity, allow_min, opts))
            } else {
                args_all
            };

            let n_rec_heads = count_rec_only(hsize, m, allow_min, opts);
            let n_non_rec_heads = n_heads.saturating_sub(n_rec_heads);
            let block_size = n_non_rec_heads
                .saturating_mul(args_all)
                .saturating_add(n_rec_heads.saturating_mul(args_rec));

            if *skip >= block_size {
                *skip -= block_size;
                continue;
            }

            // Walk heads one-by-one; use skip/rem to bypass whole per-head
            // arg-tuple groups without materialising them.
            for_each_grf(hsize, m, allow_min, opts, &mut |h: &Grf| {
                if *rem == 0 {
                    return;
                }

                // Reproduce the same head-pruning logic as for_each_grf.
                if opts.skip_comp_zero && matches!(h, Grf::Zero(_)) {
                    return;
                }
                if opts.skip_comp_proj && matches!(h, Grf::Proj(_, _)) {
                    return;
                }
                if opts.comp_assoc {
                    if let Grf::Comp(_, inner_gs, _) = h {
                        if inner_gs.len() == 1 {
                            return;
                        }
                    }
                }

                let h_is_rec = matches!(h, Grf::Rec(_, _));
                let per_head_args = if h_is_rec { args_rec } else { args_all };

                if *skip >= per_head_args {
                    *skip -= per_head_args;
                    return;
                }

                let h_box = Box::new(h.clone());
                let mut args = Vec::with_capacity(m);
                seek_args(
                    gs_total,
                    m,
                    arity,
                    allow_min,
                    opts,
                    h_is_rec && opts.skip_rec_zero_arg,
                    skip,
                    rem,
                    &mut args,
                    &mut |gs: &[Grf]| {
                        callback(&Grf::Comp(h_box.clone(), gs.to_vec(), arity));
                    },
                );
            });
        }
    }

    // ---- Rec section ----
    if arity >= 1 && *rem > 0 {
        'rec: for gsize in 1..n {
            if *rem == 0 {
                break 'rec;
            }
            let hsize = n - gsize;

            let g_total = count_grf(gsize, arity - 1, allow_min, opts);
            let h_total = count_grf(hsize, arity + 1, allow_min, opts);
            // skip_rec_zero_base prunes exactly 2 pairs at n==2 across ALL g's.
            let pruned_in_block = if opts.skip_rec_zero_base && n == 2 { 2usize } else { 0 };
            let gsize_block = g_total
                .saturating_mul(h_total)
                .saturating_sub(pruned_in_block);

            if *skip >= gsize_block {
                *skip -= gsize_block;
                continue;
            }

            // Walk g's one-by-one; for each g skip the whole h-block if possible.
            for_each_grf(gsize, arity - 1, allow_min, opts, &mut |g: &Grf| {
                if *rem == 0 {
                    return;
                }
                let g_box = Box::new(g.clone());
                let g_is_zero = matches!(g, Grf::Zero(_));
                // skip_rec_zero_base: prune R(Z, Z) and R(Z, P(_,2)) at n==2.
                let pruned_h =
                    if opts.skip_rec_zero_base && g_is_zero && n == 2 { 2usize } else { 0 };
                let h_count = h_total.saturating_sub(pruned_h);

                if *skip >= h_count {
                    *skip -= h_count;
                    return;
                }

                if pruned_h == 0 {
                    // No per-g pruning; seek through h's normally.
                    seek_grfs(hsize, arity + 1, allow_min, opts, skip, rem, &mut |h: &Grf| {
                        callback(&Grf::Rec(g_box.clone(), Box::new(h.clone())));
                    });
                } else {
                    // n==2, g_is_zero, hsize==1.  h's are size-1 atoms of arity+1.
                    // Pruned: Zero(arity+1) and Proj(arity+1, 2).
                    // Valid order: Proj(ar1,1), Proj(ar1,3..=ar1).
                    // (ar1 = arity+1 >= 2, so Succ never present.)
                    let ar1 = arity + 1;
                    let valid_hs: Vec<Grf> = std::iter::once(Grf::Proj(ar1, 1))
                        .chain((3..=ar1).map(|i| Grf::Proj(ar1, i)))
                        .collect();
                    for h in &valid_hs {
                        if *rem == 0 {
                            return;
                        }
                        if *skip > 0 {
                            *skip -= 1;
                            continue;
                        }
                        callback(&Grf::Rec(g_box.clone(), Box::new(h.clone())));
                        *rem -= 1;
                    }
                }
            });
        }
    }

    // ---- Min section ----
    if allow_min && *rem > 0 {
        seek_grfs(n, arity + 1, allow_min, opts, skip, rem, &mut |f: &Grf| {
            callback(&Grf::Min(Box::new(f.clone())));
        });
    }
}

/// Seek through ordered `remaining_count`-tuples of arity-GRFs summing to
/// `remaining_size`, appending each selected element to `current`.
///
/// When `first_must_not_be_zero` is true the first element must not be
/// `Zero(arity)` (implements `skip_rec_zero_arg` for Rec heads).
fn seek_args(
    remaining_size: usize,
    remaining_count: usize,
    arity: usize,
    allow_min: bool,
    opts: PruningOpts,
    first_must_not_be_zero: bool,
    skip: &mut usize,
    rem: &mut usize,
    current: &mut Vec<Grf>,
    callback: &mut dyn FnMut(&[Grf]),
) {
    if *rem == 0 {
        return;
    }
    if remaining_count == 0 {
        if remaining_size == 0 {
            if *skip > 0 {
                *skip -= 1;
            } else {
                callback(current);
                *rem -= 1;
            }
        }
        return;
    }

    let is_first = first_must_not_be_zero && current.is_empty();
    let max_first = remaining_size.saturating_sub(remaining_count - 1);

    for x in 1..=max_first {
        if *rem == 0 {
            return;
        }

        let rest_count =
            count_many_fast(remaining_size - x, remaining_count - 1, arity, allow_min, opts);
        if rest_count == 0 {
            continue;
        }

        // How many valid leading-g choices are there for this size-x slot?
        let g_valid_count = if is_first && x == 1 {
            // Zero(arity) is excluded; all other size-1 atoms are allowed.
            count_grf(1, arity, allow_min, opts).saturating_sub(1)
        } else {
            count_grf(x, arity, allow_min, opts)
        };
        if g_valid_count == 0 {
            continue;
        }

        let block = g_valid_count.saturating_mul(rest_count);
        if block == 0 {
            continue;
        }
        if *skip >= block {
            *skip -= block;
            continue;
        }

        // Inside this size-x block: iterate g's, skipping whole rest_count groups.
        if is_first && x == 1 {
            // Enumerate non-Zero size-1 atoms in canonical order.
            let mut non_zero_atoms: Vec<Grf> =
                (1..=arity).map(|i| Grf::Proj(arity, i)).collect();
            if arity == 1 {
                non_zero_atoms.push(Grf::Succ);
            }
            for atom in &non_zero_atoms {
                if *rem == 0 {
                    return;
                }
                if *skip >= rest_count {
                    *skip -= rest_count;
                    continue;
                }
                current.push(atom.clone());
                seek_args(
                    remaining_size - 1,
                    remaining_count - 1,
                    arity,
                    allow_min,
                    opts,
                    false,
                    skip,
                    rem,
                    current,
                    callback,
                );
                current.pop();
            }
        } else {
            // General case: enumerate size-x GRFs, skipping by rest_count groups.
            for_each_grf(x, arity, allow_min, opts, &mut |g: &Grf| {
                if *rem == 0 {
                    return;
                }
                if *skip >= rest_count {
                    *skip -= rest_count;
                    return;
                }
                current.push(g.clone());
                seek_args(
                    remaining_size - x,
                    remaining_count - 1,
                    arity,
                    allow_min,
                    opts,
                    false,
                    skip,
                    rem,
                    current,
                    callback,
                );
                current.pop();
            });
        }
    }
}

/// Emit or skip a single atom, updating the skip/rem counters.
fn emit_atom(skip: &mut usize, rem: &mut usize, grf: &Grf, callback: &mut dyn FnMut(&Grf)) {
    if *skip > 0 {
        *skip -= 1;
        return;
    }
    if *rem > 0 {
        callback(grf);
        *rem -= 1;
    }
}

// ---------------------------------------------------------------------------
// GRF counting (pure DP, no GRF trees materialised)
// ---------------------------------------------------------------------------

type CountKey = (usize, usize, bool, PruningOpts);

thread_local! {
    static COUNT_CACHE: RefCell<HashMap<CountKey, usize>> = RefCell::new(HashMap::new());
    // count_as_head(size, arity, allow_min, opts):
    //   count of GRFs valid as a Comp head under `opts`.
    //   = count_grf minus single-argument Comps (when comp_assoc) and minus
    //     Zero/Proj atoms (when skip_comp_*).
    static AS_HEAD_CACHE: RefCell<HashMap<CountKey, usize>> = RefCell::new(HashMap::new());
}

/// Count GRFs of given `size` and `arity` without building any GRF tree.
/// Results are memoised in a thread-local DP table.
pub fn count_grf(size: usize, arity: usize, allow_min: bool, opts: PruningOpts) -> usize {
    let key = (size, arity, allow_min, opts);
    if let Some(c) = COUNT_CACHE.with(|cache| cache.borrow().get(&key).copied()) {
        return c;
    }
    let result = compute_count(size, arity, allow_min, opts);
    COUNT_CACHE.with(|cache| cache.borrow_mut().insert(key, result));
    result
}

/// Count of GRFs that are valid as a `Comp` head under `opts`.
///
/// Differs from `count_grf` in two ways:
/// - With `skip_comp_*`: Zero and Proj atoms are excluded (they would make
///   `C(Z,…)` or `C(P,…)`, always equivalent to simpler expressions).
/// - With `comp_assoc`: single-argument Comps are excluded (we always prefer
///   the right-associated canonical form).
fn count_as_head(size: usize, arity: usize, allow_min: bool, opts: PruningOpts) -> usize {
    let key = (size, arity, allow_min, opts);
    if let Some(c) = AS_HEAD_CACHE.with(|cache| cache.borrow().get(&key).copied()) {
        return c;
    }
    let result = compute_as_head(size, arity, allow_min, opts);
    AS_HEAD_CACHE.with(|cache| cache.borrow_mut().insert(key, result));
    result
}

fn compute_as_head(size: usize, arity: usize, allow_min: bool, opts: PruningOpts) -> usize {
    if size == 1 {
        let mut count = 0;
        if arity == 1 {
            count += 1;  // S is always a legal head
        }
        if !opts.skip_comp_zero {
            count += 1;  // Z only valid if not skipping C(Z, ...)
        }
        if !opts.skip_comp_proj {
            count += arity;  // P_i only valid if not skipping C(P, ...)
        }
        return count;
    }

    // Start from the full count of all generated GRFs of this size/arity.
    let all = count_grf(size, arity, allow_min, opts);

    // With comp_assoc: subtract single-argument Comps — they are generated as
    // standalone GRFs but must not be used as Comp heads.
    //
    // A single-arg Comp of size `size` and arity `arity` has the form
    //   C(f, [g])  where  f.arity()=1, g.arity()=arity, f.size()+g.size()=size-1
    // and f must itself be a valid Comp head (not a single-arg Comp).
    if !opts.comp_assoc || size < 3 {
        return all;
    }

    let inner_total = size - 1; // f.size() + g.size()
    let mut single_arg_count = 0usize;
    for fsize in 1..inner_total {
        let gsize = inner_total - fsize;
        // f must be a valid comp head of arity 1
        let f_count = count_as_head(fsize, 1, allow_min, opts);
        // g can be any generated GRF of arity `arity`
        let g_count = count_grf(gsize, arity, allow_min, opts);
        single_arg_count = single_arg_count.saturating_add(f_count.saturating_mul(g_count));
    }

    // When skip_rec_zero_arg is on, C(R(g,h), Z(arity)) single-arg Comps are pruned
    // and already excluded from count_grf, but the loop above still counts them via
    // count_as_head(fsize=inner_total-1, 1) * count_grf(gsize=1, arity) because
    // Rec heads pass count_as_head and Z(arity) is included in count_grf(1, arity).
    // Correct by subtracting the count of these pruned expressions.
    if opts.skip_rec_zero_arg && inner_total >= 2 {
        let pruned_sa = count_rec_only(inner_total - 1, 1, allow_min, opts);
        single_arg_count = single_arg_count.saturating_sub(pruned_sa);
    }

    all.saturating_sub(single_arg_count)
}

fn compute_count(size: usize, arity: usize, allow_min: bool, opts: PruningOpts) -> usize {
    if size == 0 {
        return 0;
    }
    if size == 1 {
        // Zero(arity): 1; Succ: 1 if arity==1; Proj(arity,i): arity choices
        return 1 + usize::from(arity == 1) + arity;
    }
    let n = size - 1;
    let mut total = 0usize;

    // C(h, g1..gm): h ∈ GRF_m (valid head), each gi ∈ GRF_arity
    for hsize in 1..=n {
        let gs_total = n - hsize;
        for m in 1..=gs_total {
            // count_as_head handles skip_comp_* and comp_assoc filters.
            let h_count = count_as_head(hsize, m, allow_min, opts);
            if h_count == 0 {
                continue;
            }
            total = total.saturating_add(
                h_count.saturating_mul(count_many_fast(gs_total, m, arity, allow_min, opts)),
            );
        }
    }

    // skip_rec_zero_arg: subtract C(R(g,h), Z(arity), f2,...,fm) for all m,g,h.
    // These are pruned because the first arg is structurally Zero, forcing n=0,
    // so the equivalent C(g, f2,...) (strictly smaller) is generated instead.
    if opts.skip_rec_zero_arg {
        for hsize in 1..=n {
            let gs_total = n - hsize;
            if gs_total == 0 {
                continue; // need at least one arg (the Zero)
            }
            for m in 1..=gs_total {
                let rec_count = count_rec_only(hsize, m, allow_min, opts);
                if rec_count == 0 {
                    continue;
                }
                // First arg is Z(arity): 1 choice, size 1.
                // Remaining m-1 args of arity `arity` summing to gs_total-1.
                let rest = count_many_fast(gs_total - 1, m - 1, arity, allow_min, opts);
                total = total.saturating_sub(rec_count.saturating_mul(rest));
            }
        }
    }

    // R(g, h): g ∈ GRF_{arity-1}, h ∈ GRF_{arity+1}
    if arity >= 1 {
        for gsize in 1..n {
            total = total.saturating_add(
                count_grf(gsize, arity - 1, allow_min, opts)
                    .saturating_mul(count_grf(n - gsize, arity + 1, allow_min, opts)),
            );
        }
        // skip_rec_zero_base: at size=3 (n=2), prune R(Z(arity-1), Z(arity+1)) and
        // R(Z(arity-1), P(arity+1,2)) — 2 expressions, both always ≡ Z(arity).
        if opts.skip_rec_zero_base && n == 2 {
            total = total.saturating_sub(2);
        }
    }

    // M(f): f ∈ GRF_{arity+1}
    if allow_min {
        total = total.saturating_add(count_grf(n, arity + 1, allow_min, opts));
    }

    total
}

/// Count only the `R(g, h)` (Rec) expressions of exactly `size` and `arity`.
/// Used to compute the skip_rec_zero_arg subtraction in `compute_count`.
fn count_rec_only(size: usize, arity: usize, allow_min: bool, opts: PruningOpts) -> usize {
    if size < 3 || arity == 0 {
        return 0;
    }
    let n = size - 1;
    let mut total = 0usize;
    for gsize in 1..n {
        total = total.saturating_add(
            count_grf(gsize, arity - 1, allow_min, opts)
                .saturating_mul(count_grf(n - gsize, arity + 1, allow_min, opts)),
        );
    }
    // skip_rec_zero_base: R(Z(arity-1), Z(arity+1)) and R(Z(arity-1), P(arity+1,2))
    // are pruned — exactly 2 expressions at size=3 for each arity ≥ 1.
    if opts.skip_rec_zero_base && size == 3 {
        total = total.saturating_sub(2);
    }
    total
}

fn count_many_fast(
    total_size: usize,
    num_funcs: usize,
    arity: usize,
    allow_min: bool,
    opts: PruningOpts,
) -> usize {
    if num_funcs > total_size {
        return 0;
    }
    if num_funcs == 0 {
        return usize::from(total_size == 0);
    }
    let max_first = total_size.saturating_sub(num_funcs - 1);
    let mut total = 0usize;
    for x in 1..=max_first {
        total = total.saturating_add(
            count_grf(x, arity, allow_min, opts).saturating_mul(count_many_fast(
                total_size - x,
                num_funcs - 1,
                arity,
                allow_min,
                opts,
            )),
        );
    }
    total
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    /// Collect all GRFs of given size/arity into a Vec via streaming.
    fn collect(size: usize, arity: usize, allow_min: bool, opts: PruningOpts) -> Vec<Grf> {
        let mut grfs = Vec::new();
        stream_grf(size, arity, allow_min, opts, &mut |g| grfs.push(g.clone()));

        // Assert every GRF in the streamed set has the correct size and arity.
        for grf in &grfs {
            assert_eq!(grf.size(), size, "size mismatch for {grf}");
            assert_eq!(grf.arity(), arity, "arity mismatch for {grf}");
            if !allow_min {
                assert!(grf.is_prf(), "non-PRF when allow_min=false: {grf}");
            }
        }

        grfs
    }

    const NO_PRUNE: PruningOpts = PruningOpts::none();
    const SKIP_COMP_ZERO: PruningOpts = PruningOpts {
        skip_comp_zero: true,
        ..NO_PRUNE
    };
    const SKIP_COMP_PROJ: PruningOpts = PruningOpts {
        skip_comp_proj: true,
        ..NO_PRUNE
    };
    const SKIP_COMP_TRIVIAL: PruningOpts = PruningOpts {
        skip_comp_zero: true,
        skip_comp_proj: true,
        ..NO_PRUNE
    };
    const COMP_ASSOC: PruningOpts = PruningOpts {
        comp_assoc: true,
        ..NO_PRUNE
    };
    const SKIP_REC_ZERO_BASE: PruningOpts = PruningOpts {
        skip_rec_zero_base: true,
        ..NO_PRUNE
    };
    const SKIP_REC_ZERO: PruningOpts = PruningOpts {
        skip_rec_zero_arg: true,
        ..NO_PRUNE
    };
    const ALL_OPTS: PruningOpts = PruningOpts::all();

    // --- atom counts (size=1) ---

    #[test]
    fn test_atoms_arity0() {
        assert_eq!(collect(1, 0, true, NO_PRUNE).len(), 1); // Z0 only
    }

    #[test]
    fn test_atoms_arity1() {
        assert_eq!(collect(1, 1, true, NO_PRUNE).len(), 3); // Z1, S, P(1,1)
    }

    #[test]
    fn test_atoms_arity2() {
        assert_eq!(collect(1, 2, true, NO_PRUNE).len(), 3); // Z2, P(2,1), P(2,2)
    }

    #[test]
    fn test_atoms_arity3() {
        assert_eq!(collect(1, 3, true, NO_PRUNE).len(), 4); // Z3, P(3,1..3)
    }

    // --- size-2 ---

    #[test]
    fn test_size2_arity0_with_min() {
        assert_eq!(collect(2, 0, true, NO_PRUNE).len(), 3); // M(Z1), M(S), M(P(1,1))
    }

    #[test]
    fn test_size2_arity0_prf() {
        assert_eq!(collect(2, 0, false, NO_PRUNE).len(), 0);
    }

    // --- size-3 ---

    #[test]
    fn test_size3_arity0_with_min() {
        assert_eq!(collect(3, 0, true, NO_PRUNE).len(), 6);
    }

    #[test]
    fn test_size3_arity0_prf() {
        let all = collect(3, 0, false, NO_PRUNE);
        assert_eq!(all.len(), 3);
        let champion = Grf::comp(Grf::Succ, vec![Grf::Zero(0)]);
        assert!(
            all.iter().any(|g| *g == champion),
            "C(S,Z0) should be in size-3 PRF_0"
        );
    }

    #[test]
    fn test_size3_arity1_with_min() {
        assert_eq!(collect(3, 1, true, NO_PRUNE).len(), 16);
    }

    // --- size-4 ---

    #[test]
    fn test_size4_arity0_with_min() {
        assert_eq!(collect(4, 0, true, NO_PRUNE).len(), 31);
    }

    // --- larger sizes ---

    #[test]
    fn test_verify_sizes_5_to_7() {
        for size in 5..=7 {
            for arity in 0..=3 {
                collect(size, arity, false, NO_PRUNE);
                collect(size, arity, true, NO_PRUNE);
            }
        }
    }

    // --- skip_trivial ---

    #[test]
    fn test_skip_trivial_removes_zero_proj_comps() {
        let full = collect(3, 0, false, NO_PRUNE);
        let trim = collect(3, 0, false, SKIP_COMP_TRIVIAL);
        assert_eq!(full.len(), 3);
        assert_eq!(trim.len(), 1);
        assert_eq!(trim[0], Grf::comp(Grf::Succ, vec![Grf::Zero(0)]));
    }

    #[test]
    fn test_skip_trivial_never_more_than_full() {
        for size in 1..=8 {
            for arity in 0..=2 {
                let full = count_grf(size, arity, false, NO_PRUNE);
                let trim = count_grf(size, arity, false, SKIP_COMP_TRIVIAL);
                assert!(
                    trim <= full,
                    "skip_trivial produced more GRFs at size={size} arity={arity}"
                );
            }
        }
    }

    // --- comp_assoc ---

    #[test]
    fn test_comp_assoc_removes_left_associated_comps() {
        // C(C(S, Z1), Z0) should be removed; C(S, C(Z1, Z0)) generated instead.
        let full = collect(5, 0, false, NO_PRUNE);
        let assoc = collect(5, 0, false, COMP_ASSOC);

        let left_assoc = "C(C(S, Z1), Z0)".parse::<Grf>().unwrap();
        let right_assoc = "C(S, C(Z1, Z0))".parse::<Grf>().unwrap();

        assert!(
            full.iter().any(|g| *g == left_assoc),
            "C(C(S,Z1),Z0) must exist in full set"
        );
        assert!(
            full.iter().any(|g| *g == right_assoc),
            "C(S,C(Z1,Z0)) must exist in full set"
        );
        assert!(
            !assoc.iter().any(|g| *g == left_assoc),
            "C(C(S,Z1),Z0) should be pruned with comp_assoc"
        );
        assert!(
            assoc.iter().any(|g| *g == right_assoc),
            "C(S,C(Z1,Z0)) should still be generated with comp_assoc"
        );
    }

    #[test]
    fn test_comp_assoc_never_more_than_full() {
        for size in 1..=8 {
            for arity in 0..=2 {
                let full = count_grf(size, arity, false, NO_PRUNE);
                let assoc = count_grf(size, arity, false, COMP_ASSOC);
                assert!(
                    assoc <= full,
                    "comp_assoc produced more GRFs at size={size} arity={arity}"
                );
            }
        }
    }

    #[test]
    fn test_comp_assoc_all_opts_fewer_than_skip_trivial() {
        for size in 1..=8 {
            for arity in 0..=2 {
                let st = count_grf(size, arity, false, SKIP_COMP_TRIVIAL);
                let all = count_grf(size, arity, false, ALL_OPTS);
                assert!(
                    all <= st,
                    "ALL_OPTS produced more GRFs than SKIP_COMP_TRIVIAL at size={size} arity={arity}"
                );
            }
        }
    }

    // --- no duplicates ---

    #[test]
    fn test_no_duplicates() {
        use std::collections::HashSet;
        for size in 1..=7 {
            let all = collect(size, 0, false, NO_PRUNE);
            let unique: HashSet<Grf> = all.iter().cloned().collect();
            assert_eq!(all.len(), unique.len(), "duplicates at size={size}");
        }
    }

    #[test]
    fn test_no_duplicates_comp_assoc() {
        use std::collections::HashSet;
        for size in 1..=7 {
            for arity in 0..=2 {
                let all = collect(size, arity, false, COMP_ASSOC);
                let unique: HashSet<Grf> = all.iter().cloned().collect();
                assert_eq!(
                    all.len(),
                    unique.len(),
                    "duplicates with comp_assoc at size={size} arity={arity}"
                );
            }
        }
    }

    // --- skip_rec_zero_arg ---

    // --- skip_rec_zero_base ---

    #[test]
    fn test_skip_rec_zero_base_removes_specific_forms() {
        // R(Z0, Z2) and R(Z0, P(2,2)) should be pruned (≡ Z1).
        let pruned = collect(3, 1, false, SKIP_REC_ZERO_BASE);
        let rz0z2 = "R(Z0, Z2)".parse::<Grf>().unwrap();
        let rz0p22 = "R(Z0, P(2,2))".parse::<Grf>().unwrap();
        assert!(
            !pruned.iter().any(|g| *g == rz0z2),
            "R(Z0,Z2) should be pruned by skip_rec_zero_base"
        );
        assert!(
            !pruned.iter().any(|g| *g == rz0p22),
            "R(Z0,P(2,2)) should be pruned by skip_rec_zero_base"
        );

        // R(Z0, P(2,1)) should NOT be pruned (step=counter, not acc).
        let rz0p21 = "R(Z0, P(2,1))".parse::<Grf>().unwrap();
        assert!(
            pruned.iter().any(|g| *g == rz0p21),
            "R(Z0,P(2,1)) should not be pruned (step returns counter, not zero)"
        );
    }

    #[test]
    fn test_skip_rec_zero_base_never_more_than_full() {
        for size in 1..=8 {
            for arity in 0..=2 {
                let full = count_grf(size, arity, false, NO_PRUNE);
                let pruned = count_grf(size, arity, false, SKIP_REC_ZERO_BASE);
                assert!(
                    pruned <= full,
                    "skip_rec_zero_base produced more GRFs at size={size} arity={arity}"
                );
            }
        }
    }

    #[test]
    fn test_skip_rec_zero_arg_removes_specific_form() {
        // C(R(Z0, Z2), Z0) should be removed (head is Rec, first arg is Zero).
        // It is equivalent to the strictly smaller C(Z0) = Z0 (size 1).
        let pruned = collect(5, 0, false, SKIP_REC_ZERO);
        let target = "C(R(Z0, Z2), Z0)".parse::<Grf>().unwrap();
        assert!(
            !pruned.iter().any(|g| *g == target),
            "C(R(Z0,Z2),Z0) should be pruned by skip_rec_zero_arg"
        );

        // C(R(Z0, Z2), C(S, Z0)) should NOT be removed (first arg C(S,Z0) is not Zero).
        let full = collect(7, 0, false, NO_PRUNE);
        let non_pruned = "C(R(Z0, Z2), C(S, Z0))".parse::<Grf>().unwrap();
        assert!(
            full.iter().any(|g| *g == non_pruned),
            "C(R(Z0,Z2),C(S,Z0)) must exist in full set"
        );
        let with_rule = collect(7, 0, false, SKIP_REC_ZERO);
        assert!(
            with_rule.iter().any(|g| *g == non_pruned),
            "C(R(Z0,Z2),C(S,Z0)) should not be pruned (first arg is not Zero)"
        );
    }

    #[test]
    fn test_skip_rec_zero_arg_never_more_than_full() {
        for size in 1..=8 {
            for arity in 0..=2 {
                let full = count_grf(size, arity, false, NO_PRUNE);
                let pruned = count_grf(size, arity, false, SKIP_REC_ZERO);
                assert!(
                    pruned <= full,
                    "skip_rec_zero_arg produced more GRFs at size={size} arity={arity}"
                );
            }
        }
    }

    // --- seek_stream_grf matches stream_grf slices ---

    /// Collect via seek_stream_grf and compare against stream_grf[start..start+count].
    fn check_seek(
        size: usize,
        arity: usize,
        allow_min: bool,
        opts: PruningOpts,
        start: usize,
        count: usize,
    ) {
        let full = collect(size, arity, allow_min, opts);
        let end = (start + count).min(full.len());
        let expected: Vec<Grf> = if start <= full.len() {
            full[start..end].to_vec()
        } else {
            vec![]
        };

        let mut got: Vec<Grf> = Vec::new();
        seek_stream_grf(size, arity, allow_min, opts, start, count, &mut |g| {
            got.push(g.clone())
        });

        assert_eq!(
            got, expected,
            "seek mismatch: size={size} arity={arity} allow_min={allow_min} \
             opts={opts:?} start={start} count={count}"
        );
    }

    #[test]
    fn test_seek_zero_count() {
        // count=0 should always produce nothing.
        for size in 1..=5 {
            for arity in 0..=2 {
                check_seek(size, arity, false, NO_PRUNE, 0, 0);
                check_seek(size, arity, false, NO_PRUNE, 5, 0);
            }
        }
    }

    #[test]
    fn test_seek_out_of_range() {
        // start beyond the total should produce nothing.
        for size in 1..=5 {
            for arity in 0..=2 {
                let total = count_grf(size, arity, false, NO_PRUNE);
                check_seek(size, arity, false, NO_PRUNE, total, 10);
                check_seek(size, arity, false, NO_PRUNE, total + 100, 10);
            }
        }
    }

    #[test]
    fn test_seek_full_range_no_prune() {
        // seek(start=0, count=total) should reproduce stream_grf exactly.
        for size in 1..=7 {
            for arity in 0..=2 {
                let total = count_grf(size, arity, false, NO_PRUNE);
                check_seek(size, arity, false, NO_PRUNE, 0, total);
            }
        }
    }

    #[test]
    fn test_seek_every_single_element() {
        // seek(start=i, count=1) should give the i-th GRF from stream.
        for size in 1..=6 {
            for arity in 0..=2 {
                let full = collect(size, arity, false, NO_PRUNE);
                for (i, expected) in full.iter().enumerate() {
                    let mut got: Vec<Grf> = Vec::new();
                    seek_stream_grf(size, arity, false, NO_PRUNE, i, 1, &mut |g| {
                        got.push(g.clone())
                    });
                    assert_eq!(
                        got.len(),
                        1,
                        "seek single: wrong count at size={size} arity={arity} i={i}"
                    );
                    assert_eq!(
                        got[0], *expected,
                        "seek single mismatch at size={size} arity={arity} i={i}"
                    );
                }
            }
        }
    }

    #[test]
    fn test_seek_sliding_window() {
        // All windows of width W should concatenate to the full list.
        const W: usize = 3;
        for size in 1..=6 {
            for arity in 0..=2 {
                let full = collect(size, arity, false, NO_PRUNE);
                for start in 0..full.len() {
                    check_seek(size, arity, false, NO_PRUNE, start, W);
                }
            }
        }
    }

    #[test]
    fn test_seek_all_pruning_opts() {
        // Check seek correctness for each pruning config.
        for size in 1..=6 {
            for arity in 0..=2 {
                for allow_min in [false, true] {
                    for opts in [
                        NO_PRUNE,
                        SKIP_COMP_ZERO,
                        SKIP_COMP_PROJ,
                        SKIP_COMP_TRIVIAL,
                        COMP_ASSOC,
                        SKIP_REC_ZERO_BASE,
                        SKIP_REC_ZERO,
                        ALL_OPTS,
                    ] {
                        let total = count_grf(size, arity, allow_min, opts);
                        // Full seek matches full stream.
                        check_seek(size, arity, allow_min, opts, 0, total);
                        // Middle window.
                        if total >= 2 {
                            check_seek(size, arity, allow_min, opts, 1, total - 1);
                        }
                        // Last element.
                        if total >= 1 {
                            check_seek(size, arity, allow_min, opts, total - 1, 1);
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn test_seek_allow_min() {
        // allow_min=true, full seek.
        for size in 1..=6 {
            for arity in 0..=2 {
                let total = count_grf(size, arity, true, NO_PRUNE);
                check_seek(size, arity, true, NO_PRUNE, 0, total);
                if total >= 1 {
                    check_seek(size, arity, true, NO_PRUNE, 0, 1);
                    check_seek(size, arity, true, NO_PRUNE, total - 1, 1);
                }
            }
        }
    }

    #[test]
    fn test_seek_window_covers_full() {
        // Concatenating all non-overlapping windows gives the full list.
        const W: usize = 4;
        for size in 3..=7 {
            for arity in 0..=2 {
                let full = collect(size, arity, false, ALL_OPTS);
                let mut reconstructed: Vec<Grf> = Vec::new();
                let mut start = 0;
                while start < full.len() {
                    let count = W.min(full.len() - start);
                    seek_stream_grf(size, arity, false, ALL_OPTS, start, count, &mut |g| {
                        reconstructed.push(g.clone())
                    });
                    start += count;
                }
                assert_eq!(
                    reconstructed, full,
                    "window reconstruction failed: size={size} arity={arity}"
                );
            }
        }
    }

    // --- count_grf matches actual stream count ---

    #[test]
    fn test_count_matches_stream() {
        for size in 1..=7 {
            for arity in 0..=3 {
                for allow_min in [false, true] {
                    for opts in [NO_PRUNE, SKIP_COMP_ZERO, SKIP_COMP_PROJ, SKIP_COMP_TRIVIAL,
                                 COMP_ASSOC, SKIP_REC_ZERO_BASE, SKIP_REC_ZERO, ALL_OPTS] {
                        let actual = collect(size, arity, allow_min, opts).len();
                        let count = count_grf(size, arity, allow_min, opts);
                        assert_eq!(
                            actual, count,
                            "count_grf mismatch: size={size} arity={arity} \
                             allow_min={allow_min} opts={opts:?}: \
                             actual={actual} count={count}"
                        );
                    }
                }
            }
        }
    }
}
