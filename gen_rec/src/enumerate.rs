use crate::grf::Grf;
use crate::optimize::{compute_inline_constraints, InlineConstraints};
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
                    return;
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
                // Compute constraints once per head; O(h.size()) upfront instead of
                // O(h.size()) per arg-tuple.
                let inline_c: Option<InlineConstraints> = if opts.skip_inline_proj {
                    Some(compute_inline_constraints(h))
                } else {
                    None
                };
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
                        // skip_inline_proj: C(h, g1..gm) where every gi is Proj or Zero
                        // is equivalent to inline_proj(h, k, rewiring), which is smaller.
                        // O(m) check using precomputed constraints.
                        if let Some(ref ic) = inline_c {
                            let rewiring: Option<Vec<usize>> = gs.iter().map(|g| match g {
                                Grf::Proj(_, i) => Some(*i),
                                Grf::Zero(_) => Some(0),
                                _ => None,
                            }).collect();
                            if let Some(rw) = rewiring {
                                if ic.allows(&rw, arity) {
                                    return;
                                }
                            }
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
            if opts.skip_min_trivial_zero {
                if matches!(f, Grf::Zero(_)) { return; }
                if matches!(f, Grf::Proj(_, _)) { return; }
            }
            if opts.skip_min_dominated {
                // (a) f ignores the search variable (arg 1 of f): M(f) is a restriction of Z_{arity}.
                if !f.used_args().contains(&1) { return; }
                // (b) f never returns 0: M(f) always diverges, dominated by Z_{arity}.
                if f.is_never_zero() { return; }
            }
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
///
/// Panics if `opts.skip_inline_proj` is set — seek relies on `count_grf` for
/// position arithmetic, which does not account for that flag.
pub fn seek_stream_grf<F: FnMut(&Grf)>(
    size: usize,
    arity: usize,
    allow_min: bool,
    opts: PruningOpts,
    start: usize,
    count: usize,
    callback: &mut F,
) {
    assert!(!opts.skip_inline_proj, "seek_stream_grf does not support skip_inline_proj");
    assert!(!opts.skip_min_dominated, "seek_stream_grf does not support skip_min_dominated");
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
                args_all.saturating_sub(count_many_fast(
                    gs_total - 1,
                    m - 1,
                    arity,
                    allow_min,
                    opts,
                ))
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

            // Split heads into three contiguous sections (in for_each_grf order):
            //   1. Pre-Rec: atoms + Comp forms (each yields args_all arg-tuples)
            //   2. Rec:     Rec forms          (each yields args_rec arg-tuples)
            //   3. Min:     Min forms           (each yields args_all arg-tuples)
            // Use integer division to jump to the right head within each section.
            let n_min_heads = if allow_min && hsize >= 2 {
                let inner_size = hsize - 1;
                let base = count_grf(inner_size, m + 1, allow_min, opts);
                if opts.skip_min_trivial_zero && inner_size == 1 {
                    base.saturating_sub(1 + (m + 1))
                } else {
                    base
                }
            } else { 0 };
            let n_pre_rec_heads = n_non_rec_heads.saturating_sub(n_min_heads);
            let pre_rec_block = n_pre_rec_heads.saturating_mul(args_all);
            let rec_block = n_rec_heads.saturating_mul(args_rec);

            // Section 1: pre-Rec heads (atoms + Comp forms).
            if *rem > 0 && *skip < pre_rec_block {
                let head_skip = *skip / args_all;
                *skip %= args_all;
                let max_heads = (*rem / args_all + 2).min(n_pre_rec_heads - head_skip);
                let mut local_skip = head_skip;
                let mut local_rem = max_heads;
                seek_pre_rec_heads(hsize, m, allow_min, opts, &mut local_skip, &mut local_rem,
                    &mut |h: &Grf| {
                        if *rem == 0 { return; }
                        let h_box = Box::new(h.clone());
                        let mut args = Vec::with_capacity(m);
                        seek_args(gs_total, m, arity, allow_min, opts, false,
                            skip, rem, &mut args,
                            &mut |gs: &[Grf]| {
                                callback(&Grf::Comp(h_box.clone(), gs.to_vec(), arity));
                            });
                    });
            } else if *skip >= pre_rec_block {
                *skip -= pre_rec_block;
            }

            // Section 2: Rec heads.
            if *rem > 0 && *skip < rec_block {
                let head_skip = *skip / args_rec;
                *skip %= args_rec;
                let max_heads = (*rem / args_rec + 2).min(n_rec_heads - head_skip);
                let mut local_skip = head_skip;
                let mut local_rem = max_heads;
                seek_rec_only(hsize, m, allow_min, opts, &mut local_skip, &mut local_rem,
                    &mut |h: &Grf| {
                        if *rem == 0 { return; }
                        let h_box = Box::new(h.clone());
                        let mut args = Vec::with_capacity(m);
                        seek_args(gs_total, m, arity, allow_min, opts,
                            opts.skip_rec_zero_arg,
                            skip, rem, &mut args,
                            &mut |gs: &[Grf]| {
                                callback(&Grf::Comp(h_box.clone(), gs.to_vec(), arity));
                            });
                    });
            } else if *skip >= rec_block {
                *skip -= rec_block;
            }

            // Section 3: Min heads (M(f) where f ∈ GRF_{m+1, hsize-1}, filtered by opts).
            if *rem > 0 && n_min_heads > 0 {
                let min_block = n_min_heads.saturating_mul(args_all);
                if *skip < min_block {
                    let head_skip = *skip / args_all;
                    *skip %= args_all;
                    let max_heads = (*rem / args_all + 2).min(n_min_heads - head_skip);
                    let mut local_skip = head_skip;
                    let mut local_rem = max_heads;
                    if opts.skip_min_trivial_zero && hsize == 2 {
                        // inner_size == 1: all Zero and Proj pruned; only Succ survives (when ar==1).
                        let ar = m + 1;
                        let valid_inners: Vec<Grf> =
                            if ar == 1 { vec![Grf::Succ] } else { vec![] };
                        for f in &valid_inners {
                            if *rem == 0 || local_rem == 0 { break; }
                            if local_skip > 0 { local_skip -= 1; continue; }
                            let h_box = Box::new(Grf::Min(Box::new(f.clone())));
                            let mut args = Vec::with_capacity(m);
                            seek_args(gs_total, m, arity, allow_min, opts, false,
                                skip, rem, &mut args,
                                &mut |gs: &[Grf]| {
                                    callback(&Grf::Comp(h_box.clone(), gs.to_vec(), arity));
                                });
                            local_rem -= 1;
                        }
                    } else {
                        seek_grfs(hsize - 1, m + 1, allow_min, opts,
                            &mut local_skip, &mut local_rem,
                            &mut |f: &Grf| {
                                if *rem == 0 { return; }
                                let h_box = Box::new(Grf::Min(Box::new(f.clone())));
                                let mut args = Vec::with_capacity(m);
                                seek_args(gs_total, m, arity, allow_min, opts, false,
                                    skip, rem, &mut args,
                                    &mut |gs: &[Grf]| {
                                        callback(&Grf::Comp(h_box.clone(), gs.to_vec(), arity));
                                    });
                            });
                    }
                } else {
                    *skip -= min_block;
                }
            }
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
            let pruned_in_block = if opts.skip_rec_zero_base && n == 2 {
                2usize
            } else {
                0
            };
            let gsize_block = g_total
                .saturating_mul(h_total)
                .saturating_sub(pruned_in_block);

            if *skip >= gsize_block {
                *skip -= gsize_block;
                continue;
            }

            if n == 2 {
                // n==2: at most ~4 g's (size-1 atoms) and h_count may vary per g
                // (skip_rec_zero_base prunes 2 h's when g is Zero).  Keep sequential.
                for_each_grf(gsize, arity - 1, allow_min, opts, &mut |g: &Grf| {
                    if *rem == 0 {
                        return;
                    }
                    let g_box = Box::new(g.clone());
                    let g_is_zero = matches!(g, Grf::Zero(_));
                    let pruned_h = if opts.skip_rec_zero_base && g_is_zero { 2usize } else { 0 };
                    let h_count = h_total.saturating_sub(pruned_h);
                    if *skip >= h_count {
                        *skip -= h_count;
                        return;
                    }
                    if pruned_h == 0 {
                        seek_grfs(hsize, arity + 1, allow_min, opts, skip, rem, &mut |h: &Grf| {
                            callback(&Grf::Rec(g_box.clone(), Box::new(h.clone())));
                        });
                    } else {
                        // n==2, g_is_zero, hsize==1.  Pruned: Zero(arity+1) and Proj(arity+1,2).
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
            } else {
                // n > 2: pruned_h == 0 for all g's, so h_count == h_total uniformly.
                // Jump to the g_skip_count-th g via division instead of O(g_count) iteration.
                let g_skip_count = *skip / h_total;
                *skip %= h_total;
                let max_needed = (*rem / h_total + 2).min(g_total - g_skip_count);
                let mut local_skip = g_skip_count;
                let mut local_rem = max_needed;
                seek_grfs(gsize, arity - 1, allow_min, opts, &mut local_skip, &mut local_rem, &mut |g: &Grf| {
                    if *rem == 0 {
                        return;
                    }
                    let g_box = Box::new(g.clone());
                    seek_grfs(hsize, arity + 1, allow_min, opts, skip, rem, &mut |h: &Grf| {
                        callback(&Grf::Rec(g_box.clone(), Box::new(h.clone())));
                    });
                });
            }
        }
    }

    // ---- Min section ----
    if allow_min && *rem > 0 {
        if opts.skip_min_trivial_zero && n == 1 {
            // At n==1, skip_min_trivial_zero prunes Zero(ar) and all Proj(ar,_).
            // Only Succ survives, and only when ar == 1.
            let ar = arity + 1;
            if ar == 1 && *rem > 0 {
                if *skip > 0 { *skip -= 1; }
                else { callback(&Grf::Min(Box::new(Grf::Succ))); *rem -= 1; }
            }
        } else {
            seek_grfs(n, arity + 1, allow_min, opts, skip, rem, &mut |f: &Grf| {
                callback(&Grf::Min(Box::new(f.clone())));
            });
        }
    }
}

/// Seek within valid Comp heads of (size, arity), emitting only atoms and Comp
/// forms — the "pre-Rec" heads that appear before Rec and Min in `for_each_grf`
/// order.  Head-pruning (skip_comp_zero, skip_comp_proj, comp_assoc) is applied.
///
/// Count = `count_as_head(size,arity) - count_rec_only(size,arity) - count_min_as_head(size,arity)`.
fn seek_pre_rec_heads(
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
    let n_min_heads = if allow_min && size >= 2 {
        let inner_size = size - 1;
        let base = count_grf(inner_size, arity + 1, allow_min, opts);
        if opts.skip_min_trivial_zero && inner_size == 1 { base.saturating_sub(1 + (arity + 1)) } else { base }
    } else { 0 };
    let total = count_as_head(size, arity, allow_min, opts)
        .saturating_sub(count_rec_only(size, arity, allow_min, opts))
        .saturating_sub(n_min_heads);
    if *skip >= total {
        *skip -= total;
        return;
    }

    if size == 1 {
        // Atoms with head-pruning.
        if !opts.skip_comp_zero {
            emit_atom(skip, rem, &Grf::Zero(arity), callback);
        }
        for i in 1..=arity {
            if *rem == 0 {
                return;
            }
            if !opts.skip_comp_proj {
                emit_atom(skip, rem, &Grf::Proj(arity, i), callback);
            }
        }
        if arity == 1 {
            emit_atom(skip, rem, &Grf::Succ, callback);
        }
        return;
    }

    // size >= 3: Comp forms only (no Rec, no Min), with comp_assoc pruning.
    // comp_assoc prunes single-arg Comps (m2 == 1) at the outer level.
    // For each (h2size, m2) block, compute the block count using count_as_head for
    // inner heads; skip (comp_assoc && m2==1) blocks entirely since they're excluded
    // from `total`.
    let n = size - 1;
    'comp: for h2size in 1..=n {
        let gs2_total = n - h2size;
        for m2 in 1..=gs2_total {
            if *rem == 0 {
                break 'comp;
            }
            // comp_assoc prunes outer single-arg Comps: Comp(h2, [g2], arity) when m2==1.
            if opts.comp_assoc && m2 == 1 {
                continue;
            }
            let args2_all = count_many_fast(gs2_total, m2, arity, allow_min, opts);
            let n2_heads = count_as_head(h2size, m2, allow_min, opts);
            if n2_heads == 0 || args2_all == 0 {
                continue;
            }
            let args2_rec = if opts.skip_rec_zero_arg && gs2_total >= 1 {
                args2_all.saturating_sub(count_many_fast(
                    gs2_total - 1, m2 - 1, arity, allow_min, opts,
                ))
            } else {
                args2_all
            };
            let n2_rec_heads = count_rec_only(h2size, m2, allow_min, opts);
            let n2_non_rec_heads = n2_heads.saturating_sub(n2_rec_heads);
            let block2 = n2_non_rec_heads
                .saturating_mul(args2_all)
                .saturating_add(n2_rec_heads.saturating_mul(args2_rec));
            if *skip >= block2 {
                *skip -= block2;
                continue;
            }
            // Inside this block: walk inner heads one by one with per-head arg-group skipping.
            // (Inner head counts are bounded by count_as_head(h2size, m2), typically small
            // relative to the outer head counts we optimised above.)
            for_each_grf(h2size, m2, allow_min, opts, &mut |h2: &Grf| {
                if *rem == 0 { return; }
                if opts.skip_comp_zero && matches!(h2, Grf::Zero(_)) { return; }
                if opts.skip_comp_proj && matches!(h2, Grf::Proj(_, _)) { return; }
                if opts.comp_assoc {
                    if let Grf::Comp(_, inner_gs, _) = h2 {
                        if inner_gs.len() == 1 { return; }
                    }
                }
                let h2_is_rec = matches!(h2, Grf::Rec(_, _));
                let per_h2_args = if h2_is_rec { args2_rec } else { args2_all };
                if *skip >= per_h2_args { *skip -= per_h2_args; return; }
                let h2_box = Box::new(h2.clone());
                let mut args2 = Vec::with_capacity(m2);
                seek_args(
                    gs2_total, m2, arity, allow_min, opts,
                    h2_is_rec && opts.skip_rec_zero_arg,
                    skip, rem, &mut args2,
                    &mut |gs2: &[Grf]| {
                        callback(&Grf::Comp(h2_box.clone(), gs2.to_vec(), arity));
                    },
                );
            });
        }
    }
}

/// Seek within only the `R(g, h)` (Rec) forms of exactly (size, arity),
/// in the same order as `for_each_grf`.  Handles `skip_rec_zero_base` at size==3.
fn seek_rec_only(
    size: usize,
    arity: usize,
    allow_min: bool,
    opts: PruningOpts,
    skip: &mut usize,
    rem: &mut usize,
    callback: &mut dyn FnMut(&Grf),
) {
    if *rem == 0 || arity == 0 || size < 3 {
        return;
    }
    let total = count_rec_only(size, arity, allow_min, opts);
    if *skip >= total {
        *skip -= total;
        return;
    }
    let n = size - 1;
    for gsize in 1..n {
        if *rem == 0 {
            break;
        }
        let hsize = n - gsize;
        let g_total = count_grf(gsize, arity - 1, allow_min, opts);
        let h_total = count_grf(hsize, arity + 1, allow_min, opts);
        let pruned_in_block = if opts.skip_rec_zero_base && n == 2 { 2usize } else { 0 };
        let block = g_total.saturating_mul(h_total).saturating_sub(pruned_in_block);
        if *skip >= block {
            *skip -= block;
            continue;
        }
        if n == 2 {
            // Sequential — same as the n==2 branch in the Rec section of seek_grfs.
            for_each_grf(gsize, arity - 1, allow_min, opts, &mut |g: &Grf| {
                if *rem == 0 { return; }
                let g_box = Box::new(g.clone());
                let g_is_zero = matches!(g, Grf::Zero(_));
                let pruned_h = if opts.skip_rec_zero_base && g_is_zero { 2usize } else { 0 };
                let h_count = h_total.saturating_sub(pruned_h);
                if *skip >= h_count { *skip -= h_count; return; }
                if pruned_h == 0 {
                    seek_grfs(hsize, arity + 1, allow_min, opts, skip, rem, &mut |h: &Grf| {
                        callback(&Grf::Rec(g_box.clone(), Box::new(h.clone())));
                    });
                } else {
                    let ar1 = arity + 1;
                    let valid_hs: Vec<Grf> = std::iter::once(Grf::Proj(ar1, 1))
                        .chain((3..=ar1).map(|i| Grf::Proj(ar1, i)))
                        .collect();
                    for h in &valid_hs {
                        if *rem == 0 { return; }
                        if *skip > 0 { *skip -= 1; continue; }
                        callback(&Grf::Rec(g_box.clone(), Box::new(h.clone())));
                        *rem -= 1;
                    }
                }
            });
        } else {
            // Division trick — same as n>2 branch in seek_grfs.
            let g_skip_count = *skip / h_total;
            *skip %= h_total;
            let max_needed = (*rem / h_total + 2).min(g_total - g_skip_count);
            let mut local_skip = g_skip_count;
            let mut local_rem = max_needed;
            seek_grfs(gsize, arity - 1, allow_min, opts, &mut local_skip, &mut local_rem,
                &mut |g: &Grf| {
                    if *rem == 0 { return; }
                    let g_box = Box::new(g.clone());
                    seek_grfs(hsize, arity + 1, allow_min, opts, skip, rem, &mut |h: &Grf| {
                        callback(&Grf::Rec(g_box.clone(), Box::new(h.clone())));
                    });
                });
        }
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

        let rest_count = count_many_fast(
            remaining_size - x,
            remaining_count - 1,
            arity,
            allow_min,
            opts,
        );
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
            let mut non_zero_atoms: Vec<Grf> = (1..=arity).map(|i| Grf::Proj(arity, i)).collect();
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
            // Jump to the g_skip_count-th GRF via division instead of O(g_count) iteration.
            // After the first g (which may emit fewer than rest_count tuples due to *skip),
            // each subsequent g contributes exactly rest_count tuples, so we need at most
            // ceil(*rem / rest_count) + 1 g's total.
            let g_skip_count = *skip / rest_count;
            *skip %= rest_count;
            let max_needed = (*rem / rest_count + 2).min(g_valid_count - g_skip_count);
            let mut local_skip = g_skip_count;
            let mut local_rem = max_needed;
            seek_grfs(x, arity, allow_min, opts, &mut local_skip, &mut local_rem, &mut |g: &Grf| {
                if *rem == 0 {
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
///
/// Panics if `opts.skip_inline_proj` is set — that flag is not accounted for
/// in the DP and would produce incorrect counts.
pub fn count_grf(size: usize, arity: usize, allow_min: bool, opts: PruningOpts) -> usize {
    assert!(!opts.skip_inline_proj, "count_grf does not support skip_inline_proj");
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
            count += 1; // S is always a legal head
        }
        if !opts.skip_comp_zero {
            count += 1; // Z only valid if not skipping C(Z, ...)
        }
        if !opts.skip_comp_proj {
            count += arity; // P_i only valid if not skipping C(P, ...)
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
                count_grf(gsize, arity - 1, allow_min, opts).saturating_mul(count_grf(
                    n - gsize,
                    arity + 1,
                    allow_min,
                    opts,
                )),
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
        let inner = count_grf(n, arity + 1, allow_min, opts);
        // skip_min_trivial_zero: at n==1, prune Zero(arity+1) and all Proj(arity+1,_).
        // That's 1 + (arity+1) forms. Inner count at n==1 = 1 + (arity+1) + [arity+1==1],
        // so remaining is [arity+1==1] (just Succ when inner arity is 1). No underflow.
        let pruned = if opts.skip_min_trivial_zero && n == 1 { 1 + (arity + 1) } else { 0 };
        total = total.saturating_add(inner.saturating_sub(pruned));
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
            count_grf(gsize, arity - 1, allow_min, opts).saturating_mul(count_grf(
                n - gsize,
                arity + 1,
                allow_min,
                opts,
            )),
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
        total = total.saturating_add(count_grf(x, arity, allow_min, opts).saturating_mul(
            count_many_fast(total_size - x, num_funcs - 1, arity, allow_min, opts),
        ));
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
    const SKIP_INLINE_PROJ: PruningOpts = PruningOpts {
        skip_inline_proj: true,
        ..NO_PRUNE
    };
    const SKIP_MIN_TRIVIAL: PruningOpts = PruningOpts {
        skip_min_trivial_zero: true,
        ..NO_PRUNE
    };
    const SKIP_MIN_DOMINATED: PruningOpts = PruningOpts {
        skip_min_trivial_zero: true,
        skip_min_dominated: true,
        ..NO_PRUNE
    };

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
                let all = count_grf(size, arity, false, PruningOpts::default());
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

    // --- skip_inline_proj ---

    #[test]
    fn test_skip_inline_proj_removes_specific_forms() {
        // C(R(Z1, P(3,3)), P(4,1), P(4,4)) — all args are Proj, inlineable → R(Z3, P(5,5)).
        let pruned = collect(6, 4, false, SKIP_INLINE_PROJ);
        let target = "C(R(Z1,P(3,3)),P(4,1),P(4,4))".parse::<Grf>().unwrap();
        assert!(
            !pruned.iter().any(|g| *g == target),
            "C(R(Z1,P(3,3)),P(4,1),P(4,4)) should be pruned"
        );

        // C(S, P(1,1)) — arity-1, single Proj arg, inlines to S.  Should be pruned.
        let pruned3 = collect(3, 1, false, SKIP_INLINE_PROJ);
        let target3 = "C(S,P(1,1))".parse::<Grf>().unwrap();
        assert!(
            !pruned3.iter().any(|g| *g == target3),
            "C(S,P(1,1)) should be pruned (inlines to S)"
        );

        // C(S, Z1) — inline_proj(S, 1, [0]) fails (S requires rewiring [1]).
        // This computes \x.1, not zero; correctly NOT pruned.
        let target_z = "C(S,Z1)".parse::<Grf>().unwrap();
        assert!(
            pruned3.iter().any(|g| *g == target_z),
            "C(S,Z1) should NOT be pruned (Succ can't be rewired with a zero slot)"
        );

        // C(S, P(2,1)) — arity-2, but S has arity 1 so new_arity would be 2 ≠ 1.
        // inline_proj(S, 2, [1]) returns None → NOT pruned.
        let pruned3_ar2 = collect(3, 2, false, SKIP_INLINE_PROJ);
        let target_ar2 = "C(S,P(2,1))".parse::<Grf>().unwrap();
        assert!(
            pruned3_ar2.iter().any(|g| *g == target_ar2),
            "C(S,P(2,1)) should NOT be pruned (Succ can't be rewired to arity 2)"
        );

        // C(R(Z1,P(3,3)), C(S,P(4,1)), P(4,4)) — first arg is not P/Z, NOT pruned.
        let full = collect(8, 4, false, NO_PRUNE);
        let not_pruned = "C(R(Z1,P(3,3)),C(S,P(4,1)),P(4,4))".parse::<Grf>().unwrap();
        assert!(
            full.iter().any(|g| *g == not_pruned),
            "C(R(Z1,P(3,3)),C(S,P(4,1)),P(4,4)) must exist without pruning"
        );
        let pruned8 = collect(8, 4, false, SKIP_INLINE_PROJ);
        assert!(
            pruned8.iter().any(|g| *g == not_pruned),
            "C(R(Z1,P(3,3)),C(S,P(4,1)),P(4,4)) should NOT be pruned (non-P/Z arg)"
        );
    }

    #[test]
    fn test_skip_inline_proj_never_more_than_full() {
        for size in 1..=8 {
            for arity in 0..=2 {
                let full = collect(size, arity, false, NO_PRUNE).len();
                let pruned = collect(size, arity, false, SKIP_INLINE_PROJ).len();
                assert!(
                    pruned <= full,
                    "skip_inline_proj produced more GRFs at size={size} arity={arity}"
                );
            }
        }
    }

    #[test]
    #[should_panic(expected = "count_grf does not support skip_inline_proj")]
    fn count_grf_panics_on_skip_inline_proj() {
        count_grf(5, 1, false, PruningOpts::all());
    }

    #[test]
    #[should_panic(expected = "seek_stream_grf does not support skip_inline_proj")]
    fn seek_stream_grf_panics_on_skip_inline_proj() {
        seek_stream_grf(5, 1, false, PruningOpts::all(), 0, 1, &mut |_| {});
    }

    // --- skip_min_trivial_zero ---

    #[test]
    fn test_skip_min_trivial_zero_removes_specific_forms() {
        // M(Z1) and M(P(1,1)) — size 2, arity 0 — should be pruned.
        let full = collect(2, 0, true, NO_PRUNE);
        let pruned = collect(2, 0, true, SKIP_MIN_TRIVIAL);
        let m_zero = "M(Z1)".parse::<Grf>().unwrap();
        let m_proj1 = "M(P(1,1))".parse::<Grf>().unwrap();
        let m_succ = "M(S)".parse::<Grf>().unwrap();
        assert!(full.iter().any(|g| *g == m_zero), "M(Z1) must appear without pruning");
        assert!(full.iter().any(|g| *g == m_proj1), "M(P(1,1)) must appear without pruning");
        assert!(!pruned.iter().any(|g| *g == m_zero), "M(Z1) should be pruned by skip_min_trivial_zero");
        assert!(!pruned.iter().any(|g| *g == m_proj1), "M(P(1,1)) should be pruned by skip_min_trivial_zero");
        // M(S) = M(Succ) at arity 0: Succ is not Zero or Proj, so it survives.
        assert!(pruned.iter().any(|g| *g == m_succ), "M(S) should NOT be pruned by skip_min_trivial_zero");
    }

    #[test]
    fn test_skip_min_trivial_zero_arity1() {
        // M(Z2), M(P(2,1)), M(P(2,2)) — size 2, arity 1 — all pruned (Zero and all Proj).
        // No size-2 Min survives at arity 1 since inner arity is 2 and Succ has arity 1 ≠ 2.
        let pruned = collect(2, 1, true, SKIP_MIN_TRIVIAL);
        let m_zero2 = "M(Z2)".parse::<Grf>().unwrap();
        let m_proj21 = "M(P(2,1))".parse::<Grf>().unwrap();
        let m_proj22 = "M(P(2,2))".parse::<Grf>().unwrap();
        assert!(!pruned.iter().any(|g| *g == m_zero2), "M(Z2) should be pruned");
        assert!(!pruned.iter().any(|g| *g == m_proj21), "M(P(2,1)) should be pruned");
        assert!(!pruned.iter().any(|g| *g == m_proj22), "M(P(2,2)) should be pruned (all Proj pruned)");
        assert!(pruned.iter().all(|g| !matches!(g, Grf::Min(_))), "no size-2 Min survives at arity 1");
    }

    #[test]
    fn test_skip_min_dominated_removes_all_size2_min() {
        // With both flags, NO M(atom) survives for any arity — smallest novel Min has size ≥ 4.
        for arity in 0..=2 {
            let pruned = collect(2, arity, true, SKIP_MIN_DOMINATED);
            assert!(
                pruned.iter().all(|g| !matches!(g, Grf::Min(_))),
                "all size-2 Min expressions should be pruned at arity={arity}, got: {:?}",
                pruned.iter().filter(|g| matches!(g, Grf::Min(_))).collect::<Vec<_>>()
            );
        }
    }

    #[test]
    fn test_skip_min_trivial_count_matches_stream() {
        // count_grf must agree with stream_grf count under skip_min_trivial_zero.
        for size in 1..=8 {
            for arity in 0..=2 {
                let stream_count = collect(size, arity, true, SKIP_MIN_TRIVIAL).len();
                let count = count_grf(size, arity, true, SKIP_MIN_TRIVIAL);
                assert_eq!(
                    count, stream_count,
                    "count/stream mismatch at size={size} arity={arity} skip_min_trivial_zero"
                );
            }
        }
    }

    #[test]
    fn test_skip_min_trivial_never_more_than_full() {
        for size in 1..=8 {
            for arity in 0..=2 {
                let full = collect(size, arity, true, NO_PRUNE).len();
                let pruned = collect(size, arity, true, SKIP_MIN_TRIVIAL).len();
                assert!(pruned <= full, "skip_min_trivial_zero produced more at size={size} arity={arity}");
            }
        }
    }

    #[test]
    #[should_panic(expected = "seek_stream_grf does not support skip_min_dominated")]
    fn seek_stream_grf_panics_on_skip_min_dominated() {
        seek_stream_grf(5, 1, true, SKIP_MIN_DOMINATED, 0, 1, &mut |_| {});
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
                        SKIP_MIN_TRIVIAL,
                        PruningOpts::default(),
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
                let full = collect(size, arity, false, PruningOpts::default());
                let mut reconstructed: Vec<Grf> = Vec::new();
                let mut start = 0;
                while start < full.len() {
                    let count = W.min(full.len() - start);
                    seek_stream_grf(size, arity, false, PruningOpts::default(), start, count, &mut |g| {
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
                    for opts in [
                        NO_PRUNE,
                        SKIP_COMP_ZERO,
                        SKIP_COMP_PROJ,
                        SKIP_COMP_TRIVIAL,
                        COMP_ASSOC,
                        SKIP_REC_ZERO_BASE,
                        SKIP_REC_ZERO,
                        PruningOpts::default(),
                    ] {
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

    // Verify seek correctness at larger sizes where the old O(g_count) iteration would hang.
    #[test]
    fn test_seek_mid_sizes_arity0() {
        // Reference check (collect) for sizes where the full stream is feasible.
        for size in 8..=12 {
            let total = count_grf(size, 0, false, PruningOpts::default());
            if total == 0 {
                continue;
            }
            for frac in [4usize, 3, 2] {
                let start = (total / frac).saturating_sub(1);
                check_seek(size, 0, false, PruningOpts::default(), start, 5);
            }
            check_seek(size, 0, false, PruningOpts::default(), total.saturating_sub(3), 5);
        }
    }

    // Large sizes: self-consistency only (count=10 window vs 10 individual count=1 seeks).
    #[test]
    fn test_seek_large_sizes_arity0() {
        // Self-consistency check for larger sizes: a count=10 window must agree with
        // ten individual count=1 seeks at the same ranks.
        for size in 13..=18 {
            let total = count_grf(size, 0, false, PruningOpts::default());
            if total == 0 {
                continue;
            }
            let start = total / 4;
            let mut batch: Vec<Grf> = Vec::new();
            seek_stream_grf(size, 0, false, PruningOpts::default(), start, 10, &mut |g| {
                batch.push(g.clone());
            });
            assert_eq!(batch.len(), 10);
            for (i, grf) in batch.iter().enumerate() {
                let mut single: Vec<Grf> = Vec::new();
                seek_stream_grf(size, 0, false, PruningOpts::default(), start + i, 1, &mut |g| {
                    single.push(g.clone());
                });
                assert_eq!(single.len(), 1);
                assert_eq!(
                    &single[0], grf,
                    "self-consistency failure: size={size} rank={}",
                    start + i
                );
            }
        }
    }

    // Verify that seek at the exact position that previously caused a hang returns correct GRFs
    // in negligible time.  The count at size=19 is ~56.8B; rank 16.3B is well into the stream.
    // We can't run collect(19, …) as a reference (too slow), so instead verify the 10-element
    // window is self-consistent: same GRFs as a seek with count=1 at each individual rank.
    #[test]
    fn test_seek_large_rank_arity0() {
        let size = 19;
        let start: usize = 16_300_000_000;
        let count = 10;
        let opts = PruningOpts::default();

        let mut batch: Vec<Grf> = Vec::new();
        seek_stream_grf(size, 0, false, opts, start, count, &mut |g| {
            batch.push(g.clone());
        });
        assert_eq!(batch.len(), count, "expected {count} GRFs from seek at rank {start}");

        // Each GRF must also be produced by a count=1 seek at its individual rank.
        for (i, grf) in batch.iter().enumerate() {
            let mut single: Vec<Grf> = Vec::new();
            seek_stream_grf(size, 0, false, opts, start + i, 1, &mut |g| {
                single.push(g.clone());
            });
            assert_eq!(single.len(), 1);
            assert_eq!(
                &single[0], grf,
                "seek rank {} disagrees with window element {}",
                start + i,
                i
            );
        }
    }
}
