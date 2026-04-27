/// Options controlling which GRFs are pruned during enumeration.
///
/// Each flag removes a provably redundant subset of expressions: for every
/// GRF that is skipped, an equivalent (or simpler) GRF is still generated.
///
/// Flags are independent and can be combined freely.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct PruningOpts {
    /// Skip `C(Z_m, …) = Z`
    pub skip_comp_zero: bool,

    /// Skip `C(P^m_i, g0, ... gm) = gi`
    pub skip_comp_proj: bool,

    /// Canonicalise composition via associativity.
    ///
    /// The identity `C(C(f, g), k) = C(f, C(g, k))` means every expression
    /// with a single-argument Comp as its head has an equivalent form with a
    /// "flatter" head.  We always prefer the right-associated form, so
    /// `C(h, …)` is skipped whenever `h` is itself a single-argument Comp.
    ///
    /// Synergises with `skip_trivial`: in the canonical form `C(f, C(g, k))`,
    /// if `g` is `Z` or `P` then `C(g, k)` is already pruned by
    /// `skip_trivial`, so the whole expression disappears for free.
    pub comp_assoc: bool,

    /// Skip `R(Z(k), h)` when `h` is `Z(k+2)` or `P(k+2, 2)`.
    ///
    /// Both cases produce a function that is always 0 = `Z(k+1)`:
    /// - `h = Z(k+2)`: step always returns 0, base is 0.
    /// - `h = P(k+2, 2)`: step returns the accumulator; accumulator starts at 0
    ///   (from the Z base) and is returned unchanged every step, so stays 0.
    ///
    /// The equivalent `Z(k+1)` has size 1 vs 3 for `R(Z, h)`.
    pub skip_rec_zero_base: bool,

    /// Skip `C(R(g, h), Z(p), f2, …)`.
    ///
    /// When the first argument to a Rec is structurally `Zero`, the recursion
    /// counter is always 0, so only the base case fires:
    ///   `C(R(g, h), Z(p), f2, …)(x) = R(g,h)(0, f2(x), …) = g(f2(x), …)`
    ///               = `C(g, f2, …)(x)`
    /// The equivalent `C(g, f2, …)` is strictly smaller (by `h.size() + 1`)
    /// and will be generated independently by the enumerator.
    pub skip_rec_zero_arg: bool,

    /// Skip `C(h, g1…gm)` when every `gi` is `Proj` or `Zero` and
    /// `inline_proj(h, k, rewiring)` succeeds.
    ///
    /// Such a composition is always equivalent to the inlined result, which
    /// is strictly smaller (size `h.size()` vs `h.size() + m + 1`).
    ///
    /// Only supported in `stream_grf` / `for_each_grf`. `count_grf` and
    /// `seek_stream_grf` do not account for this flag; do not use it with
    /// those functions.
    pub skip_inline_proj: bool,
}

impl PruningOpts {
    pub const fn default() -> PruningOpts {
        PruningOpts {
            skip_comp_zero: true,
            skip_comp_proj: true,
            comp_assoc: true,
            skip_rec_zero_base: true,
            skip_rec_zero_arg: true,
            // Not included: skip_inline_proj is stream_grf-only and not
            // supported by count_grf / seek_stream_grf.
            skip_inline_proj: false,
        }
    }

    pub const fn none() -> PruningOpts {
        PruningOpts {
            skip_comp_zero: false,
            skip_comp_proj: false,
            comp_assoc: false,
            skip_rec_zero_base: false,
            skip_rec_zero_arg: false,
            skip_inline_proj: false,
        }
    }
    pub const fn all() -> PruningOpts {
        PruningOpts {
            skip_comp_zero: true,
            skip_comp_proj: true,
            comp_assoc: true,
            skip_rec_zero_base: true,
            skip_rec_zero_arg: true,
            skip_inline_proj: true,
        }
    }
}
