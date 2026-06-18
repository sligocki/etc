// ---------------------------------------------------------------------------
// Pruning option metadata
// ---------------------------------------------------------------------------

/// Metadata for a single pruning flag, used for CLI parsing, config output,
/// and building enumeration chains in tools like `count`.
pub struct FlagMeta {
    /// Short name used in CLI flags and config output (e.g. `"comp_rnf"`).
    pub name: &'static str,
    /// Human-readable description for legend output.
    pub desc: &'static str,
    /// `true` iff the flag is compatible with `count_grf` and `seek_stream_grf`.
    pub count_compat: bool,
    /// `true` iff the flag is on in `PruningOpts::recommended()`.
    pub recommended: bool,
    /// `true` iff the flag is only meaningful when `allow_min = true`.
    pub min_only: bool,
    /// Read the flag value from a `PruningOpts`.
    pub get: fn(&PruningOpts) -> bool,
    /// Write the flag value into a `PruningOpts`.
    pub set: fn(&mut PruningOpts, bool),
}

// ---------------------------------------------------------------------------
// Code-gen macro
// ---------------------------------------------------------------------------

macro_rules! define_pruning_flags {
    (
        $( { $field:ident, $name:literal, cc=$cc:ident, rec=$rec:ident, mo=$mo:ident, $desc:literal } ),*
        $(,)?
    ) => {
        /// Options controlling which GRFs are pruned during enumeration.
        ///
        /// All flags are independent and can be combined freely.  See [`FLAGS`]
        /// for per-flag documentation and compatibility information.
        ///
        /// Typical usage: start from [`PruningOpts::recommended`] (the standard
        /// preset) and optionally enable additional stream-only flags via
        /// [`PruningOpts::with_stream_opts`].
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
        pub struct PruningOpts {
            $( pub $field: bool, )*
        }

        /// All flags off.
        impl Default for PruningOpts {
            fn default() -> Self {
                PruningOpts { $( $field: false, )* }
            }
        }

        impl PruningOpts {
            /// All recommended (default-on) flags enabled; stream-only flags off.
            /// Use this as the starting point for most enumerations.
            pub fn recommended() -> Self {
                PruningOpts { $( $field: define_pruning_flags!(@b $rec), )* }
            }

            /// All flags on.
            pub fn all() -> Self {
                PruningOpts { $( $field: true, )* }
            }

            /// Return a copy with all stream-only flags cleared, safe to pass
            /// to `count_grf` / `seek_stream_grf`.
            pub fn for_counting(mut self) -> Self {
                for meta in FLAGS {
                    if !meta.count_compat {
                        (meta.set)(&mut self, false);
                    }
                }
                self
            }

            /// Panic if any flag that is incompatible with `count_grf` /
            /// `seek_stream_grf` is set.
            pub fn assert_count_compat(&self) {
                for meta in FLAGS {
                    if !meta.count_compat && (meta.get)(self) {
                        panic!(
                            "count_grf/seek_stream_grf does not support '{}'",
                            meta.name
                        );
                    }
                }
            }

            /// Return the names of active stream-only flags.
            pub fn stream_opt_names(&self) -> Vec<&'static str> {
                FLAGS.iter()
                    .filter(|m| !m.count_compat && (m.get)(self))
                    .map(|m| m.name)
                    .collect()
            }

            /// Enable any flags by name on top of `self`.  Panics on unknown names.
            /// Use in tests and internal code; for CLI use [`with_stream_opts`].
            pub fn with_flags(mut self, names: &str) -> Self {
                for name in names.split(',').map(str::trim).filter(|s| !s.is_empty()) {
                    let meta = FLAGS.iter().find(|m| m.name == name)
                        .unwrap_or_else(|| panic!("unknown pruning flag '{}'", name));
                    (meta.set)(&mut self, true);
                }
                self
            }

            /// Apply `+flag` / `-flag` adjustments from a comma-separated spec.
            ///
            /// Each token is `+name` (enable), `-name` (disable), or bare `name` (enable).
            /// Returns an error string if any name is unknown.
            pub fn apply_flag_adjustments(mut self, spec: &str) -> Result<Self, String> {
                for token in spec.split(',').map(str::trim).filter(|s| !s.is_empty()) {
                    let (name, value) = if let Some(s) = token.strip_prefix('+') {
                        (s, true)
                    } else if let Some(s) = token.strip_prefix('-') {
                        (s, false)
                    } else {
                        (token, true)
                    };
                    let meta = FLAGS.iter().find(|m| m.name == name).ok_or_else(|| {
                        let known: Vec<_> = FLAGS.iter().map(|m| m.name).collect();
                        format!("unknown flag '{}'; known: {}", name, known.join(", "))
                    })?;
                    (meta.set)(&mut self, value);
                }
                Ok(self)
            }

            /// Enable stream-only flags by name on top of `self`.
            ///
            /// `names` is a comma-separated list of flag names,
            /// e.g. `"inline_proj,comp_rnf"`.  Returns an error string if any
            /// name is unknown or refers to an always-on flag.
            pub fn with_stream_opts(mut self, names: &str) -> Result<Self, String> {
                for name in names.split(',').map(str::trim).filter(|s| !s.is_empty()) {
                    let meta = FLAGS.iter().find(|m| m.name == name).ok_or_else(|| {
                        let known: Vec<_> = FLAGS.iter()
                            .filter(|m| !m.count_compat)
                            .map(|m| m.name)
                            .collect();
                        format!(
                            "unknown stream opt '{}'; known: {}",
                            name,
                            known.join(", ")
                        )
                    })?;
                    if meta.count_compat {
                        return Err(format!(
                            "'{}' is always-on by default, not a stream opt",
                            name
                        ));
                    }
                    (meta.set)(&mut self, true);
                }
                Ok(self)
            }
        }

        /// All pruning flags in canonical chain order (count-compat first, then
        /// stream-only).  Iterate this to build enumeration tables, CLI help,
        /// config output, or compat checks without touching individual binaries.
        pub static FLAGS: &[FlagMeta] = &[
            $(
                FlagMeta {
                    name:         $name,
                    desc:         $desc,
                    count_compat: define_pruning_flags!(@b $cc),
                    recommended:  define_pruning_flags!(@b $rec),
                    min_only:     define_pruning_flags!(@b $mo),
                    get: |o: &PruningOpts| o.$field,
                    set: |o: &mut PruningOpts, v: bool| { o.$field = v; },
                },
            )*
        ];
    };
    (@b yes) => { true  };
    (@b no)  => { false };
}

// ---------------------------------------------------------------------------
// Flag declarations — one line per flag, in canonical chain order
// ---------------------------------------------------------------------------
//
// Ordering note: the `count` binary builds its cumulative config table by
// partitioning flags into cc=yes first, then cc=no — so inter-group ordering
// doesn't cause panics.  Within each group, the order here determines how
// flags are applied cumulatively (and thus which column shows their marginal
// benefit), so keep related rules together.

define_pruning_flags! {
    { comp_proj,     "comp_proj",     cc=yes, rec=yes, mo=no,  "C(P,…) → one of its args" },
    { comp_zero,     "comp_zero",     cc=yes, rec=yes, mo=no,  "C(Z,…) → Z" },
    { rec_zero_arg,  "rec_zero_arg",  cc=yes, rec=yes, mo=no,  "C(R(g,h),Z,…) → C(g,…)" },
    { rec_pos_step,  "rec_pos_step",  cc=no,  rec=yes, mo=no,  "C(R(a,b), c, …) → prune if c>0 and b ignores arg2" },
    { rec_proj_base, "rec_proj_base", cc=yes, rec=yes, mo=no,  "R(P_i,P2) / R(P_i,P_{i+2}) → P_{i+1}" },
    { comp_assoc,    "comp_assoc",    cc=yes, rec=yes, mo=no,  "C(C(f,g),h1…) → C(f,C(g,h1…))" },
    { comp_null_null,"comp_null_null",cc=yes, rec=yes, mo=no,  "C0(h) → h" },
    // TODO: I'm not 100% sure it is safe to skip C(h) ... and it is only like a 1.2% savings.
    { comp_null,     "comp_null",     cc=yes, rec=no,  mo=no,  "Ck(h) → h^k  (not 100% safe)" },
    { rec_zero_base, "rec_zero_base", cc=yes, rec=yes, mo=no,  "R(Z,Z) / R(Z,P2) → Z" },
    { min_trivial,   "min_trivial",   cc=yes, rec=yes, mo=yes, "M(Z) / M(P) → Z" },
    { min_dom,       "min_dom",       cc=no,  rec=yes, mo=yes, "M(f) dominated by Z_{k-1}" },
    { inline_proj,   "inline_proj",   cc=no,  rec=yes, mo=no,  "C(h,P/Z…) → inlined h" },
    { comp_rnf,      "comp_rnf",      cc=no,  rec=yes, mo=no,  "C(h,…) require h in Rewire Normal Form (all args used, canonical order)" },
    { rec_step_p2,   "rec_step_p2",   cc=no,  rec=yes, mo=no,  "C(R(g,P2),h1,…) → C(g,h2,…)" },
}

// ---------------------------------------------------------------------------
// Pruning Rules Engine
// ---------------------------------------------------------------------------

use crate::grf::{Grf, GrfKind};
use crate::optimize::InlineConstraints;

pub struct Pruner {
    pub opts: PruningOpts,
}

impl Pruner {
    pub fn new(opts: PruningOpts) -> Self {
        Self { opts }
    }

    pub fn should_prune_comp_head(&self, h: &Grf, m: usize) -> bool {
        if self.opts.comp_zero && matches!(&h.kind, GrfKind::Zero(_)) {
            return true;
        }
        if self.opts.comp_proj && matches!(&h.kind, GrfKind::Proj(_, _)) {
            return true;
        }
        if self.opts.comp_assoc {
            if let GrfKind::Comp(_, inner_gs, _) = &h.kind {
                if inner_gs.len() == 1 {
                    return true;
                }
            }
        }
        if self.opts.comp_rnf {
            if h.used_args().len() < m {
                return true;
            }
            let order = h.canonical_arg_order();
            if order.iter().enumerate().any(|(i, &a)| a != i + 1) {
                return true;
            }
        }
        if self.opts.rec_step_p2 {
            if let GrfKind::Rec(_, step) = &h.kind {
                if matches!(&step.kind, GrfKind::Proj(_, 2)) {
                    return true;
                }
            }
        }
        false
    }

    pub fn should_prune_comp_args(
        &self,
        h: &Grf,
        gs: &[Grf],
        arity: usize,
        inline_c: Option<&InlineConstraints>,
    ) -> bool {
        let h_is_rec = matches!(&h.kind, GrfKind::Rec(_, _));
        if self.opts.rec_zero_arg
            && h_is_rec
            && gs.first().map_or(false, |g| matches!(&g.kind, GrfKind::Zero(_)))
        {
            return true;
        }
        if self.opts.rec_pos_step && h_is_rec {
            if let GrfKind::Rec(a, b) = &h.kind {
                if !b.used_args().contains(&2) && gs.first().map_or(false, |g| g.is_never_zero()) {
                    let a_is_zero = matches!(&a.kind, GrfKind::Zero(_));
                    let b_uses_arg1 = b.used_args().contains(&1);
                    if !b_uses_arg1 || !a_is_zero {
                        return true;
                    }
                }
            }
        }
        if let Some(ic) = inline_c {
            let rewiring: Option<Vec<usize>> = gs
                .iter()
                .map(|g| match &g.kind {
                    GrfKind::Proj(_, i) => Some(*i),
                    GrfKind::Zero(_) => Some(0),
                    _ => None,
                })
                .collect();
            if let Some(rw) = rewiring {
                if ic.allows(&rw, arity) {
                    return true;
                }
            }
        }
        false
    }

    pub fn should_prune_rec(&self, g: &Grf, h: &Grf) -> bool {
        let g_is_zero = matches!(&g.kind, GrfKind::Zero(_));
        if self.opts.rec_zero_base
            && g_is_zero
            && matches!(&h.kind, GrfKind::Zero(_) | GrfKind::Proj(_, 2))
        {
            return true;
        }
        if self.opts.rec_proj_base {
            if let (GrfKind::Proj(_, i), GrfKind::Proj(_, j)) = (&g.kind, &h.kind) {
                if *j == 2 || *j == i + 2 {
                    return true;
                }
            }
        }
        false
    }

    pub fn should_prune_min(&self, f: &Grf) -> bool {
        if self.opts.min_trivial {
            if matches!(&f.kind, GrfKind::Zero(_)) {
                return true;
            }
            if matches!(&f.kind, GrfKind::Proj(_, _)) {
                return true;
            }
        }
        if self.opts.min_dom {
            if !f.used_args().contains(&1) {
                return true;
            }
            if f.is_never_zero() {
                return true;
            }
        }
        false
    }
}
