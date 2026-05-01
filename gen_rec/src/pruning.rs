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

define_pruning_flags! {
    { comp_proj,     "comp_proj",     cc=yes, rec=yes, mo=no,  "C(P,…) → one of its args" },
    { comp_zero,     "comp_zero",     cc=yes, rec=yes, mo=no,  "C(Z,…) → Z" },
    { rec_zero_arg,  "rec_zero_arg",  cc=yes, rec=yes, mo=no,  "C(R(g,h),Z,…) → C(g,…)" },
    { comp_assoc,    "comp_assoc",    cc=yes, rec=yes, mo=no,  "C(C(f,g),h1…) → C(f,C(g,h1…))" },
    { comp_null_null,"comp_null_null",cc=yes, rec=yes, mo=no,  "C0(h) → h" },
    // TODO: I'm not 100% sure it is safe to skip C(h) ... and it is only like a 1.2% savings.
    { comp_null,     "comp_null",     cc=yes, rec=no,  mo=no,  "Ck(h) → h^k  (not 100% safe)" },
    { rec_zero_base, "rec_zero_base", cc=yes, rec=yes, mo=no,  "R(Z,Z) / R(Z,P2) → Z" },
    { min_trivial,   "min_trivial",   cc=yes, rec=yes, mo=yes, "M(Z) / M(P) → Z" },
    { min_dom,       "min_dom",       cc=no,  rec=yes, mo=yes, "M(f) dominated by Z_{k-1}" },
    { inline_proj,   "inline_proj",   cc=no,  rec=yes, mo=no,  "C(h,P/Z…) → inlined h" },
    { comp_rnf,      "comp_rnf",      cc=no,  rec=yes, mo=no,  "C(h,…) require h in Rewire Normal Form (all args used, canonical order)" },
    { rec_step_p2,   "rec_step_p2",   cc=no,  rec=no,  mo=no,  "C(R(g,P2),h1,…) → C(g,h2,…)" },
}
