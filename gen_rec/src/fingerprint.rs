/// Shared fingerprinting utilities for GRF equivalence analysis.
use crate::enumerate::stream_grf;
use crate::grf::Grf;
use crate::pruning::PruningOpts;
use crate::simulate::simulate;
use std::collections::HashMap;

/// A fingerprint: one entry per canonical input. None = timed-out, Some(v) = output value.
///
/// Two fingerprints are only meaningfully comparable when both are fully computed
/// (no None values). A None means "did not converge within the step budget" — not
/// "diverges" — so None cannot be equated with any value, including another None.
pub type Fingerprint = Vec<Option<u64>>;

/// Returns true if the fingerprint is fully computed (no timeouts).
pub fn fp_is_complete(fp: &Fingerprint) -> bool {
    fp.iter().all(|v| v.is_some())
}

/// Minimal linear congruential generator for deterministic pseudorandom inputs.
/// No external dependencies required.
struct Lcg(u64);

impl Lcg {
    fn new(seed: u64) -> Self {
        // XOR-fold to avoid degenerate all-zero state.
        Lcg(seed ^ 0x9e3779b97f4a7c15)
    }

    fn next(&mut self) -> u64 {
        self.0 = self.0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }

    /// Sample a value biased toward small numbers.
    ///
    /// Picks a random bit-length in 0..=6, then fills those bits randomly.
    /// Resulting values are in [0, 63] with approximately:
    ///   0: ~28%,  1: ~14%,  2-3: ~7% each,  4-7: ~3.5% each,  8-63: ~17% spread
    fn sample_biased(&mut self) -> u64 {
        let num_bits = self.next() % 7; // 0, 1, 2, 3, 4, 5, or 6
        if num_bits == 0 {
            0
        } else {
            self.next() & ((1u64 << num_bits) - 1)
        }
    }
}

/// Generate `count` pseudorandom input tuples for a given arity using the given seed.
/// Skips duplicates — each returned tuple is unique.
fn sampled_inputs(arity: usize, count: usize, seed: u64) -> Vec<Vec<u64>> {
    let mut rng = Lcg::new(seed);
    let mut seen = std::collections::HashSet::new();
    let mut result = Vec::with_capacity(count);
    while result.len() < count {
        let input: Vec<u64> = (0..arity).map(|_| rng.sample_biased()).collect();
        if seen.insert(input.clone()) {
            result.push(input);
        }
    }
    result
}

/// Build an exhaustive grid of all k-tuples with each component in 0..per_dim,
/// in lexicographic order.
fn grid_inputs(arity: usize, per_dim: u64) -> Vec<Vec<u64>> {
    let mut result = vec![vec![]];
    for _ in 0..arity {
        let mut next = Vec::new();
        for prefix in &result {
            for v in 0..per_dim {
                let mut row = prefix.clone();
                row.push(v);
                next.push(row);
            }
        }
        result = next;
    }
    result
}

/// Generate `count` canonical input tuples for arity ≥ 2.
///
/// Strategy: use an exhaustive grid (every combination of small values) up to
/// `count` points, then fill remaining slots with unique random samples at larger
/// values.  The grid ensures every small-value combination is represented exactly
/// once, which is the most information-dense starting set.  The random tail
/// covers larger values that the grid misses.
///
/// `per_dim` is chosen as the largest integer where per_dim^arity ≤ count.
fn grid_then_random(arity: usize, count: usize, seed: u64) -> Vec<Vec<u64>> {
    // Largest per_dim such that per_dim^arity ≤ count.
    let per_dim = {
        let mut p = 1u64;
        loop {
            let next = p + 1;
            // next^arity ≤ count?
            let product = (0..arity).try_fold(1usize, |acc, _| {
                acc.checked_mul(next as usize)
            });
            match product {
                Some(n) if n <= count => p = next,
                _ => break,
            }
        }
        p
    };

    let mut inputs = grid_inputs(arity, per_dim);
    // inputs is already ≤ count in length; fill the rest with unique random samples.
    if inputs.len() < count {
        let mut seen: std::collections::HashSet<Vec<u64>> =
            inputs.iter().cloned().collect();
        let mut rng = Lcg::new(seed);
        while inputs.len() < count {
            let input: Vec<u64> = (0..arity).map(|_| rng.sample_biased()).collect();
            if seen.insert(input.clone()) {
                inputs.push(input);
            }
        }
    }
    inputs
}

/// Generate `n` canonical inputs for a given arity.
///
/// Arity 0: always returns a single empty input (fp_size has no effect).
/// Arity 1: exhaustive {0, 1, ..., n-1}.
/// Arity ≥ 2: exhaustive grid of small values up to n points, then unique random
///   samples for the remainder.  See `grid_then_random` for details.
///
/// NOTE: unlike the old pure-random approach, `canonical_inputs_n(arity, n)` is
/// NOT a prefix of `canonical_inputs_n(arity, m)` for m > n when arity ≥ 2,
/// because the grid size (per_dim) depends on n.  Fingerprints computed at
/// different fp_sizes are therefore not comparable by slicing; each fp_size must
/// be re-computed independently.
pub fn canonical_inputs_n(arity: usize, n: usize) -> Vec<Vec<u64>> {
    match arity {
        0 => vec![vec![]],
        1 => (0u64..n as u64).map(|v| vec![v]).collect(),
        k => grid_then_random(k, n, 0xdeadbeefdeadbeef_u64.wrapping_mul(k as u64)),
    }
}

/// Generate the canonical input set for a given arity.
///
/// Arity 0: single empty input.
/// Arity 1: exhaustive {0..7} — small enough to cover completely.
/// Arity ≥ 2: 32 points via `grid_then_random` — an exhaustive grid of small
///   values (e.g. all 5×5=25 pairs for arity 2, plus 7 random extras), then
///   unique random samples to fill the remainder.
pub fn canonical_inputs(arity: usize) -> Vec<Vec<u64>> {
    match arity {
        0 => vec![vec![]],
        1 => (0u64..8).map(|v| vec![v]).collect(),
        k => grid_then_random(k, 32, 0xdeadbeefdeadbeef_u64.wrapping_mul(k as u64)),
    }
}

/// Compute the fingerprint of a GRF on the given canonical inputs.
pub fn compute_fp(grf: &Grf, inputs: &[Vec<u64>], max_steps: u64) -> Fingerprint {
    inputs
        .iter()
        .map(|inp| {
            let (result, _) = simulate(grf, inp, max_steps);
            result.into_value()
        })
        .collect()
}

/// A broader input set used to verify candidate replacements before committing.
///
/// Uses an exhaustive grid on small values (guaranteeing that every value 0..k
/// appears in every dimension) rather than random sampling. This is complementary
/// to the pseudorandom canonical inputs: canonical covers a wide range including
/// larger values, verification guarantees exhaustive coverage of small values.
///
/// For arity ≥ 4 the grid would explode, so we fall back to pseudorandom with a
/// different seed from canonical_inputs.
pub fn verification_inputs(arity: usize) -> Vec<Vec<u64>> {
    match arity {
        0 => vec![vec![]],
        1 => (0u64..16).map(|v| vec![v]).collect(),
        k @ 2..=3 => {
            let per_dim: u64 = if k == 2 { 8 } else { 5 };
            let mut result: Vec<Vec<u64>> = vec![vec![]];
            for _ in 0..k {
                let mut next = Vec::new();
                for prefix in &result {
                    for v in 0..per_dim {
                        let mut row = prefix.clone();
                        row.push(v);
                        next.push(row);
                    }
                }
                result = next;
            }
            result
        }
        k => sampled_inputs(k, 64, 0xcafebabecafebabe_u64.wrapping_mul(k as u64)),
    }
}

/// A database of the smallest known GRF for each fully-computed fingerprint,
/// keyed by (arity, fingerprint).
///
/// Only entries where every canonical input converged within the step budget are
/// stored. Partial fingerprints (any None) are discarded — a None means "unknown
/// value", not "diverges", so it cannot safely be used for equivalence matching.
pub struct FingerprintDb {
    /// (arity, fingerprint) → smallest GRF with that fingerprint
    map: HashMap<(usize, Fingerprint), Grf>,
    /// canonical inputs per arity (cached to avoid recomputation)
    inputs: HashMap<usize, Vec<Vec<u64>>>,
    max_steps: u64,
}

impl FingerprintDb {
    /// Build a DB of all novel GRFs up to `max_size` for arities 0..=`max_arity`.
    ///
    /// GRFs whose fingerprint contains any None (timed out within `max_steps`) are
    /// silently skipped — their functional identity is unknown.
    pub fn build(max_size: usize, max_arity: usize, allow_min: bool, max_steps: u64) -> Self {
        let opts = PruningOpts::default();
        let mut db = FingerprintDb {
            map: HashMap::new(),
            inputs: HashMap::new(),
            max_steps,
        };

        for arity in 0..=max_arity {
            let inputs = canonical_inputs(arity);
            for size in 1..=max_size {
                stream_grf(size, arity, allow_min, opts, &mut |grf: &Grf| {
                    let fp = compute_fp(grf, &inputs, max_steps);
                    if fp_is_complete(&fp) {
                        let key = (arity, fp);
                        // Only insert if this is the first (smallest) GRF for this fingerprint.
                        db.map.entry(key).or_insert_with(|| grf.clone());
                    }
                });
            }
            db.inputs.insert(arity, inputs);
        }

        db
    }

    /// Create an empty `FingerprintDb` with no entries.
    /// Entries can be added with `add_entry`. Used by `novel_db` when loading from files.
    pub fn build_empty(max_steps: u64) -> Self {
        FingerprintDb {
            map: HashMap::new(),
            inputs: HashMap::new(),
            max_steps,
        }
    }

    /// Insert a (fingerprint, grf) pair. Keeps the smaller GRF if one already exists.
    /// The canonical inputs for `arity` are cached on first use.
    pub fn add_entry(&mut self, arity: usize, fp: Fingerprint, grf: Grf) {
        self.inputs.entry(arity).or_insert_with(|| canonical_inputs(arity));
        self.map
            .entry((arity, fp))
            .and_modify(|existing| {
                if grf.size() < existing.size() {
                    *existing = grf.clone();
                }
            })
            .or_insert(grf);
    }

    pub fn compute_fp(&self, grf: &Grf) -> Fingerprint {
        let arity = grf.arity();
        let inputs = self.inputs.get(&arity).unwrap();
        compute_fp(grf, inputs, self.max_steps)
    }

    /// Look up the smallest known GRF equivalent to `grf`, if one exists in the DB
    /// and is strictly smaller.
    ///
    /// Returns `None` if:
    /// - `grf`'s fingerprint has any timeout (unknown functional identity), or
    /// - no smaller equivalent is in the DB, or
    /// - the verification check on a broader input set fails (false positive guard).
    pub fn lookup_smaller(&self, grf: &Grf) -> Option<&Grf> {
        let arity = grf.arity();
        let inputs = self.inputs.get(&arity)?;
        let fp = compute_fp(grf, inputs, self.max_steps);
        if !fp_is_complete(&fp) {
            return None;
        }
        let key = (arity, fp);
        let candidate = self.map.get(&key)?;
        if candidate.size() >= grf.size() {
            return None;
        }

        // The canonical input set is small — two GRFs can agree there but differ on
        // larger inputs. Verify on a broader grid before committing to the replacement.
        let verify = verification_inputs(arity);
        let vfp_grf = compute_fp(grf, &verify, self.max_steps);
        let vfp_cand = compute_fp(candidate, &verify, self.max_steps);
        if fp_is_complete(&vfp_grf) && vfp_grf == vfp_cand {
            Some(candidate)
        } else {
            None
        }
    }

}
