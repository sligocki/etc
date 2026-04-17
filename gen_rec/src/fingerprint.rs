/// Shared fingerprinting utilities for GRF equivalence analysis.
use crate::enumerate::stream_grf;
use crate::grf::Grf;
use crate::pruning::PruningOpts;
use crate::simulate::simulate;
use std::collections::HashMap;
use std::io::{self, BufRead};
use std::path::Path;

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
fn sampled_inputs(arity: usize, count: usize, seed: u64) -> Vec<Vec<u64>> {
    let mut rng = Lcg::new(seed);
    (0..count)
        .map(|_| (0..arity).map(|_| rng.sample_biased()).collect())
        .collect()
}

/// Generate the canonical input set for a given arity.
///
/// Arity 0: single empty input.
/// Arity 1: exhaustive {0..7} — small enough to cover completely.
/// Arity ≥ 2: 32 pseudorandom points with a small-biased distribution (values in
///   [0,63]), seeded deterministically per arity. Fixed points cover a wider range
///   than a small grid while keeping the count constant regardless of arity.
pub fn canonical_inputs(arity: usize) -> Vec<Vec<u64>> {
    match arity {
        0 => vec![vec![]],
        1 => (0u64..8).map(|v| vec![v]).collect(),
        k => sampled_inputs(k, 32, 0xdeadbeefdeadbeef_u64.wrapping_mul(k as u64)),
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

    /// Build a `FingerprintDb` by loading a novel DB file and re-fingerprinting its entries.
    ///
    /// The file format is the same as written by `novel --save`:
    /// - Line 1: `allow_min=<bool> max_size=<usize> max_steps=<u64>` (metadata, ignored here)
    /// - Subsequent lines: `<size>\t<grf_string>`
    /// - Lines starting with `#` are ignored.
    ///
    /// `max_steps` controls the simulation budget used for all future `lookup_smaller` calls.
    /// It need not match the value stored in the file header.
    pub fn from_novel_db(path: &Path, max_steps: u64) -> io::Result<Self> {
        let file = std::fs::File::open(path)?;
        let reader = io::BufReader::new(file);
        let mut db = FingerprintDb {
            map: HashMap::new(),
            inputs: HashMap::new(),
            max_steps,
        };

        for (lineno, line) in reader.lines().enumerate() {
            let line = line?;
            let line = line.trim();
            // Skip blank lines and the header / comments
            if line.is_empty() || line.starts_with('#') {
                continue;
            }
            // Header line (first non-comment line) starts with a known key
            if line.starts_with("allow_min=") {
                continue;
            }
            // Data line: "<size>\t<grf_string>"
            let mut parts = line.splitn(2, '\t');
            let _size_str = parts.next().ok_or_else(|| {
                io::Error::new(io::ErrorKind::InvalidData, format!("line {lineno}: missing size"))
            })?;
            let grf_str = parts.next().ok_or_else(|| {
                io::Error::new(io::ErrorKind::InvalidData, format!("line {lineno}: missing grf"))
            })?;
            let grf: Grf = grf_str.parse().map_err(|e| {
                io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!("line {lineno}: parse error: {e}"),
                )
            })?;

            let arity = grf.arity();
            let inputs = db.inputs.entry(arity).or_insert_with(|| canonical_inputs(arity));
            let fp = compute_fp(&grf, inputs, max_steps);
            if fp_is_complete(&fp) {
                db.map.entry((arity, fp)).or_insert(grf);
            }
        }

        Ok(db)
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
