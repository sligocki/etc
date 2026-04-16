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

/// Generate the canonical input set for a given arity.
/// For arity k, produce all k-tuples drawn from {0 .. per_dim-1}
/// where per_dim is chosen so the total stays ≤ ~32 test cases.
pub fn canonical_inputs(arity: usize) -> Vec<Vec<u64>> {
    if arity == 0 {
        return vec![vec![]];
    }
    let per_dim: u64 = match arity {
        1 => 8, // 8 inputs
        2 => 4, // 16 inputs
        3 => 3, // 27 inputs
        _ => 2, // 2^arity inputs
    };
    let mut result: Vec<Vec<u64>> = vec![vec![]];
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
/// The canonical inputs (used for the DB keys) are intentionally small so the DB
/// stays tractable. But two GRFs can agree on those small inputs and still differ
/// on larger ones. Before substituting, we re-check on this denser grid.
pub fn verification_inputs(arity: usize) -> Vec<Vec<u64>> {
    if arity == 0 {
        return vec![vec![]];
    }
    let per_dim: u64 = match arity {
        1 => 16,
        2 => 8,
        3 => 5,
        _ => 3,
    };
    let mut result: Vec<Vec<u64>> = vec![vec![]];
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
