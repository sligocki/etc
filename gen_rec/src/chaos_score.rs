use crate::base::Num;

/// Measures how hard it is to predict the sequence f(0), f(1), f(2), ...
///
/// A "tournament" of independent predictors runs in parallel.  Each tracks its
/// own consecutive-correct-prediction streak.  The chaos score is the index of
/// the first term t at which *any* predictor has been right for `stability`
/// consecutive steps.  A low score means the pattern was detected early;
/// `None` means no predictor ever stabilised (most chaotic / interesting).
///
/// Predictors:
///   - Berlekamp-Massey (BM): finds the shortest linear recurrence that fits
///     the history so far.  Subsumes polynomial and Fibonacci-type sequences.
///     BM is run mod a Mersenne prime; results are verified exactly over Z
///     before any prediction is trusted.
///   - Periodic with period k (k = 2..=max_period): fast-path for small
///     periods, which BM can miss when the history is short relative to 2*k.

// ── Modular arithmetic helpers (Mersenne prime M_61) ─────────────────────────

const PRIME: u64 = (1u64 << 61) - 1;

fn mod_mul(a: u64, b: u64, p: u64) -> u64 {
    ((a as u128 * b as u128) % p as u128) as u64
}

fn mod_pow(mut base: u64, mut exp: u64, p: u64) -> u64 {
    let mut result = 1u64;
    base %= p;
    while exp > 0 {
        if exp & 1 == 1 {
            result = mod_mul(result, base, p);
        }
        exp >>= 1;
        base = mod_mul(base, base, p);
    }
    result
}

fn mod_inv(a: u64, p: u64) -> u64 {
    mod_pow(a, p - 2, p)
}

// ── Berlekamp-Massey over Z/pZ ────────────────────────────────────────────────

/// Returns `(l, c)` where `l` is the LFSR length and `c[1..=l]` are the
/// connection-polynomial coefficients (over Z/pZ, values in `0..p`).
///
/// The recurrence is: s[n] ≡ -c[1]·s[n-1] - c[2]·s[n-2] - … - c[l]·s[n-l] (mod p)
fn bm_mod_p(s: &[u64], p: u64) -> (usize, Vec<u64>) {
    let n = s.len();
    let sp: Vec<u64> = s.iter().map(|&v| v % p).collect();

    // c and b are connection polynomials stored as coefficient vectors (c[0]=1 implicit).
    let mut c: Vec<u64> = vec![0; n + 1]; // c[0]=1 always
    let mut b: Vec<u64> = vec![0; n + 1];
    c[0] = 1;
    b[0] = 1;

    let mut l = 0usize;
    let mut m = 1usize;
    let mut bval: u64 = 1;

    for i in 0..n {
        // Discrepancy: d = s[i] + sum_{j=1}^{l} c[j]*s[i-j]  (mod p)
        let mut d: u64 = sp[i];
        for j in 1..=l {
            d = (d + mod_mul(c[j], sp[i - j], p)) % p;
        }

        if d == 0 {
            m += 1;
        } else if 2 * l <= i {
            let t = c.clone();
            let coef = mod_mul(d, mod_inv(bval, p), p);
            for j in 0..=n - m {
                if b[j] != 0 {
                    let sub = mod_mul(coef, b[j], p);
                    c[m + j] = (c[m + j] + p - sub) % p;
                }
            }
            l = i + 1 - l;
            b = t;
            bval = d;
            m = 1;
        } else {
            let coef = mod_mul(d, mod_inv(bval, p), p);
            for j in 0..=n - m {
                if b[j] != 0 {
                    let sub = mod_mul(coef, b[j], p);
                    c[m + j] = (c[m + j] + p - sub) % p;
                }
            }
            m += 1;
        }
    }

    (l, c)
}

/// Lift a value from Z/pZ to the balanced integer range `[-(p-1)/2, p/2]`.
fn lift(v: u64, p: u64) -> i64 {
    let half = (p / 2) as i64;
    let vi = v as i64;
    if vi > half { vi - p as i64 } else { vi }
}

// ── Predictor trait and implementations ───────────────────────────────────────

trait Predictor {
    /// Given `history` (all values seen so far), predict the *next* value.
    /// Returns `None` when there is not enough data, arithmetic overflows,
    /// or the pattern check fails.
    fn predict(&self, history: &[u64]) -> Option<u64>;
}

struct BerlekampMasseyPredictor {
    max_recurrence: usize,
    /// Skip this many initial terms when fitting the recurrence.  Handles
    /// sequences with a transient prefix that doesn't satisfy the eventual
    /// linear recurrence (e.g. a[0]=1, then a[n]=2*a[n-1]+1 for n≥1).
    transient: usize,
}

impl Predictor for BerlekampMasseyPredictor {
    fn predict(&self, history: &[u64]) -> Option<u64> {
        let n = history.len();
        let k = self.transient;
        if n < k + 2 {
            return None;
        }

        let sub = &history[k..];
        let sn = sub.len();
        let (l, c) = bm_mod_p(sub, PRIME);

        // l == 0: all-zero subsequence; 2*l > sn: not enough data for unique LFSR.
        if l == 0 || 2 * l > sn || l > self.max_recurrence {
            return None;
        }

        // Lift connection-polynomial coefficients to signed integers.
        // Recurrence coefficient r[j] = -c[j+1] lifted to Z.
        let recur: Vec<i64> = (1..=l).map(|j| -lift(c[j], PRIME)).collect();

        // Verify the recurrence holds *exactly* over Z for sub[l..sn].
        // This eliminates any false positives from the mod-p computation.
        for i in l..sn {
            let mut pred: i128 = 0;
            for (j, &r) in recur.iter().enumerate() {
                pred = pred.checked_add((r as i128).checked_mul(sub[i - 1 - j] as i128)?)?;
            }
            if pred < 0 || pred as u64 != sub[i] {
                return None;
            }
        }

        // Predict using the last l terms of history.  These are guaranteed to
        // lie within the valid region: 2*l <= sn implies l <= n-k, so n-l >= k.
        let mut pred: i128 = 0;
        for (j, &r) in recur.iter().enumerate() {
            pred = pred.checked_add((r as i128).checked_mul(history[n - 1 - j] as i128)?)?;
        }
        if pred < 0 { None } else { u64::try_from(pred).ok() }
    }
}

struct PeriodicPredictor {
    period: usize,
}

impl Predictor for PeriodicPredictor {
    fn predict(&self, history: &[u64]) -> Option<u64> {
        let k = self.period;
        if history.len() < k {
            return None;
        }
        Some(history[history.len() - k])
    }
}

fn make_predictors(max_recurrence: usize, max_period: usize, max_transient: usize) -> Vec<Box<dyn Predictor>> {
    let mut v: Vec<Box<dyn Predictor>> = Vec::new();
    for transient in 0..=max_transient {
        v.push(Box::new(BerlekampMasseyPredictor { max_recurrence, transient }));
    }
    for k in 2..=max_period {
        v.push(Box::new(PeriodicPredictor { period: k }));
    }
    v
}

// ── Public API ────────────────────────────────────────────────────────────────

/// Compute the chaos score for a fully-defined sequence (no missing values).
///
/// Returns `Some(lock_on_index)` where `lock_on_index` is the index of the
/// *first* term at which a predictor has just completed `stability` consecutive
/// correct predictions.  Returns `None` if no predictor ever achieves this.
///
/// - `stability`: consecutive correct predictions required to declare a pattern found.
/// - `max_recurrence`: reject BM recurrences longer than this (avoids overfitting).
/// - `max_period`: also run direct period-k checks for k = 2..=max_period
///   (faster convergence for periodic sequences with short history).
/// Compute the mistake count for a fully-defined sequence (no missing values).
///
/// Each predictor tracks its own mistake count (wrong predictions made while
/// `Some(wrong)`) and its current consecutive-correct streak.  When any
/// predictor first achieves `stability` consecutive correct predictions, return
/// that predictor's total mistake count up to that point.
///
/// Returns `None` if no predictor ever stabilises.
/// Returns `Some(0)` if a predictor locked on with zero wrong guesses (it just
/// needed a warm-up period before making predictions).
///
/// - `stability`: consecutive correct predictions required to declare a lock-on.
/// - `max_recurrence`: reject BM recurrences longer than this.
/// - `max_period`: also run direct period-k checks for k = 2..=max_period.
/// Returns `Some(t)` where `t` is the step index (0-based) at which the first
/// predictor completed `stability` consecutive correct predictions.  A lower
/// value means the pattern was detected earlier.  `None` means no predictor
/// ever stabilised (most chaotic / interesting).
pub fn chaos_score(
    vals: &[Num],
    stability: usize,
    max_recurrence: usize,
    max_period: usize,
    max_transient: usize,
    end_slack: usize,
) -> Option<usize> {
    // Convert Num values to u64 for the BM/periodic predictors (which work mod PRIME).
    let vals_u64: Vec<u64> = vals.iter().map(|&v| (v % PRIME as Num) as u64).collect();
    let vals = vals_u64.as_slice();

    let predictors = make_predictors(max_recurrence, max_period, max_transient);
    let np = predictors.len();
    let mut streaks = vec![0usize; np];

    for t in 0..vals.len().saturating_sub(1) {
        let history = &vals[0..=t];
        let target = vals[t + 1];
        for (i, pred) in predictors.iter().enumerate() {
            match pred.predict(history) {
                Some(p) if p == target => {
                    streaks[i] += 1;
                    if streaks[i] >= stability {
                        return Some(t);
                    }
                }
                Some(_) => {
                    streaks[i] = 0;
                }
                None => {} // still warming up
            }
        }
    }

    // End-of-sequence tolerance: if a predictor has been correct for all
    // remaining terms and its streak is within end_slack of the threshold,
    // declare lock-on.  Prevents missing obvious patterns in short sequences
    // that time out before enough terms are available to satisfy stability.
    if end_slack > 0 {
        let threshold = stability.saturating_sub(end_slack).max(1);
        if streaks.iter().any(|&s| s >= threshold) {
            return Some(vals.len().saturating_sub(2));
        }
    }

    None
}

// ── Tests ─────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    fn score(vals: &[u64]) -> Option<usize> {
        let vals_num: Vec<Num> = vals.iter().map(|&v| v as Num).collect();
        chaos_score(&vals_num, 12, 16, 8, 3, 0)
    }

    // --- BerlekampMasseyPredictor unit tests ---

    #[test]
    fn bm_constant() {
        let p = BerlekampMasseyPredictor { max_recurrence: 16, transient: 0 };
        assert_eq!(p.predict(&[7, 7, 7, 7]), Some(7));
    }

    #[test]
    fn bm_linear() {
        // 0, 2, 4, 6 → next = 8  (recurrence: s[n] = 2*s[n-1] - s[n-2])
        let p = BerlekampMasseyPredictor { max_recurrence: 16, transient: 0 };
        assert_eq!(p.predict(&[0, 2, 4, 6]), Some(8));
    }

    #[test]
    fn bm_fibonacci() {
        // 1, 1, 2, 3, 5, 8 → next = 13
        let p = BerlekampMasseyPredictor { max_recurrence: 16, transient: 0 };
        assert_eq!(p.predict(&[1, 1, 2, 3, 5, 8]), Some(13));
    }

    #[test]
    fn bm_quadratic() {
        // n^2: 0, 1, 4, 9, 16, 25 → next = 36
        let p = BerlekampMasseyPredictor { max_recurrence: 16, transient: 0 };
        assert_eq!(p.predict(&[0, 1, 4, 9, 16, 25]), Some(36));
    }

    #[test]
    fn bm_periodic() {
        // period 3: 5, 7, 3, 5, 7, 3 → next = 5
        let p = BerlekampMasseyPredictor { max_recurrence: 16, transient: 0 };
        assert_eq!(p.predict(&[5, 7, 3, 5, 7, 3]), Some(5));
    }

    #[test]
    fn bm_not_enough_data() {
        let p = BerlekampMasseyPredictor { max_recurrence: 16, transient: 0 };
        assert_eq!(p.predict(&[3]), None);
    }

    #[test]
    fn bm_decreasing_sequence_returns_none() {
        // 10, 9, 8, 7 → next = 6, but 6 is a valid u64 so Some(6).
        // (This is just testing it doesn't panic; decreasing sequences are fine.)
        let p = BerlekampMasseyPredictor { max_recurrence: 16, transient: 0 };
        assert_eq!(p.predict(&[10, 9, 8, 7]), Some(6));
    }

    // --- PeriodicPredictor unit tests ---

    #[test]
    fn periodic_period2() {
        let p = PeriodicPredictor { period: 2 };
        assert_eq!(p.predict(&[3, 5, 3, 5]), Some(3));
    }

    #[test]
    fn periodic_not_enough_data() {
        let p = PeriodicPredictor { period: 3 };
        assert_eq!(p.predict(&[1, 2]), None);
    }

    // --- chaos_score integration tests ---

    #[test]
    fn constant_sequence_lockson() {
        // BM finds l=1 at t=1; stability=12 reached at t=12.
        let vals: Vec<u64> = vec![7; 30];
        assert_eq!(score(&vals), Some(12));
    }

    #[test]
    fn linear_sequence_lockson() {
        // BM makes 1 wrong prediction at t=1 (only 2 points, fits geometric),
        // then finds the true l=2 recurrence at t=3 and locks on at t=14.
        let vals: Vec<u64> = (0..40).map(|n: u64| 3 * n + 1).collect();
        assert_eq!(score(&vals), Some(14));
    }

    #[test]
    fn quadratic_sequence_lockson() {
        // BM makes 1 wrong prediction at t=3 (spurious l=2 fit), then finds
        // the true l=3 recurrence at t=5 and locks on at t=16.
        let vals: Vec<u64> = (0u64..40).map(|n| n * n).collect();
        assert_eq!(score(&vals), Some(16));
    }

    #[test]
    fn fibonacci_sequence_lockson() {
        // BM makes 1 wrong prediction at t=1, finds l=2 at t=3, locks on t=14.
        let mut vals = vec![1u64, 1];
        while vals.len() < 40 {
            let n = vals.len();
            vals.push(vals[n - 1] + vals[n - 2]);
        }
        assert_eq!(score(&vals), Some(14));
    }

    #[test]
    fn periodic_sequence_lockson() {
        // Period-3 predictor: no warm-up mistakes, locks on at t=13.
        let vals: Vec<u64> = (0..40).map(|n: u64| (n % 3) + 1).collect();
        assert_eq!(score(&vals), Some(13));
    }

    #[test]
    fn transient_then_linear_detectable() {
        // Transient [2,2,2] followed by linear [3,4,5,...].
        // With max_transient=3 the BM predictor that skips the first 3 terms
        // finds the recurrence cleanly (0 mistakes); detectable regardless.
        let vals: Vec<u64> = (0u64..40)
            .map(|n| if n < 3 { 2 } else { n })
            .collect();
        let s = score(&vals);
        assert!(s.is_some(), "transient prefix sequence should be detectable");
    }

    #[test]
    fn transient_first_term_detected() {
        // a[0]=1 is a transient; a[n] = 2*a[n-1]+1 for n>=1 → [1,2,5,11,23,47,...].
        // BM with transient=1 fits [2,5,11,...] directly (0 mistakes).
        // BM with transient=0 also works on a long-enough sequence: it finds l=3
        // (verifying from i=3 onward, avoiding the a[0] conflict) with 2 mistakes.
        let vals_long: Vec<Num> = std::iter::once(1)
            .chain((1u64..20).scan(2u64, |s, _| { let v = *s; *s = 2 * v + 1; Some(v) }).map(|v| v as Num))
            .collect();
        // transient=0: BM finds l=3 (verification skips a[0..2]), locks on at t=16.
        assert_eq!(chaos_score(&vals_long, 12, 16, 8, 0, 0), Some(16));
        // transient=1: BM finds l=2 on the suffix, locks on at t=15 (one step earlier).
        let s1 = chaos_score(&vals_long, 12, 16, 8, 1, 0);
        assert_eq!(s1, Some(15), "transient=1 BM should lock on one step earlier");

        // Short version (15 terms, like a timed-out holdout entry):
        // transient=0 + end_slack=0 can't gather enough streak.
        let vals_short: Vec<Num> = std::iter::once(1)
            .chain((1u64..15).scan(2u64, |s, _| { let v = *s; *s = 2 * v + 1; Some(v) }).map(|v| v as Num))
            .collect();
        assert_eq!(chaos_score(&vals_short, 12, 16, 8, 0, 0), None);
        // transient=1 + end_slack=2 reaches end-of-sequence threshold
        let s2 = chaos_score(&vals_short, 12, 16, 8, 1, 2);
        assert!(s2.is_some(), "transient=1 with end_slack=2 should detect short sequence");
    }

    #[test]
    fn exponential_short_sequence_end_slack() {
        // 2^(n+1) - 1: [1 3 7 15 31 ... 32767] (15 terms, like a timed-out inner PRF).
        // BM finds recurrence s[n] = 3s[n-1] - 2s[n-2] and is correct for 11 straight
        // terms, but stability=12 is unreachable without slack.
        let vals: Vec<Num> = (0u64..15).map(|n| ((1u64 << (n + 1)) - 1) as Num).collect();
        assert_eq!(chaos_score(&vals, 12, 16, 8, 0, 0), None); // strict: 11 < 12
        let s = chaos_score(&vals, 12, 16, 8, 0, 2);           // end_slack=2: 11 >= 10
        assert!(s.is_some(), "should lock on with end_slack=2; streak=11, threshold=10");
    }

    #[test]
    fn random_looking_sequence_no_lock() {
        // LCG output: defeats simple polynomial/periodic predictors.
        let mut x: u64 = 1;
        let vals: Vec<Num> = (0..50)
            .map(|_| {
                x = x.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                ((x >> 33) + 1) as Num
            })
            .collect();
        let s = chaos_score(&vals, 5, 16, 8, 0, 0);
        assert!(s.is_none(), "unexpected lock-on at {:?}", s);
    }
}
