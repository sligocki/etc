/// Numeric type for GRF values and step counts. Swap to `u128` or bignum to widen.
pub type Num = u64;

/// Arithmetic interface for GRF value types.
///
/// Implemented for `u64` (returns `None` on overflow) and `rug::Integer` (arbitrary
/// precision — never returns `None` from checked operations).
pub trait SimNum:
    Clone + PartialEq + Eq + PartialOrd + Ord
    + std::fmt::Debug + std::fmt::Display + 'static
{
    fn zero() -> Self;
    fn one()  -> Self;
    /// Checked successor. Returns `None` only for `u64` at `u64::MAX`.
    fn succ(self) -> Option<Self>;
    /// Checked addition. Returns `None` only on `u64` overflow.
    fn checked_add(self, rhs: Self) -> Option<Self>;
    /// Multiply `self` by a `u64` counter. Returns `None` only on `u64` overflow.
    fn checked_mul_u64(self, n: u64) -> Option<Self>;
    /// Saturating predecessor: zero stays zero (used in step-count formulas).
    fn pred(self) -> Self;
    fn from_u64(n: u64) -> Self;
    /// Saturating cast to `u64` (used only for step-count approximations).
    fn to_u64_sat(&self) -> u64;
    fn is_zero(&self) -> bool;
    /// Saturating addition in place (used for `base_approx` accumulation).
    fn saturating_add_assign(&mut self, rhs: Self);
    /// Saturating addition by value. Default impl uses `saturating_add_assign`.
    fn saturating_add(mut self, rhs: Self) -> Self {
        self.saturating_add_assign(rhs);
        self
    }
}

impl SimNum for u64 {
    fn zero() -> Self { 0 }
    fn one()  -> Self { 1 }
    fn succ(self) -> Option<Self> { self.checked_add(1) }
    fn checked_add(self, rhs: Self) -> Option<Self> { u64::checked_add(self, rhs) }
    fn checked_mul_u64(self, n: u64) -> Option<Self> { self.checked_mul(n) }
    fn pred(self) -> Self { self.saturating_sub(1) }
    fn from_u64(n: u64) -> Self { n }
    fn to_u64_sat(&self) -> u64 { *self }
    fn is_zero(&self) -> bool { *self == 0 }
    fn saturating_add_assign(&mut self, rhs: Self) { *self = u64::saturating_add(*self, rhs); }
}

impl SimNum for rug::Integer {
    fn zero() -> Self { rug::Integer::new() }
    fn one()  -> Self { rug::Integer::from(1u64) }
    fn succ(self) -> Option<Self> { Some(self + 1u64) }
    fn checked_add(self, rhs: Self) -> Option<Self> { Some(self + rhs) }
    fn checked_mul_u64(self, n: u64) -> Option<Self> { Some(self * n) }
    fn pred(self) -> Self {
        if self == 0u64 { rug::Integer::new() } else { self - 1u64 }
    }
    fn from_u64(n: u64) -> Self { rug::Integer::from(n) }
    fn to_u64_sat(&self) -> u64 { self.to_u64().unwrap_or(u64::MAX) }
    fn is_zero(&self) -> bool { *self == 0u64 }
    fn saturating_add_assign(&mut self, rhs: Self) { *self += rhs; }
}
