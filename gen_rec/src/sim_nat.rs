/// Native fixed-width natural number type (u64). Used everywhere performance matters.
pub type SmallNat = u64;

/// Arbitrary-precision natural number type. Used when `SmallNat` overflows.
pub type BigNat = rug::Integer;

/// Arithmetic interface over natural-number types.
///
/// Implemented for `SmallNat` (returns `None` on overflow) and `BigNat` (arbitrary
/// precision — never returns `None` from checked operations).
pub trait SimNat:
    Clone + PartialEq + Eq + PartialOrd + Ord + std::fmt::Debug + std::fmt::Display + 'static
{
    fn zero() -> Self;
    fn one() -> Self;
    /// Checked successor. Returns `None` only for `SmallNat` at `SmallNat::MAX`.
    fn succ(self) -> Option<Self>;
    /// Checked addition. Returns `None` only on `SmallNat` overflow.
    fn checked_add(self, rhs: Self) -> Option<Self>;
    /// Checked subtraction. Returns `None` if `self < rhs` (result would be negative).
    fn checked_sub(self, rhs: Self) -> Option<Self>;
    /// Multiply `self` by a `SmallNat` counter. Returns `None` only on `SmallNat` overflow.
    fn checked_mul_u64(self, n: u64) -> Option<Self>;
    /// Saturating predecessor: zero stays zero (used in step-count formulas).
    fn pred(self) -> Self;
    fn from_u64(n: u64) -> Self;
    /// Saturating cast to `u64` (used only for step-count approximations).
    fn to_u64_sat(&self) -> u64;
    fn is_zero(&self) -> bool;
    /// Saturating addition in place (used for `base_approx` accumulation).
    fn checked_rem(self, rhs: Self) -> Option<Self>;
    fn checked_div_ceil_u64(self, rhs: u64) -> Option<Self>;
    fn saturating_add_assign(&mut self, rhs: Self);
    /// Saturating addition by value. Default impl uses `saturating_add_assign`.
    fn saturating_add(mut self, rhs: Self) -> Self {
        self.saturating_add_assign(rhs);
        self
    }
}

impl SimNat for SmallNat {
    fn zero() -> Self {
        0
    }
    fn one() -> Self {
        1
    }
    fn succ(self) -> Option<Self> {
        self.checked_add(1)
    }
    fn checked_add(self, rhs: Self) -> Option<Self> {
        u64::checked_add(self, rhs)
    }
    fn checked_sub(self, rhs: Self) -> Option<Self> {
        u64::checked_sub(self, rhs)
    }
    fn checked_mul_u64(self, n: u64) -> Option<Self> {
        self.checked_mul(n)
    }
    fn pred(self) -> Self {
        self.saturating_sub(1)
    }
    fn from_u64(n: u64) -> Self {
        n
    }
    fn to_u64_sat(&self) -> u64 {
        *self
    }
    fn is_zero(&self) -> bool {
        *self == 0
    }
    fn checked_rem(self, rhs: Self) -> Option<Self> {
        self.checked_rem(rhs)
    }
    fn checked_div_ceil_u64(self, rhs: u64) -> Option<Self> {
        if rhs == 0 {
            None
        } else {
            Some(self.div_ceil(rhs))
        }
    }
    fn saturating_add_assign(&mut self, rhs: Self) {
        *self = u64::saturating_add(*self, rhs);
    }
}

impl SimNat for BigNat {
    fn zero() -> Self {
        rug::Integer::new()
    }
    fn one() -> Self {
        rug::Integer::from(1u64)
    }
    fn succ(self) -> Option<Self> {
        Some(self + 1u64)
    }
    fn checked_add(self, rhs: Self) -> Option<Self> {
        Some(self + rhs)
    }
    fn checked_sub(self, rhs: Self) -> Option<Self> {
        if self >= rhs { Some(self - rhs) } else { None }
    }
    fn checked_mul_u64(self, n: u64) -> Option<Self> {
        Some(self * n)
    }
    fn pred(self) -> Self {
        if self == 0u64 {
            rug::Integer::new()
        } else {
            self - 1u64
        }
    }
    fn from_u64(n: u64) -> Self {
        rug::Integer::from(n)
    }
    fn to_u64_sat(&self) -> u64 {
        self.to_u64().unwrap_or(u64::MAX)
    }
    fn is_zero(&self) -> bool {
        *self == 0u64
    }
    fn checked_rem(self, rhs: Self) -> Option<Self> {
        if rhs == 0u64 { None } else { Some(self % rhs) }
    }
    fn checked_div_ceil_u64(self, rhs: u64) -> Option<Self> {
        if rhs == 0 {
            None
        } else {
            let num = self + (rhs - 1);
            Some(num / rhs)
        }
    }
    fn saturating_add_assign(&mut self, rhs: Self) {
        *self += rhs;
    }
}
