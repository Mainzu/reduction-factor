#![no_std]
#![doc = include_str!("../README.md")]

use core::fmt;
use core::num::NonZeroUsize;
use core::ops::{Add, Deref, DerefMut, Mul, MulAssign, Sub};

use num_traits::{One, Zero};

/// A newtype representing a reduction factor of `(1 - T)`.
///
/// See the [module-level documentation](self) for more information.
///
/// Note that this type does not implement the [`num_traits::One`](https://docs.rs/num-traits/latest/num_traits/identities/trait.One.html) trait.
/// This is intentional as the trait requires `one()` to return the multiplicative identity, which for `Reduction` is [`Reduction::none()`].
/// However, having `Reduction::one()` return a `Reduction(T::zero())` would be highly confusing.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Reduction<T>(pub T);

impl<T: fmt::Display> fmt::Display for Reduction<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(1 - {})", self.0)
    }
}

impl<T> Reduction<T> {
    /// Creates a new `Reduction` from the given inner value.
    #[inline]
    #[must_use]
    pub const fn new(value: T) -> Self {
        Self(value)
    }

    /// Creates a `Reduction` representing no reduction (0%).
    ///
    /// This is the multiplicative identity for composition: any reduction composed
    /// with `none` remains unchanged.
    ///
    /// Its multiplier is 1.
    #[must_use]
    pub fn none() -> Self
    where
        T: Zero,
    {
        Self(T::zero())
    }

    /// Creates a `Reduction` representing a full reduction (100%).
    ///
    /// This is the absorbing element for composition: any reduction composed
    /// with `full` results in `full`.
    ///
    /// Note that for floats, this property may not hold exactly.
    ///
    /// Its multiplier is 0.
    #[must_use]
    pub fn full() -> Self
    where
        T: One,
    {
        Self(T::one())
    }

    /// Consumes the `Reduction` and returns the inner value `x`.
    #[inline]
    pub fn inner(self) -> T {
        self.0
    }
}
impl<T: One + Sub<Output = T>> Reduction<T> {
    /// Calculates the multiplicative factor, `1 - self.0`.
    ///
    /// This is the value that is multiplied with a base value when the reduction is applied.
    ///
    /// # Example
    /// ```
    /// use reduction_factor::Reduction;
    /// let r = Reduction(0.25f32);
    /// assert_eq!(r.multiplier(), 0.75);
    /// ```
    pub fn multiplier(self) -> T {
        T::one() - self.0
    }

    /// Applies the reduction to a given value.
    ///
    /// This is equivalent to `value * self.multiplier()`.
    ///
    /// This operation is also available through multiplication: `reduction * value`.
    ///
    /// # Example
    /// ```
    /// use reduction_factor::Reduction;
    /// let r = Reduction(0.25f32);
    /// assert_eq!(r.reduce(100.0), 75.0);
    /// assert_eq!(r * 100.0, 75.0);
    /// ```
    #[doc(alias = "apply")]
    pub fn reduce(self, value: T) -> T {
        value * self.multiplier()
    }

    /// Returns the complement of the reduction.
    ///
    /// The complement of `Reduction(x)` is `Reduction(1 - x)`.
    /// For example, the complement of a 25% reduction is an 75% reduction.
    ///
    /// # Example
    /// ```
    /// use reduction_factor::Reduction;
    /// let r = Reduction(0.25f32);
    /// let complement = r.complement();
    /// assert_eq!(*complement, 0.75);
    /// ```
    #[doc(alias = "invert")]
    pub fn complement(self) -> Self {
        Self(self.multiplier())
    }
}
impl<T: Add<Output = T> + Sub<Output = T> + Mul<Output = T> + Clone> Reduction<T> {
    /// Composes this reduction with another, returning a new `Reduction`.
    ///
    /// This is equivalent to applying one reduction and then the other.
    ///
    /// The formula for the new inner value is `x + y - xy` where
    /// `x` and `y` are the inner values of the two reductions.
    ///
    /// This operation is also available through multiplication: `r1 * r2`.
    ///
    /// # Example
    /// ```
    /// use reduction_factor::Reduction;
    /// let r1 = Reduction(0.20f32);
    /// let r2 = Reduction(0.10f32);
    /// let stacked = r1.compose(r2);
    /// assert_eq!(*stacked, 0.28);
    /// assert_eq!(r1 * r2, stacked); // Equivalent
    /// ```
    #[doc(alias = "stack")]
    #[doc(alias = "combine")]
    pub fn compose(self, other: Self) -> Self {
        // (1 - x) * (1 - y) = 1 - x - y + xy = 1 - (x + y - xy)
        Self(self.0.clone() + other.0.clone() - self.0 * other.0)
    }

    /// In-place version of [`compose`](Self::compose).
    #[doc(alias = "stack_inplace")]
    #[doc(alias = "combine_inplace")]
    pub fn compose_inplace(&mut self, other: Self)
    where
        // `Default` bound is added because it's not worth dealing with the trouble of temporarily taking `T` out of a `&mut T`
        T: Default,
    {
        let value = core::mem::take(&mut self.0);
        self.0 = value.clone() + other.0.clone() - value * other.0;
    }

    /// Composes the reduction with itself `exponent` times.
    ///
    /// `pow(0)` returns `Reduction(0)` the identity reduction, [`Reduction::none()`].
    ///
    /// # Example
    /// ```
    /// use reduction_factor::Reduction;
    /// let r = Reduction(0.5f32);
    /// // Applying a 50% reduction twice results in a 75% reduction.
    /// let r2 = r.pow(2);
    /// assert_eq!(*r2, 0.75);
    /// assert_eq!(r * r, r2);
    /// ```
    ///
    /// Zero exponent returns the identity reduction.
    /// ```
    /// use reduction_factor::Reduction;
    /// let r = Reduction(0.5f32);
    ///
    /// let r0 = r.pow(0);
    /// assert_eq!(*r0, 0.0);
    /// assert_eq!(r0, Reduction::none());
    /// ```
    #[doc(alias = "repeat")]
    pub fn pow(&self, exponent: usize) -> Self
    where
        T: Zero,
    {
        if exponent == 0 {
            Self::none()
        } else if exponent % 2 == 0 {
            let tmp = self.pow(exponent / 2);
            tmp.clone().compose(tmp)
        } else {
            self.clone().compose(self.pow(exponent - 1))
        }
    }

    /// Composes the reduction with itself `exponent` times for a non-zero exponent.
    ///
    /// The main difference from [`Reduction::pow()`] is that `T: Zero` isn't required.
    ///
    /// # Example
    /// ```
    /// use reduction_factor::Reduction;
    /// use core::num::NonZeroUsize;
    ///
    /// let r = Reduction(0.5f32);
    /// // Applying a 50% reduction twice results in a 75% reduction.
    /// let r2 = r.pow_nonzero(NonZeroUsize::new(2).unwrap());
    /// assert_eq!(*r2, 0.75);
    /// assert_eq!(r * r, r2);
    /// ```
    #[doc(alias = "repeat_nonzero")]
    pub fn pow_nonzero(&self, exponent: NonZeroUsize) -> Self {
        if exponent.get() == 1 {
            self.clone()
        } else if exponent.get() % 2 == 0 {
            // SAFETY: Since exponent can't be 1, it won't go to 0
            let exponent = unsafe { NonZeroUsize::new_unchecked(exponent.get() / 2) };
            let tmp = self.pow_nonzero(exponent);
            tmp.clone().compose(tmp)
        } else {
            // SAFETY: Since exponent can't be 1, it won't go to 0
            let exponent = unsafe { NonZeroUsize::new_unchecked(exponent.get() - 1) };
            self.clone().compose(self.pow_nonzero(exponent))
        }
    }
}

impl<T> From<T> for Reduction<T> {
    #[inline]
    fn from(value: T) -> Self {
        Self::new(value)
    }
}

impl<T> Deref for Reduction<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl<T> DerefMut for Reduction<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}
impl<T> AsRef<T> for Reduction<T> {
    #[inline]
    fn as_ref(&self) -> &T {
        &self.0
    }
}
impl<T> AsMut<T> for Reduction<T> {
    #[inline]
    fn as_mut(&mut self) -> &mut T {
        &mut self.0
    }
}

impl<T: Zero> Default for Reduction<T> {
    #[inline]
    fn default() -> Self {
        Self::none()
    }
}

impl<T: Add<Output = T> + Sub<Output = T> + Mul<Output = T> + Clone> Mul for Reduction<T> {
    type Output = Self;

    /// The multiplication operator is overloaded for two `Reduction`s to perform [`compose`](Self::compose).
    ///
    /// This is the idiomatic way to compose two reductions.
    #[inline]
    fn mul(self, rhs: Self) -> Self::Output {
        self.compose(rhs)
    }
}
impl<T: Default + Add<Output = T> + Sub<Output = T> + Mul<Output = T> + Clone> MulAssign
    for Reduction<T>
{
    /// The `*=` operator is overloaded for two `Reduction`s to perform [`compose_inplace`](Self::compose_inplace).
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        self.compose_inplace(rhs)
    }
}
impl<T: One + Sub<Output = T>> Mul<T> for Reduction<T> {
    type Output = T;

    /// The multiplication operator is overloaded to [`reduce`](Self::reduce) the reduction to a value of type `T`.
    #[inline]
    fn mul(self, rhs: T) -> Self::Output {
        self.reduce(rhs)
    }
}

// Does not implement `One` because `Reduction(1)` is not the multiplicative identity
// (that's how `num_trait` defined its `One`).
// The multiplicative identity is `Reduction(0)` or `Reduction::none()`.
// But if `Reduction::one() == Reduction::none()`, that is way too confusing.

// Cannot implement `Zero` because addition between `Reduction`s is not defined.
// Even if it could be implemented, the same confusion would make it not worth it.

#[cfg(test)]
mod tests {
    use super::*;
    use core::num::NonZeroUsize;

    const EPSILON: f32 = 1e-6;

    #[test]
    fn test_apply_reduction() {
        let price = 100.0f32;
        let discount = Reduction(0.25);
        assert!((discount * price - 75.0).abs() < EPSILON);
    }

    #[test]
    fn test_compose() {
        let r1 = Reduction(0.20f32);
        let r2 = Reduction(0.10f32);
        let combined = r1 * r2;
        assert!((combined.inner() - 0.28).abs() < EPSILON);
    }

    #[test]
    fn test_identity_and_default() {
        let r1 = Reduction(0.3f32);
        assert_eq!(r1 * Reduction::none(), r1);
        assert_eq!(Reduction::none() * r1, r1);
        assert_eq!(Reduction::<f32>::default(), Reduction::none());
    }

    #[test]
    fn test_full_reduction() {
        let r1 = Reduction(0.3f32);
        let full = Reduction::full();
        assert!((*(r1 * full) - *full).abs() < EPSILON);
        assert!((*(full * r1) - *full).abs() < EPSILON);
        assert!((full * 100.0f32).abs() < EPSILON);
    }

    #[test]
    fn test_pow() {
        let r = Reduction(0.5f32);
        assert_eq!(r.pow(0), Reduction::none());
        assert_eq!(r.pow(1), r);
        assert!((r.pow(2).inner() - 0.75).abs() < EPSILON); // 0.5 + 0.5 - 0.25 = 0.75
        assert!((r.pow(3).inner() - 0.875).abs() < EPSILON);
    }

    #[test]
    fn test_pow_nonzero() {
        let r = Reduction(0.5f32);
        assert_eq!(r.pow_nonzero(NonZeroUsize::new(1).unwrap()), r);
        assert!((r.pow_nonzero(NonZeroUsize::new(2).unwrap()).inner() - 0.75).abs() < EPSILON);
    }

    #[test]
    fn test_complement() {
        let r = Reduction(0.2f32);
        let c = r.complement();
        assert!((c.inner() - 0.8).abs() < EPSILON);
        assert!((c.complement().inner() - 0.2).abs() < EPSILON);
    }
}
