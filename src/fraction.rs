//! Fraction type & its trait implementations

use std::fmt::Display;

use crate::traits::Mediant;
use crate::types::FractionError;
use crate::{prelude::*, traits::Reciprocal};
use num_traits::{Bounded, One, Zero};

/// A fraction (x ÷ y) represented by two primitive integers.
#[derive(Debug, Copy, Clone)]
pub struct Fraction<T: Number> {
    /// Top half of the fraction    
    pub numerator: T,
    /// Bottom half of the fraction.
    pub denominator: T,
}

// Misc. Impls
// These are sets of functions that aren't an implementation of a trait
impl<T: Number> Fraction<T> {
    /// Creates a new Fraction
    ///
    /// # Examples
    /// ```
    /// use beetle_fraction::prelude::*;
    /// let one_half: Fraction<i32> = Fraction::new(1, 2); // Represents (1 / 2)
    /// assert_eq!(one_half, Fraction {numerator: 1, denominator: 2});
    /// ```
    pub fn new(numerator: T, denominator: T) -> Self {
        Self {
            numerator,
            denominator,
        }
    }

    /// Version of the `new` function with some extra safety checks
    ///
    /// # Safety Checks:
    /// - must be non-zero, to prevent implied division by zero
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// use beetle_fraction::prelude::*;
    /// let bad_fraction = Fraction::checked_new(1, 0); // is the error variant, because of implied division by zero
    /// assert!(bad_fraction.is_err())
    ///
    /// ```
    pub fn checked_new(numerator: T, denominator: T) -> Result<Self, FractionError> {
        if denominator.is_zero() {
            Err(FractionError::ImpliedDivisionByZero)
        } else {
            Ok(Self {
                numerator,
                denominator,
            })
        }
    }
}

impl<T: Number> Bounded for Fraction<T> {
    fn max_value() -> Self {
        frac![T::one(), T::max_value()]
    }

    fn min_value() -> Self {
        frac![T::zero(), T::one()]
    }
}

impl<T: Number> One for Fraction<T> {
    fn one() -> Self {
        Self {
            numerator: T::one(),
            denominator: T::one(),
        }
    }

    fn set_one(&mut self) {
        *self = Self::one();
    }

    fn is_one(&self) -> bool {
        // Numerator and denominator are the same
        // Denominator must not be zero, since division by zero is undefined
        (self.numerator == self.denominator) && (!self.denominator.is_zero())
    }
}

impl<T: Number> Zero for Fraction<T> {
    fn is_zero(&self) -> bool {
        self.numerator.is_zero()
    }

    fn zero() -> Self {
        Self {
            numerator: T::zero(),
            denominator: T::one(),
        }
    }

    fn set_zero(&mut self) {
        *self = Self::zero();
    }
}

impl<T: Number> Reciprocal for Fraction<T> {
    fn reciprocal(&self) -> Self {
        frac![self.denominator, self.numerator]
    }
}

impl<T: Number> Simplify for Fraction<T> {
    fn simplest_form(&self) -> Self {
        let fac: T = num::integer::gcd(self.numerator, self.denominator);
        frac![self.numerator / fac, self.denominator / fac]
    }

    fn simplify(&mut self) {
        *self = self.simplest_form();
    }
}

impl<T: Number> Mediant for Fraction<T> {
    fn mediant(&self, rhs: &Self) -> Self {
        frac![
            self.numerator + rhs.numerator,
            self.denominator + rhs.denominator
        ]
    }
}

impl<T: Number> Display for Fraction<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?} / {:?}", self.numerator, self.denominator)
    }
}

impl<T: Number> Default for Fraction<T> {
    fn default() -> Self {
        Self::one()
    }
}

impl<T: Number> PartialEq for Fraction<T> {
    fn eq(&self, other: &Self) -> bool {
        (self.numerator == other.numerator) && (self.denominator == other.denominator)
    }
}

impl<T: Number> PartialOrd for Fraction<T> {
    fn gt(&self, other: &Self) -> bool {
        (self.numerator * other.denominator) > (self.denominator * other.numerator)
    }

    fn ge(&self, other: &Self) -> bool {
        (self.numerator * other.denominator) >= (self.denominator * other.numerator)
    }

    fn le(&self, other: &Self) -> bool {
        (self.numerator * other.denominator) <= (self.denominator * other.numerator)
    }

    fn lt(&self, other: &Self) -> bool {
        (self.numerator * other.denominator) < (self.denominator * other.numerator)
    }

    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        use std::cmp::Ordering;
        if self == other {
            Some(Ordering::Equal)
        } else if self > other {
            Some(Ordering::Greater)
        } else if self < other {
            Some(Ordering::Less)
        } else {
            None
        }
    }
}

/// For converting `To` and `From` `Fraction`s
pub mod conversions {

    /// Conversions between Fractions and Collections (like tuples)
    pub mod collections {
        use crate::{frac, fraction::Fraction, traits::Number};

        // TUPLE -> Fraction
        impl<T: Number> From<(T, T)> for Fraction<T> {
            fn from(tup: (T, T)) -> Self {
                frac![tup.0, tup.1]
            }
        }

        // Slice -> Fraction
        impl<T: Number> From<[T; 2]> for Fraction<T> {
            fn from(arr: [T; 2]) -> Self {
                let [a, b] = arr;
                frac![a, b]
            }
        }
    }

    /// Conversions between Fractions and Unit types (u8, i8, u32, etc.)
    pub mod units {

        use num::Zero;

        use crate::{frac, fraction::Fraction, traits::Number};

        impl Fraction<i128> {
            /// Attempts to convert an f64 < 1 into a Fraction.
            /// This does not check that the f64 is actually less than 1.0
            /// If an f64 greater than 1 is passed to this function, you will receive an incorrect Fraction as a result, use from_float instead.
            /// # Safety
            /// I've not done extensive testing on this besides with intended inputs.
            /// It's probably best not to pass NaN, Infinity, or floats > 1 to this function, as it doesn't test against them.
            pub unsafe fn float_less_than_one_to_fraction(f: f64) -> Option<Fraction<i128>> {
                let f_digits: i32 = (f.to_string().len() - 2).try_into().ok()?;
                let power_of_ten: f64 = 10f64.powi(f_digits);
                let ans = f * power_of_ten;

                if !ans.is_finite() {
                    return None;
                }

                let power_of_ten_int: i128 = power_of_ten.to_int_unchecked();

                let fract = frac![ans.to_int_unchecked(), power_of_ten_int];
                Some(fract)
            }

            /// Attempts to convert an f64 to a Fraction<i128>
            /// # Safety
            /// To my knowledge there are no safety issues.
            /// I've tested this with random floats in the range i128::MIN .. i128::MAX with no issues.
            /// I've tested this with NaN and Infinity with no issues.
            /// This is only unsafe for simplicty and performance reasons, I'll probably make it safe later.
            pub unsafe fn from_float(f: f64) -> Option<Self> {
                if !f.is_finite() {
                    return None;
                }

                // To ensure to_int_unchecked succeeds, we need to make sure
                let upper_bound = (i128::MAX - 1) as f64;
                let lower_bound = (i128::MIN + 1) as f64;

                let try_cast_to_int = |x: f64| -> Option<i128> {
                    if (x > lower_bound) && (x < upper_bound) {
                        Some(x.to_int_unchecked())
                    } else {
                        None
                    }
                };

                // If F is an integer 'I', just return frac![I, 1]
                if f.fract().is_zero() {
                    let i = try_cast_to_int(f)?;
                    return Some(frac![i, 1]);
                }

                // The integer and fractional parts of the float (the parts before and after the decimal point)
                let integer = f.trunc();
                let numerator: i128 = try_cast_to_int(integer)?;
                let to_add = Self::float_less_than_one_to_fraction(f.fract())?;

                let ans = frac![numerator, 1] + to_add;
                Some(ans)
            }
        }

        // Fraction -> f32
        // The reason we use Into is because converting Fractions into Floats is trivial, whereas converting Floats to Fractions can sometimes fail, like if the Float is Infinity or NaN.
        #[allow(clippy::from_over_into)]
        impl<T: Number + Into<f32>> Into<f32> for Fraction<T> {
            fn into(self) -> f32 {
                self.numerator.into() / self.denominator.into()
            }
        }

        // Fraction -> f64
        #[allow(clippy::from_over_into)]
        impl<T: Number + Into<f64>> Into<f64> for Fraction<T> {
            fn into(self) -> f64 {
                self.numerator.into() / self.denominator.into()
            }
        }
    }
}
/// Standard math operators like + - * / pow
pub mod standard_ops {
    use crate::prelude::*;

    use num::{One, Zero};
    use num_traits::Pow;

    use std::{
        iter::{Product, Sum},
        ops::{Add, Div, Mul, Neg, Sub},
    };

    // Implements Negation for Fraction<T> where T is a signed integer
    impl<T> Neg for Fraction<T>
    where
        T: Number + Neg<Output = T>,
    {
        type Output = Self;

        fn neg(self) -> Self::Output {
            frac![-self.numerator, self.denominator]
        }
    }

    impl<T: Number> Add for Fraction<T> {
        type Output = Self;

        fn add(self, other: Self) -> Self::Output {
            frac![
                (self.numerator * other.denominator) + (self.denominator * other.numerator),
                self.denominator * other.denominator
            ]
        }
    }

    impl<T: Number> Sub for Fraction<T> {
        type Output = Self;

        fn sub(self, other: Self) -> Self::Output {
            frac![
                (self.numerator * other.denominator) - (self.denominator * other.numerator),
                (self.denominator * other.denominator)
            ]
        }
    }

    impl<T: Number> Mul for Fraction<T> {
        type Output = Self;
        fn mul(self, other: Self) -> Self::Output {
            frac![
                self.numerator * other.numerator,
                self.denominator * other.denominator
            ]
        }
    }

    impl<T: Number> Div for Fraction<T> {
        type Output = Self;
        fn div(self, other: Self) -> Self::Output {
            if other.is_zero() {
                panic!("Division by a Fraction equal to zero is disallowed.");
            }
            frac![
                self.numerator * other.denominator,
                self.denominator * other.numerator
            ]
        }
    }

    impl<T: Number> Pow<u32> for Fraction<T> {
        type Output = Self;
        fn pow(self, rhs: u32) -> Self::Output {
            // This is a more compact version of 'exponentiation by squaring',
            // which is faster than just repeated multiplication.
            (0..32)
                .rev()
                .map(|x| rhs & 1 << x > 0)
                .fold(Self::one(), |acc, digit| {
                    if digit { acc * acc * self } else { acc * acc }.simplest_form()
                })
        }
    }

    // Calculates the Sum of some Iterator of Fractions.
    impl<T: Number> Sum for Fraction<T> {
        fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
            iter.reduce(|a, b| a + b).unwrap_or_else(Fraction::zero)
        }
    }

    impl<T: Number> Product for Fraction<T> {
        fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
            iter.reduce(|a, b| a * b).unwrap_or_else(Fraction::one)
        }
    }
}

/// Assignment Operators like `+=`, `-=`, '*=', `/=`, etc.
pub mod assignment_ops {
    use crate::prelude::*;
    use std::ops::{AddAssign, DivAssign, MulAssign, SubAssign};

    impl<T> AddAssign for Fraction<T>
    where
        T: Number,
    {
        fn add_assign(&mut self, rhs: Self) {
            *self = *self + rhs;
        }
    }

    impl<T> SubAssign for Fraction<T>
    where
        T: Number,
    {
        fn sub_assign(&mut self, rhs: Self) {
            *self = *self - rhs;
        }
    }

    impl<T> MulAssign for Fraction<T>
    where
        T: Number,
    {
        fn mul_assign(&mut self, rhs: Self) {
            *self = *self * rhs;
        }
    }

    impl<T> DivAssign for Fraction<T>
    where
        T: Number,
    {
        fn div_assign(&mut self, rhs: Self) {
            *self = *self / rhs;
        }
    }
}

/// Checked versions of operators like `+` and `-`
pub mod checked_ops {
    use crate::prelude::*;
    use num::{CheckedAdd, CheckedDiv, CheckedMul, CheckedSub};

    impl<T> CheckedAdd for Fraction<T>
    where
        T: Number + CheckedMul + CheckedAdd,
    {
        fn checked_add(&self, v: &Self) -> Option<Self> {
            // Calculate both halves of the numerator, overflows immediately return None
            let numerator_left = self.numerator.checked_mul(&v.denominator);
            let numerator_right = self.denominator.checked_mul(&v.numerator);

            // Calculate numerator and denominator, any overflows immediately return None
            let numerator = numerator_left?.checked_add(&numerator_right?)?;
            let denominator = self.denominator.checked_mul(&v.denominator)?;

            Some(frac![numerator, denominator])
        }
    }

    impl<T> CheckedSub for Fraction<T>
    where
        T: Number + CheckedMul + CheckedSub,
    {
        fn checked_sub(&self, v: &Self) -> Option<Self> {
            // Calculate both halves of the numerator, overflows immediately return None
            let numerator_left = self.numerator.checked_mul(&v.denominator);
            let numerator_right = self.denominator.checked_mul(&v.numerator);

            // Calculate numerator and denominator, any overflows immediately return None
            let numerator = numerator_left?.checked_sub(&numerator_right?)?;
            let denominator = self.denominator.checked_mul(&v.denominator)?;

            Some(frac![numerator, denominator])
        }
    }

    impl<T> CheckedMul for Fraction<T>
    where
        T: Number + CheckedMul,
    {
        fn checked_mul(&self, v: &Self) -> Option<Self> {
            let numerator = self.numerator.checked_mul(&v.numerator)?;
            let denominator = self.denominator.checked_mul(&v.denominator)?;
            Some(frac![numerator, denominator])
        }
    }

    impl<T> CheckedDiv for Fraction<T>
    where
        T: Number + CheckedMul,
    {
        fn checked_div(&self, v: &Self) -> Option<Self> {
            let numerator = self.numerator.checked_mul(&v.denominator)?;
            let denominator = self.denominator.checked_mul(&v.numerator)?;
            Some(frac![numerator, denominator])
        }
    }
}

/// Unchecked versions of operators like `+` and `-`. USE WITH CAUTION.
pub mod unchecked_ops {}

/// Implements variants of math operations that saturate at the bounds of a Fraction's type.
pub mod saturating_ops {
    use crate::prelude::*;
    use num::Zero;
    use num::{CheckedAdd, CheckedMul};
    use num_traits::SaturatingAdd;

    impl<T> SaturatingAdd for Fraction<T>
    where
        T: Number + CheckedAdd + CheckedMul,
    {
        fn saturating_add(&self, v: &Self) -> Self {
            // NO UNDERFLOW / OVERFLOW
            if let Some(ans) = (*self).checked_add(v) {
                ans
            }
            // OVERFLOW
            else if self < &Self::zero() || v >= &Self::zero() {
                // Largest possible Fraction<T>
                Fraction::new(T::max_value(), T::one())

            // UNDERFLOW
            } else {
                // Smallest possible Fraction<T>
                Fraction::new(T::min_value(), T::one())
            }
        }
    }
}
