//! Fraction type & its trait implementations

use num_traits::{One, Zero};

use crate::prelude::*;
use crate::traits::{IsFraction, MakeMe, Mediant};

/// A fraction (x ÷ y) represented by two primitive integers.
#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub struct Fraction<T: Number> {
    /// Top half of the fraction    
    pub numerator: T,
    /// Bottom half of the fraction.
    pub denominator: T,
}

impl<T: Number> MakeMe<T> for Fraction<T> {
    fn new(numerator: T, denominator: T) -> Self {
        Self {
            numerator,
            denominator,
        }
    }

    fn checked_new(numerator: T, denominator: T) -> Option<Self> {
        if denominator.is_zero() {
            None
        } else {
            Some(Self::new(numerator, denominator))
        }
    }
}

impl<T: Number> IsFraction<T> for Fraction<T> {
    fn numerator(&self) -> T {
        self.numerator
    }

    fn set_numerator(&mut self, n: T) {
        self.numerator = n;
    }

    fn denominator(&self) -> T {
        self.denominator
    }

    fn set_denominator(&mut self, n: T) {
        self.denominator = n;
    }

    fn numerator_ref(&self) -> &T {
        &self.numerator
    }

    fn denominator_ref(&self) -> &T {
        &self.denominator
    }
}

impl<T: Number> Mediant for Fraction<T> {
    fn mediant(&self, rhs: &Self) -> Self {
        Self::new(
            self.numerator() + rhs.numerator(),
            self.denominator() + rhs.denominator(),
        )
    }
}

impl<T: Number> Simplify<T> for Fraction<T> {}

impl<T: Number> One for Fraction<T> {
    fn one() -> Self {
        Self {
            numerator: T::one(),
            denominator: T::one(),
        }
    }

    fn is_one(&self) -> bool {
        // Numerator and denominator are the same
        // Denominator must not be zero, since division by zero is undefined
        (self.numerator == self.denominator) && (!self.denominator.is_zero())
    }
}

impl<T: Number> Zero for Fraction<T> {
    fn zero() -> Self {
        Self {
            numerator: T::zero(),
            denominator: T::one(),
        }
    }

    fn is_zero(&self) -> bool {
        self.numerator.is_zero()
    }
}

impl<T: Number> Default for Fraction<T> {
    fn default() -> Self {
        Self::one()
    }
}

impl<T: Number + std::fmt::Display> std::fmt::Display for Fraction<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} / {}", self.numerator_ref(), self.denominator_ref())
    }
}

impl<T: Number> PartialOrd for Fraction<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        let a = self.numerator() * other.denominator();
        let b = self.denominator() * other.numerator();
        a.partial_cmp(&b)
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
        use crate::{frac, int, prelude::*};
        use digitize::FloatDigits;
        use floating_cat::CatFloat::*;
        use floating_cat::*;
        use std::fmt::Display;

        impl<T: Number> From<T> for Fraction<T> {
            fn from(value: T) -> Self {
                Self {
                    numerator: value,
                    denominator: T::one(),
                }
            }
        }

        #[derive(Debug)]
        #[allow(dead_code)]
        enum FloatToFractionError {
            IsInfinte(f64),
            IsNan(f64),
            HasTooManyDigits(f64),
        }

        impl Display for FloatToFractionError {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                match &self {
                    FloatToFractionError::IsInfinte(x) => {
                        write!(f, "Error: {x} is Positive or Negative Infinity")
                    }
                    FloatToFractionError::IsNan(x) => {
                        write!(f, "Error: {x} is Positive or Negative NaN")
                    }
                    FloatToFractionError::HasTooManyDigits(x) => {
                        write!(f, "Error: {x} has too many digits")
                    }
                }
            }
        }

        impl std::error::Error for FloatToFractionError {}

        impl Fraction<i128> {
            /// Attempts to convert an `f64` to a `Fraction<i128>`
            /// # Safety
            /// To my knowledge there are no safety issues.
            /// I've tested this with random floats in the range `i128::MIN..i128::MAX` with no issues.
            /// I've tested this with NaN and Infinity with no issues.
            /// This is only unsafe for simplicty and performance reasons, I'll probably make it safe later.
            pub unsafe fn from_f64(f: f64) -> Option<Self> {
                // To ensure to_int_unchecked succeeds, we need to make sure
                let upper_bound = (i128::MAX - 1) as f64;
                let lower_bound = (i128::MIN + 1) as f64;

                /// Attempts to convert an f64 < 1 into a Fraction.
                /// This does not check that the f64 is actually less than 1.0
                /// If an f64 greater than 1 is passed to this function, you will receive an incorrect Fraction as a result, use from_float instead.
                /// # Safety
                /// I've not done extensive testing on this besides with intended inputs.            
                pub unsafe fn float_less_than_one_to_fraction(f: f64) -> Option<Fraction<i128>> {
                    debug_assert!((f.is_sign_positive()) && (f <= 1.));

                    // let number_of_digits: i32 = (f.to_string().len() - 2).try_into().ok()?;
                    let number_of_digits: i32 = f.digits_right_of_dot().len().try_into().ok()?;
                    let power_of_ten: f64 = 10f64.powi(number_of_digits);
                    let ans: i128 = (f * power_of_ten).to_int_unchecked();

                    let fract = frac![ans, power_of_ten.to_int_unchecked()];
                    Some(fract)
                }

                let try_cast_to_int = |x: f64| -> Option<i128> {
                    if x > lower_bound && x < upper_bound {
                        Some(x.to_int_unchecked())
                    } else {
                        None
                    }
                };

                let integer_like_float_to_fraction =
                    |ilf: f64| -> Option<Self> { try_cast_to_int(ilf).map(|x| int![x]) };

                match f.category() {
                    // Integer-like (1.0, 1000.0, -0.0, etc.)
                    IntegerLike(integer) => integer_like_float_to_fraction(integer),

                    // Fraction-like (0.5, 0.1, -0.333, etc)
                    FractionLike(fraction) => float_less_than_one_to_fraction(fraction),

                    // Float-like (1.5, -2.6, etc)
                    IntegerAndFractionalPart(integer, fraction) => Some(
                        integer_like_float_to_fraction(integer)?
                            + float_less_than_one_to_fraction(fraction)?,
                    ),
                    Nan | Infinity => None,
                }
            }
        }

        impl<T: Number + num::ToPrimitive> Fraction<T> {
            /// Returns the float that represents the result of `self.numerator / self.denominator`.
            /// If the numerator or denominator are too large to be cast as floats, this returns None.            
            pub fn as_f64(&self) -> Option<f64> {
                Some(self.numerator().to_f64()? / self.denominator().to_f64()?)
            }
        }
    }
}
/// Standard math operators like + - * / pow
pub mod standard_ops {
    use super::Fraction;
    use crate::traits::*;

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
            Self::new(-self.numerator, self.denominator)
        }
    }

    impl<T: Number> Add for Fraction<T> {
        type Output = Self;

        fn add(self, other: Self) -> Self::Output {
            Self::new(
                (self.numerator * other.denominator) + (self.denominator * other.numerator),
                self.denominator * other.denominator,
            )
        }
    }

    impl<T: Number> Sub for Fraction<T> {
        type Output = Self;

        fn sub(self, other: Self) -> Self::Output {
            Self::new(
                self.numerator * other.denominator - self.denominator * other.numerator,
                self.denominator * other.denominator,
            )
        }
    }

    impl<T: Number> Mul for Fraction<T> {
        type Output = Self;
        fn mul(self, other: Self) -> Self::Output {
            Self::new(
                self.numerator * other.numerator,
                self.denominator * other.denominator,
            )
        }
    }

    impl<T: Number> Div for Fraction<T> {
        type Output = Self;

        fn div(self, other: Self) -> Self::Output {
            if other.is_zero() {
                panic!("Division by a Fraction equal to zero is disallowed.");
            }
            Self::new(
                self.numerator * other.denominator,
                self.denominator * other.numerator,
            )
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

            Some(Self::new(numerator, denominator))
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

            Some(Self::new(numerator, denominator))
        }
    }

    impl<T> CheckedMul for Fraction<T>
    where
        T: Number + CheckedMul,
    {
        fn checked_mul(&self, v: &Self) -> Option<Self> {
            let numerator = self.numerator.checked_mul(&v.numerator)?;
            let denominator = self.denominator.checked_mul(&v.denominator)?;
            Some(Self::new(numerator, denominator))
        }
    }

    impl<T> CheckedDiv for Fraction<T>
    where
        T: Number + CheckedMul,
    {
        fn checked_div(&self, v: &Self) -> Option<Self> {
            let numerator = self.numerator.checked_mul(&v.denominator)?;
            let denominator = self.denominator.checked_mul(&v.numerator)?;
            Some(Self::new(numerator, denominator))
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
