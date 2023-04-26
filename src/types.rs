//! Types, Structs, and Type Conversions, and Non-Math-Related Impl blocks.

use crate::{frac, Number};
use num::integer::gcd;
use num::{One, Zero};
use std::fmt;

/// Stores a Fraction (x / y) as two distinct integers
#[derive(Default, Copy, Clone, Debug)]
pub struct Fraction<T: Number> {
    /// Top half of the fraction    
    pub numerator: T,
    /// Bottom half of the fraction.
    pub denominator: T,
}

/// Operations involving Fractions that return `Result`s will return one of these variants as an `Err`
#[derive(Debug, Copy, Clone)]
pub enum FractionErrors {
    /// Denotes that a Fraction was created whose denominator was zero, and thus considered an error in its context.    
    ImpliedDivisionByZero,

    /// Represents the failure of an operation when the `numerator` of the fraction overflows
    NumeratorOverflow,

    /// Represents the failure of an operation when the `denominator` of the fraction overflows
    DenominatorOverflow,

    /// Used to denote when casting a string as a Fraction failed
    UnableToParseString,

    /// Represents a failure to parse a Float in some misc. way
    FailureToParseFloat,
}

// One & Zero impls
impl<T: Number> One for Fraction<T> {
    fn is_one(&self) -> bool {
        // Numerator and denominator are the same
        // Denominator must not be zero, since division by zero is undefined
        (self.numerator == self.denominator) && (!self.denominator.is_zero())
    }

    fn one() -> Self {
        Self {
            numerator: T::one(),
            denominator: T::one(),
        }
    }

    fn set_one(&mut self) {
        *self = Fraction::one();
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
        *self = Fraction::zero();
    }
}

// Misc. Impls
// These are sets of functions that aren't an implementation of a trait
impl<T: Number> Fraction<T> {
    /// Creates a new Fraction
    ///
    /// # Examples
    /// ```
    /// # use beetle_fraction::types::Fraction;
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
    /// Safety Checks:
    /// - must be non-zero, to prevent implied division by zero
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// use beetle_fraction::types::Fraction;
    /// let bad_fraction = Fraction::checked_new(1, 0); // is the error variant, because of implied division by zero
    /// assert!(bad_fraction.is_err())
    ///
    /// ```
    pub fn checked_new(numerator: T, denominator: T) -> Result<Self, FractionErrors> {
        if denominator.is_zero() {
            Err(FractionErrors::ImpliedDivisionByZero)
        } else {
            Ok(Self {
                numerator,
                denominator,
            })
        }
    }

    /// Takes a reference to a fraction and returns it in simplest form
    ///
    /// # Examples
    ///
    /// ```
    /// use beetle_fraction::types::Fraction;
    ///
    /// let two_fourths = Fraction::new(2, 4);
    /// let one_half = Fraction::new(1, 2);
    /// assert_eq!(two_fourths.simplest_form(), one_half);
    /// ```
    pub fn simplest_form(&self) -> Self {
        let fac: T = gcd(self.numerator, self.denominator);
        frac![self.numerator / fac, self.denominator / fac]
    }

    /// Shorthand for `my_fraction = my_fraction.simplest_form();`
    ///
    /// # Examples
    /// ```
    /// # use beetle_fraction::{types::Fraction, frac};
    /// let mut half: Fraction<u8> = frac![50, 100];
    /// half.simplify();
    /// assert!((half.numerator == 1) && (half.denominator == 2));
    /// ```
    pub fn simplify(&mut self) {
        *self = self.simplest_form();
    }
}

impl<T: Number> fmt::Display for Fraction<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?} / {:?}", self.numerator, self.denominator)
    }
}

/// Functions to convert Into and From Fractions
pub mod conversions {
    /// Conversions between Fractions and Collections (like tuples)
    pub mod collections {
        use crate::{frac, types::Fraction, Number};

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

        use crate::{frac, types::Fraction, Number};

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
