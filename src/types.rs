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

/// Errors caused when trying to convert an f32/f64 to a Fraction<i128>.
/// Usually happen because the Float is too big or small, is NaN, or Infinity
pub enum FractionFromFloatError {
    /// Happens when f32/f64's infinities are casted as Fractions    
    InfinityIsNotARatio,

    /// Trying to cast an f64's whole number part to an integer sometimes fails if that integer part is too large
    WholeNumberPartOfFloatWasTooLargeToParse,

    /// Happens when checked_add or checked_sub return None
    Overflow,
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
    /// Conversions between Fractions and Collections (namely Tuples & Strings)
    pub mod collections {
        use crate::{frac, types::Fraction, Number};

        // TUPLE -> FRACTION
        impl<T: Number> From<(T, T)> for Fraction<T> {
            fn from(tup: (T, T)) -> Self {
                frac![tup.0, tup.1]
            }
        }
    }

    /// # Conversions between Fractions and Unit types (u8, i8, u32, etc.)
    pub mod units {

        use crate::{int, types::Fraction, Number};
        use nom::{bytes::complete::tag, IResult};

        /// Tries casting an f64 as an integer.
        /// Only returns f as an integer, if its fractional part is zero, and f is finite.
        /// The sign of the float is also returned
        fn try_cast_f64_as_i128(f: f64) -> Option<i128> {
            if f.is_finite() && (f.fract() == 0.) {
                Some(f as i128)
            } else {
                None
            }
        }

        fn split_on_dot(input: &str) -> IResult<&str, [&str; 2]> {
            let (before, after) = tag(".")(input)?;
            Ok(("", [before, after]))
        }

        fn f64_to_fraction(f: f64) -> Option<Fraction<i128>> {
            // Handle NaN & Infinity
            if !f.is_finite() {
                return None;
            }
            // Handle if `f` can be converted to an i128 without losing information
            // Essentially, `if f == ((f as i128) as f64)`, then we return `frac![f as i128]`
            if f == -0. {
                return Some(-int![0]);
            }
            if let Some(x) = try_cast_f64_as_i128(f) {
                return Some(int![x]);
            }

            let float_as_string = f.to_string();
            let (_, [integer_part, fraction_part_pre]) = split_on_dot(&float_as_string).ok()?;

            let integer_part: Fraction<i128> = int![integer_part.parse().ok()?];

            let len: u32 = fraction_part_pre.len().try_into().ok()?;
            let power_of_ten = 10_i128.checked_pow(len)?;
            let fraction_part =
                Fraction::new(fraction_part_pre.parse().ok()?, power_of_ten).simplest_form();

            Some(integer_part + fraction_part)
        }

        // // (Try) f64 -> Fraction<i128>
        // impl TryFrom<f64> for Fraction<i128> {
        //     type Error = crate::types::FractionFromFloatError;

        //     fn try_from(f: f64) -> Result<Self, Self::Error> {
        //         // If Float isn't a number, It cannot be converted to a Fraction
        //         if !f.is_finite() {
        //             return Err(Self::Error::InfinityIsNotARatio);
        //         }

        //         // Handle if `f` can be converted to an i128 without losing information
        //         // Essentially, `if f == ((f as i128) as f64)`, then we return `frac![f as i128]`
        //         if f == -0. {
        //             return Ok(frac![0, -1]);
        //         }
        //         if let Some(x) = try_cast_f64_as_i128(f) {
        //             return Ok(int![x]);
        //         }

        //         let binding: String = f.to_string();
        //         let mut split_by_decimal_point: Vec<&str> = Vec::with_capacity(2);
        //         split_by_decimal_point.extend(binding.split('.').take(2));

        //         // The integer part of the float is everything left of the decimal point
        //         // If conversion to integer type T isn't successful, return an Error
        //         let integer: i128 = if let Ok(x) = split_by_decimal_point[0].parse() {
        //             x
        //         } else {
        //             return Err(Self::Error::WholeNumberPartOfFloatWasTooLargeToParse);
        //         };

        //         // - The fraction part of the float is everything that comes to the right of the decimal point
        //         // - We need to store it as a string first to prevent a warning/error
        //         // - Convert integer and fractional from strings into Vectors of digits (u8's)
        //         let fractional: Vec<u8> = split_by_decimal_point[1]
        //             .to_string()
        //             .chars()
        //             .map(|x: char| x.to_string().parse::<u8>().unwrap())
        //             .collect();

        //         let mut result: Fraction<i128> = int!(integer);

        //         /*
        //         1. Cast every digit in the fraction part as u128
        //         2. Iterate the fraction part
        //         3. Turn every digit into its fraction representation
        //         4. Add all those fractions together

        //         Ex:
        //         (1.25) => 1 + (2/10) + (5/100)
        //         (-1.25) => -1 - (2/10) - (5/100)
        //         */
        //         for (index, digit) in fractional.into_iter().map(i128::from).enumerate() {
        //             // Add (1 / (10 ** power)) to the current total
        //             let Ok(power) = (index + 1).try_into() else {
        //                 return Err(Self::Error::FailureToParseFloat);
        //             };
        //             let power_ten = 10_i128.pow(power);
        //             if f.is_sign_positive() {
        //                 result = if let Some(n) = result.checked_add(&frac![digit, power_ten]) {
        //                     n
        //                 } else {
        //                     return Err(Self::Error::FailureToParseFloat);
        //                 };
        //             } else {
        //                 Some(result) = match result.checked_sub(&frac![digit, power_ten]) {
        //                     Some(n) => n,
        //                     None => {
        //                         return Err(Self::Error::FailureToParseFloat);
        //                     }
        //                 };
        //             }
        //             result.simplify();
        //         }

        //         Ok(result)
        //     }
        // }

        // Fraction -> f32
        impl<T: Number + Into<f32>> Into<f32> for Fraction<T> {
            fn into(self) -> f32 {
                self.numerator.into() / self.denominator.into()
            }
        }

        // Fraction -> f64
        impl<T: Number + Into<f64>> Into<f64> for Fraction<T> {
            fn into(self) -> f64 {
                self.numerator.into() / self.denominator.into()
            }
        }
    }
}
