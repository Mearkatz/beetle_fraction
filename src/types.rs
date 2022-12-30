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

/// Operations involving Fractions that return `Result`'s will return one of these variants as an `Err`
#[derive(Debug, Copy, Clone)]
pub enum FractionErrors {
    /// Denotes that a Fraction was created whose denominator was zero, and thus considered an error in its context.
    /// This isn't very useful right now.
    ImpliedDivisionByZero,

    /// Represents the failure of an operation when the `numerator` of the fraction overflows
    NumeratorOverflow,

    /// Represents the failure of an operation when the `denominator` of the fraction overflows
    DenominatorOverflow,

    /// Used to denote when casting a string as a Fraction failed
    UnableToParseString,

    /// Trying to cast a f64 containing either infinity to a Fraction returns this Error.
    /// Infinity cannot, to my knowledge, be represented as the ratio of two integers.
    InfinityIsNotARatio,

    /// Trying to cast an f64's whole number part to an integer sometimes fails if that integer part is too large
    WholeNumberPartOfFloatWasTooLargeToParse,

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
        use crate::{frac, int, types::Fraction, Number};
        use num::traits::{CheckedAdd, CheckedSub};

        // (Try) f64 -> Fraction<i128>
        impl TryFrom<f64> for Fraction<i128> {
            type Error = crate::types::FractionErrors;

            fn try_from(f: f64) -> Result<Self, Self::Error> {
                // If Float isn't a number, It cannot be converted to a Fraction
                if !f.is_finite() {
                    return Err(Self::Error::InfinityIsNotARatio);
                }
                // If Float is an integer, just return that integer as a Fraction
                // It's an easy conversion
                if (f.fract() == 0.) || (f.fract() == -0.) {
                    return Ok(int!(0));
                } else if f.fract() == -0. {
                    return Ok(-int![0]);
                }

                let binding: String = f.to_string();
                let split_by_decimal_point: Vec<&str> = binding.split('.').collect();
                // The integer part of the float is everything left of the decimal point
                // If conversion to integer type T isn't successful, return an Error
                let integer: i128 = if let Ok(x) = split_by_decimal_point[0].parse() {
                    x
                } else {
                    return Err(Self::Error::WholeNumberPartOfFloatWasTooLargeToParse);
                };

                // - The fraction part of the float is everything that comes to the right of the decimal point
                // - We need to store it as a string first to prevent a warning/error
                // - Convert integer and fractional from strings into Vectors of digits (u8's)
                let fractional: Vec<u8> = split_by_decimal_point[1]
                    .to_string()
                    .chars()
                    .map(|x: char| x.to_string().parse::<u8>().unwrap())
                    .collect();

                let mut result: Fraction<i128> = int!(integer);

                /*
                1. Cast every digit in the fraction part as u128
                2. Iterate the fraction part
                3. Turn every digit into its fraction representation
                4. Add all those fractions together

                Ex:
                (1.25) => 1 + (2/10) + (5/100)
                (-1.25) => -1 - (2/10) - (5/100)
                */
                for (index, digit) in fractional.into_iter().map(i128::from).enumerate() {
                    // Add (1 / (10 ** power)) to the current total
                    let power: u32 = match (index + 1).try_into() {
                        Ok(n) => n,
                        Err(_) => {
                            return Err(Self::Error::FailureToParseFloat);
                        }
                    };
                    let power_ten = 10_i128.pow(power);
                    if f.is_sign_positive() {
                        result = match result.checked_add(&frac![digit, power_ten]) {
                            Some(n) => n,
                            None => {
                                return Err(Self::Error::FailureToParseFloat);
                            }
                        };
                    } else {
                        result = match result.checked_sub(&frac![digit, power_ten]) {
                            Some(n) => n,
                            None => {
                                return Err(Self::Error::FailureToParseFloat);
                            }
                        };
                    }
                    result.simplify();
                }

                Ok(result)
            }
        }

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
