//! Types, Structs, and Type Conversions, and Non-Math-Related Impl blocks.

use crate::Number;
use num::integer::gcd;
use num::{One, Zero};
use std::fmt;

/// Stores a Fraction (x / y)
#[derive(Default, Copy, Clone, Debug)]
pub struct Fraction<T: Number> {
    pub x: T,
    pub y: T,
}
pub enum FractionErrors {
    ImpliedDivisionByZero, // Occurs when Fraction::new is called with a `y` value of zero. (Does this actually matter ?)
    NumeratorOverflow,
    DenominatorOverflow,
}

// One & Zero impls
impl<T: Number> One for Fraction<T> {
    fn is_one(&self) -> bool {
        // Numerator and denominator are the same
        // Denominator must not be zero, since division by zero is undefined
        (self.x == self.y) && (!self.y.is_zero())
    }

    fn one() -> Self {
        Self {
            x: T::one(),
            y: T::one(),
        }
    }

    fn set_one(&mut self) {
        *self = Fraction::one();
    }
}

impl<T: Number> Zero for Fraction<T> {
    fn is_zero(&self) -> bool {
        self.x.is_zero()
    }

    fn zero() -> Self {
        Self {
            x: T::zero(),
            y: T::one(),
        }
    }

    fn set_zero(&mut self) {
        *self = Fraction::zero();
    }
}

// Misc. Impls
// These are sets of functions that aren't an implementation of a trait
impl<T: Number> Fraction<T> {
    /**
    Creates a new Fraction<T>
    # Examples
    ```
    use beetle_fraction::types::Fraction;
    let one_half = Fraction::new(1, 2); // represents (1 / 2)
    assert_eq!(one_half, Fraction {1, 2});
    ```
    */
    pub fn new(x: T, y: T) -> Self {
        Self { x, y }
    }

    /// Version of the `new` function with some extra safety checks
    ///
    /// Safety Checks:
    /// 1. y (denominator) must be non-zero, to prevent implied division by zero
    pub fn checked_new(x: T, y: T) -> Result<Self, FractionErrors> {
        if y.is_zero() {
            Err(FractionErrors::ImpliedDivisionByZero)
        } else {
            Ok(Self { x, y })
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
        let fac: T = gcd(self.x, self.y);
        Self {
            x: self.x / fac,
            y: self.y / fac,
        }
    }

    /// Shorthand for `my_fraction = my_fraction.simplest_form();`
    pub fn simplify(&mut self) {
        *self = self.simplest_form();
    }

    /// # Creates a Unit Fraction.
    /// A unit fraction always has a numerator of 1
    pub fn unit(y: T) -> Self {
        Self { x: T::one(), y }
    }
}

// Display impl
// Allows for printing any Fraction to the terminal in a readable way.
impl<T: Number> fmt::Display for Fraction<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?} / {:?}", self.x, self.y)
    }
}

/// # Type Conversions
/// Allows converting Fractions into other types and vice versa.
pub mod conversions {
    /// Conversions between Fractions and Collections (namely Tuples & Strings)
    pub mod collections {
        use crate::{frac, Fraction, Number};

        // TUPLE -> FRAC
        impl<T: Number> From<(T, T)> for Fraction<T> {
            fn from(tup: (T, T)) -> Self {
                frac![tup.0, tup.1]
            }
        }

        // FRAC -> TUPLE
        impl<T: Number> Into<(T, T)> for Fraction<T> {
            fn into(self) -> (T, T) {
                (self.x, self.y)
            }
        }

        // FRAC -> STRING (If T only implements Debug)
        // Purposefully removed:
        // Reason: to_string is given for free
        // impl<T: Number> Into<String> for Fraction<T> {
        //     fn into(self) -> String {
        //         format!("{:?} / {:?}", self.x, self.y)
        //     }
        // }
    }

    /// # Conversions between Fractions and Unit types (u8, i8, u32, etc.)
    pub mod units {

        use crate::{frac, int, Fraction, Number};

        // Number -> Frac
        // Purposefully removed.
        // Reason:
        // - int![x, y] is preferred
        // - we also don't want Into automatically generated, because:
        //      - All integers X can be turned into Fractions via int![X, 1],
        //      - Fractions F whose simplest form's denominators are not 1 cannot be converted to integers accurately
        //
        //
        // impl<T: Number> From<T> for Fraction<T> {
        //     fn from(val: T) -> Self {
        //         Fraction { x: val, y: T::one() }
        //     }
        // }

        /*
        FLOAT CONVERSION:
        (INTO AND FROM)
        */

        /// Converts an &f64 into a Fraction<i128>
        /// Because not all Floats can be represented as the ratio of two integers, this can fail.
        /// If this fails, it returns None
        /// This will only panic due to overflow.

        pub fn float_to_fraction(f: &f64) -> Option<Fraction<i128>> {
            // If Float isn't a number, It cannot be converted to a Fraction
            if !f.is_finite() {
                return None;
            }
            // If Float is an integer, just return that integer as a Fraction
            // It's an easy conversion
            if f.fract() == 0. {
                let float_as_integer = f.trunc() as i128;
                return Some(int![float_as_integer]);
            }

            // else if f == &0. {
            //     return Some(int![0])
            // }

            let binding: String = f.to_string();
            let split_by_decimal_point: Vec<&str> = binding.split('.').collect();
            // The integer part of the float is everything left of the decimal point
            // If conversion to integer type T isn't successful, return None
            // Also store whether the fraction is negative
            let integer: i128 = split_by_decimal_point[0].parse().ok()?;

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
                let power: u32 = (index + 1).try_into().ok()?;
                let power_ten = 10_i128.pow(power);
                if f > &0. {
                    result += frac![digit, power_ten];
                } else {
                    result -= frac![digit, power_ten];
                }
                result.simplify();
            }

            Some(result)
        }

        // Frac -> f32
        impl<T: Number + Into<f32>> Into<f32> for Fraction<T> {
            fn into(self) -> f32 {
                self.x.into() / self.y.into()
            }
        }

        // Frac -> f64
        impl<T: Number + Into<f64>> Into<f64> for Fraction<T> {
            fn into(self) -> f64 {
                self.x.into() / self.y.into()
            }
        }
    }
}
