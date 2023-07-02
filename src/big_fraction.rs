//! Big-Fraction type & its trait implementations

use crate::traits::{IsFraction, MakeMe, Mediant, Simplify};
use num::BigInt;
use num_traits::{One, Zero};

/// A fraction (x ÷ y) represented by two `BigInt`s.
///
/// Note:
/// Unlike `Fraction`,
/// this type can represent arbitrarily large fractions without ever overflowing
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct BigFraction {
    /// Top half of the fraction    
    pub numerator: BigInt,
    /// Bottom half of the fraction
    pub denominator: BigInt,
}

impl MakeMe<BigInt> for BigFraction {
    fn new(numerator: BigInt, denominator: BigInt) -> Self {
        Self {
            numerator,
            denominator,
        }
    }
    fn checked_new(numerator: BigInt, denominator: BigInt) -> Option<Self> {
        if denominator.is_zero() {
            None
        } else {
            Some(Self::new(numerator, denominator))
        }
    }
}

impl IsFraction<BigInt> for BigFraction {
    fn numerator(&self) -> BigInt {
        self.numerator.clone()
    }

    fn set_numerator(&mut self, n: BigInt) {
        self.numerator = n;
    }

    fn denominator(&self) -> BigInt {
        self.denominator.clone()
    }

    fn set_denominator(&mut self, n: BigInt) {
        self.numerator = n;
    }

    fn numerator_ref(&self) -> &BigInt {
        &self.numerator
    }

    fn denominator_ref(&self) -> &BigInt {
        &self.denominator
    }
}

impl Mediant for BigFraction {
    fn mediant(&self, rhs: &Self) -> Self {
        Self::new(
            self.numerator() + rhs.numerator(),
            self.denominator() + rhs.denominator(),
        )
    }
}

impl Simplify<BigInt> for BigFraction {}

impl One for BigFraction {
    fn one() -> Self {
        Self {
            numerator: BigInt::one(),
            denominator: BigInt::one(),
        }
    }

    fn is_one(&self) -> bool {
        // Numerator and denominator are the same
        // Denominator must not be zero, since division by zero is undefined
        (self.numerator == self.denominator) && (!self.denominator.is_zero())
    }
}

impl Zero for BigFraction {
    fn zero() -> Self {
        Self {
            numerator: BigInt::zero(),
            denominator: BigInt::one(),
        }
    }

    fn is_zero(&self) -> bool {
        self.numerator.is_zero()
    }
}

impl Default for BigFraction {
    fn default() -> Self {
        Self::one()
    }
}

impl std::fmt::Display for BigFraction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} / {}", self.numerator_ref(), self.denominator_ref())
    }
}

impl PartialOrd for BigFraction {
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
        use num::BigInt;

        use crate::{big_fraction::BigFraction, bigfrac};

        // TUPLE -> Fraction
        impl From<(BigInt, BigInt)> for BigFraction {
            fn from(value: (BigInt, BigInt)) -> Self {
                bigfrac![value.0, value.1]
            }
        }

        // Slice -> Fraction
        impl From<[BigInt; 2]> for BigFraction {
            fn from(arr: [BigInt; 2]) -> Self {
                let [a, b] = arr;
                bigfrac![a, b]
            }
        }
    }

    /// Conversions between Fractions and Unit types (u8, i8, u32, etc.)
    pub mod units {
        use digitize::FloatDigits;
        use num::{bigint::Sign, BigInt};
        use num_traits::{One, ToPrimitive};

        use crate::{
            big_fraction::BigFraction,
            traits::{IsFraction, MakeMe},
        };
        use floating_cat::{CatFloat::*, Category};
        use std::fmt::Display;

        #[derive(Debug)]
        #[allow(dead_code)]
        enum FloatToBigFractionError {
            FloatIsInfinte(f64),
            FloatIsNan(f64),
        }

        impl Display for FloatToBigFractionError {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                match self {
                    FloatToBigFractionError::FloatIsInfinte(x) => {
                        write!(f, "Error: {x} is Positive or Negative Infinity")
                    }
                    FloatToBigFractionError::FloatIsNan(x) => {
                        write!(f, "Error: {x} is Positive or Negative NaN")
                    }
                }
            }
        }

        impl std::error::Error for FloatToBigFractionError {}

        impl BigFraction {
            /// Attempts to convert an `f64` to a `BigFraction`
            /// # Safety
            /// To my knowledge there are no safety issues.
            /// I've tested this with random floats in the range `i128::MIN..i128::MAX` with no issues.
            /// I've tested this with NaN and Infinity with no issues.
            /// This is only unsafe for simplicty and performance reasons, I'll probably make it safe later.
            pub unsafe fn from_f64(f: f64) -> Option<Self> {
                /// Attempts to convert an f64 < 1 into a Fraction.
                /// This does not check that the f64 is actually less than 1.0
                /// If an f64 greater than 1 is passed to this function, you will receive an incorrect Fraction as a result, use from_float instead.
                /// # Safety
                /// I've not done extensive testing on this besides with intended inputs.            
                pub unsafe fn float_less_than_one_to_fraction(f: f64) -> BigFraction {
                    debug_assert!((f > 0.) && (f < 1.));

                    let number_of_digits: i32 = f.digits_left_of_dot().len() as i32;
                    let power_of_ten: f64 = 10f64.powi(number_of_digits);
                    let ans: BigInt = integer_like_float_to_bigint(f * power_of_ten);

                    BigFraction::new(ans, integer_like_float_to_bigint(power_of_ten))
                }

                fn integer_like_float_to_bigint(x: f64) -> BigInt {
                    // Debugging: Make sure Infinity or Nan aren't passed to this function
                    debug_assert!(!x.category().is_infinity());
                    debug_assert!(!x.category().is_nan());
                    let sign = if x.is_sign_positive() {
                        Sign::Plus
                    } else {
                        Sign::Minus
                    };
                    let digits = x.digits_left_of_dot();
                    BigInt::new(sign, digits.into())
                }

                let integer_like_float_to_fraction = |ilf: f64| -> Self {
                    BigFraction::new(integer_like_float_to_bigint(ilf), One::one())
                };

                match f.category() {
                    // Integer-like (1.0, 1000.0, -0.0, etc.)
                    IntegerLike(integer) => Some(integer_like_float_to_fraction(integer)),

                    // Fraction-like (0.5, 0.1, -0.333, etc)
                    FractionLike(fraction) => Some(float_less_than_one_to_fraction(fraction)),

                    // Float-like (1.5, -2.6, etc)
                    IntegerAndFractionalPart(integer, fraction) => Some(
                        integer_like_float_to_fraction(integer)
                            + float_less_than_one_to_fraction(fraction),
                    ),
                    Nan | Infinity => None,
                }
            }

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
    use num::{One, Zero};
    use num_traits::Pow;

    use std::{
        iter::{Product, Sum},
        ops::{Add, Div, Mul, Neg, Sub},
    };

    use crate::{
        big_fraction::BigFraction,
        traits::{IsFraction, MakeMe},
    };

    // Implements Negation for Fraction<T> where T is a signed integer
    impl Neg for BigFraction {
        type Output = Self;

        fn neg(self) -> Self::Output {
            Self::new(-self.numerator(), self.denominator())
        }
    }

    impl Add for BigFraction {
        type Output = Self;

        fn add(self, other: Self) -> Self::Output {
            Self::new(
                (self.numerator() * other.denominator()) + (self.denominator() * other.numerator()),
                self.denominator() * other.denominator(),
            )
        }
    }

    impl Sub for BigFraction {
        type Output = Self;

        fn sub(self, other: Self) -> Self::Output {
            Self::new(
                (self.numerator() * other.denominator()) - (self.denominator() * other.numerator()),
                self.denominator() * other.denominator(),
            )
        }
    }

    impl Mul for BigFraction {
        type Output = Self;
        fn mul(self, other: Self) -> Self::Output {
            Self::new(
                self.numerator() * other.numerator(),
                self.denominator() * other.denominator(),
            )
        }
    }

    impl Div for BigFraction {
        type Output = Self;

        fn div(self, other: Self) -> Self::Output {
            if other.is_zero() {
                panic!("Division by a Fraction equal to zero is disallowed.");
            }
            Self::new(
                self.numerator() * other.denominator(),
                self.denominator() * other.numerator(),
            )
        }
    }

    impl Pow<u32> for BigFraction {
        type Output = Self;
        fn pow(self, rhs: u32) -> Self::Output {
            // This is a more compact version of 'exponentiation by squaring',
            // which is faster than just repeated multiplication.
            (0..32)
                .rev()
                .map(|x| rhs & 1 << x > 0)
                .fold(Self::one(), |acc, digit| {
                    if digit {
                        acc.clone() * acc * self.clone()
                    } else {
                        acc.clone() * acc
                    }
                })
        }
    }

    impl Sum for BigFraction {
        fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
            iter.reduce(|a, b| a + b).unwrap_or_else(Self::zero)
        }
    }

    impl Product for BigFraction {
        fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
            iter.reduce(|a, b| a * b).unwrap_or_else(Self::one)
        }
    }
}

/// Assignment Operators like `+=`, `-=`, '*=', `/=`, etc.
pub mod assignment_ops {
    use crate::big_fraction::BigFraction;
    use std::ops::{AddAssign, DivAssign, MulAssign, SubAssign};

    impl AddAssign for BigFraction {
        fn add_assign(&mut self, rhs: Self) {
            *self = self.clone() + rhs
        }
    }

    impl SubAssign for BigFraction {
        fn sub_assign(&mut self, rhs: Self) {
            *self = self.clone() - rhs
        }
    }

    impl MulAssign for BigFraction {
        fn mul_assign(&mut self, rhs: Self) {
            *self = self.clone() * rhs
        }
    }

    impl DivAssign for BigFraction {
        fn div_assign(&mut self, rhs: Self) {
            *self = self.clone() / rhs
        }
    }
}
