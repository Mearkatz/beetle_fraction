//! Big-Fraction type & its trait implementations

/*
TODO:
- BIG_FRACTION STRUCT,
- Traits for Big Fraction:
    - One,
    - Zero,
    - Default,
    - Simply,
    - Mediant
    - Bounded,
    - Display,

- Modules:
    - Conversions,
    - Standard Ops,
    - Assignment Ops,
    - Checked Ops,
    - Unchecked Ops,
    - Saturating Ops,
    - Comparison Ops,
*/

use crate::traits::{Mediant, Reciprocal, Simplify};
use crate::types::FractionError;
use num::BigInt;
use num_traits::{One, Zero};

/// A fraction (x ÷ y) represented by two `BigInt`s.
///
/// Note:
/// Unlike `beetle_fraction::fraction::Fraction`, this Fraction can represent arbitrarily large Fractions without ever overflowing
#[derive(Debug, Clone)]
pub struct BigFraction {
    /// Top half of the fraction    
    pub numerator: BigInt,
    /// Bottom half of the fraction
    pub denominator: BigInt,
}

impl BigFraction {
    /// Produces a BigInt and returns it
    pub fn new(numerator: BigInt, denominator: BigInt) -> Self {
        Self {
            numerator,
            denominator,
        }
    }

    /// Produces a BigInt and returns it, but only if the denominator is non-zero.
    /// If the denominator equals zero, this implies division by zero, which is disallowed
    pub fn checked_new(numerator: BigInt, denominator: BigInt) -> Result<Self, FractionError> {
        if denominator.is_zero() {
            Err(FractionError::ImpliedDivisionByZero)
        } else {
            Ok(Self::new(numerator, denominator))
        }
    }
}

impl One for BigFraction {
    fn one() -> Self {
        let b = BigInt::one();
        Self::new(b.clone(), b)
    }

    fn set_one(&mut self) {
        *self = One::one();
    }

    fn is_one(&self) -> bool
    where
        Self: PartialEq,
    {
        *self == Self::one()
    }
}

impl Zero for BigFraction {
    fn zero() -> Self {
        let b = BigInt::one();
        Self::new(b.clone(), b)
    }

    fn set_zero(&mut self) {
        *self = Self::zero();
    }

    fn is_zero(&self) -> bool
    where
        Self: PartialEq,
    {
        *self == Self::zero()
    }
}

impl Reciprocal for BigFraction {
    fn reciprocal(&self) -> Self {
        Self::new(self.denominator.clone(), self.numerator.clone())
    }
}

impl Simplify for BigFraction {
    fn simplest_form(&self) -> Self {
        let fac: BigInt = num::integer::gcd(self.numerator.clone(), self.denominator.clone());
        Self::new(
            self.numerator.clone() / fac.clone(),
            self.denominator.clone() / fac,
        )
    }

    fn simplify(&mut self) {
        *self = self.simplest_form();
    }
}

impl Mediant for BigFraction {
    fn mediant(&self, rhs: &Self) -> Self {
        Self::new(
            self.numerator.clone() + rhs.numerator.clone(),
            self.denominator.clone() + rhs.denominator.clone(),
        )
    }
}

impl std::fmt::Display for BigFraction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?} / {:?}", self.numerator, self.denominator)
    }
}

impl Default for BigFraction {
    fn default() -> Self {
        Self::one()
    }
}

impl PartialEq for BigFraction {
    fn eq(&self, other: &Self) -> bool {
        (self.numerator == other.numerator) && (self.denominator == other.denominator)
    }
}

impl PartialOrd for BigFraction {
    fn gt(&self, other: &Self) -> bool {
        self.numerator.clone() * other.denominator.clone()
            > self.denominator.clone() * other.numerator.clone()
    }

    fn ge(&self, other: &Self) -> bool {
        self.numerator.clone() * other.denominator.clone()
            >= self.denominator.clone() * other.numerator.clone()
    }

    fn le(&self, other: &Self) -> bool {
        self.numerator.clone() * other.denominator.clone()
            <= self.denominator.clone() * other.numerator.clone()
    }

    fn lt(&self, other: &Self) -> bool {
        self.numerator.clone() * other.denominator.clone()
            < self.denominator.clone() * other.numerator.clone()
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

/// For converting `To` and `From` `BigFraction`s
pub mod conversions {}

/// Standard math operators like + - * / pow
pub mod standard_ops {
    use crate::traits::Simplify;

    use super::BigFraction;
    use num::{One, Zero};
    use num_traits::Pow;
    use std::{
        iter::{Product, Sum},
        ops::{Add, Div, Mul, Neg, Sub},
    };

    // Implements Negation for Fraction<T> where T is a signed integer
    impl Neg for BigFraction {
        type Output = Self;

        fn neg(self) -> Self::Output {
            Self::new(-self.numerator, self.denominator)
        }
    }

    impl Add for BigFraction {
        type Output = Self;

        fn add(self, other: Self) -> Self::Output {
            Self::new(
                self.numerator.clone() * other.denominator.clone()
                    + self.denominator.clone() * other.numerator.clone(),
                self.denominator * other.denominator,
            )
        }
    }

    impl Sub for BigFraction {
        type Output = Self;

        fn sub(self, other: Self) -> Self::Output {
            Self::new(
                self.numerator.clone() * other.denominator.clone()
                    - self.denominator.clone() * other.numerator.clone(),
                self.denominator * other.denominator,
            )
        }
    }

    impl Mul for BigFraction {
        type Output = Self;
        fn mul(self, other: Self) -> Self::Output {
            Self::new(
                self.numerator * other.numerator,
                self.denominator * other.denominator,
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
                self.numerator * other.denominator,
                self.denominator * other.numerator,
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
                        acc.pow(2) * self.clone()
                    } else {
                        acc.pow(2)
                    }
                    .simplest_form()
                })
        }
    }

    // Calculates the Sum of some Iterator of Fractions.
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
    use super::BigFraction;
    use std::ops::{AddAssign, DivAssign, MulAssign, SubAssign};

    impl AddAssign for BigFraction {
        fn add_assign(&mut self, rhs: Self) {
            *self = (*self).clone() + rhs;
        }
    }

    impl SubAssign for BigFraction {
        fn sub_assign(&mut self, rhs: Self) {
            *self = (*self).clone() - rhs;
        }
    }

    impl MulAssign for BigFraction {
        fn mul_assign(&mut self, rhs: Self) {
            *self = (*self).clone() * rhs;
        }
    }

    impl DivAssign for BigFraction {
        fn div_assign(&mut self, rhs: Self) {
            *self = (*self).clone() / rhs;
        }
    }
}

/// Checked versions of operators like `+` and `-`
pub mod checked_ops {
    use num::{CheckedAdd, CheckedDiv, CheckedMul, CheckedSub};

    use super::BigFraction;

    impl CheckedAdd for BigFraction {
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

    impl CheckedSub for BigFraction {
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

    impl CheckedMul for BigFraction {
        fn checked_mul(&self, v: &Self) -> Option<Self> {
            let numerator = self.numerator.checked_mul(&v.numerator)?;
            let denominator = self.denominator.checked_mul(&v.denominator)?;
            Some(Self::new(numerator, denominator))
        }
    }

    impl CheckedDiv for BigFraction {
        fn checked_div(&self, v: &Self) -> Option<Self> {
            let numerator = self.numerator.checked_mul(&v.denominator)?;
            let denominator = self.denominator.checked_mul(&v.numerator)?;
            Some(Self::new(numerator, denominator))
        }
    }
}
