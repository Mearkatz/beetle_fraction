//! Contains operations and their variants (Addition, Checked_Addition, etc.)

/// Contains implementations of common math operations like Addition & Subtraction for Fractions
pub mod common {
    use crate::{frac, Fraction, Number};
    use num::{One, Zero};
    use std::{
        iter::{Product, Sum},
        ops::{Add, Div, Mul, Neg, Sub},
    };

    // Implements Negation for Fraction<T> where T is a signed integer
    impl<T: Number + Neg<Output = T>> Neg for Fraction<T> {
        type Output = Self;

        fn neg(self) -> Self::Output {
            frac![-self.x, self.y]
        }
    }

    impl<T: Number> Add for Fraction<T> {
        type Output = Self;

        fn add(self, other: Self) -> Self::Output {
            frac![(self.x * other.y) + (self.y * other.x), self.y * other.y]
        }
    }

    impl<T: Number> Sub for Fraction<T> {
        type Output = Self;

        fn sub(self, other: Self) -> Self::Output {
            frac![(self.x * other.y) - (self.y * other.x), (self.y * other.y)]
        }
    }

    impl<T: Number> Mul for Fraction<T> {
        type Output = Self;
        fn mul(self, other: Self) -> Self::Output {
            frac![self.x * other.x, self.y * other.y]
        }
    }

    impl<T: Number> Div for Fraction<T> {
        type Output = Self;
        fn div(self, other: Self) -> Self::Output {
            if other.is_zero() {
                panic!("Division by a Fraction equal to zero is disallowed.");
            }
            frac![self.x * other.y, self.y * other.x]
        }
    }

    // Misc. Math functions
    impl<T: Number> Fraction<T> {
        /// # Exponentiation function
        /// Raises `self` to the power of `n`
        ///
        /// # Examples
        ///
        /// ```
        /// use beetle_fraction::ops::common::Fraction;
        ///
        /// let fraction = frac![2, 1];
        /// assert_eq!(fraction.pow(3), frac![8, 1]);
        /// ```
        pub fn pow(&self, n: isize) -> Self {
            // Exponentation by repeated multiplication.
            // There are faster ways, but this works for now.
            let partial_result: Fraction<T> =
                { std::iter::repeat(*self).take(n.unsigned_abs()).product() };

            // A ^ -b == 1 / (a ^ b)
            match n > 0 {
                true => partial_result,
                false => partial_result.reciprocal(),
            }
        }

        /// Returns the reciprocal of a fraction, by swapping its numerator and denominator        
        ///
        /// # Examples
        ///
        /// ```
        /// use beetle_fraction::ops::common::Fraction;
        ///
        /// let fraction = frac[1, 2];
        /// assert_eq!(fraction.reciprocal(), frac![2, 1]);
        /// ```
        pub fn reciprocal(&self) -> Self {
            Self {
                x: self.y,
                y: self.x,
            }
        }

        /// Identical to reciprocal
        pub fn flip(&self) -> Self {
            frac![self.y, self.x]
        }

        /// Operation that adds
        pub fn mediant(&self, other: &Self) -> Self {
            frac![self.x + other.x, self.y + other.y]
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

pub mod assignment {
    //! # Assignment Operations
    //!
    //! These are versions of the normal operations whose result is not returned, but instead set as the value of the object they're called with.
    //! A good example of this is the `+=` operator in most programming languages
    //! This is referred to here as `AddAssign`.

    use std::ops::{AddAssign, DivAssign, MulAssign, SubAssign};

    use crate::{Fraction, Number};

    impl<T: Number> AddAssign for Fraction<T> {
        fn add_assign(&mut self, rhs: Self) {
            *self = *self + rhs;
        }
    }

    impl<T: Number> SubAssign for Fraction<T> {
        fn sub_assign(&mut self, rhs: Self) {
            *self = *self - rhs;
        }
    }

    impl<T: Number> MulAssign for Fraction<T> {
        fn mul_assign(&mut self, rhs: Self) {
            *self = *self * rhs;
        }
    }

    impl<T: Number> DivAssign for Fraction<T> {
        fn div_assign(&mut self, rhs: Self) {
            *self = *self / rhs;
        }
    }
}

pub mod checked {
    // use std::ops::{
    //     Neg,
    //     Add, Sub, Mul, Div, Rem,
    //     AddAssign, SubAssign, MulAssign, DivAssign, RemAssign
    // };
    use crate::{frac, Fraction, Number};
    use num::{CheckedAdd, CheckedDiv, CheckedMul, CheckedSub};

    impl<T: Number + CheckedMul + CheckedAdd> CheckedAdd for Fraction<T> {
        fn checked_add(&self, v: &Self) -> Option<Self> {
            // Calculate both halves of the numerator, overflows immediately return None
            let numerator_left = self.x.checked_mul(&v.y);
            let numerator_right = self.y.checked_mul(&v.x);

            // Calculate numerator and denominator, any overflows immediately return None
            let numerator = numerator_left?.checked_add(&numerator_right?)?;
            let denominator = self.y.checked_mul(&v.y)?;

            Some(frac![numerator, denominator])
        }
    }

    impl<T: Number + CheckedMul + CheckedSub> CheckedSub for Fraction<T> {
        fn checked_sub(&self, v: &Self) -> Option<Self> {
            // Calculate both halves of the numerator, overflows immediately return None
            let numerator_left = self.x.checked_mul(&v.y);
            let numerator_right = self.y.checked_mul(&v.x);

            // Calculate numerator and denominator, any overflows immediately return None
            let numerator = numerator_left?.checked_sub(&numerator_right?)?;
            let denominator = self.y.checked_mul(&v.y)?;

            Some(frac![numerator, denominator])
        }
    }

    impl<T: Number + CheckedMul> CheckedMul for Fraction<T> {
        fn checked_mul(&self, v: &Self) -> Option<Self> {
            let numerator = self.x.checked_mul(&v.x)?;
            let denominator = self.y.checked_mul(&v.y)?;
            Some(frac![numerator, denominator])
        }
    }

    impl<T: Number + CheckedMul> CheckedDiv for Fraction<T> {
        fn checked_div(&self, v: &Self) -> Option<Self> {
            let numerator = self.x.checked_mul(&v.y)?;
            let denominator = self.y.checked_mul(&v.x)?;
            Some(frac![numerator, denominator])
        }
    }
}

pub mod unchecked {}

/// Implements variants of math operations that saturate at the bounds of a Fraction's type.
pub mod saturating {
    // use crate::{Fraction, Number};
    // use num::traits::SaturatingAdd;

    // impl<T: Number> SaturatingAdd for Fraction<T> {
    //     fn saturating_add(&self, v: &Self) -> Self {
    //         // Get the min & max value for type T
    //         let smallest = T::min_value();
    //         let biggest = T::max_value();

    //         let decreasing = (self > 0) && ();
    //     }
    // }
}

/// Implements the comparison operators > < >= <= == != , as well as PartialOrd for Fraction
pub mod comparisons {
    use crate::{Fraction, Number};
    // use num::{integer::lcm, Zero};
    use std::cmp::{PartialEq, PartialOrd};

    impl<T: Number> PartialEq for Fraction<T> {
        fn eq(&self, other: &Self) -> bool {
            // let e = lcm(self.y, other.y);
            // (e / self.y) == (e / other.y)

            // Let's just return whether their difference is zero
            // (*self - *other).is_zero()
            (self.x * other.y) == (self.y * other.x)
        }
    }

    impl<T: Number> PartialOrd for Fraction<T> {
        fn gt(&self, other: &Self) -> bool {
            (self.x * other.y) > (self.y * other.x)
        }

        fn ge(&self, other: &Self) -> bool {
            (self.x * other.y) >= (self.y * other.x)
        }

        fn le(&self, other: &Self) -> bool {
            (self.x * other.y) <= (self.y * other.x)
        }

        fn lt(&self, other: &Self) -> bool {
            (self.x * other.y) < (self.y * other.x)
        }

        fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
            use std::cmp::Ordering;
            if self == other {
                return Some(Ordering::Equal);
            } else if self > other {
                return Some(Ordering::Greater);
            } else if self < other {
                return Some(Ordering::Less);
            }
            None
        }
    }
}
