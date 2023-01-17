//! Contains operations and their variants (Addition, Checked_Addition, etc.)

/// Common math operators like `+`, `-`, `*`, `/`, etc.
pub mod common {
    use crate::{frac, types::Fraction, Number};

    use num::{One, Zero};
    use num_traits::Pow;

    use std::{
        iter::{Product, Sum},
        ops::{Add, Div, Mul, Neg, Sub},
    };

    // Implements Negation for Fraction<T> where T is a signed integer
    impl<T: Number + Neg<Output = T>> Neg for Fraction<T> {
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
            (0..32)
                .rev()
                .map(|x| rhs & 1 << x > 0)
                .fold(Self::one(), |acc, digit| {if digit { acc * acc * self } else { acc * acc}}.simplest_form() )
        }
    }

    // MISC IMPL'S
    impl<T: Number> Fraction<T> {        
        /// Returns the reciprocal of a fraction, by swapping its numerator and denominator        
        ///
        /// # Examples
        ///
        /// ```        
        /// # use beetle_fraction::frac;
        /// # use beetle_fraction::types::Fraction;
        /// let fraction = frac![1, 2];
        /// assert_eq!(fraction.reciprocal(), frac![2, 1]);
        /// ```
        pub fn reciprocal(&self) -> Self {
            Self {
                numerator: self.denominator,
                denominator: self.numerator,
            }
        }

        /// Computes the mediant of two fractions.
        /// The mediant of (a / b) and (c / d) is ((a + b) / (c + d))
        pub fn mediant(&self, other: &Self) -> Self {
            frac![
                self.numerator + other.numerator,
                self.denominator + other.denominator
            ]
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
pub mod assignment {

    use std::ops::{AddAssign, DivAssign, MulAssign, SubAssign};

    use crate::{types::Fraction, Number};

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

/// Checked versions of operators like `+` and `-`
pub mod checked {
    use crate::{frac, types::Fraction, Number};
    use num::{CheckedAdd, CheckedDiv, CheckedMul, CheckedSub};

    impl<T: Number + CheckedMul + CheckedAdd> CheckedAdd for Fraction<T> {
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

    impl<T: Number + CheckedMul + CheckedSub> CheckedSub for Fraction<T> {
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

    impl<T: Number + CheckedMul> CheckedMul for Fraction<T> {
        fn checked_mul(&self, v: &Self) -> Option<Self> {
            let numerator = self.numerator.checked_mul(&v.numerator)?;
            let denominator = self.denominator.checked_mul(&v.denominator)?;
            Some(frac![numerator, denominator])
        }
    }

    impl<T: Number + CheckedMul> CheckedDiv for Fraction<T> {
        fn checked_div(&self, v: &Self) -> Option<Self> {
            let numerator = self.numerator.checked_mul(&v.denominator)?;
            let denominator = self.denominator.checked_mul(&v.numerator)?;
            Some(frac![numerator, denominator])
        }
    }
}

/// Unchecked versions of operators like `+` and `-`. USE WITH CAUTION.
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
    use crate::{types::Fraction, Number};
    // use num::{integer::lcm, Zero};
    use std::cmp::{PartialEq, PartialOrd};

    impl<T: Number> PartialEq for Fraction<T> {
        fn eq(&self, other: &Self) -> bool {
            // let e = lcm(self.denominator, other.denominator);
            // (e / self.denominator) == (e / other.denominator)

            // Let's just return whether their difference is zero
            // (*self - *other).is_zero()
            (self.numerator * other.denominator) == (self.denominator * other.numerator)
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
