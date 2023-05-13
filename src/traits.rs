//! ....traits

use num::{Bounded, Integer};
use std::fmt::Debug;

/// Allows types to be used as the numerator or denominator of a Fraction.
pub trait Number: Debug + Integer + Bounded + Copy {}
impl<N> Number for N where N: Debug + Integer + Bounded + Copy {}

/// Allows for calculating the mediant of two Fractions
pub trait Mediant {
    /// produces a Fraction that lies between `self` and `rhs`    
    fn mediant(&self, rhs: &Self) -> Self;
}

/// Allows for simplifying of Fractions
pub trait Simplify {
    /// Takes a reference to a fraction and returns it in simplest form
    ///
    /// # Examples
    ///
    /// ```
    /// use beetle_fraction::prelude::*;    
    /// let two_fourths = Fraction::new(2, 4);
    /// let one_half = Fraction::new(1, 2);
    /// assert_eq!(two_fourths.simplest_form(), one_half);
    /// ```
    fn simplest_form(&self) -> Self;

    /// Shorthand for `my_fraction = my_fraction.simplest_form();`
    ///
    /// # Examples
    /// ```
    /// use beetle_fraction::prelude::*;
    /// let mut half: Fraction<u8> = frac![50, 100];
    /// half.simplify();
    /// assert!((half.numerator == 1) && (half.denominator == 2));
    /// ```
    fn simplify(&mut self);
}
