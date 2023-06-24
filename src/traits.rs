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
pub trait Simplify<T: Integer + Clone>: IsFraction<T> {
    /// Takes a reference to a fraction and returns it in simplest form
    fn simplest_form(&self) -> Self {
        let fac = self.numerator_ref().gcd(self.denominator_ref());
        Self::new(self.numerator() / fac.clone(), self.denominator() / fac)
    }

    /// Simplifies a Fraction in-place.
    /// Shorthand for `my_fraction = my_fraction.simplest_form();`
    fn simplify(&mut self) {
        *self = self.simplest_form()
    }
}

/// Allows for switching the numerator and denominator of a fraction
pub trait Reciprocal<T: Number>: IsFraction<T> {
    /// Returns a Fraction with its numerator and denominator switched
    fn reciprocal(&self) -> Self {
        Self::new(self.denominator(), self.numerator())
    }
}

/// Allows for creation of Fractions with methods
pub trait MakeMe<T>: Sized {
    /// Creates a new fraction and returns it
    fn new(numerator: T, denominator: T) -> Self;

    /// Tries creating a new fraction.
    /// If the denominator equals zero, this returns None,
    fn checked_new(numerator: T, denominator: T) -> Option<Self>;
}

/// For something to be a Fraction, it must at least have a Numerator and Denominator
pub trait IsFraction<T>: Debug + Clone + MakeMe<T> {
    /// A copy of this fraction's numerator
    fn numerator(&self) -> T;

    /// A reference to this Fraction's numerator
    fn numerator_ref(&self) -> &T;

    /// Reassigns this Fraction's numerator to `n`
    fn set_numerator(&mut self, n: T);

    /// This Fraction's denominator
    fn denominator(&self) -> T;

    /// A reference to this Fraction's denominator
    fn denominator_ref(&self) -> &T;

    /// Reassigns this Fraction's denominator to `n`
    fn set_denominator(&mut self, n: T);
}
