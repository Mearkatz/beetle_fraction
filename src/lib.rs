/*!
    # Fraction Type

    A set of functions and structs for doing math with rational numbers.

    Fraction is the main struct for this project.
    Later there will also be a SuperFraction, allowing its fields to be Fractions or a Numbers
*/

#![deny(missing_docs)]

// Dependencies
use num::{Bounded, Integer};
use std::fmt::Debug;

// Modules
pub mod macros;
pub mod ops;
pub mod types;

// Re-Exports
// pub use crate::types::*;

/// Allows types to be used as the numerator / denominator of a Fraction.
pub trait Number: Bounded + Clone + Copy + Debug + Integer {}
impl<N> Number for N where N: Bounded + Clone + Copy + Debug + Integer {}
