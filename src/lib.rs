/*!
    # Beetle-Fraction

    A set of functions and structs for doing math with rational numbers.

    Fraction is the main struct for this project.
    Later there will also be a SuperFraction, allowing its fields to be Fractions or a Numbers
*/

#![deny(missing_docs, clippy::unwrap_used)]

// Dependencies
use num::{Bounded, Integer};
use std::fmt::Debug;

// Modules
pub mod macros;
pub mod ops;
pub mod types;

/// Allows types to be used as the numerator / denominator of a Fraction.
pub trait Number: Copy + Debug + Integer + Bounded {}

// Impl Number on types which:
// - can be copied
//      - implicitly copies all the bits into any copies made)
// - can be cloned
//      - explicitly copies all the bits into any clones made via `.clone()`)
// - Has bounds (a minimum and maximum value, for u8's these are u8::MIN (0) and u8::MAX (255))
impl<N> Number for N where N: Copy + Debug + Integer + Bounded {}
