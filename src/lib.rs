/*!
    # Beetle-Fraction

    A set of functions and structs for doing math with rational numbers.

    Fraction is the main struct for this project.
    Later there will also be a SuperFraction, allowing its fields to be Fractions or a Numbers
*/

#![deny(missing_docs, clippy::unwrap_used)]

// Modules
pub mod fraction;
pub mod macros;
pub mod traits;
pub mod types;

/// A prelude for frequently used types, traits, & macros
pub mod prelude {
    pub use crate::fraction::Fraction;
    pub use crate::traits::{Number, Simplify};
    pub use crate::{frac, int, unit};
}
