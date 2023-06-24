/*!
    # Beetle-Fraction

    A set of functions and structs for doing math with rational numbers.

    Example program:
    ```
    # use beetle_fraction::*;
    # use beetle_fraction::prelude::*;
    fn main() {
        let half = frac![1, 2];
        assert_eq!(half * half, frac![1, 4]);
    }
    ```
*/

#![deny(missing_docs, clippy::unwrap_used)]

// Modules
pub mod big_fraction;
pub mod fraction;
pub mod macros;
pub mod traits;
pub mod types;

/// A prelude for frequently used types, traits, & macros
pub mod prelude {
    pub use crate::fraction::Fraction;
    pub use crate::macros::*;
    pub use crate::traits::*;
}
