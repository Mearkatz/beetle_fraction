/*!
    # Beetle-Fraction

    A set of functions and structs for doing math with rational numbers.

    Example program:
    ```rust
    fn main() {
        use beetle_fraction::prelude::*;
        let f = frac![1, 2];

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
    pub use crate::traits::{Number, Simplify};
    pub use crate::{frac, int, unit};
}
