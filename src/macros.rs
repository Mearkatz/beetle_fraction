//! Macros for creating and manipulating Fractions

/// Shorthand for `Fraction::new(x, y);`
#[macro_export]
macro_rules! frac {
    ($x: expr, $y: expr) => {
        Fraction { x: $x, y: $y }
    };
}

/// Shorthand for `Fraction::new(1, y);`
#[macro_export]
macro_rules! unit {
    ($n: expr) => {
        Fraction { x: 1, y: $n }
    };
}

/// Shorthand for `Fraction::new(x, 1);`
#[macro_export]
macro_rules! int {
    ($n: expr) => {
        // Fraction::from($n)
        Fraction { x: $n, y: 1 }
    };
}
