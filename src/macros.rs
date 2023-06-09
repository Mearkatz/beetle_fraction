//! Macros for creating and manipulating Fractions

/// Shorthand for `Fraction::new(x, y);`
///
/// # Examples
/// ```
/// # use beetle_fraction::*;
/// # use beetle_fraction::prelude::*;
/// # use beetle_fraction::big_fraction::*;
/// let half: Fraction<u8> = Fraction::new(1, 2);
/// let also_half: Fraction<u8> = frac![1, 2];
/// assert_eq!(half, also_half);
/// ```
#[macro_export]
macro_rules! frac {
    ($numerator: expr, $denominator: expr) => {{
        Fraction {
            numerator: $numerator,
            denominator: $denominator,
        }
    }};
}

/// Shorthand for BigFraction::from(Fraction::new(x, y))
///
/// # Examples
/// ```
///  # use beetle_fraction::*;
///  # use beetle_fraction::prelude::*;
///  # use beetle_fraction::big_fraction::*;
///  let half: BigFraction = BigFraction::new(1u32.into(), 2u32.into());
///  let also_half: BigFraction = bigfrac![1, 2];
///  assert_eq!(half, also_half);
/// ```
#[macro_export]
macro_rules! bigfrac {
    ($numerator: expr, $denominator: expr) => {{
        BigFraction {
            numerator: $numerator.into(),
            denominator: $denominator.into(),
        }
    }};
}

/// Shorthand for `Fraction::new(1, y);`
///
/// # Examples
/// ```
/// # use beetle_fraction::*;
/// # use beetle_fraction::prelude::*;
/// let sixteenth = unit![16];
/// assert_eq!(sixteenth, Fraction::new(1, 16));
/// ```
#[macro_export]
macro_rules! unit {
    ($n: expr) => {{
        Fraction {
            numerator: 1,
            denominator: $n,
        }
    }};
}

/// Shorthand for `Fraction::new(x, 1);`
///
/// # Examples
/// ```
/// # use beetle_fraction::*;
/// # use beetle_fraction::prelude::*;
/// let sixteen = int![16];
/// assert_eq!(sixteen, Fraction::new(16, 1));
/// ```
#[macro_export]
macro_rules! int {
    ($n: expr) => {{
        Fraction {
            numerator: $n,
            denominator: 1,
        }
    }};
}
