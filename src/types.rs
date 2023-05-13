//! Type definitions & their non-trait impl's

/// Operations involving Fractions that return `Result`s will return one of these variants as an `Err`
#[derive(Debug, Copy, Clone)]
pub enum FractionError {
    /// Denotes that a Fraction was created whose denominator was zero, and thus considered an error in its context.    
    ImpliedDivisionByZero,

    /// Represents the failure of an operation when the `numerator` of the fraction overflows
    NumeratorOverflow,

    /// Represents the failure of an operation when the `denominator` of the fraction overflows
    DenominatorOverflow,

    /// Used to denote when casting a string as a Fraction failed
    UnableToParseString,

    /// Represents a failure to parse a Float in some misc. way
    FailureToParseFloat,
}
