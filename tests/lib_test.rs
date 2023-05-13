//! A set of tests to make sure the crate is working properly

#[cfg(test)]
mod lib_test {
    use beetle_fraction::prelude::*;
    use num::traits::ops::checked::CheckedAdd;
    use num_traits::Pow;
    use rand::{thread_rng, Rng};

    #[test]
    pub fn macros_work() {
        let a: u32 = 5;
        let b: u32 = 29;

        // Asserts the following, which must be true:
        // (a / 1) * (1 / b) = (a / b)
        assert_eq!(int!(a) * unit!(b), frac![a, b]);
    }

    #[test]
    pub fn float_conversions_works() {
        // Turn Fraction into Float
        let fract: Fraction<u8> = frac![1, 2];
        let _float: f64 = fract.into();
        let _float: f32 = fract.into();

        let mut rng = thread_rng();
        let trials = 10_000_000;
        const TOLERANCE: f64 = 1e-20;
        let tolerable_answer = |original: f64, ans: Fraction<i128>| -> bool {
            let ans_float: f64 = (ans.numerator as f64) / (ans.denominator as f64);
            let abs_diff = (original - ans_float).abs();
            abs_diff < TOLERANCE
        };

        const MIN: f64 = (i128::MIN) as f64;
        const MAX: f64 = (i128::MAX) as f64;

        for _ in 0..trials {
            let f: f64 = rng.gen_range(MIN..MAX);
            let ans = unsafe { Fraction::from_float(f).unwrap() };
            assert!(tolerable_answer(f, ans));
        }
    }

    #[test]
    pub fn fraction_to_string_works() {
        let f = frac![1, 2];
        let s = f.to_string();
        assert_eq!(&s, "1 / 2");
    }

    #[test]
    pub fn common_math_works() {
        // TESTING CONSTANTS
        type LittleType = i16; // LittleType::MIN .. MAX is the range of possible fraction numerators and denominators
        type BigType = i64; // Fractions are actually of this type instead of LittleType to prevent overflows
        type Fractype = Fraction<BigType>;

        // Random Fraction closure that produces random Fraction<i64>'s using the rand crate's thread_rng()
        let mut rng = thread_rng();
        let mut random_fraction = || -> Fractype {
            let x: LittleType = rng.gen();
            let y: LittleType = rng.gen();

            // If either random number is 0, set it to 1 instead.
            // This is to prevent division by zero errors
            let x = if x == 0 { 1 } else { x };
            let y = if y == 0 { 1 } else { x };

            frac![x as BigType, y as BigType]
        };

        // Random fractions to be tested
        const TEST_FRACTION_PAIRS: usize = 500_000;
        let test_fractions: Vec<(Fraction<i64>, Fraction<i64>)> = {
            std::iter::repeat(())
                .take(TEST_FRACTION_PAIRS)
                .map(|_| (random_fraction(), random_fraction()))
                .collect()
        };

        // =================================
        //          RUN THE TESTS
        // =================================
        for (f, g) in test_fractions.into_iter() {
            add(f, g);
            mul(f, g);
            sub(f, g);
            div(f, g);
            pow(f, g);
            neg(f, g);
            add(f, g);
            comparisons(f, g);
        }

        // Asserts that the result of addition is the expected result
        fn add(f: Fractype, g: Fractype) {
            let (a, b) = (f.numerator, f.denominator);
            let (c, d) = (g.numerator, g.denominator);
            assert_eq!(f + g, frac![(a * d) + (b * c), b * d])
        }

        // Asserts that the result of subtraction is the expected result
        fn sub(f: Fractype, g: Fractype) {
            let (a, b) = (f.numerator, f.denominator);
            let (c, d) = (g.numerator, g.denominator);
            assert_eq!(f - g, frac![(a * d) - (b * c), b * d])
        }

        // Asserts that the result of multiplication is the expected result
        fn mul(f: Fractype, g: Fractype) {
            let (a, b) = (f.numerator, f.denominator);
            let (c, d) = (g.numerator, g.denominator);
            assert_eq!(f * g, frac![a * c, b * d])
        }

        // Asserts that the result of division is the expected result
        fn div(f: Fractype, g: Fractype) {
            let (a, b) = (f.numerator, f.denominator);
            let (c, d) = (g.numerator, g.denominator);
            assert_eq!(f / g, frac![a * d, b * c])
        }

        // Asserts that the result of negation is the expected result
        fn neg(f: Fractype, _g: Fractype) {
            assert_eq!(-f, frac![-f.numerator, f.denominator])
        }

        // Asserts that the result of exponentiation is the expected result
        fn pow(f: Fractype, _g: Fractype) {
            assert_eq!(f.pow(2).simplest_form(), (f * f).simplest_form())
        }

        // Asserts that the result of comparison operations are the expected result
        fn comparisons(f: Fractype, g: Fractype) {
            // Make sure comparisons don't panic
            let _ = f.partial_cmp(&g);
            assert_eq!(f, f);

            // One and ONLY ONE of these MUST be true for this function to return true
            assert!([f < g, f <= g, f > g, f >= g, f == g, f != g]
                .into_iter()
                .reduce(|a, b| a ^ b)
                .unwrap_or(false));
        }
    }

    #[test]
    pub fn checked_math_works() {
        // u8::MAX + 1 should overflow
        let f: Fraction<u8> = int![u8::MAX];
        assert!(f.checked_add(&int![1]).is_none());

        // u128::MAX + 1 should overflow
        let f: Fraction<u128> = int![u128::MAX];
        assert!(f.checked_add(&int![1]).is_none());
    }
}
