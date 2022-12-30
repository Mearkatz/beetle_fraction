//! A set of tests to make sure the crate is working properly

#[cfg(test)]
mod lib_test {
    use beetle_fraction::{frac, int, types::Fraction, unit};
    use num::traits::ops::checked::CheckedAdd;
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

        // Turn Float into Fraction
        let fract: Fraction<i128> = (-1.5_f64).try_into().unwrap();
        assert_eq!(fract, frac![-3, 2]);
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
            assert!(add(f, g));
            assert!(mul(f, g));
            assert!(sub(f, g));
            assert!(div(f, g));
            assert!(neg(f, g));
            assert!(pow(f, g));
            assert!(comparisons(f, g));
        }

        // Returns whether adding two fractions returns the expected result
        fn add(f: Fractype, g: Fractype) -> bool {
            let (a, b) = (f.numerator, f.denominator);
            let (c, d) = (g.numerator, g.denominator);
            f + g == frac![(a * d) + (b * c), b * d]
        }

        fn sub(f: Fractype, g: Fractype) -> bool {
            let (a, b) = (f.numerator, f.denominator);
            let (c, d) = (g.numerator, g.denominator);
            f - g == frac![(a * d) - (b * c), b * d]
        }

        fn mul(f: Fractype, g: Fractype) -> bool {
            let (a, b) = (f.numerator, f.denominator);
            let (c, d) = (g.numerator, g.denominator);
            f * g == frac![a * c, b * d]
        }

        fn div(f: Fractype, g: Fractype) -> bool {
            let (a, b) = (f.numerator, f.denominator);
            let (c, d) = (g.numerator, g.denominator);
            f / g == frac![a * d, b * c]
        }

        fn neg(f: Fractype, _g: Fractype) -> bool {
            -f == frac![-f.numerator, f.denominator]
        }

        fn pow(f: Fractype, _g: Fractype) -> bool {
            f.pow(-1) == frac![f.denominator, f.numerator]
        }

        fn comparisons(f: Fractype, g: Fractype) -> bool {
            // Make sure comparisons don't panic
            let _ = f.partial_cmp(&g);
            assert_eq!(f, f);

            // One and ONLY ONE of these MUST be true for this function to return true
            [f < g, f <= g, f > g, f >= g, f == g, f != g]
                .into_iter()
                .reduce(|a, b| a ^ b)
                .unwrap_or(false)
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
