// aprox_eq Copyright (c) 2023 Evan Overman (https://an-prata.it).
// Licensed under the MIT License.
// See LICENSE file in repository root for complete license text.

// Makes it so the `aprox_eq::*` path works within this crate for tests.
extern crate self as aprox_eq;
pub use aprox_derive::AproxEq;

/// Trait for aproximate equality, mostly for dealing with small amounts of
/// error that accumulate in floating point numbers which can be particularly
/// annoying when trying to unit test.
///
/// ## Derivable
///
/// This trait can be derived, doing so implements [`aprox_eq()`] so that it
/// compares all fields of the two structs, if one field is not aproximately
/// equal then neither is the struct. This requires that all fields also
/// implement [`AproxEq`]. The default implementation of [`aprox_ne()`] is used
/// if [`AproxEq`] is derived.
///
/// [`AproxEq`]: AproxEq
/// [`aprox_eq()`]: AproxEq::aprox_eq()
/// [`aprox_ne()`]: AproxEq::aprox_ne()
pub trait AproxEq<T = Self>
where
    T: ?Sized,
{
    /// Should return true if the two operands are aproximately equal, the
    /// exact meaning of "aproximate" is up to the implementing struct to
    /// decide but should be narrow enough that no values with a practical
    /// difference are aproximately equal and vise versa.
    ///
    /// # Examples
    ///
    /// ```
    /// use crate::aprox_eq::AproxEq;
    ///
    /// let a = 0.2_f32;
    /// let b = 0.3_f32;
    ///
    /// (a).aprox_eq(&b);  // This should probably be false.
    ///
    /// let a = 0.8_f64;
    /// let b = 0.799999999999999_f64;
    ///
    /// (a).aprox_eq(&b);  // This is definately almost same number.
    /// ```
    #[must_use]
    fn aprox_eq(&self, other: &T) -> bool;

    /// Returns true if not aproximately equal, simple negation of
    /// [`aprox_eq()`] by default.
    ///
    /// [`aprox_eq()`]: AproxEq::aprox_eq()
    ///
    /// # Examples
    ///
    /// ```
    /// use crate::aprox_eq::AproxEq;
    ///
    /// let a = 1_f32;
    /// let b = 1_f32;
    /// let c = 2_f32;
    ///
    /// a.aprox_ne(&b);  // false
    /// a.aprox_ne(&c);  // true
    /// ```
    #[inline]
    #[must_use]
    fn aprox_ne(&self, other: &T) -> bool {
        !self.aprox_eq(other)
    }
}

/// Behaves exactly like [`assert_eq`] but calls on the [`aprox_eq()`] function
/// as provided by the [`AproxEq`] trait instead of [`eq()`] as provided by
/// [`PartialEq`].
///
/// [`assert_eq`]: assert_eq
/// [`aprox_eq()`]: AproxEq::aprox_eq()
/// [`AproxEq`]: AproxEq
/// [`eq()`]: PartialEq::eq()
/// [`PartialEq`]: PartialEq
#[macro_export]
macro_rules! assert_aprox_eq {
    ($left:expr, $right:expr) => {
        assert!(
            aprox_eq::AproxEq::aprox_eq(&$left, &$right),
            "assertion failed: `left.aprox_eq(right)`\n  left: `{:#?}`,\n right: `{:#?}`",
            $left,
            $right,
        );
    };
}

/// Behaves exactly like [`assert_ne`] but calls on the [`aprox_ne()`] function
/// as provided by the [`AproxEq`] trait instead of [`ne()`].
///
/// [`assert_ne`]: assert_ne
/// [`aprox_ne()`]: AproxEq::aprox_ne()
/// [`AproxEq`]: AproxEq
/// [`ne()`]: PartialEq::ne()
#[macro_export]
macro_rules! assert_aprox_ne {
    ($left:expr, $right:expr) => {
        assert!(
            aprox_eq::AproxEq::aprox_ne(&$left, &$right),
            "assertion failed: `left.aprox_ne(right)`\n  left: `{:#?}`,\n right: `{:#?}`",
            $left,
            $right,
        );
    };
}

impl<T, U> AproxEq<Vec<U>> for Vec<T>
where
    T: AproxEq<U>,
    U: AproxEq<T>,
{
    fn aprox_eq(&self, other: &Vec<U>) -> bool {
        match self.len() == other.len() {
            true => self
                .iter()
                .zip(other)
                .fold(true, |acc, (a, b)| acc && a.aprox_eq(&b)),

            false => false,
        }
    }
}

impl AproxEq for f64 {
    fn aprox_eq(&self, other: &Self) -> bool {
        // Aproximately equal if within 10^-16 of eachother.
        (self - other).abs() < 1e-12
    }
}

impl AproxEq for f32 {
    fn aprox_eq(&self, other: &Self) -> bool {
        // Aproximately equal if within 10^-8 of eachother.
        (self - other).abs() < 1e-6
    }
}

#[cfg(test)]
mod tests {
    use crate::AproxEq;

    #[derive(AproxEq, Debug)]
    struct SomeFoats {
        pub a: f64,
        pub b: f32,
    }

    #[derive(AproxEq, Debug)]
    struct SomeAproxEq(SomeFoats, SomeFoats);

    #[test]
    fn basic_aprox_eq() {
        assert_aprox_eq!(1.0002_f64, 1.0001999999999999_f64);
        assert_aprox_ne!(1.002_f32, 1.001_f32);
    }

    #[test]
    fn ownership_retainance() {
        let a = 1_f64;
        let b = 1_f64;

        assert_aprox_eq!(a, b);

        let c = a + b;

        assert_aprox_ne!(a, c);
    }

    #[test]
    fn derive() {
        assert_aprox_eq!(
            SomeFoats { a: 3f64, b: 2f32 },
            SomeFoats { a: 3f64, b: 2f32 }
        );

        assert_aprox_eq!(
            SomeAproxEq(
                SomeFoats { a: 3f64, b: 2f32 },
                SomeFoats { a: 5f64, b: 4f32 }
            ),
            SomeAproxEq(
                SomeFoats { a: 3f64, b: 2f32 },
                SomeFoats { a: 5f64, b: 4f32 }
            )
        );
    }

    #[test]
    fn vec_aprox_eq() {
        let vec0 = vec![0f32, 1f32, 1.2f32, 42f32];
        let vec1 = vec0.clone();
        let vec2 = vec![0.1f32, 0f32, 1.2f32, 42f32];

        assert_aprox_eq!(vec0, vec1);
        assert_aprox_ne!(vec0, vec2);
    }

    #[test]
    fn vec_different_types() {
        let vec0 = vec![0f32, 1f32, 1.2f32, 42f32];
        let vec1 = vec![0f64, 1f64, 1.2f64, 42f64];

        assert_aprox_eq!(vec0, vec1);
    }

    impl AproxEq<f32> for f64 {
        fn aprox_eq(&self, other: &f32) -> bool {
            (*self as f32).aprox_eq(other)
        }
    }

    impl AproxEq<f64> for f32 {
        fn aprox_eq(&self, other: &f64) -> bool {
            self.aprox_eq(&(*other as f32))
        }
    }
}
