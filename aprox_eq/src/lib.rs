// aprox_eq Copyright (c) 2024 Evan Overman (https://an-prata.it).
// Licensed under the MIT License.
// See LICENSE file in repository root for complete license text.

#![feature(float_next_up_down)]

mod floats;

// Makes it so the `aprox_eq::*` path works within this crate for tests.
extern crate self as aprox_eq;
use std::{borrow::Cow, ops::Deref};

pub use aprox_derive::AproxEq;
use floats::FloatingComponentMask;

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

// For when specialization becomes stable.

//impl<T, U> AproxEq for T
//where
//    T: Iterator<Item = U>,
//    U: AproxEq,
//{
//    /// Aproximate equality on iterators only compares elements up to the last
//    /// element of the shortest iterator.
//    default fn aprox_eq(&self, other: &Self) -> bool {
//        self.iter()
//            .zip(other)
//            .map(|(a, b)| a.aprox_eq(b))
//            .fold(true, |a, b| a && b)
//    }
//}

impl<T, U> AproxEq<&U> for &T
where
    T: ?Sized,
    U: ?Sized,
    T: AproxEq<U>,
{
    #[inline]
    fn aprox_eq(&self, other: &&U) -> bool {
        AproxEq::aprox_eq(*self, *other)
    }
}

impl<T, U> AproxEq<&U> for &mut T
where
    T: ?Sized,
    U: ?Sized,
    T: AproxEq<U>,
{
    #[inline]
    fn aprox_eq(&self, other: &&U) -> bool {
        AproxEq::aprox_eq(*self, *other)
    }
}

impl<T, U> AproxEq<&mut U> for &T
where
    T: ?Sized,
    U: ?Sized,
    T: AproxEq<U>,
{
    #[inline]
    fn aprox_eq(&self, other: &&mut U) -> bool {
        AproxEq::aprox_eq(*self, *other)
    }
}

impl<T, U> AproxEq<&mut U> for &mut T
where
    T: ?Sized,
    U: ?Sized,
    T: AproxEq<U>,
{
    #[inline]
    fn aprox_eq(&self, other: &&mut U) -> bool {
        AproxEq::aprox_eq(*self, *other)
    }
}

impl<T, U> AproxEq<Vec<U>> for Vec<T>
where
    T: AproxEq<U>,
{
    #[inline]
    fn aprox_eq(&self, other: &Vec<U>) -> bool {
        self.as_slice().aprox_eq(other.as_slice())
    }
}

impl<T, U> AproxEq<[U]> for [T]
where
    T: AproxEq<U>,
{
    /// Compares two slices, if they are of different lengths then they cannot
    /// be equal.
    fn aprox_eq(&self, other: &[U]) -> bool {
        match self.len() == other.len() {
            true => self.iter().zip(other).all(|(a, b)| a.aprox_eq(&b)),
            false => false,
        }
    }
}

impl<T, U, const N: usize> AproxEq<[U; N]> for [T; N]
where
    T: AproxEq<U>,
{
    /// Compares two arrays of equal and constant length for aproximate
    /// equality.
    fn aprox_eq(&self, other: &[U; N]) -> bool {
        self.iter().zip(other).all(|(a, b)| a.aprox_eq(&b))
    }
}

impl<T, U> AproxEq<Box<U>> for Box<T>
where
    T: AproxEq<U>,
{
    #[inline]
    fn aprox_eq(&self, other: &Box<U>) -> bool {
        self.deref().aprox_eq(other.deref())
    }
}

impl<'a, T, U> AproxEq<Cow<'a, U>> for Cow<'a, T>
where
    T: AproxEq<U> + Clone,
    U: Clone,
{
    #[inline]
    fn aprox_eq(&self, other: &Cow<U>) -> bool {
        self.deref().aprox_eq(other.deref())
    }
}

impl<T, U> AproxEq<Option<U>> for Option<T>
where
    T: AproxEq<U>,
{
    fn aprox_eq(&self, other: &Option<U>) -> bool {
        if self.is_some() && other.is_some() {
            return self.as_ref().unwrap().aprox_eq(other.as_ref().unwrap());
        }

        if self.is_none() && other.is_none() {
            return true;
        }

        false
    }
}

const F32_TOLERANCE: u32 = 2;
const F64_TOLERANCE: u64 = 8;

impl AproxEq for f64 {
    fn aprox_eq(&self, other: &Self) -> bool {
        if self.eq_sgnificance(other) {
            self.mantissa().abs_diff(other.mantissa()) < F64_TOLERANCE
        } else {
            let exp_diff = self.exponent().abs_diff(other.exponent());
            let promoted_diff = self
                .promote_mantissa(F64_TOLERANCE as u32)
                .abs_diff(other.promote_mantissa(F64_TOLERANCE as u32));

            !(self.mantissa().abs_diff(other.mantissa()) < F64_TOLERANCE)
                && self.sign() == other.sign()
                && exp_diff == 1
                && promoted_diff < F64_TOLERANCE
        }
    }
}

impl AproxEq for f32 {
    fn aprox_eq(&self, other: &Self) -> bool {
        if self.eq_sgnificance(other) {
            self.mantissa().abs_diff(other.mantissa()) < F32_TOLERANCE
        } else {
            let exp_diff = self.exponent().abs_diff(other.exponent());
            let promoted_diff = self
                .promote_mantissa(F32_TOLERANCE)
                .abs_diff(other.promote_mantissa(F32_TOLERANCE));

            !(self.mantissa().abs_diff(other.mantissa()) < F32_TOLERANCE)
                && self.sign() == other.sign()
                && exp_diff == 1
                && promoted_diff < F32_TOLERANCE
        }
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

    #[derive(Debug, AproxEq)]
    enum MyEnum {
        Var0(f32),
        Var1(f64),
        Var2(f32, f32, f64),
        Var3 { a: f32, b: f64 },
    }

    #[test]
    fn aprox_eq_basic() {
        assert_aprox_eq!(1.0002_f64, 1.0001999999999999_f64);
        assert_aprox_ne!(1.002_f64, 1.001_f64);
        assert_aprox_eq!(1.0002_f32, 1.0001999999999999_f32);
        assert_aprox_ne!(1.002_f32, 1.001_f32);
    }

    #[test]
    fn aprox_eq_very_small() {
        assert_aprox_eq!(0.000_000_001_f64, 0.000_000_001_000_000_000_000_001_f64);
        assert_aprox_ne!(0.000_000_001_f64, 0.000_000_001_000_000_000_000_008_f64);
    }

    #[test]
    fn aprox_eq_very_large() {
        assert_aprox_eq!(1_000_000_000_f32, 1_000_000_010_f32);
        assert_aprox_ne!(1_000_000_000_f32, 1_000_000_100_f32);
        assert_aprox_eq!(1_000_000_000_f64, 1_000_000_000.000_000_1_f64);
        assert_aprox_ne!(1_000_000_000_f64, 1_000_000_000.000_001_f64);
    }

    #[test]
    fn increments() {
        let mut a = 0.0f32;
        let mut b = a.next_up();

        while b.is_finite() {
            assert_aprox_eq!(a, b);
            a = a.next_up();
            b = b.next_up();
        }
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
    fn derive_struct() {
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
    fn derive_enum() {
        assert_aprox_eq!(MyEnum::Var0(0f32), MyEnum::Var0(0f32));
        assert_aprox_ne!(MyEnum::Var0(0f32), MyEnum::Var1(0f64));
        assert_aprox_eq!(
            MyEnum::Var2(0f32, 1f32, 2f64),
            MyEnum::Var2(0f32, 1f32, 2f64)
        );
        assert_aprox_eq!(
            MyEnum::Var3 { a: 3f32, b: 6f64 },
            MyEnum::Var3 { a: 3f32, b: 6f64 }
        );
    }

    #[test]
    fn derive_unti() {
        #[derive(Debug, AproxEq)]
        struct UnitStruct;

        #[derive(Debug, AproxEq)]
        enum UnitEnum {
            UnitVariant,
        }

        #[derive(Debug, AproxEq)]
        struct EmptyStruct {}

        #[derive(Debug, AproxEq)]
        struct EmptyTupleStruct();

        assert_aprox_eq!(UnitStruct, UnitStruct);
        assert_aprox_eq!(UnitEnum::UnitVariant, UnitEnum::UnitVariant);
        assert_aprox_eq!(EmptyStruct {}, EmptyStruct {});
        assert_aprox_eq!(EmptyTupleStruct(), EmptyTupleStruct());
    }

    #[test]
    fn vec_aprox_eq() {
        let vec0 = vec![0f32, 1f32, 1.2f32, 42f32];
        let vec1 = vec0.clone();
        let vec2 = vec![0.1f32, 0f32, 1.2f32, 42f32];
        let vec3 = vec![0.1f32, 0f32, 1.2f32, 42f32, 32f32, 128f32, 0.3f32];

        assert_aprox_eq!(vec0, vec1);
        assert_aprox_ne!(vec0, vec2);
        assert_aprox_ne!(vec0, vec3);
    }

    #[test]
    fn slice_and_arr_aprox_eq() {
        let arr0 = [0f32, 1f32, 1.2f32, 42f32];
        let arr1 = [0f32, 1f32, 1.2f32, 42f32];

        assert_aprox_eq!(arr0, arr1);
        assert_aprox_eq!(arr0.as_slice(), arr1.as_slice());
    }

    #[test]
    fn box_aprox_eq() {
        let box0 = Box::new(12.2f32);
        let box1 = Box::new(12.2f32);

        assert_aprox_eq!(box0, box1);
    }

    #[test]
    fn option_aprox_eq() {
        assert_aprox_eq!(None::<f32>, None::<f32>);
        assert_aprox_eq!(Some(1f32), Some(1f32));
        assert_aprox_ne!(None::<f32>, Some(1f32));
    }
}
