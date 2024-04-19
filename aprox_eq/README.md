# aprox_eq
Crate for determining aproximate equality, particularly between floating point numbers. This library is intended mostly as a quick to import and derivable way of mitigating floating point error. Because of the way floating point number work, loosing accurate decimal places as the order of magnitude increase, and gaining them as it goes down, a simple tolerance is sub-optimal. Instead `aprox_eq` uses an understanding of the standard behind floating point numbers, and actually makes its aproximations based on the accuracy of the floating point standard at the order of magnitude of the floats being compared. This means looks at the bits of the mantissa, the fractional part of the float, and comparing them to be with a certain range of integer values, while taking into consideration the equality of the exponent and sign of the floating oint number.

# TL;DR: as your floats get more precise, so does `aprox_eq`
```rust
use aprox_eq::{assert_aprox_eq, assert_aprox_ne, AproxEq};

// You can derive the `AproxEq` trait the same way you can with `Eq` or `PartialEq`!

#[derive(AproxEq, Debug)]
struct MyStruct {
    a: f32,
    b: f64,
}

fn main() {
    let x = MyStruct {
        a: 3.2f32,
        b: 4.8f64,
    };

    let y = MyStruct {
        a: 3.2f32 - 1e-8,
        b: 4.8f64 - 1e-14,
    };

    assert_aprox_eq!(x, y);

    // Some normal size numbers
    assert_aprox_eq!(1.0002_f64, 1.0001999999999999_f64);
    assert_aprox_ne!(1.002_f64, 1.001_f64);

    // Tiny numbers, `aprox_eq` now requires that the numbers are closer to
    // eachother, since the float type can now store a higher precision
    assert_aprox_eq!(0.000_000_001_f64, 0.000_000_001_000_000_000_000_001_f64);
    assert_aprox_ne!(0.000_000_001_f64, 0.000_000_001_000_000_000_000_008_f64);

    // Large numbers, `aprox_eq` will now allow the numbers to be a greater
    // difference in value, since the float type has lost some precision
    assert_aprox_eq!(1_000_000_000_f32, 1_000_000_010_f32);
    assert_aprox_ne!(1_000_000_000_f32, 1_000_000_100_f32);
}
```

