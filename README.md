# aprox_eq
Crate for determining aproximate equality, particularly between floating point numbers. This library is intended mostly as a quick to import and derivable way of mitigating floating point error. The `aprox_eq` folder has this crate, the `float_err` folder contains a binary application for calculating floating point error, its pretty simple but informs the `1e-12` for `f64` and `1e-6` for `f32` constant values used for determining aproximate equality. A google sheet with this data can be found [here](https://docs.google.com/spreadsheets/d/1In00LHwgNE-IQBjctHq1QW63a7rRg4kM2sKsBDc1dkk/edit?usp=sharing) and pdf exports of its pages are in the root of the repo.

```rust
use aprox_eq::{assert_aprox_eq, assert_aprox_ne, AproxEq};

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

    // This is going to be just outside the bounds of `aprox_eq`'s impl of
    // `AproxEq` for `f32` and `f64`, which will return false for any two
    // numbers with an absolute difference of `10^-6` and `10^-12` respectively.
    //
    // These bounds are extremely tight for these floating point types to ensure
    // that anything much larger than some accumulated floating point error is
    // not aproximately equal.
    let y = MyStruct {
        a: 3.2f32 - 1e-6,
        b: 4.8f64 - 1e-12,
    };

    // However, for their respective types any two numbers within those bounds
    // are considered aproximately equal, even if they arent exactly the same
    // number, allowing for very precise mitigation of floating point error.
    let z = MyStruct {
        a: 3.2f32 - 1e-7,
        b: 4.8f64 - 1e-13,
    };

    assert_aprox_ne!(x, y);
    assert_aprox_eq!(x, z);
}
```

