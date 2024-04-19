// aprox_eq Copyright (c) 2024 Evan Overman (https://an-prata.it).
// Licensed under the MIT License.
// See LICENSE file in repository root for complete license text.

pub(crate) trait FloatingComponentMask {
    type WidthInt;

    /// A bit mask which, when masking the binary representation of the implementing type, will
    /// yield the "sign" component of the type.
    const SIGN_MASK: Self::WidthInt;

    /// A bit mask which, when masking the binary representation of the implementing type, will
    /// yield the "exponent" component of the type.
    const EXPONENT_MASK: Self::WidthInt;

    /// A bit mask which, when masking the binary representation of the implementing type, will
    ///yield the "mantissa" (significand, coefficiant, fraction, etc) component of the type.
    const MANTISSA_MASK: Self::WidthInt;

    /// If the mantissa would have been equal to `MANTISSA_MASK`, returns 0, otherwise returns the
    /// mantissa.
    fn promote_mantissa(&self, tolerance: u32) -> Self::WidthInt;

    /// Gets the sign of `self`, shifted such that the components least significant bit is in the
    /// returned integer's least significant position.
    fn sign(&self) -> Self::WidthInt;

    /// Gets the exponent of `self`, shifted such that the components least significant bit is in
    /// the returned integer's least significant position.
    fn exponent(&self) -> Self::WidthInt;

    /// Gets the mantissa (significand, coefficiant, fraction, etc) of `self`, shifted such that
    /// the components least significant bit is in the returned integer's least significant
    /// position.
    fn mantissa(&self) -> Self::WidthInt;

    /// Returns true if all non mantissa components are equal.
    fn eq_sgnificance(&self, other: &Self) -> bool;
}

impl FloatingComponentMask for f32 {
    type WidthInt = u32;

    const SIGN_MASK: Self::WidthInt = 0b1 << 31;
    const EXPONENT_MASK: Self::WidthInt = 0b111_1111_1 << (f32::MANTISSA_DIGITS - 1);
    const MANTISSA_MASK: Self::WidthInt = !(Self::SIGN_MASK | Self::EXPONENT_MASK);

    fn sign(&self) -> Self::WidthInt {
        (self.to_bits() & Self::SIGN_MASK) >> 31
    }

    fn exponent(&self) -> Self::WidthInt {
        (self.to_bits() & Self::EXPONENT_MASK) >> (f32::MANTISSA_DIGITS - 1)
    }

    fn mantissa(&self) -> Self::WidthInt {
        self.to_bits() & Self::MANTISSA_MASK
    }

    fn promote_mantissa(&self, tolerance: u32) -> Self::WidthInt {
        let mantissa = self.mantissa().saturating_add(tolerance) & Self::MANTISSA_MASK;

        if mantissa == Self::MANTISSA_MASK {
            0u32
        } else {
            mantissa
        }
    }

    fn eq_sgnificance(&self, other: &Self) -> bool {
        (self.to_bits() & !Self::MANTISSA_MASK) == (other.to_bits() & !Self::MANTISSA_MASK)
    }
}

impl FloatingComponentMask for f64 {
    type WidthInt = u64;

    const SIGN_MASK: Self::WidthInt = 0b1 << 63;
    const EXPONENT_MASK: Self::WidthInt = 0b111_1111_1111 << (f64::MANTISSA_DIGITS - 1);
    const MANTISSA_MASK: Self::WidthInt = !(Self::SIGN_MASK | Self::EXPONENT_MASK);

    fn sign(&self) -> Self::WidthInt {
        (self.to_bits() & Self::SIGN_MASK) >> 63
    }

    fn exponent(&self) -> Self::WidthInt {
        (self.to_bits() & Self::EXPONENT_MASK) >> (f64::MANTISSA_DIGITS - 1)
    }

    fn mantissa(&self) -> Self::WidthInt {
        self.to_bits() & Self::MANTISSA_MASK
    }

    fn promote_mantissa(&self, tolerance: u32) -> Self::WidthInt {
        let mantissa = self.mantissa().saturating_add(tolerance as u64) & Self::MANTISSA_MASK;

        if mantissa == Self::MANTISSA_MASK {
            0u64
        } else {
            mantissa
        }
    }

    fn eq_sgnificance(&self, other: &Self) -> bool {
        (self.to_bits() & !Self::MANTISSA_MASK) == (other.to_bits() & !Self::MANTISSA_MASK)
    }
}

#[cfg(test)]
mod tests {
    use crate::floats::FloatingComponentMask;

    #[test]
    fn f32_bit_masks() {
        let a = 1.0285932900803419e-38f32;
        assert_eq!(a.sign(), 0u32);
        assert_eq!(a.exponent(), 0u32);
        assert_eq!(a.mantissa(), 0b111_0000_0000_0000_1111_1111u32);

        let a = -8.854580707618707e+21f32; // -1.4106160901776828e-36f32;
        assert_eq!(a.sign(), 1u32);
        assert_eq!(a.exponent(), 0b110_0011_1u32);
        assert_eq!(a.mantissa(), 0b111_0000_0000_0000_1111_1111u32);
    }

    #[test]
    fn f64_bit_masks() {
        let a = -1.5377146758692568e+159f64;
        assert_eq!(a.sign(), 1u64);
        assert_eq!(a.exponent(), 0b110_0000_1111u64);
        assert_eq!(
            a.mantissa(),
            0b1100_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0001u64
        );
    }
}
