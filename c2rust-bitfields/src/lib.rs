//! A library for working with bitfields.
//!
//! This crate provides a `FieldType` trait that can be implemented for any
//! type that can be used as a bitfield. It also provides a `BitfieldStruct`
//! derive macro that can be used to generate getter and setter methods for
//! bitfields in a struct.

#![cfg_attr(feature = "no_std", no_std)]

pub use c2rust_bitfields_derive::BitfieldStruct;

/// A trait for types that can be used as bitfields.
pub trait FieldType: Sized {
    /// Whether the type is signed.
    const IS_SIGNED: bool;

    /// The total number of bits in the type.
    #[cfg(not(feature = "no_std"))]
    const TOTAL_BIT_SIZE: usize = ::std::mem::size_of::<Self>() * 8;
    /// The total number of bits in the type.
    #[cfg(feature = "no_std")]
    const TOTAL_BIT_SIZE: usize = ::core::mem::size_of::<Self>() * 8;

    /// Gets the value of a single bit.
    ///
    /// # Arguments
    ///
    /// * `bit` - The index of the bit to get.
    ///
    /// # Returns
    ///
    /// The value of the bit.
    fn get_bit(&self, bit: usize) -> bool;

    /// Sets the value of a bitfield.
    ///
    /// # Arguments
    ///
    /// * `field` - The bitfield to set the value of.
    /// * `bit_range` - The range of bits to set.
    fn set_field(&self, field: &mut [u8], bit_range: (usize, usize)) {
        fn zero_bit(byte: &mut u8, n_bit: u64) {
            let bit = 1 << n_bit;

            *byte &= !bit as u8;
        }

        fn one_bit(byte: &mut u8, n_bit: u64) {
            let bit = 1 << n_bit;

            *byte |= bit as u8;
        }

        let (lhs_bit, rhs_bit) = bit_range;

        for (i, bit_index) in (lhs_bit..=rhs_bit).enumerate() {
            let byte_index = bit_index / 8;
            let byte = &mut field[byte_index];

            if self.get_bit(i) {
                one_bit(byte, (bit_index % 8) as u64);
            } else {
                zero_bit(byte, (bit_index % 8) as u64);
            }
        }
    }

    /// Gets the value of a bitfield.
    ///
    /// # Arguments
    ///
    /// * `field` - The bitfield to get the value of.
    /// * `bit_range` - The range of bits to get.
    ///
    /// # Returns
    ///
    /// The value of the bitfield.
    fn get_field(field: &[u8], bit_range: (usize, usize)) -> Self;
}

macro_rules! impl_int {
    ($($typ: ident),+) => {
        $(
            impl FieldType for $typ {
                const IS_SIGNED: bool = $typ::MIN != 0;

                fn get_bit(&self, bit: usize) -> bool {
                    ((*self >> bit) & 1) == 1
                }

                fn get_field(field: &[u8], bit_range: (usize, usize)) -> Self {
                    let (lhs_bit, rhs_bit) = bit_range;
                    let mut val = 0;

                    for (i, bit_index) in (lhs_bit..=rhs_bit).enumerate() {
                        let byte_index = bit_index / 8;
                        let byte = field[byte_index];
                        let bit = 1 << (bit_index % 8);
                        let read_bit = byte & bit;

                        if read_bit != 0 {
                            let write_bit = 1 << i;

                            val |= write_bit;
                        }
                    }

                    // If the int type is signed, sign extend unconditionally
                    if Self::IS_SIGNED {
                        let bit_width = rhs_bit - lhs_bit + 1;
                        let unused_bits = Self::TOTAL_BIT_SIZE - bit_width;

                        val <<= unused_bits;
                        val >>= unused_bits;
                    }

                    val
                }
            }
        )+
    };
}

impl_int! {u8, u16, u32, u64, u128, i8, i16, i32, i64, i128}

impl FieldType for bool {
    const IS_SIGNED: bool = false;

    fn get_bit(&self, _bit: usize) -> bool {
        *self
    }

    fn get_field(field: &[u8], bit_range: (usize, usize)) -> Self {
        let (lhs_bit, rhs_bit) = bit_range;
        let mut val = false;

        for bit_index in lhs_bit..=rhs_bit {
            let byte_index = bit_index / 8;
            let byte = field[byte_index];
            let bit = 1 << (bit_index % 8);
            let read_bit = byte & bit;

            if read_bit != 0 {
                val = true;
            }
        }

        val
    }
}
