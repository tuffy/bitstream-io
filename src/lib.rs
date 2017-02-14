use std::ops::{BitOrAssign, Shl, ShlAssign, ShrAssign, BitAnd};
use std::fmt::Debug;

pub mod read;
pub mod write;

pub use read::BitRead;
pub use read::BitReaderBE;
pub use read::BitReaderLE;

pub use write::BitWrite;
pub use write::BitWriterBE;
pub use write::BitWriterLE;

pub trait Numeric: Sized + Copy + Default + Debug +
    ShlAssign<Self> + ShrAssign<Self> + Shl<u32,Output=Self> +
    BitOrAssign<Self> + BitAnd<Self,Output=Self> {
    fn one() -> Self;
    fn from_bit(bit: bool) -> Self;
    fn to_bit(self) -> bool;
}

macro_rules! define_numeric {
    ($t:ty) => {
        impl Numeric for $t {
            #[inline(always)]
            fn one() -> Self {1}
            #[inline(always)]
            fn from_bit(bit: bool) -> Self {if bit {1} else {0}}
            #[inline(always)]
            fn to_bit(self) -> bool {self != 0}
        }
    }
}

pub trait SignedNumeric: Numeric {
    fn is_negative(self) -> bool;
    fn as_negative(self, bits: u32) -> Self;
    fn as_unsigned(self, bits: u32) -> Self;
}

macro_rules! define_signed_numeric {
    ($t:ty) => {
        impl SignedNumeric for $t {
            #[inline(always)]
            fn is_negative(self) -> bool {self < 0}
            #[inline(always)]
            fn as_negative(self, bits: u32) -> Self {self + (-1 << (bits - 1))}
            #[inline(always)]
            fn as_unsigned(self, bits: u32) -> Self {self - (-1 << (bits - 1))}
        }
    }
}

define_numeric!(u8);
define_numeric!(i8);
define_numeric!(u16);
define_numeric!(i16);
define_numeric!(u32);
define_numeric!(i32);
define_numeric!(u64);
define_numeric!(i64);

define_signed_numeric!(i8);
define_signed_numeric!(i16);
define_signed_numeric!(i32);
define_signed_numeric!(i64);
