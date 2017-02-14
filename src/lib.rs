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

pub trait SignedNumeric: Numeric {
    fn is_negative(self) -> bool;
    fn as_negative(self, bits: u32) -> Self;
    fn as_unsigned(self, bits: u32) -> Self;
}

impl Numeric for u8 {
    #[inline(always)]
    fn one() -> Self {1}
    #[inline(always)]
    fn from_bit(bit: bool) -> Self {if bit {1} else {0}}
    #[inline(always)]
    fn to_bit(self) -> bool {self != 0}
}

impl Numeric for u16 {
    #[inline(always)]
    fn one() -> Self {1}
    #[inline(always)]
    fn from_bit(bit: bool) -> Self {if bit {1} else {0}}
    #[inline(always)]
    fn to_bit(self) -> bool {self != 0}
}

impl Numeric for u32 {
    #[inline(always)]
    fn one() -> Self {1}
    #[inline(always)]
    fn from_bit(bit: bool) -> Self {if bit {1} else {0}}
    #[inline(always)]
    fn to_bit(self) -> bool {self != 0}
}

impl Numeric for i32 {
    #[inline(always)]
    fn one() -> Self {1}
    #[inline(always)]
    fn from_bit(bit: bool) -> Self {if bit {1} else {0}}
    #[inline(always)]
    fn to_bit(self) -> bool {self != 0}
}

impl SignedNumeric for i32 {
    #[inline(always)]
    fn is_negative(self) -> bool {self < 0}
    #[inline(always)]
    fn as_negative(self, bits: u32) -> Self {self + (-1 << (bits - 1))}
    #[inline(always)]
    fn as_unsigned(self, bits: u32) -> Self {self - (-1 << (bits - 1))}
}

impl Numeric for u64 {
    #[inline(always)]
    fn one() -> Self {1}
    #[inline(always)]
    fn from_bit(bit: bool) -> Self {if bit {1} else {0}}
    #[inline(always)]
    fn to_bit(self) -> bool {self != 0}
}

impl Numeric for i64 {
    #[inline(always)]
    fn one() -> Self {1}
    #[inline(always)]
    fn from_bit(bit: bool) -> Self {if bit {1} else {0}}
    #[inline(always)]
    fn to_bit(self) -> bool {self != 0}
}

impl SignedNumeric for i64 {
    #[inline(always)]
    fn is_negative(self) -> bool {self < 0}
    #[inline(always)]
    fn as_negative(self, bits: u32) -> Self {self + (-1 << (bits - 1))}
    #[inline(always)]
    fn as_unsigned(self, bits: u32) -> Self {self - (-1 << (bits - 1))}
}
