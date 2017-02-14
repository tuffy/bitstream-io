use std::ops::{BitOrAssign, Shl, ShlAssign, ShrAssign, BitAnd};

pub mod read;
pub mod write;

pub use read::BitRead;
pub use read::BitReaderBE;
pub use read::BitReaderLE;

pub use write::BitWrite;
pub use write::BitWriterBE;
pub use write::BitWriterLE;

pub trait Numeric: Sized + Copy + Default +
    ShlAssign<Self> + ShrAssign<Self> + Shl<u32,Output=Self> +
    BitOrAssign<Self> + BitAnd<Self,Output=Self> {
    fn one() -> Self;
    fn from_bit(bit: bool) -> Self;
    fn to_bit(self) -> bool;
}

impl Numeric for u8 {
    #[inline]
    fn one() -> Self {1}
    #[inline]
    fn from_bit(bit: bool) -> Self {if bit {1} else {0}}
    #[inline]
    fn to_bit(self) -> bool {self != 0}
}

impl Numeric for u16 {
    #[inline]
    fn one() -> Self {1}
    #[inline]
    fn from_bit(bit: bool) -> Self {if bit {1} else {0}}
    #[inline]
    fn to_bit(self) -> bool {self != 0}
}

impl Numeric for u32 {
    #[inline]
    fn one() -> Self {1}
    #[inline]
    fn from_bit(bit: bool) -> Self {if bit {1} else {0}}
    #[inline]
    fn to_bit(self) -> bool {self != 0}
}

impl Numeric for u64 {
    #[inline]
    fn one() -> Self {1}
    #[inline]
    fn from_bit(bit: bool) -> Self {if bit {1} else {0}}
    #[inline]
    fn to_bit(self) -> bool {self != 0}
}
