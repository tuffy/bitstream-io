use std::ops::{BitOrAssign, Shl, Shr, ShlAssign, ShrAssign, BitAnd,
               Rem, RemAssign};
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
    ShlAssign<u32> + ShrAssign<u32> +
    Shl<u32,Output=Self> + Shr<u32,Output=Self> +
    BitOrAssign<Self> + BitAnd<Self,Output=Self> +
    Rem<Self,Output=Self> + RemAssign<Self> {
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

pub struct BitQueueBE<A: Numeric> {value: A, bits: u32}

impl<A: Numeric> BitQueueBE<A> {
    #[inline]
    pub fn new() -> BitQueueBE<A> {BitQueueBE{value: A::default(), bits: 0}}

    #[inline(always)]
    pub fn value(self) -> A {self.value}

    #[inline(always)]
    pub fn len(&self) -> u32 {self.bits}

    #[inline(always)]
    pub fn is_empty(&self) -> bool {self.bits == 0}

    pub fn clear(&mut self) {self.value = A::default(); self.bits = 0;}

    pub fn push(&mut self, bits: u32, value: A) {
        self.value <<= bits;
        self.value |= value;
        self.bits += bits;
    }

    pub fn pop(&mut self, bits: u32) -> A {
        let offset = self.bits - bits;
        let to_return = self.value >> offset;
        self.value %= A::one() << offset;
        self.bits -= bits;
        to_return
    }
}

pub struct BitQueueLE<A: Numeric> {value: A, bits: u32}

impl<A: Numeric> BitQueueLE<A> {
    #[inline]
    pub fn new() -> BitQueueLE<A> {BitQueueLE{value: A::default(), bits: 0}}

    #[inline(always)]
    pub fn value(self) -> A {self.value}

    #[inline(always)]
    pub fn len(&self) -> u32 {self.bits}

    #[inline(always)]
    pub fn is_empty(&self) -> bool {self.bits == 0}

    pub fn clear(&mut self) {self.value = A::default(); self.bits = 0;}

    pub fn push(&mut self, bits: u32, mut value: A) {
        value <<= self.bits;
        self.value |= value;
        self.bits += bits;
    }

    pub fn pop(&mut self, bits: u32) -> A {
        let to_return = self.value % (A::one() << bits);
        self.value >>= bits;
        self.bits -= bits;
        to_return
    }
}
