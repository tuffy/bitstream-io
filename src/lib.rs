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
    fn from_u8(u: u8) -> Self;
    fn to_u8(self) -> u8;
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
            #[inline(always)]
            fn from_u8(u: u8) -> Self {u as $t}
            #[inline(always)]
            fn to_u8(self) -> u8 {self as u8}
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

pub trait BitQueue<N: Numeric> {
    /// Discards queue's current status and sets it to new bits and value
    fn set(&mut self, value: N, bits: u32);

    /// Consumes queue and returns its internal value
    fn value(self) -> N;

    /// Current length of queue, in bits
    fn len(&self) -> u32;

    /// Whether or not the queue is empty
    #[inline(always)]
    fn is_empty(&self) -> bool {self.len() == 0}

    /// Discards queue's current status and sets bits and value to 0
    #[inline(always)]
    fn clear(&mut self) {self.set(N::default(), 0)}

    /// Pushes a new value onto the back of the queue
    /// using the given number of bits.
    /// May panic if the total number of bits exceeds
    /// the size of the type being pushed onto.
    fn push(&mut self, bits: u32, value: N);

    /// Pops a value from the front of the queue
    /// with the given number of bits.
    /// May panic if the total number of bytes popped
    /// exceeds the length of the queue.
    fn pop(&mut self, bits: u32) -> N;
}

pub struct BitQueueBE<N: Numeric> {value: N, bits: u32}

impl<N: Numeric> BitQueueBE<N> {
    #[inline]
    pub fn new() -> BitQueueBE<N> {
        BitQueueBE{value: N::default(), bits: 0}
    }
}

impl<N: Numeric> BitQueue<N> for BitQueueBE<N> {
    #[inline]
    fn set(&mut self, value: N, bits: u32) {
        self.value = value; self.bits = bits;
    }

    #[inline(always)]
    fn value(self) -> N {self.value}

    #[inline(always)]
    fn len(&self) -> u32 {self.bits}

    fn push(&mut self, bits: u32, value: N) {
        self.value <<= bits;
        self.value |= value;
        self.bits += bits;
    }

    fn pop(&mut self, bits: u32) -> N {
        let offset = self.bits - bits;
        let to_return = self.value >> offset;
        self.value %= N::one() << offset;
        self.bits -= bits;
        to_return
    }
}

pub struct BitQueueLE<N: Numeric> {value: N, bits: u32}

impl<N: Numeric> BitQueueLE<N> {
    #[inline]
    pub fn new() -> BitQueueLE<N> {
        BitQueueLE{value: N::default(), bits: 0}
    }
}

impl<N: Numeric> BitQueue<N> for BitQueueLE<N> {
    #[inline]
    fn set(&mut self, value: N, bits: u32) {
        self.value = value; self.bits = bits;
    }

    #[inline(always)]
    fn value(self) -> N {self.value}

    #[inline(always)]
    fn len(&self) -> u32 {self.bits}

    fn push(&mut self, bits: u32, mut value: N) {
        value <<= self.bits;
        self.value |= value;
        self.bits += bits;
    }

    fn pop(&mut self, bits: u32) -> N {
        let to_return = self.value % (N::one() << bits);
        self.value >>= bits;
        self.bits -= bits;
        to_return
    }
}
