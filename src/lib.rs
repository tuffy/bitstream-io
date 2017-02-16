//! Traits and helpers for bitstream handling functionality
//!
//! Bitstream readers and bitstream writers are designed
//! for reading potentially un-aligned binary values
//! into unsigned or signed integers from an underlying binary stream.
//!
//! The only requirement for reader streams is that they must
//! implement the [`BufRead`] trait, and the only requirement
//! for writer streams is that they must implement the [`Write`] trait.
//!
//! In addition, reader streams do not consume any more bytes
//! from the underlying reader than necessary, buffering only a
//! single partial byte as needed.
//! Writer streams also write out all whole bytes as they are accumulated.
//!
//! Readers and writers are also designed to work with integer
//! types of any possible size.  Many of Rust's built-in integer types are
//! supported by default, but others can be added with minimal effort.
//!
//! ## Type Sizes
//!
//! Because both the type sizes and bit counts are variable,
//! it is the responsibity of the programmer to ensure that
//! the capacity of one's variables does not exceed the
//! requested bit count when reading or writing.
//! Otherwise, an overflow error panic may occur.
//!
//! For example, reading 8 bits from the stream to a 32-bit variable
//! is harmless.
//! But reading 32 bits from the stream to an 8-bit variable
//! may result in a panic.
//! Similarly, writing a 32-bit variable in 8 bits is harmless
//! only so long as the topmost 24 bits are unoccupied.

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


/// This trait extends many common integer types (both unsigned and signed)
/// with a few trivial methods so that they can be used
/// with the bitstream handling traits.
pub trait Numeric: Sized + Copy + Default + Debug +
    ShlAssign<u32> + ShrAssign<u32> +
    Shl<u32,Output=Self> + Shr<u32,Output=Self> +
    BitOrAssign<Self> + BitAnd<Self,Output=Self> +
    Rem<Self,Output=Self> + RemAssign<Self> {

    /// The value of 1 in this type
    fn one() -> Self;

    /// Returns true if this value is 0, in its type
    fn is_zero(self) -> bool;

    /// Returns a u8 value in this type.
    fn from_u8(u: u8) -> Self;

    /// Assuming 0 <= value < 256, returns this value as a u8 type.
    fn to_u8(self) -> u8;
}

macro_rules! define_numeric {
    ($t:ty) => {
        impl Numeric for $t {
            #[inline(always)]
            fn one() -> Self {1}
            #[inline(always)]
            fn is_zero(self) -> bool {self == 0}
            #[inline(always)]
            fn from_u8(u: u8) -> Self {u as $t}
            #[inline(always)]
            fn to_u8(self) -> u8 {self as u8}
        }
    }
}

/// This trait extends many common signed integer types
/// so that they can be used with the bitstream handling traits.
pub trait SignedNumeric: Numeric {
    /// Returns true if this value is negative
    fn is_negative(self) -> bool;

    /// Given a two-complement positive value and certain number of bits,
    /// returns this value as a negative number.
    fn as_negative(self, bits: u32) -> Self;

    /// Given a negative value and a certain number of bits,
    /// returns this value as a twos-complement positive number.
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

/// This trait is for treating numeric types as a queue of bits
/// which values can be pushed to and popped from in
/// order to implement bitstream readers and writers.
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

/// This is a wrapper around some unsigned type
/// to turn it into a big-endian queue.
pub struct BitQueueBE<N: Numeric> {value: N, bits: u32}

impl<N: Numeric> BitQueueBE<N> {
    /// Wraps an existing value in a big-endian bit queue
    /// with the given number of bits.
    /// It is up to the programmer to ensure that the value
    /// is not larger than the given number of bits can contain.
    #[inline]
    pub fn from_value(value: N, bits: u32) -> BitQueueBE<N> {
        BitQueueBE{value: value, bits: bits}
    }

    /// Creates an empty queue with a value and bit count of 0.
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
        /*FIXME - optimize this in release?*/
        if !self.value.is_zero() {
            self.value <<= bits;
        }
        self.value |= value;
        self.bits += bits;
    }

    fn pop(&mut self, bits: u32) -> N {
        if bits < self.bits {
            let offset = self.bits - bits;
            let to_return = self.value >> offset;
            self.value %= N::one() << offset;
            self.bits -= bits;
            to_return
        } else {
            let to_return = self.value;
            self.value = N::default();
            self.bits = 0;
            to_return
        }
    }
}

/// This is a wrapper around some unsigned type
/// to turn it into a big-endian queue.
pub struct BitQueueLE<N: Numeric> {value: N, bits: u32}

impl<N: Numeric> BitQueueLE<N> {
    /// Wraps an existing value in a little-endian bit queue
    /// with the given number of bits.
    /// It is up to the programmer to ensure that the value
    /// is not larger than the given number of bits can contain.
    #[inline]
    pub fn from_value(value: N, bits: u32) -> BitQueueLE<N> {
        BitQueueLE{value: value, bits: bits}
    }

    /// Creates an empty queue with a value and bit count of 0.
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
        if bits < self.bits {
            let to_return = self.value % (N::one() << bits);
            self.value >>= bits;
            self.bits -= bits;
            to_return
        } else {
            let to_return = self.value;
            self.value = N::default();
            self.bits = 0;
            to_return
        }
    }
}
