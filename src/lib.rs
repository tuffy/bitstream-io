// Copyright 2017 Brian Langenberger
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Traits and helpers for bitstream handling functionality
//!
//! Bitstream readers are for reading signed and unsigned integer
//! values from a stream whose sizes may not be whole bytes.
//! Bitstream writers are for writing signed and unsigned integer
//! values to a stream, also potentially un-aligned at a whole byte.
//!
//! Both big-endian and little-endian streams are supported.
//!
//! The only requirement for wrapped reader streams is that they must
//! implement the `Read` trait, and the only requirement
//! for writer streams is that they must implement the `Write` trait.
//!
//! In addition, reader streams do not consume any more bytes
//! from the underlying reader than necessary, buffering only a
//! single partial byte as needed.
//! Writer streams also write out all whole bytes as they are accumulated.
//!
//! Readers and writers are also designed to work with integer
//! types of any possible size.
//! Many of Rust's built-in integer types are supported by default.
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
//! is harmless (the topmost 24 bits are left empty),
//! but reading 32 bits from the stream to an 8-bit variable
//! may result in a panic.
//! Similarly, writing a 32-bit variable to 8 bits is also harmless
//! (the topmost 24 bits are ignored), but writing an 8-bit variable
//! to 32 bits in the stream may cause a panic.

use std::ops::{Shl, ShlAssign, Shr, ShrAssign, Rem, RemAssign, BitOrAssign,
               BitXor, Not, Sub};
use std::marker::PhantomData;
use std::fmt::Debug;

pub mod read;
pub mod write;
pub mod huffman;
pub use read::BitReader;
pub use write::BitWriter;


/// This trait extends many common integer types (both unsigned and signed)
/// with a few trivial methods so that they can be used
/// with the bitstream handling traits.
pub trait Numeric: Sized + Copy + Default + Debug +
    Shl<u32,Output=Self> + ShlAssign<u32> +
    Shr<u32,Output=Self> + ShrAssign<u32> +
    Rem<Self,Output=Self> + RemAssign<Self> +
    BitOrAssign<Self> + BitXor<Self,Output=Self> + Not<Output=Self> +
    Sub<Self,Output=Self> {

    /// The value of 1 in this type
    fn one() -> Self;

    /// Returns true if this value is 0, in its type
    fn is_zero(self) -> bool;

    /// Returns a `u8` value in this type
    fn from_u8(u: u8) -> Self;

    /// Assuming 0 <= value < 256, returns this value as a `u8` type
    fn to_u8(self) -> u8;

    /// Counts the number of 1 bits
    fn count_ones(self) -> u32;

    /// Counts the number of leading zeros
    fn leading_zeros(self) -> u32;

    /// Counts the number of trailing zeros
    fn trailing_zeros(self) -> u32;

    /// Size of type in bits
    fn bits_size() -> u32;
}

macro_rules! define_numeric {
    ($t:ty, $bits:expr) => {
        impl Numeric for $t {
            #[inline(always)]
            fn one() -> Self {1}
            #[inline(always)]
            fn is_zero(self) -> bool {self == 0}
            #[inline(always)]
            fn from_u8(u: u8) -> Self {u as $t}
            #[inline(always)]
            fn to_u8(self) -> u8 {self as u8}
            #[inline(always)]
            fn count_ones(self) -> u32 {self.count_ones()}
            #[inline(always)]
            fn leading_zeros(self) -> u32 {self.leading_zeros()}
            #[inline(always)]
            fn trailing_zeros(self) -> u32 {self.trailing_zeros()}
            #[inline(always)]
            fn bits_size() -> u32 {$bits}
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

define_numeric!(u8, 8);
define_numeric!(i8, 8);
define_numeric!(u16, 16);
define_numeric!(i16, 16);
define_numeric!(u32, 32);
define_numeric!(i32, 32);
define_numeric!(u64, 64);
define_numeric!(i64, 64);

define_signed_numeric!(i8);
define_signed_numeric!(i16);
define_signed_numeric!(i32);
define_signed_numeric!(i64);

pub trait Endianness {
    fn leading_sign() -> bool;

    fn push<N>(bits_acc: &mut u32,
               value_acc: &mut N,
               bits: u32,
               value: N) where N: Numeric;

    fn pop<N>(bits_acc: &mut u32,
              value_acc: &mut N,
              bits: u32) -> N where N: Numeric;

    fn drop<N>(bits_acc: &mut u32,
               value_acc: &mut N,
               bits: u32) where N: Numeric;

    fn next_zeros<N>(bits: u32, value: N) -> u32 where N: Numeric;

    fn next_ones<N>(bits: u32, value: N) -> u32 where N: Numeric;
}

pub struct BigEndian {}
pub type BE = BigEndian;

impl Endianness for BigEndian {
    #[inline(always)]
    fn leading_sign() -> bool {true}

    fn push<N>(bits_acc: &mut u32,
               value_acc: &mut N,
               bits: u32,
               value: N) where N: Numeric {
        if !value_acc.is_zero() {
            *value_acc <<= bits;
        }
        *value_acc |= value;
        *bits_acc += bits;
    }

    fn pop<N>(bits_acc: &mut u32,
              value_acc: &mut N,
              bits: u32) -> N where N: Numeric {
        if bits < *bits_acc {
            let offset = *bits_acc - bits;
            let to_return = *value_acc >> offset;
            *value_acc %= N::one() << offset;
            *bits_acc -= bits;
            to_return
        } else {
            let to_return = *value_acc;
            *value_acc = N::default();
            *bits_acc = 0;
            to_return
        }
    }

    fn drop<N>(bits_acc: &mut u32,
               value_acc: &mut N,
               bits: u32) where N: Numeric {
        if bits < *bits_acc {
            *value_acc %= N::one() << (*bits_acc - bits);
            *bits_acc -= bits;
        } else {
            *value_acc = N::default();
            *bits_acc = 0;
        }
    }

    #[inline]
    fn next_zeros<N>(bits: u32, value: N) -> u32 where N: Numeric {
        value.leading_zeros() - (N::bits_size() - bits)
    }

    #[inline]
    fn next_ones<N>(bits: u32, value: N) -> u32 where N: Numeric {
        if bits < N::bits_size() {
            (value ^ ((N::one() << bits) - N::one())).leading_zeros() -
            (N::bits_size() - bits)
        } else {
            (!value).leading_zeros()
        }
    }
}

pub struct LittleEndian {}
pub type LE = LittleEndian;

impl Endianness for LittleEndian {
    #[inline(always)]
    fn leading_sign() -> bool {false}

    fn push<N>(bits_acc: &mut u32,
               value_acc: &mut N,
               bits: u32,
               mut value: N) where N: Numeric {
        value <<= *bits_acc;
        *value_acc |= value;
        *bits_acc += bits;
    }

    fn pop<N>(bits_acc: &mut u32,
              value_acc: &mut N,
              bits: u32) -> N where N: Numeric {
        if bits < *bits_acc {
            let to_return = *value_acc % (N::one() << bits);
            *value_acc >>= bits;
            *bits_acc -= bits;
            to_return
        } else {
            let to_return = *value_acc;
            *value_acc = N::default();
            *bits_acc = 0;
            to_return
        }
    }

    fn drop<N>(bits_acc: &mut u32,
               value_acc: &mut N,
               bits: u32) where N: Numeric {
        if bits < *bits_acc {
            *value_acc >>= bits;
            *bits_acc -= bits;
        } else {
            *value_acc = N::default();
            *bits_acc = 0;
        }
    }

    #[inline]
    fn next_zeros<N>(_: u32, value: N) -> u32 where N: Numeric {
        value.trailing_zeros()
    }

    #[inline]
    fn next_ones<N>(_: u32, value: N) -> u32 where N: Numeric {
        (value ^ !N::default()).trailing_zeros()
    }
}

pub struct BitQueue<E: Endianness, N: Numeric> {
    phantom: PhantomData<E>,
    value: N,
    bits: u32,
}

impl<E: Endianness, N: Numeric> BitQueue<E, N> {
    /// Returns a new empty queue
    #[inline]
    pub fn new() -> BitQueue<E, N> {
        BitQueue{phantom: PhantomData, value: N::default(), bits: 0}
    }

    /// Creates a new queue from the given value with the given size
    #[inline]
    pub fn from_value(value: N, bits: u32) -> BitQueue<E,N> {
        BitQueue{phantom: PhantomData, value: value, bits: bits}
    }

    /// Sets the queue to a given value with the given number of bits
    #[inline]
    pub fn set(&mut self, value: N, bits: u32) {
        self.value = value;
        self.bits = bits;
    }

    /// Consumes the queue and returns its current value
    #[inline(always)]
    pub fn value(self) -> N {self.value}

    /// Returns the total bits in the queue
    #[inline(always)]
    pub fn len(&self) -> u32 {self.bits}

    /// Returns true if the queue is empty
    #[inline(always)]
    pub fn is_empty(&self) -> bool {self.bits == 0}

    /// Drops all values in the queue
    #[inline(always)]
    pub fn clear(&mut self) {self.set(N::default(), 0)}

    /// Returns true if all bits remaining in the queue are 0
    #[inline(always)]
    pub fn all_0(&self) -> bool {self.value.count_ones() == 0}

    /// Returns true if all bits remaining in the queue are 1
    #[inline(always)]
    pub fn all_1(&self) -> bool {self.value.count_ones() == self.bits}

    /// Pushes a value with the given number of bits onto the tail of the queue
    #[inline(always)]
    pub fn push(&mut self, bits: u32, value: N) {
        E::push(&mut self.bits, &mut self.value, bits, value)
    }

    /// Pops a value with the given number of bits from the head of the queue
    #[inline(always)]
    pub fn pop(&mut self, bits: u32) -> N {
        E::pop(&mut self.bits, &mut self.value, bits)
    }

    /// Drops the given number of bits from the head of the queue
    /// without returning them.
    #[inline(always)]
    pub fn drop(&mut self, bits: u32) {
        E::drop(&mut self.bits, &mut self.value, bits)
    }

    /// Pops all 0 bits up to and including the next 1 bit
    /// and returns the amount of 0 bits popped
    #[inline]
    pub fn pop_0(&mut self) -> u32 {
        let zeros = E::next_zeros(self.bits, self.value);
        self.drop(zeros + 1);
        zeros
    }

    /// Pops all 1 bits up to and including the next 0 bit
    /// and returns the amount of 1 bits popped
    #[inline]
    pub fn pop_1(&mut self) -> u32 {
        let ones = E::next_ones(self.bits, self.value);
        self.drop(ones + 1);
        ones
    }
}
