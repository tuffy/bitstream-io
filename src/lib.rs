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

//! # Minimum Compiler Version
//!
//! Beginning with version 2.4, the minimum compiler version has been
//! updated to Rust 1.79.
//!
//! The issue is that reading an excessive number of
//! bits to a type which is too small to hold them,
//! or writing an excessive number of bits from too small of a type,
//! are always errors:
//! ```
//! use std::io::{Read, Cursor};
//! use bitstream_io::{BigEndian, BitReader, BitRead};
//! let data = [0; 10];
//! let mut r = BitReader::endian(Cursor::new(&data), BigEndian);
//! let x: Result<u32, _> = r.read(64);  // reading 64 bits to u32 always fails at runtime
//! assert!(x.is_err());
//! ```
//! but those errors will not be caught until the program runs,
//! which is less than ideal for the common case in which
//! the number of bits is already known at compile-time.
//!
//! But starting with Rust 1.79, we can now have read and write methods
//! which take a constant number of bits and can validate the number of bits
//! are small enough for the type being read/written at compile-time:
//! ```rust,ignore
//! use std::io::{Read, Cursor};
//! use bitstream_io::{BigEndian, BitReader, BitRead};
//! let data = [0; 10];
//! let mut r = BitReader::endian(Cursor::new(&data), BigEndian);
//! let x: Result<u32, _> = r.read_in::<64, _>();  // doesn't compile at all
//! ```
//! Since catching potential bugs at compile-time is preferable
//! to encountering errors at runtime, this will hopefully be
//! an improvement in the long run.

//! # Changes From 2.X.X
//!
//! `BitRead` and `BitWrite` traits previously used their
//! `read` and `write` methods as the base upon which the
//! the rest of the trait was implemented.
//! Starting with version 3, the new `read_unsigned` and
//! `write_unsigned` methods are the base,
//! which take only unsigned integer types.
//! `read_signed` and `write_signed` are implemented
//! in terms of `read_unsigned` and `write_signed`
//! based on the stream's endianness.
//! The updated `read` and `write` methods take either
//! signed or unsigned integer types (as they did before)
//! and simply call `read|write_unsigned` or `read|write_signed`
//! as needed.
//! This change makes the interface both more symmetical
//! and harder to accidentally misuse.

//! # Migrating From Pre 1.0.0
//!
//! There are now `BitRead` and `BitWrite` traits for bitstream
//! reading and writing (analogous to the standard library's
//! `Read` and `Write` traits) which you will also need to import.
//! The upside to this approach is that library consumers
//! can now make functions and methods generic over any sort
//! of bit reader or bit writer, regardless of the underlying
//! stream byte source or endianness.

#![warn(missing_docs)]
#![forbid(unsafe_code)]
#![no_std]

extern crate alloc;
#[cfg(feature = "std")]
extern crate std;

#[cfg(not(feature = "std"))]
use core2::io;

use core::ops::{BitOrAssign, BitXor, Not, Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub};
use core::{fmt::Debug, marker::PhantomData, mem};
#[cfg(feature = "std")]
use std::io;

pub mod huffman;
pub mod read;
pub mod write;
pub use read::{
    BitRead, BitReader, ByteRead, ByteReader, FromBitStream, FromBitStreamWith, FromByteStream,
    FromByteStreamWith, HuffmanRead,
};
pub use write::{
    BitCounter, BitRecorder, BitWrite, BitWriter, ByteWrite, ByteWriter, HuffmanWrite, ToBitStream,
    ToBitStreamWith, ToByteStream, ToByteStreamWith,
};

/// A trait intended for simple fixed-length primitives (such as ints and floats)
/// which allows them to be read and written to streams of
/// different endiannesses verbatim.
pub trait Primitive {
    /// The raw byte representation of this numeric type
    type Bytes: AsRef<[u8]> + AsMut<[u8]>;

    /// An empty buffer of this type's size
    fn buffer() -> Self::Bytes;

    /// Our value in big-endian bytes
    fn to_be_bytes(self) -> Self::Bytes;

    /// Our value in little-endian bytes
    fn to_le_bytes(self) -> Self::Bytes;

    /// Convert big-endian bytes to our value
    fn from_be_bytes(bytes: Self::Bytes) -> Self;

    /// Convert little-endian bytes to our value
    fn from_le_bytes(bytes: Self::Bytes) -> Self;
}

macro_rules! define_primitive_numeric {
    ($t:ty) => {
        impl Primitive for $t {
            type Bytes = [u8; mem::size_of::<$t>()];

            #[inline(always)]
            fn buffer() -> Self::Bytes {
                [0; mem::size_of::<$t>()]
            }
            #[inline(always)]
            fn to_be_bytes(self) -> Self::Bytes {
                self.to_be_bytes()
            }
            #[inline(always)]
            fn to_le_bytes(self) -> Self::Bytes {
                self.to_le_bytes()
            }
            #[inline(always)]
            fn from_be_bytes(bytes: Self::Bytes) -> Self {
                <$t>::from_be_bytes(bytes)
            }
            #[inline(always)]
            fn from_le_bytes(bytes: Self::Bytes) -> Self {
                <$t>::from_le_bytes(bytes)
            }
        }
    };
}

impl<const N: usize> Primitive for [u8; N] {
    type Bytes = [u8; N];

    #[inline(always)]
    fn buffer() -> Self::Bytes {
        [0; N]
    }

    #[inline(always)]
    fn to_be_bytes(self) -> Self::Bytes {
        self
    }

    #[inline(always)]
    fn to_le_bytes(self) -> Self::Bytes {
        self
    }

    #[inline(always)]
    fn from_be_bytes(bytes: Self::Bytes) -> Self {
        bytes
    }

    #[inline(always)]
    fn from_le_bytes(bytes: Self::Bytes) -> Self {
        bytes
    }
}

/// This trait is for integer types which can be read or written
/// to a bit stream as a partial amount of bits.
/// It unifies signed and unsigned integer types by delegating
/// reads and writes to the signed and unsigned reading
/// and writing methods as appropriate.
pub trait Integer {
    /// Reads a value of ourself from the stream
    /// with the given number of bits.
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    /// Also returns an error if our type is too small
    /// to hold the requested number of bits.
    fn read<R: BitRead + ?Sized>(reader: &mut R, bits: u32) -> io::Result<Self>
    where
        Self: Sized;

    /// Reads a value of ourself from the stream
    /// with the given number of bits.
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    /// A compile-time error occurs if the given number of bits
    /// is larger than our type.
    fn read_in<const BITS: u32, R: BitRead + ?Sized>(reader: &mut R) -> io::Result<Self>
    where
        Self: Sized;

    /// Writes ourself to the stream using the given number of bits.
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    /// Returns an error if our value is too small
    /// to hold the given number of bits.
    /// Returns an error if our value is too large
    /// to fit the given number of bits.
    fn write<W: BitWrite + ?Sized>(self, writer: &mut W, bits: u32) -> io::Result<()>;

    /// Writes ourself to the stream using the given const number of bits.
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    /// Returns an error if our value is too large
    /// to fit the given number of bits.
    /// A compile-time error occurs if the given number of bits
    /// is larger than our type.
    fn write_out<const BITS: u32, W: BitWrite + ?Sized>(self, writer: &mut W) -> io::Result<()>;
}

/// This trait extends many common integer types (both unsigned and signed)
/// with a few trivial methods so that they can be used
/// with the bitstream handling traits.
pub trait Numeric:
    Primitive
    + Sized
    + Copy
    + Default
    + Debug
    + PartialOrd
    + Shl<u32, Output = Self>
    + ShlAssign<u32>
    + Shr<u32, Output = Self>
    + ShrAssign<u32>
    + Rem<Self, Output = Self>
    + RemAssign<Self>
    + BitOrAssign<Self>
    + BitXor<Self, Output = Self>
    + Not<Output = Self>
    + Sub<Self, Output = Self>
{
    /// Size of type in bits
    const BITS_SIZE: u32;

    /// The value of 1 in this type
    const ONE: Self;

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
}

macro_rules! define_numeric {
    ($t:ty) => {
        define_primitive_numeric!($t);

        impl Numeric for $t {
            const BITS_SIZE: u32 = mem::size_of::<$t>() as u32 * 8;

            const ONE: Self = 1;

            #[inline(always)]
            fn is_zero(self) -> bool {
                self == 0
            }
            #[inline(always)]
            fn from_u8(u: u8) -> Self {
                u as $t
            }
            #[inline(always)]
            fn to_u8(self) -> u8 {
                self as u8
            }
            #[inline(always)]
            fn count_ones(self) -> u32 {
                self.count_ones()
            }
            #[inline(always)]
            fn leading_zeros(self) -> u32 {
                self.leading_zeros()
            }
            #[inline(always)]
            fn trailing_zeros(self) -> u32 {
                self.trailing_zeros()
            }
        }
    };
}

/// This trait extends many common unsigned integer types
/// so that they can be used with the bitstream handling traits.
pub trait UnsignedNumeric: Numeric + Into<crate::write::UnsignedValue> {
    /// The signed variant of ourself
    type Signed: SignedNumeric<Unsigned = Self>;

    /// Given a twos-complement value,
    /// return this value is a non-negative signed number.
    /// The location of the sign bit depends on the stream's endianness
    /// and is not stored in the result.
    ///
    /// # Example
    /// ```
    /// use bitstream_io::UnsignedNumeric;
    /// assert_eq!(0b00000001u8.as_non_negative(), 1i8);
    /// ```
    fn as_non_negative(self) -> Self::Signed;

    /// Given a two-complement positive value and certain number of bits,
    /// returns this value as a negative signed number.
    /// The location of the sign bit depends on the stream's endianness
    /// and is not stored in the result.
    ///
    /// # Example
    /// ```
    /// use bitstream_io::UnsignedNumeric;
    /// assert_eq!(0b01111111u8.as_negative(8), -1i8);
    /// ```
    fn as_negative(self, bits: u32) -> Self::Signed;

    /// Given a two-complement positive value and certain number of bits,
    /// returns this value as a negative number.
    ///
    /// # Example
    /// ```
    /// use bitstream_io::UnsignedNumeric;
    /// assert_eq!(0b01111111u8.as_negative_fixed::<8>(), -1i8);
    /// ```
    fn as_negative_fixed<const BITS: u32>(self) -> Self::Signed;
}

macro_rules! define_unsigned_numeric {
    ($t:ty, $s:ty) => {
        define_numeric!($t);

        impl UnsignedNumeric for $t {
            type Signed = $s;

            #[inline(always)]
            fn as_non_negative(self) -> Self::Signed {
                self as $s
            }
            #[inline(always)]
            fn as_negative(self, bits: u32) -> Self::Signed {
                (self as $s) + (-1 << (bits - 1))
            }
            #[inline(always)]
            fn as_negative_fixed<const BITS: u32>(self) -> Self::Signed {
                (self as $s) + (-1 << (BITS - 1))
            }
        }

        impl Integer for $t {
            #[inline]
            fn read<R: BitRead + ?Sized>(reader: &mut R, bits: u32) -> io::Result<Self>
            where
                Self: Sized,
            {
                reader.read_unsigned(bits)
            }

            #[inline]
            fn read_in<const BITS: u32, R: BitRead + ?Sized>(reader: &mut R) -> io::Result<Self>
            where
                Self: Sized,
            {
                reader.read_unsigned_in::<BITS, _>()
            }

            #[inline]
            fn write<W: BitWrite + ?Sized>(self, writer: &mut W, bits: u32) -> io::Result<()> {
                writer.write_unsigned(bits, self)
            }

            #[inline]
            fn write_out<const BITS: u32, W: BitWrite + ?Sized>(
                self,
                writer: &mut W,
            ) -> io::Result<()> {
                writer.write_unsigned_out::<BITS, _>(self)
            }
        }
    };
}

/// This trait extends many common signed integer types
/// so that they can be used with the bitstream handling traits.
pub trait SignedNumeric: Numeric + Into<crate::write::SignedValue> {
    /// The unsigned variant of ourself
    type Unsigned: UnsignedNumeric<Signed = Self>;

    /// Returns true if this value is negative
    ///
    /// # Example
    /// ```
    /// use bitstream_io::SignedNumeric;
    /// assert!(!1i8.is_negative());
    /// assert!((-1i8).is_negative());
    /// ```
    fn is_negative(self) -> bool;

    /// Returns ourself as a non-negative value.
    /// The location of the sign bit depends on the stream's endianness
    /// and is not stored in the result.
    ///
    /// # Example
    /// ```
    /// use bitstream_io::SignedNumeric;
    /// assert_eq!(1i8.as_non_negative(), 0b00000001u8);
    /// ```
    fn as_non_negative(self) -> Self::Unsigned;

    /// Given a negative value and a certain number of bits,
    /// returns this value as a twos-complement positive number.
    /// The location of the sign bit depends on the stream's endianness
    /// and is not stored in the result.
    ///
    /// # Example
    /// ```
    /// use bitstream_io::SignedNumeric;
    /// assert_eq!((-1i8).as_negative(8), 0b01111111u8);
    /// ```
    fn as_negative(self, bits: u32) -> Self::Unsigned;

    /// Given a negative value and a certain number of bits,
    /// returns this value as a twos-complement positive number.
    ///
    /// # Example
    /// ```
    /// use bitstream_io::SignedNumeric;
    /// assert_eq!((-1i8).as_negative_fixed::<8>(), 0b01111111u8);
    /// ```
    fn as_negative_fixed<const BITS: u32>(self) -> Self::Unsigned;
}

macro_rules! define_signed_numeric {
    ($t:ty, $u:ty) => {
        define_numeric!($t);

        impl SignedNumeric for $t {
            type Unsigned = $u;

            #[inline(always)]
            fn is_negative(self) -> bool {
                self.is_negative()
            }
            fn as_non_negative(self) -> Self::Unsigned {
                self as $u
            }
            fn as_negative(self, bits: u32) -> Self::Unsigned {
                (self - (-1 << (bits - 1))) as $u
            }
            fn as_negative_fixed<const BITS: u32>(self) -> Self::Unsigned {
                (self - (-1 << (BITS - 1))) as $u
            }
        }

        impl Integer for $t {
            #[inline]
            fn read<R: BitRead + ?Sized>(reader: &mut R, bits: u32) -> io::Result<Self>
            where
                Self: Sized,
            {
                reader.read_signed(bits)
            }

            #[inline]
            fn read_in<const BITS: u32, R: BitRead + ?Sized>(reader: &mut R) -> io::Result<Self>
            where
                Self: Sized,
            {
                reader.read_signed_in::<BITS, _>()
            }

            #[inline]
            fn write<W: BitWrite + ?Sized>(self, writer: &mut W, bits: u32) -> io::Result<()> {
                writer.write_signed(bits, self)
            }

            #[inline]
            fn write_out<const BITS: u32, W: BitWrite + ?Sized>(
                self,
                writer: &mut W,
            ) -> io::Result<()> {
                writer.write_signed_out::<BITS, _>(self)
            }
        }
    };
}

define_unsigned_numeric!(u8, i8);
define_unsigned_numeric!(u16, i16);
define_unsigned_numeric!(u32, i32);
define_unsigned_numeric!(u64, i64);
define_unsigned_numeric!(u128, i128);

define_signed_numeric!(i8, u8);
define_signed_numeric!(i16, u16);
define_signed_numeric!(i32, u32);
define_signed_numeric!(i64, u64);
define_signed_numeric!(i128, u128);

define_primitive_numeric!(f32);
define_primitive_numeric!(f64);

/// A stream's endianness, or byte order, for determining
/// how bits should be read.
///
/// It comes in `BigEndian` and `LittleEndian` varieties
/// (which may be shortened to `BE` and `LE`)
/// and is not something programmers should have to implement
/// in most cases.
pub trait Endianness: Sized {
    /// Pushes the given bits and value onto an accumulator
    /// with the given bits and value.
    fn push<N>(queue: &mut BitQueue<Self, N>, bits: u32, value: N)
    where
        N: Numeric;

    /// Pushes the given constant number of bits and value onto an accumulator
    /// with the given bits and value.
    fn push_fixed<const B: u32, N>(queue: &mut BitQueue<Self, N>, value: N)
    where
        N: Numeric;

    /// Pops a value with the given number of bits from an accumulator
    /// with the given bits and value.
    fn pop<N>(queue: &mut BitQueue<Self, N>, bits: u32) -> N
    where
        N: Numeric;

    /// Pops a value with the given number of constant bits
    /// from an accumulator with the given bits and value.
    fn pop_fixed<const B: u32, N>(queue: &mut BitQueue<Self, N>) -> N
    where
        N: Numeric;

    /// Drops the given number of bits from an accumulator
    /// with the given bits and value.
    fn drop<N>(queue: &mut BitQueue<Self, N>, bits: u32)
    where
        N: Numeric;

    /// Returns the next number of 0 bits from an accumulator
    /// with the given bits and value.
    fn next_zeros<N>(queue: &BitQueue<Self, N>) -> u32
    where
        N: Numeric;

    /// Returns the next number of 1 bits from an accumulator
    /// with the given bits and value.
    fn next_ones<N>(queue: &BitQueue<Self, N>) -> u32
    where
        N: Numeric;

    /// Reads signed value from reader in this endianness
    fn read_signed<R, S>(r: &mut R, bits: u32) -> io::Result<S>
    where
        R: BitRead,
        S: SignedNumeric;

    /// Reads signed value from reader in this endianness
    fn read_signed_fixed<R, const B: u32, S>(r: &mut R) -> io::Result<S>
    where
        R: BitRead,
        S: SignedNumeric;

    /// Writes signed value to writer in this endianness
    fn write_signed<W, S>(w: &mut W, bits: u32, value: S) -> io::Result<()>
    where
        W: BitWrite,
        S: SignedNumeric;

    /// Writes signed value to writer in this endianness
    fn write_signed_fixed<W, const B: u32, S>(w: &mut W, value: S) -> io::Result<()>
    where
        W: BitWrite,
        S: SignedNumeric;

    /// Reads convertable numeric value from reader in this endianness
    fn read_primitive<R, V>(r: &mut R) -> io::Result<V>
    where
        R: BitRead,
        V: Primitive;

    /// Writes convertable numeric value to writer in this endianness
    fn write_primitive<W, V>(w: &mut W, value: V) -> io::Result<()>
    where
        W: BitWrite,
        V: Primitive;

    /// Reads entire numeric value from reader in this endianness
    fn read_numeric<R, V>(r: R) -> io::Result<V>
    where
        R: io::Read,
        V: Primitive;

    /// Writes entire numeric value to writer in this endianness
    fn write_numeric<W, V>(w: W, value: V) -> io::Result<()>
    where
        W: io::Write,
        V: Primitive;
}

/// Big-endian, or most significant bits first
#[derive(Copy, Clone, Debug)]
pub struct BigEndian;

/// Big-endian, or most significant bits first
pub type BE = BigEndian;

impl Endianness for BigEndian {
    #[inline]
    fn push<N>(queue: &mut BitQueue<Self, N>, bits: u32, value: N)
    where
        N: Numeric,
    {
        if !queue.value.is_zero() {
            queue.value <<= bits;
        }
        queue.value |= value;
        queue.bits += bits;
    }

    #[inline]
    fn push_fixed<const B: u32, N>(queue: &mut BitQueue<Self, N>, value: N)
    where
        N: Numeric,
    {
        if !queue.value.is_zero() {
            queue.value <<= B;
        }
        queue.value |= value;
        queue.bits += B;
    }

    #[inline]
    fn pop<N>(queue: &mut BitQueue<Self, N>, bits: u32) -> N
    where
        N: Numeric,
    {
        if bits < queue.bits {
            let offset = queue.bits - bits;
            let to_return = queue.value >> offset;
            queue.value %= N::ONE << offset;
            queue.bits -= bits;
            to_return
        } else {
            let to_return = queue.value;
            queue.value = N::default();
            queue.bits = 0;
            to_return
        }
    }

    #[inline]
    fn pop_fixed<const B: u32, N>(queue: &mut BitQueue<Self, N>) -> N
    where
        N: Numeric,
    {
        if B < queue.bits {
            let offset = queue.bits - B;
            let to_return = queue.value >> offset;
            queue.value %= N::ONE << offset;
            queue.bits -= B;
            to_return
        } else {
            let to_return = queue.value;
            queue.value = N::default();
            queue.bits = 0;
            to_return
        }
    }

    #[inline]
    fn drop<N>(queue: &mut BitQueue<Self, N>, bits: u32)
    where
        N: Numeric,
    {
        if bits < queue.bits {
            queue.value %= N::ONE << (queue.bits - bits);
            queue.bits -= bits;
        } else {
            queue.value = N::default();
            queue.bits = 0;
        }
    }

    #[inline]
    fn next_zeros<N>(queue: &BitQueue<Self, N>) -> u32
    where
        N: Numeric,
    {
        queue.value.leading_zeros() - (N::BITS_SIZE - queue.bits)
    }

    #[inline]
    fn next_ones<N>(queue: &BitQueue<Self, N>) -> u32
    where
        N: Numeric,
    {
        if queue.bits < N::BITS_SIZE {
            (queue.value ^ ((N::ONE << queue.bits) - N::ONE)).leading_zeros()
                - (N::BITS_SIZE - queue.bits)
        } else {
            (!queue.value).leading_zeros()
        }
    }

    fn read_signed<R, S>(r: &mut R, bits: u32) -> io::Result<S>
    where
        R: BitRead,
        S: SignedNumeric,
    {
        if bits == S::BITS_SIZE {
            r.read_to()
        } else {
            let is_negative = r.read_bit()?;
            let unsigned = r.read_unsigned::<S::Unsigned>(bits - 1)?;
            Ok(if is_negative {
                unsigned.as_negative(bits)
            } else {
                unsigned.as_non_negative()
            })
        }
    }

    fn read_signed_fixed<R, const B: u32, S>(r: &mut R) -> io::Result<S>
    where
        R: BitRead,
        S: SignedNumeric,
    {
        if B == S::BITS_SIZE {
            r.read_to()
        } else {
            let is_negative = r.read_bit()?;
            let unsigned = r.read_unsigned::<S::Unsigned>(B - 1)?;
            Ok(if is_negative {
                unsigned.as_negative_fixed::<B>()
            } else {
                unsigned.as_non_negative()
            })
        }
    }

    fn write_signed<W, S>(w: &mut W, bits: u32, value: S) -> io::Result<()>
    where
        W: BitWrite,
        S: SignedNumeric,
    {
        if bits == S::BITS_SIZE {
            w.write_bytes(value.to_be_bytes().as_ref())
        } else if value.is_negative() {
            w.write_bit(true)
                .and_then(|()| w.write_unsigned(bits - 1, value.as_negative(bits)))
        } else {
            w.write_bit(false)
                .and_then(|()| w.write_unsigned(bits - 1, value.as_non_negative()))
        }
    }

    fn write_signed_fixed<W, const B: u32, S>(w: &mut W, value: S) -> io::Result<()>
    where
        W: BitWrite,
        S: SignedNumeric,
    {
        if B == S::BITS_SIZE {
            w.write_bytes(value.to_be_bytes().as_ref())
        } else if value.is_negative() {
            w.write_bit(true)
                .and_then(|()| w.write_unsigned(B - 1, value.as_negative_fixed::<B>()))
        } else {
            w.write_bit(false)
                .and_then(|()| w.write_unsigned(B - 1, value.as_non_negative()))
        }
    }

    #[inline]
    fn read_primitive<R, V>(r: &mut R) -> io::Result<V>
    where
        R: BitRead,
        V: Primitive,
    {
        let mut buffer = V::buffer();
        r.read_bytes(buffer.as_mut())?;
        Ok(V::from_be_bytes(buffer))
    }

    #[inline]
    fn write_primitive<W, V>(w: &mut W, value: V) -> io::Result<()>
    where
        W: BitWrite,
        V: Primitive,
    {
        w.write_bytes(value.to_be_bytes().as_ref())
    }

    #[inline]
    fn read_numeric<R, V>(mut r: R) -> io::Result<V>
    where
        R: io::Read,
        V: Primitive,
    {
        let mut buffer = V::buffer();
        r.read_exact(buffer.as_mut())?;
        Ok(V::from_be_bytes(buffer))
    }

    #[inline]
    fn write_numeric<W, V>(mut w: W, value: V) -> io::Result<()>
    where
        W: io::Write,
        V: Primitive,
    {
        w.write_all(value.to_be_bytes().as_ref())
    }
}

/// Little-endian, or least significant bits first
#[derive(Copy, Clone, Debug)]
pub struct LittleEndian;

/// Little-endian, or least significant bits first
pub type LE = LittleEndian;

impl Endianness for LittleEndian {
    #[inline]
    fn push<N>(queue: &mut BitQueue<Self, N>, bits: u32, mut value: N)
    where
        N: Numeric,
    {
        if !value.is_zero() {
            value <<= queue.bits;
            queue.value |= value;
        }
        queue.bits += bits;
    }

    #[inline]
    fn push_fixed<const B: u32, N>(queue: &mut BitQueue<Self, N>, mut value: N)
    where
        N: Numeric,
    {
        if !value.is_zero() {
            value <<= queue.bits;
            queue.value |= value;
        }
        queue.bits += B;
    }

    #[inline]
    fn pop<N>(queue: &mut BitQueue<Self, N>, bits: u32) -> N
    where
        N: Numeric,
    {
        if bits < queue.bits {
            let to_return = queue.value % (N::ONE << bits);
            queue.value >>= bits;
            queue.bits -= bits;
            to_return
        } else {
            let to_return = queue.value;
            queue.value = N::default();
            queue.bits = 0;
            to_return
        }
    }

    fn pop_fixed<const B: u32, N>(queue: &mut BitQueue<Self, N>) -> N
    where
        N: Numeric,
    {
        if B < queue.bits {
            let to_return = queue.value % (N::ONE << B);
            queue.value >>= B;
            queue.bits -= B;
            to_return
        } else {
            let to_return = queue.value;
            queue.value = N::default();
            queue.bits = 0;
            to_return
        }
    }

    #[inline]
    fn drop<N>(queue: &mut BitQueue<Self, N>, bits: u32)
    where
        N: Numeric,
    {
        if bits < queue.bits {
            queue.value >>= bits;
            queue.bits -= bits;
        } else {
            queue.value = N::default();
            queue.bits = 0;
        }
    }

    #[inline(always)]
    fn next_zeros<N>(queue: &BitQueue<Self, N>) -> u32
    where
        N: Numeric,
    {
        queue.value.trailing_zeros()
    }

    #[inline]
    fn next_ones<N>(queue: &BitQueue<Self, N>) -> u32
    where
        N: Numeric,
    {
        (queue.value ^ !N::default()).trailing_zeros()
    }

    fn read_signed<R, S>(r: &mut R, bits: u32) -> io::Result<S>
    where
        R: BitRead,
        S: SignedNumeric,
    {
        if bits == S::BITS_SIZE {
            r.read_to()
        } else {
            let unsigned = r.read_unsigned::<S::Unsigned>(bits - 1)?;
            let is_negative = r.read_bit()?;
            Ok(if is_negative {
                unsigned.as_negative(bits)
            } else {
                unsigned.as_non_negative()
            })
        }
    }

    fn read_signed_fixed<R, const B: u32, S>(r: &mut R) -> io::Result<S>
    where
        R: BitRead,
        S: SignedNumeric,
    {
        if B == S::BITS_SIZE {
            r.read_to()
        } else {
            let unsigned = r.read_unsigned::<S::Unsigned>(B - 1)?;
            let is_negative = r.read_bit()?;
            Ok(if is_negative {
                unsigned.as_negative_fixed::<B>()
            } else {
                unsigned.as_non_negative()
            })
        }
    }

    fn write_signed<W, S>(w: &mut W, bits: u32, value: S) -> io::Result<()>
    where
        W: BitWrite,
        S: SignedNumeric,
    {
        if bits == S::BITS_SIZE {
            w.write_bytes(value.to_le_bytes().as_ref())
        } else if value.is_negative() {
            w.write_unsigned(bits - 1, value.as_negative(bits))
                .and_then(|()| w.write_bit(true))
        } else {
            w.write_unsigned(bits - 1, value.as_non_negative())
                .and_then(|()| w.write_bit(false))
        }
    }

    fn write_signed_fixed<W, const B: u32, S>(w: &mut W, value: S) -> io::Result<()>
    where
        W: BitWrite,
        S: SignedNumeric,
    {
        if B == S::BITS_SIZE {
            w.write_bytes(value.to_le_bytes().as_ref())
        } else if value.is_negative() {
            w.write_unsigned(B - 1, value.as_negative_fixed::<B>())
                .and_then(|()| w.write_bit(true))
        } else {
            w.write_unsigned(B - 1, value.as_non_negative())
                .and_then(|()| w.write_bit(false))
        }
    }

    #[inline]
    fn read_primitive<R, V>(r: &mut R) -> io::Result<V>
    where
        R: BitRead,
        V: Primitive,
    {
        let mut buffer = V::buffer();
        r.read_bytes(buffer.as_mut())?;
        Ok(V::from_le_bytes(buffer))
    }

    #[inline]
    fn write_primitive<W, V>(w: &mut W, value: V) -> io::Result<()>
    where
        W: BitWrite,
        V: Primitive,
    {
        w.write_bytes(value.to_le_bytes().as_ref())
    }

    fn read_numeric<R, V>(mut r: R) -> io::Result<V>
    where
        R: io::Read,
        V: Primitive,
    {
        let mut buffer = V::buffer();
        r.read_exact(buffer.as_mut())?;
        Ok(V::from_le_bytes(buffer))
    }

    #[inline]
    fn write_numeric<W, V>(mut w: W, value: V) -> io::Result<()>
    where
        W: io::Write,
        V: Primitive,
    {
        w.write_all(value.to_le_bytes().as_ref())
    }
}

/// A queue for efficiently pushing bits onto a value
/// and popping them off a value.
#[derive(Clone, Debug, Default)]
pub struct BitQueue<E: Endianness, N: Numeric> {
    phantom: PhantomData<E>,
    value: N,
    bits: u32,
}

impl<E: Endianness, N: Numeric> BitQueue<E, N> {
    /// Returns a new empty queue
    #[inline]
    pub fn new() -> BitQueue<E, N> {
        BitQueue {
            phantom: PhantomData,
            value: N::default(),
            bits: 0,
        }
    }

    /// Creates a new queue from the given value with the given size
    /// Panics if the value is larger than the given number of bits.
    #[inline]
    pub fn from_value(value: N, bits: u32) -> BitQueue<E, N> {
        assert!(if bits < N::BITS_SIZE {
            value < (N::ONE << bits)
        } else {
            bits <= N::BITS_SIZE
        });
        BitQueue {
            phantom: PhantomData,
            value,
            bits,
        }
    }

    /// Sets the queue to a given value with the given number of bits
    /// Panics if the value is larger than the given number of bits
    #[inline]
    pub fn set(&mut self, value: N, bits: u32) {
        assert!(if bits < N::BITS_SIZE {
            value < (N::ONE << bits)
        } else {
            bits <= N::BITS_SIZE
        });
        self.value = value;
        self.bits = bits;
    }

    /// Consumes the queue and returns its current value
    #[inline(always)]
    pub fn value(self) -> N {
        self.value
    }

    /// Returns the total bits in the queue
    #[inline(always)]
    pub fn len(&self) -> u32 {
        self.bits
    }

    /// Returns the maximum bits the queue can hold
    #[inline(always)]
    pub fn max_len(&self) -> u32 {
        N::BITS_SIZE
    }

    /// Returns the remaining bits the queue can hold
    #[inline(always)]
    pub fn remaining_len(&self) -> u32 {
        self.max_len() - self.len()
    }

    /// Returns true if the queue is empty
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.bits == 0
    }

    /// Returns true if the queue is full
    #[inline(always)]
    pub fn is_full(&self) -> bool {
        self.bits == N::BITS_SIZE
    }

    /// Drops all values in the queue
    #[inline(always)]
    pub fn clear(&mut self) {
        self.set(N::default(), 0)
    }

    /// Returns true if all bits remaining in the queue are 0
    #[inline(always)]
    #[deprecated(since = "3.0.0", note = "use contain_no::<1>() method instead")]
    pub fn all_0(&self) -> bool {
        self.contains_no::<1>()
    }

    /// Returns true if all bits remaining in the queue are 1
    #[inline(always)]
    #[deprecated(since = "3.0.0", note = "use contain_no::<0>() method instead")]
    pub fn all_1(&self) -> bool {
        self.contains_no::<0>()
    }

    /// Pushes a value with the given number of bits onto the tail of the queue
    /// Panics if the number of bits pushed is larger than the queue can hold.
    #[inline(always)]
    pub fn push(&mut self, bits: u32, value: N) {
        assert!(bits <= self.remaining_len()); // check for overflow
        E::push(self, bits, value)
    }

    /// Pushes a value with the given number of bits onto the tail of the queue
    /// Panics if the number of bits pushed is larger than the queue can hold.
    #[inline(always)]
    pub fn push_fixed<const B: u32>(&mut self, value: N) {
        assert!(B <= self.remaining_len()); // check for overflow
        E::push_fixed::<B, N>(self, value)
    }

    /// Pops a value with the given number of bits from the head of the queue
    /// Panics if the number of bits popped is larger than the number
    /// of bits in the queue.
    #[inline(always)]
    pub fn pop(&mut self, bits: u32) -> N {
        assert!(bits <= self.len()); // check for underflow
        E::pop(self, bits)
    }

    /// Pops a value with the given number of bits from the head of the queue
    pub fn pop_fixed<const B: u32>(&mut self) -> N {
        assert!(B <= self.len()); // check for underflow
        E::pop_fixed::<B, N>(self)
    }

    /// Pops all the current bits from the queue
    /// and resets it to an empty state.
    #[inline]
    pub fn pop_all(&mut self) -> N {
        let to_return = self.value;
        self.value = N::default();
        self.bits = 0;
        to_return
    }

    /// Drops the given number of bits from the head of the queue
    /// without returning them.
    /// Panics if the number of bits dropped is larger than the
    /// number of bits in the queue.
    #[inline(always)]
    pub fn drop(&mut self, bits: u32) {
        assert!(bits <= self.len()); // check for underflow
        E::drop(self, bits)
    }

    /// Returns `true` if the queue contains no instances of `STOP_BIT`.
    /// `STOP_BIT` must be 0 or 1.
    pub fn contains_no<const BIT: u8>(&self) -> bool {
        const {
            assert!(matches!(BIT, 0 | 1), "bit must be 0 or 1");
        }

        match BIT {
            0 => self.value.count_ones() == self.bits,
            1 => self.value.count_ones() == 0,
            _ => unreachable!(),
        }
    }

    /// Pops all non-`STOP_BIT` bits up to and including the next `STOP_BIT`
    /// and returns the amount of 0 bits popped.
    /// `STOP_BIT` must be 0 or 1.
    pub fn pop_until<const STOP_BIT: u8>(&mut self) -> u32 {
        const {
            assert!(matches!(STOP_BIT, 0 | 1), "stop bit must be 0 or 1");
        }

        match STOP_BIT {
            0 => {
                let ones = E::next_ones(self);
                self.drop(ones + 1);
                ones
            }
            1 => {
                let zeros = E::next_zeros(self);
                self.drop(zeros + 1);
                zeros
            }
            _ => unreachable!(),
        }
    }

    /// Pops all 0 bits up to and including the next 1 bit
    /// and returns the amount of 0 bits popped
    #[inline]
    #[deprecated(since = "3.0.0", note = "use pop_until::<1>() method instead")]
    pub fn pop_0(&mut self) -> u32 {
        self.pop_until::<1>()
    }

    /// Pops all 1 bits up to and including the next 0 bit
    /// and returns the amount of 1 bits popped
    #[inline]
    #[deprecated(since = "3.0.0", note = "use pop_until::<0>() method instead")]
    pub fn pop_1(&mut self) -> u32 {
        self.pop_until::<0>()
    }
}

impl<E: Endianness> BitQueue<E, u8> {
    /// Returns the state of the queue as a single value
    /// which can be used to perform lookups.
    #[inline(always)]
    pub fn to_state(&self) -> usize {
        (1 << self.bits) | (self.value as usize)
    }
}
