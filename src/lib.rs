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
//! implement the [`io::Read`] trait, and the only requirement
//! for writer streams is that they must implement the [`io::Write`] trait.
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
//! let x: Result<u32, _> = r.read_var(64);  // reading 64 bits to u32 always fails at runtime
//! assert!(x.is_err());
//! ```
//! but those errors will not be caught until the program runs,
//! which is less than ideal for the common case in which
//! the number of bits is already known at compile-time.
//!
//! But starting with Rust 1.79, we can now have read and write methods
//! which take a constant number of bits and can validate the number of bits
//! are small enough for the type being read/written at compile-time:
//! ```rust,compile_fail
//! use std::io::{Read, Cursor};
//! use bitstream_io::{BigEndian, BitReader, BitRead};
//! let data = [0; 10];
//! let mut r = BitReader::endian(Cursor::new(&data), BigEndian);
//! let x: Result<u32, _> = r.read::<64, _>();  // doesn't compile at all
//! ```
//! Since catching potential bugs at compile-time is preferable
//! to encountering errors at runtime, this will hopefully be
//! an improvement in the long run.

//! # Changes From 2.X.X
//!
//! Version 3.0.0 has made many breaking changes to the [`BitRead`] and
//! [`BitWrite`] traits.
//!
//! The [`BitRead::read`] method takes a constant number of bits,
//! and the [`BitRead::read_var`] method takes a variable number of bits
//! (reversing the older [`BitRead2::read_in`] and [`BitRead2::read`]
//! calling methods to emphasize using the constant-based one,
//! which can do more validation at compile-time).
//! A new [`BitRead2`] trait uses the older calling convention
//! for compatibility with existing code and is available
//! for anything implementing [`BitRead`].
//!
//! In addition, the main reading methods return primitive types which
//! implement a new [`Integer`] trait,
//! which delegates to [`BitRead::read_unsigned`]
//! or [`BitRead::read_signed`] depending on whether the output
//! is an unsigned or signed type.
//!
//! [`BitWrite::write`] and [`BitWrite::write_var`] work
//! similarly to the reader's `read` methods, taking anything
//! that implements [`Integer`] and writing an unsigned or
//! signed value to [`BitWrite::write_unsigned`] or
//! [`BitWrite::write_signed`] as appropriate.
//!
//! And as with reading, a [`BitWrite2`] trait is offered
//! for compatibility.
//!
//! In addition, the Huffman code handling has been rewritten
//! to use a small amount of macro magic to write
//! code to read and write symbols at compile-time.
//! This is significantly faster than the older version
//! and can no longer fail to compile at runtime.
//!
//! Lastly, there's a new [`BitCount`] struct which wraps a humble
//! `u32` but encodes the maximum possible number of bits
//! at the type level.
//! This is intended for file formats which encode the number
//! of bits to be read in the format itself.
//! For example, FLAC's predictor coefficient precision
//! is a 4 bit value which indicates how large each predictor
//! coefficient is in bits
//! (each coefficient might be an `i32` type).
//! By keeping track of the maximum value at compile time
//! (4 bits' worth, in this case), we can eliminate
//! any need to check that coefficients aren't too large
//! for an `i32` at runtime.
//! This is accomplished by using [`BitRead::read_count`] to
//! read a [`BitCount`] and then reading final values with
//! that number of bits using [`BitRead::read_counted`].

//! # Migrating From Pre 1.0.0
//!
//! There are now [`BitRead`] and [`BitWrite`] traits for bitstream
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

use core::num::NonZero;
use core::ops::{
    BitAnd, BitOr, BitOrAssign, BitXor, Not, Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub,
};
use core::{fmt::Debug, marker::PhantomData, mem};
#[cfg(feature = "std")]
use std::io;

pub mod huffman;
pub mod read;
pub mod write;
pub use read::{
    BitRead, BitRead2, BitReader, ByteRead, ByteReader, FromBitStream, FromBitStreamWith,
    FromByteStream, FromByteStreamWith,
};
pub use write::{
    BitCounter, BitRecorder, BitWrite, BitWrite2, BitWriter, ByteWrite, ByteWriter, ToBitStream,
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
///
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
    /// A compile-time error occurs if the given number of bits
    /// is larger than our type.
    fn read<const BITS: u32, R: BitRead + ?Sized>(reader: &mut R) -> io::Result<Self>
    where
        Self: Sized;

    /// Reads a value of ourself from the stream
    /// with the given number of bits.
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    /// Also returns an error if our type is too small
    /// to hold the requested number of bits.
    fn read_var<const MAX: u32, R>(reader: &mut R, bits: BitCount<MAX>) -> io::Result<Self>
    where
        R: BitRead + ?Sized,
        Self: Sized;

    /// Writes ourself to the stream using the given const number of bits.
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    /// Returns an error if our value is too large
    /// to fit the given number of bits.
    /// A compile-time error occurs if the given number of bits
    /// is larger than our type.
    fn write<const BITS: u32, W: BitWrite + ?Sized>(self, writer: &mut W) -> io::Result<()>;

    /// Writes ourself to the stream using the given number of bits.
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    /// Returns an error if our value is too small
    /// to hold the given number of bits.
    /// Returns an error if our value is too large
    /// to fit the given number of bits.
    fn write_var<const MAX: u32, W: BitWrite + ?Sized>(
        self,
        writer: &mut W,
        bits: BitCount<MAX>,
    ) -> io::Result<()>;
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
    + BitAnd<Self, Output = Self>
    + BitOr<Self, Output = Self>
    + BitOrAssign<Self>
    + BitXor<Self, Output = Self>
    + Not<Output = Self>
    + Sub<Self, Output = Self>
{
    /// Size of type in bits
    const BITS_SIZE: u32;

    /// The value of 0 in this type
    const ZERO: Self;

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

    /// Counts the number of leading ones
    fn leading_ones(self) -> u32;

    /// Counts the number of trailing zeros
    fn trailing_zeros(self) -> u32;

    /// Counts the number of trailing ones
    fn trailing_ones(self) -> u32;

    /// Checked shift left
    fn checked_shl(self, rhs: u32) -> Option<Self>;

    /// Checked shift right
    fn checked_shr(self, rhs: u32) -> Option<Self>;
}

macro_rules! define_numeric {
    ($t:ty) => {
        define_primitive_numeric!($t);

        impl Numeric for $t {
            const BITS_SIZE: u32 = mem::size_of::<$t>() as u32 * 8;

            const ZERO: Self = 0;

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
            fn leading_ones(self) -> u32 {
                self.leading_ones()
            }
            #[inline(always)]
            fn trailing_zeros(self) -> u32 {
                self.trailing_zeros()
            }
            #[inline(always)]
            fn trailing_ones(self) -> u32 {
                self.trailing_ones()
            }
            #[inline(always)]
            fn checked_shl(self, rhs: u32) -> Option<Self> {
                self.checked_shl(rhs)
            }
            #[inline(always)]
            fn checked_shr(self, rhs: u32) -> Option<Self> {
                self.checked_shr(rhs)
            }
        }
    };
}

/// This trait extends many common unsigned integer types
/// so that they can be used with the bitstream handling traits.
pub trait UnsignedNumeric: Numeric + Into<crate::write::UnsignedValue> {
    /// This type's most-significant bit
    const MSB_BIT: Self;

    /// This type's least significant bit
    const LSB_BIT: Self;

    /// This type with all bits set
    const ALL: Self;

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

            const MSB_BIT: Self = 1 << (Self::BITS_SIZE - 1);

            const LSB_BIT: Self = 1;

            const ALL: Self = <$t>::MAX;

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
            #[inline(always)]
            fn read<const BITS: u32, R: BitRead + ?Sized>(reader: &mut R) -> io::Result<Self>
            where
                Self: Sized,
            {
                reader.read_unsigned::<BITS, _>()
            }

            #[inline(always)]
            fn read_var<const MAX: u32, R>(reader: &mut R, bits: BitCount<MAX>) -> io::Result<Self>
            where
                R: BitRead + ?Sized,
                Self: Sized,
            {
                reader.read_unsigned_counted::<MAX, _>(bits)
            }

            #[inline(always)]
            fn write<const BITS: u32, W: BitWrite + ?Sized>(
                self,
                writer: &mut W,
            ) -> io::Result<()> {
                writer.write_unsigned::<BITS, _>(self)
            }

            #[inline(always)]
            fn write_var<const MAX: u32, W: BitWrite + ?Sized>(
                self,
                writer: &mut W,
                bits: BitCount<MAX>,
            ) -> io::Result<()> {
                writer.write_unsigned_counted(bits, self)
            }
        }

        /// Unsigned NonZero types increment their value by 1
        /// when being read and decrement it by 1
        /// when being written.
        ///
        /// # Examples
        /// ```
        /// use bitstream_io::{BitReader, BitRead, BigEndian};
        /// use core::num::NonZero;
        ///
        /// let data: &[u8] = &[0b001_00000];
        /// // reading a regular u8 in 3 bits yields 1
        /// assert_eq!(BitReader::endian(data, BigEndian).read::<3, u8>().unwrap(), 1);
        /// // reading a NonZero<u8> in 3 bits of the same data yields 2
        /// assert_eq!(BitReader::endian(data, BigEndian).read::<3, NonZero<u8>>().unwrap().get(), 2);
        /// ```
        ///
        /// ```
        /// use bitstream_io::{BitWriter, BitWrite, BigEndian};
        /// use core::num::NonZero;
        ///
        /// let mut w = BitWriter::endian(vec![], BigEndian);
        /// // writing 1 as a regular u8 in 3 bits
        /// w.write::<3, u8>(1).unwrap();
        /// w.byte_align();
        /// assert_eq!(w.into_writer(), &[0b001_00000]);
        ///
        /// let mut w = BitWriter::endian(vec![], BigEndian);
        /// // writing 1 as a NonZero<u8> in 3 bits
        /// w.write::<3, NonZero<u8>>(NonZero::new(1).unwrap()).unwrap();
        /// w.byte_align();
        /// assert_eq!(w.into_writer(), &[0b000_00000]);
        /// ```
        impl Integer for NonZero<$t> {
            fn read<const BITS: u32, R: BitRead + ?Sized>(reader: &mut R) -> io::Result<Self>
            where
                Self: Sized,
            {
                const {
                    assert!(
                        BITS < <$t>::BITS_SIZE,
                        "BITS must be less than the type's size in bits"
                    );
                }

                <$t as Integer>::read::<BITS, R>(reader).map(|u| NonZero::new(u + 1).unwrap())
            }

            fn read_var<const MAX: u32, R>(
                reader: &mut R,
                count @ BitCount { bits }: BitCount<MAX>,
            ) -> io::Result<Self>
            where
                R: BitRead + ?Sized,
                Self: Sized,
            {
                if MAX < <$t>::BITS_SIZE || bits < <$t>::BITS_SIZE {
                    <$t as Integer>::read_var::<MAX, R>(reader, count)
                        .map(|u| NonZero::new(u + 1).unwrap())
                } else {
                    Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        "bit count must be less than the type's size in bits",
                    ))
                }
            }

            fn write<const BITS: u32, W: BitWrite + ?Sized>(
                self,
                writer: &mut W,
            ) -> io::Result<()> {
                const {
                    assert!(
                        BITS < <$t>::BITS_SIZE,
                        "BITS must be less than the type's size in bits"
                    );
                }

                <$t as Integer>::write::<BITS, W>(self.get() - 1, writer)
            }

            fn write_var<const MAX: u32, W: BitWrite + ?Sized>(
                self,
                writer: &mut W,
                count @ BitCount { bits }: BitCount<MAX>,
            ) -> io::Result<()> {
                if MAX < <$t>::BITS_SIZE || bits < <$t>::BITS_SIZE {
                    <$t as Integer>::write_var::<MAX, W>(self.get() - 1, writer, count)
                } else {
                    Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        "bit count must be less than the type's size in bits",
                    ))
                }
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
            #[inline(always)]
            fn read<const BITS: u32, R: BitRead + ?Sized>(reader: &mut R) -> io::Result<Self>
            where
                Self: Sized,
            {
                reader.read_signed::<BITS, _>()
            }

            #[inline(always)]
            fn read_var<const MAX: u32, R>(reader: &mut R, bits: BitCount<MAX>) -> io::Result<Self>
            where
                R: BitRead + ?Sized,
                Self: Sized,
            {
                reader.read_signed_counted::<MAX, _>(bits)
            }

            #[inline(always)]
            fn write<const BITS: u32, W: BitWrite + ?Sized>(
                self,
                writer: &mut W,
            ) -> io::Result<()> {
                writer.write_signed::<BITS, _>(self)
            }

            #[inline(always)]
            fn write_var<const MAX: u32, W: BitWrite + ?Sized>(
                self,
                writer: &mut W,
                bits: BitCount<MAX>,
            ) -> io::Result<()> {
                writer.write_signed_counted::<MAX, _>(bits, self)
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
    /// Pops the next bit from the queue,
    /// repleneshing it from the given closure if necessary
    fn pop_bit_refill<F, E>(queue: &mut PartialByte<Self>, read_val: F) -> Result<bool, E>
    where
        F: FnOnce() -> Result<u8, E>;

    /// Pops the next unary value from the source until
    /// `STOP_BIT` is encountered, replenishing it from the given
    /// closure if necessary.
    ///
    /// `STOP_BIT` must be 0 or 1.
    fn pop_unary<const STOP_BIT: u8, F, E>(
        queue: &mut PartialByte<Self>,
        read_val: F,
    ) -> Result<u32, E>
    where
        F: FnMut() -> Result<u8, E>;

    /// Pushes the next bit into the queue,
    /// and returns `Some` value if the queue is full.
    #[inline]
    fn push_bit_flush(queue: &mut PartialByte<Self>, bit: bool) -> Option<u8> {
        Self::push_bits(&mut queue.value, &mut queue.bits, 1, u8::from(bit));
        queue.bits %= u8::BITS_SIZE;
        (queue.bits == 0).then(|| mem::take(&mut queue.value))
    }

    /// For extracting all the values from a source into a final value
    fn pop_final_value<U>(source: &mut U, source_bits: &mut u32) -> (U, u32)
    where
        U: UnsignedNumeric;

    /// For extracting multiple bits from a source
    fn pop_bits<U>(source: &mut U, source_bits: &mut u32, bits: u32) -> U
    where
        U: UnsignedNumeric;

    /// For pushing multiple bits into a final value
    fn push_bits<U>(target: &mut U, target_bits: &mut u32, bits: u32, value: U)
    where
        U: UnsignedNumeric;

    /// Aligns value to be a bit source which can be popped from
    fn source_align<U>(value: U, bits: u32) -> U
    where
        U: UnsignedNumeric;

    /// For performing bulk reads from a bit source to an output type.
    fn read_bits<const MAX: u32, U, F, E>(
        queue: &mut PartialByte<Self>,
        BitCount { bits }: BitCount<MAX>,
        read_byte: F,
    ) -> Result<U, E>
    where
        U: UnsignedNumeric,
        F: FnMut() -> Result<u8, E>,
        E: From<io::Error>,
    {
        if MAX <= U::BITS_SIZE || bits <= U::BITS_SIZE {
            read_bits::<Self, U, _, _>(queue, bits, read_byte)
        } else {
            Err(io::Error::new(io::ErrorKind::InvalidInput, "excessive bits for type read").into())
        }
    }

    /// For performing bulk reads from a bit source to an output type.
    fn read_bits_fixed<const BITS: u32, U, F, E>(
        queue: &mut PartialByte<Self>,
        read_byte: F,
    ) -> Result<U, E>
    where
        U: UnsignedNumeric,
        F: FnMut() -> Result<u8, E>,
    {
        const {
            assert!(BITS <= U::BITS_SIZE, "excessive bits for type read");
        }

        read_bits::<Self, U, _, _>(queue, BITS, read_byte)
    }

    /// For performing bulk writes of a type to a bit sink.
    fn write_bits<const MAX: u32, U, F, E>(
        queue: &mut PartialByte<Self>,
        BitCount { bits }: BitCount<MAX>,
        value: U,
        write_byte: F,
    ) -> Result<(), E>
    where
        U: UnsignedNumeric,
        F: FnMut(u8) -> Result<(), E>,
        E: From<io::Error>,
    {
        if MAX <= U::BITS_SIZE || bits <= U::BITS_SIZE {
            if bits == 0 {
                Ok(())
            } else if value <= U::ALL >> (U::BITS_SIZE - bits) {
                write_bits::<Self, U, _, _>(queue, bits, value, write_byte)
            } else {
                Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    "excessive value for bits written",
                )
                .into())
            }
        } else {
            Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "excessive bits for type written",
            )
            .into())
        }
    }

    /// For performing bulk writes of a constant value to a bit sink.
    fn write_bits_const<const BITS: u32, const VALUE: u32, F, E>(
        queue: &mut PartialByte<Self>,
        write_byte: F,
    ) -> Result<(), E>
    where
        F: FnMut(u8) -> Result<(), E>,
        E: From<io::Error>,
    {
        const {
            assert!(BITS <= u32::BITS_SIZE, "excessive bits for type written");
            assert!(
                BITS == 0 || VALUE <= (u32::ALL >> (u32::BITS_SIZE - BITS)),
                "excessive value for bits written"
            );
        }

        if BITS == 0 {
            Ok(())
        } else {
            write_bits::<Self, _, _, _>(queue, BITS, VALUE, write_byte)
        }
    }

    /// For performing bulk writes of a type to a bit sink.
    fn write_bits_fixed<const BITS: u32, U, F, E>(
        queue: &mut PartialByte<Self>,
        value: U,
        write_byte: F,
    ) -> Result<(), E>
    where
        U: UnsignedNumeric,
        F: FnMut(u8) -> Result<(), E>,
        E: From<io::Error>,
    {
        const {
            assert!(BITS <= U::BITS_SIZE, "excessive bits for type written");
        }

        if BITS == 0 {
            Ok(())
        } else if value <= (U::ALL >> (U::BITS_SIZE - BITS)) {
            write_bits::<Self, U, _, _>(queue, BITS, value, write_byte)
        } else {
            Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "excessive value for bits written",
            )
            .into())
        }
    }

    /// Reads signed value from reader in this endianness
    fn read_signed<const MAX: u32, R, S>(r: &mut R, bits: BitCount<MAX>) -> io::Result<S>
    where
        R: BitRead,
        S: SignedNumeric;

    /// Reads signed value from reader in this endianness
    fn read_signed_fixed<R, const B: u32, S>(r: &mut R) -> io::Result<S>
    where
        R: BitRead,
        S: SignedNumeric;

    /// Writes signed value to writer in this endianness
    fn write_signed<const MAX: u32, W, S>(
        w: &mut W,
        bits: BitCount<MAX>,
        value: S,
    ) -> io::Result<()>
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

/// An opaque partially-consumed byte.
#[derive(Clone, Debug)]
pub struct PartialByte<E: Endianness> {
    // our partial byte
    value: u8,
    // the number of bits in our partial byte
    bits: u32,
    // a container for our endianness
    phantom: PhantomData<E>,
}

impl<E: Endianness> Default for PartialByte<E> {
    fn default() -> Self {
        Self {
            value: 0,
            bits: 0,
            phantom: PhantomData,
        }
    }
}

impl<E: Endianness> PartialByte<E> {
    /// Returns the number of bits in our partial byte
    #[inline]
    fn bits(&self) -> u32 {
        self.bits
    }
}

fn read_bits<N, U, F, E>(queue: &mut PartialByte<N>, bits: u32, mut read_byte: F) -> Result<U, E>
where
    N: Endianness,
    U: UnsignedNumeric,
    F: FnMut() -> Result<u8, E>,
{
    if bits <= queue.bits {
        Ok(U::from_u8(N::pop_bits(
            &mut queue.value,
            &mut queue.bits,
            bits,
        )))
    } else {
        let (value, mut value_bits) = N::pop_final_value(&mut queue.value, &mut queue.bits);
        let mut value = U::from_u8(value);
        let mut bits = bits - value_bits;

        loop {
            match bits {
                0 => break Ok(value),
                1..8 => {
                    let mut last = read_byte()?;
                    let mut last_bits = 8;

                    N::push_bits(
                        &mut value,
                        &mut value_bits,
                        bits,
                        U::from_u8(N::pop_bits(&mut last, &mut last_bits, bits)),
                    );

                    queue.value = last;
                    queue.bits = last_bits;

                    break Ok(value);
                }
                _ => {
                    N::push_bits(&mut value, &mut value_bits, 8, U::from_u8(read_byte()?));
                    bits -= 8;
                }
            }
        }
    }
}

/// Performs actual value extraction to disk
fn write_bits<N, U, F, E>(
    queue: &mut PartialByte<N>,
    mut bits: u32,
    value: U,
    mut write_byte: F,
) -> Result<(), E>
where
    N: Endianness,
    U: UnsignedNumeric,
    F: FnMut(u8) -> Result<(), E>,
    E: From<io::Error>,
{
    let mut value = N::source_align(value, bits);
    let available = u8::BITS_SIZE - queue.bits;
    if bits < available {
        // all bits fit in queue, so populate it and we're done
        N::push_bits(
            &mut queue.value,
            &mut queue.bits,
            bits,
            N::pop_bits(&mut value, &mut bits.clone(), bits).to_u8(),
        );
        Ok(())
    } else {
        // push as many bits into queue as possible
        // and write it to disk

        N::push_bits(
            &mut queue.value,
            &mut queue.bits,
            available,
            N::pop_bits(&mut value, &mut bits, available).to_u8(),
        );
        write_byte(core::mem::take(&mut queue.value))?;
        queue.bits = 0;

        // write any further bytes in 8-bit increments
        while bits >= 8 {
            write_byte(N::pop_bits(&mut value, &mut bits, 8).to_u8())?;
        }

        // finally repopulate queue with any leftover bits
        if bits > 0 {
            N::push_bits(
                &mut queue.value,
                &mut queue.bits,
                bits,
                N::pop_bits(&mut value, &mut bits.clone(), bits).to_u8(),
            );
        }
        debug_assert!(value == U::ZERO);

        Ok(())
    }
}

/// A number of bits to be consumed or written, with a known maximum
#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq)]
pub struct BitCount<const MAX: u32> {
    // The amount of bits may be less than or equal to the maximum,
    // but never more.
    bits: u32,
}

impl<const MAX: u32> BitCount<MAX> {
    /// Builds a bit count from a constant number
    /// of bits, which must not be greater than `MAX`.
    ///
    /// Intended to be used for defining constants.
    ///
    /// Use `TryFrom` to conditionally build
    /// counts from values at runtime.
    ///
    /// # Example
    ///
    /// ```
    /// use bitstream_io::{BitReader, BitRead, BigEndian, BitCount};
    /// let data: &[u8] = &[0b111_00000];
    /// let mut r = BitReader::endian(data, BigEndian);
    /// // reading 3 bits from a stream out of a maximum of 8
    /// // doesn't require checking that the bit count is larger
    /// // than a u8 at runtime because specifying the maximum of 8
    /// // guarantees our bit count will not be larger than 8
    /// assert_eq!(r.read_counted::<8, u8>(BitCount::new::<3>()).unwrap(), 0b111);
    /// ```
    ///
    /// ```rust,compile_fail
    /// use bitstream_io::BitCount;
    /// // trying to build a count of 10 with a maximum of 8
    /// // fails to compile at all
    /// let count = BitCount::<8>::new::<10>();
    /// ```
    pub const fn new<const BITS: u32>() -> Self {
        const {
            assert!(BITS <= MAX, "BITS must be <= MAX");
        }

        Self { bits: BITS }
    }

    /// Add a number of bits to our count,
    /// returning a new count with a new maximum.
    ///
    /// Returns `None` if the new count goes above our new maximum
    /// or above `u32::MAX`.
    ///
    /// # Example
    ///
    /// ```
    /// use bitstream_io::BitCount;
    /// let count = BitCount::<2>::new::<1>();
    /// // adding 2 to 1 and increasing the max to 3 yields a new count of 3
    /// assert_eq!(count.checked_add::<3>(2), Some(BitCount::<3>::new::<3>()));
    /// // adding 2 to 1 without increasing the max yields None
    /// assert_eq!(count.checked_add::<2>(2), None);
    /// // adding u32::MAX to 1 while increasing the max yields None
    /// assert_eq!(count.checked_add::<{u32::MAX}>(u32::MAX), None);
    /// ```
    #[inline]
    pub const fn checked_add<const NEW_MAX: u32>(self, bits: u32) -> Option<BitCount<NEW_MAX>> {
        match self.bits.checked_add(bits) {
            Some(bits) if bits <= NEW_MAX => Some(BitCount { bits }),
            _ => None,
        }
    }

    /// Subtracts a number of bits from our count,
    /// returning a new count with the same maximum.
    ///
    /// Returns `None` if the new count goes below 0.
    ///
    /// # Example
    /// ```
    /// use bitstream_io::BitCount;
    /// let count = BitCount::<5>::new::<1>();
    /// // subtracting 1 from 1 yields a new count of 0
    /// assert_eq!(count.checked_sub(1), Some(BitCount::<5>::new::<0>()));
    /// // subtracting 2 from 1 yields None
    /// assert!(count.checked_sub(2).is_none());
    /// ```
    #[inline]
    pub const fn checked_sub(self, bits: u32) -> Option<Self> {
        // it's okay for the number of bits to be smaller than MAX
        // so subtracting into a smaller number of bits is fine
        match self.bits.checked_sub(bits) {
            Some(bits) => Some(Self { bits }),
            None => None,
        }
    }

    /// Attempt to convert our count to a count with a new
    /// bit count and new maximum.
    ///
    /// Returns `Some(count)` if the updated number of bits
    /// is less than or equal to the new maximum.
    /// Returns `None` if not.
    ///
    /// # Example
    /// ```
    /// use bitstream_io::BitCount;
    /// let count = BitCount::<5>::new::<5>();
    /// // muliplying 5 bits by 2 with a new max of 10 is ok
    /// assert_eq!(
    ///     count.try_map::<10, _>(|i| i.checked_mul(2)),
    ///     Some(BitCount::<10>::new::<10>()),
    /// );
    /// // multiplying 5 bits by 3 with a new max of 10 overflows
    /// assert_eq!(count.try_map::<10, _>(|i| i.checked_mul(3)), None);
    /// ```
    #[inline]
    pub fn try_map<const NEW_MAX: u32, F>(self, f: F) -> Option<BitCount<NEW_MAX>>
    where
        F: FnOnce(u32) -> Option<u32>,
    {
        f(self.bits)
            .filter(|bits| *bits <= NEW_MAX)
            .map(|bits| BitCount { bits })
    }
}

impl<const MAX: u32> core::convert::TryFrom<u32> for BitCount<MAX> {
    type Error = u32;

    fn try_from(bits: u32) -> Result<Self, Self::Error> {
        (bits <= MAX).then_some(Self { bits }).ok_or(bits)
    }
}

impl BitCount<{ u32::MAX }> {
    /// Builds a bit count where the maximum bits is unknown.
    ///
    /// In this case, `u32::MAX` is assumed.
    ///
    /// # Example
    /// ```
    /// use bitstream_io::BitCount;
    /// assert_eq!(BitCount::unknown(5), BitCount::<{u32::MAX}>::new::<5>());
    /// ```
    pub const fn unknown(bits: u32) -> Self {
        Self { bits }
    }
}

impl<const MAX: u32> From<BitCount<MAX>> for u32 {
    #[inline(always)]
    fn from(BitCount { bits }: BitCount<MAX>) -> u32 {
        bits
    }
}

/// Big-endian, or most significant bits first
#[derive(Copy, Clone, Debug)]
pub struct BigEndian;

/// Big-endian, or most significant bits first
pub type BE = BigEndian;

impl Endianness for BigEndian {
    fn pop_bit_refill<F, E>(queue: &mut PartialByte<Self>, read_val: F) -> Result<bool, E>
    where
        F: FnOnce() -> Result<u8, E>,
    {
        Ok(if queue.bits == 0 {
            let value = read_val()?;
            let msb = value & u8::MSB_BIT;
            queue.value = value << 1;
            queue.bits = u8::BITS_SIZE - 1;
            msb
        } else {
            let msb = queue.value & u8::MSB_BIT;
            queue.value <<= 1;
            queue.bits -= 1;
            msb
        } != 0)
    }

    fn pop_unary<const STOP_BIT: u8, F, E>(
        queue: &mut PartialByte<Self>,
        read_val: F,
    ) -> Result<u32, E>
    where
        F: FnMut() -> Result<u8, E>,
    {
        const {
            assert!(matches!(STOP_BIT, 0 | 1), "stop bit must be 0 or 1");
        }

        match STOP_BIT {
            0 => find_unary(
                queue,
                |v| v.leading_ones(),
                |q| q,
                |v, b| v.checked_shl(b),
                read_val,
            ),
            1 => find_unary(
                queue,
                |v| v.leading_zeros(),
                |_| u8::BITS_SIZE,
                |v, b| v.checked_shl(b),
                read_val,
            ),
            _ => unreachable!(),
        }
    }

    fn pop_final_value<U>(source: &mut U, source_bits: &mut u32) -> (U, u32)
    where
        U: UnsignedNumeric,
    {
        let bits = core::mem::take(source_bits);
        (
            core::mem::take(source)
                .checked_shr(U::BITS_SIZE - bits)
                .unwrap_or(U::ZERO),
            bits,
        )
    }

    #[inline(always)]
    fn source_align<U>(value: U, bits: u32) -> U
    where
        U: UnsignedNumeric,
    {
        value << (U::BITS_SIZE - bits)
    }

    #[inline]
    fn pop_bits<U>(source: &mut U, source_bits: &mut u32, bits: u32) -> U
    where
        U: UnsignedNumeric,
    {
        let value = source.checked_shr(U::BITS_SIZE - bits).unwrap_or(U::ZERO);
        *source = source.checked_shl(bits).unwrap_or(U::ZERO);
        *source_bits -= bits;
        value
    }

    #[inline]
    fn push_bits<U>(target: &mut U, target_bits: &mut u32, bits: u32, value: U)
    where
        U: UnsignedNumeric,
    {
        *target = target.checked_shl(bits).unwrap_or(U::ZERO) | value;
        *target_bits += bits;
    }

    fn read_signed<const MAX: u32, R, S>(
        r: &mut R,
        count @ BitCount { bits }: BitCount<MAX>,
    ) -> io::Result<S>
    where
        R: BitRead,
        S: SignedNumeric,
    {
        if MAX <= S::BITS_SIZE || bits <= S::BITS_SIZE {
            let is_negative = r.read_bit()?;
            let unsigned = r.read_unsigned_counted::<MAX, S::Unsigned>(
                count.checked_sub(1).ok_or(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    "signed reads need at least 1 bit for sign",
                ))?,
            )?;
            Ok(if is_negative {
                unsigned.as_negative(bits)
            } else {
                unsigned.as_non_negative()
            })
        } else {
            Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "excessive bits for type read",
            ))
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
            let unsigned = r.read_unsigned_var::<S::Unsigned>(B - 1)?;
            Ok(if is_negative {
                unsigned.as_negative_fixed::<B>()
            } else {
                unsigned.as_non_negative()
            })
        }
    }

    fn write_signed<const MAX: u32, W, S>(
        w: &mut W,
        count @ BitCount { bits }: BitCount<MAX>,
        value: S,
    ) -> io::Result<()>
    where
        W: BitWrite,
        S: SignedNumeric,
    {
        if MAX <= S::BITS_SIZE || bits <= S::BITS_SIZE {
            w.write_bit(value.is_negative())?;
            w.write_unsigned_counted(
                count.checked_sub(1).ok_or(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    "signed writes need at least 1 bit for sign",
                ))?,
                if value.is_negative() {
                    value.as_negative(bits)
                } else {
                    value.as_non_negative()
                },
            )
        } else {
            Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "excessive bits for type written",
            ))
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
                .and_then(|()| w.write_unsigned_var(B - 1, value.as_negative_fixed::<B>()))
        } else {
            w.write_bit(false)
                .and_then(|()| w.write_unsigned_var(B - 1, value.as_non_negative()))
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
    fn pop_bit_refill<F, E>(queue: &mut PartialByte<Self>, read_val: F) -> Result<bool, E>
    where
        F: FnOnce() -> Result<u8, E>,
    {
        Ok(if queue.bits == 0 {
            let value = read_val()?;
            let lsb = value & u8::LSB_BIT;
            queue.value = value >> 1;
            queue.bits = u8::BITS_SIZE - 1;
            lsb
        } else {
            let lsb = queue.value & u8::LSB_BIT;
            queue.value >>= 1;
            queue.bits -= 1;
            lsb
        } != 0)
    }

    fn pop_unary<const STOP_BIT: u8, F, E>(
        queue: &mut PartialByte<Self>,
        read_val: F,
    ) -> Result<u32, E>
    where
        F: FnMut() -> Result<u8, E>,
    {
        const {
            assert!(matches!(STOP_BIT, 0 | 1), "stop bit must be 0 or 1");
        }

        match STOP_BIT {
            0 => find_unary(
                queue,
                |v| v.trailing_ones(),
                |q| q,
                |v, b| v.checked_shr(b),
                read_val,
            ),
            1 => find_unary(
                queue,
                |v| v.trailing_zeros(),
                |_| u8::BITS_SIZE,
                |v, b| v.checked_shr(b),
                read_val,
            ),
            _ => unreachable!(),
        }
    }

    fn pop_final_value<U>(source: &mut U, source_bits: &mut u32) -> (U, u32)
    where
        U: UnsignedNumeric,
    {
        let bits = core::mem::take(source_bits);
        (
            core::mem::take(source) & (U::ALL.checked_shr(U::BITS_SIZE - bits).unwrap_or(U::ZERO)),
            bits,
        )
    }

    #[inline(always)]
    fn source_align<U>(value: U, _bits: u32) -> U
    where
        U: UnsignedNumeric,
    {
        // bits are already aligned so nothing to do
        value
    }

    #[inline]
    fn pop_bits<U>(source: &mut U, source_bits: &mut u32, bits: u32) -> U
    where
        U: UnsignedNumeric,
    {
        let value = *source & (U::ALL.checked_shr(U::BITS_SIZE - bits).unwrap_or(U::ZERO));
        *source = source.checked_shr(bits).unwrap_or(U::ZERO);
        *source_bits -= bits;
        value
    }

    #[inline]
    fn push_bits<U>(target: &mut U, target_bits: &mut u32, bits: u32, value: U)
    where
        U: UnsignedNumeric,
    {
        *target |= value.checked_shl(*target_bits).unwrap_or(U::ZERO);
        *target_bits += bits;
    }

    fn read_signed<const MAX: u32, R, S>(
        r: &mut R,
        count @ BitCount { bits }: BitCount<MAX>,
    ) -> io::Result<S>
    where
        R: BitRead,
        S: SignedNumeric,
    {
        if MAX <= S::BITS_SIZE || bits <= S::BITS_SIZE {
            let unsigned = r.read_unsigned_counted::<MAX, S::Unsigned>(
                count.checked_sub(1).ok_or(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    "signed reads need at least 1 bit for sign",
                ))?,
            )?;
            let is_negative = r.read_bit()?;
            Ok(if is_negative {
                unsigned.as_negative(bits)
            } else {
                unsigned.as_non_negative()
            })
        } else {
            Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "excessive bits for type read",
            ))
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
            let unsigned = r.read_unsigned_var::<S::Unsigned>(B - 1)?;
            let is_negative = r.read_bit()?;
            Ok(if is_negative {
                unsigned.as_negative_fixed::<B>()
            } else {
                unsigned.as_non_negative()
            })
        }
    }

    fn write_signed<const MAX: u32, W, S>(
        w: &mut W,
        count @ BitCount { bits }: BitCount<MAX>,
        value: S,
    ) -> io::Result<()>
    where
        W: BitWrite,
        S: SignedNumeric,
    {
        if MAX <= S::BITS_SIZE || bits <= S::BITS_SIZE {
            w.write_unsigned_counted(
                count.checked_sub(1).ok_or(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    "signed writes need at least 1 bit for sign",
                ))?,
                if value.is_negative() {
                    value.as_negative(bits)
                } else {
                    value.as_non_negative()
                },
            )?;
            w.write_bit(value.is_negative())
        } else {
            Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "excessive bits for type written",
            ))
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
            w.write_unsigned_var(B - 1, value.as_negative_fixed::<B>())
                .and_then(|()| w.write_bit(true))
        } else {
            w.write_unsigned_var(B - 1, value.as_non_negative())
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

#[inline]
fn find_unary<N, E>(
    queue: &mut PartialByte<N>,
    leading_bits: impl Fn(u8) -> u32,
    max_bits: impl Fn(u32) -> u32,
    checked_shift: impl Fn(u8, u32) -> Option<u8>,
    mut read_val: impl FnMut() -> Result<u8, E>,
) -> Result<u32, E>
where
    N: Endianness,
{
    let mut acc = 0;

    loop {
        match leading_bits(queue.value) {
            bits if bits == max_bits(queue.bits) => {
                // all bits exhausted
                // fetch another byte and keep going
                acc += queue.bits;
                queue.value = read_val()?;
                queue.bits = u8::BITS_SIZE;
            }
            bits => match checked_shift(queue.value, bits + 1) {
                Some(value) => {
                    // fetch part of source byte
                    queue.value = value;
                    queue.bits -= bits + 1;
                    break Ok(acc + bits);
                }
                None => {
                    // fetch all of source byte
                    queue.value = 0;
                    queue.bits = 0;
                    break Ok(acc + bits);
                }
            },
        }
    }
}
