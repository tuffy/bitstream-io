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

    /// Returns a `u8` value in this type
    fn from_u8(u: u8) -> Self;

    /// Assuming 0 <= value < 256, returns this value as a `u8` type
    fn to_u8(self) -> u8;
}

macro_rules! define_numeric {
    ($t:ty) => {
        define_primitive_numeric!($t);

        impl Numeric for $t {
            const BITS_SIZE: u32 = mem::size_of::<$t>() as u32 * 8;

            const ZERO: Self = 0;

            const ONE: Self = 1;

            #[inline(always)]
            fn from_u8(u: u8) -> Self {
                u as $t
            }
            #[inline(always)]
            fn to_u8(self) -> u8 {
                self as u8
            }
        }
    };
}

/// This trait extends many common unsigned integer types
/// so that they can be used with the bitstream handling traits.
pub trait UnsignedInteger: Numeric + Into<crate::write::UnsignedValue> {
    /// This type's most-significant bit
    const MSB_BIT: Self;

    /// This type's least significant bit
    const LSB_BIT: Self;

    /// This type with all bits set
    const ALL: Self;

    /// The signed variant of ourself
    type Signed: SignedInteger<Unsigned = Self>;

    /// Given a twos-complement value,
    /// return this value is a non-negative signed number.
    /// The location of the sign bit depends on the stream's endianness
    /// and is not stored in the result.
    ///
    /// # Example
    /// ```
    /// use bitstream_io::UnsignedInteger;
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
    /// use bitstream_io::UnsignedInteger;
    /// assert_eq!(0b01111111u8.as_negative(8), -1i8);
    /// ```
    fn as_negative(self, bits: u32) -> Self::Signed;

    /// Given a two-complement positive value and certain number of bits,
    /// returns this value as a negative number.
    ///
    /// # Example
    /// ```
    /// use bitstream_io::UnsignedInteger;
    /// assert_eq!(0b01111111u8.as_negative_fixed::<8>(), -1i8);
    /// ```
    fn as_negative_fixed<const BITS: u32>(self) -> Self::Signed;

    /// Checked shift left
    fn checked_shl(self, rhs: u32) -> Option<Self>;

    /// Checked shift right
    fn checked_shr(self, rhs: u32) -> Option<Self>;

    /// Shift left up to our length in bits
    ///
    /// If rhs equals our length in bits, returns default
    fn shl_default(self, rhs: u32) -> Self {
        self.checked_shl(rhs).unwrap_or(Self::ZERO)
    }

    /// Shift left up to our length in bits
    ///
    /// If rhs equals our length in bits, returns zero
    fn shr_default(self, rhs: u32) -> Self {
        self.checked_shr(rhs).unwrap_or(Self::ZERO)
    }
}

macro_rules! define_unsigned_integer {
    ($t:ty, $s:ty) => {
        define_numeric!($t);

        impl UnsignedInteger for $t {
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
            #[inline(always)]
            fn checked_shl(self, rhs: u32) -> Option<Self> {
                self.checked_shl(rhs)
            }
            #[inline(always)]
            fn checked_shr(self, rhs: u32) -> Option<Self> {
                self.checked_shr(rhs)
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
            #[inline]
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

            #[inline]
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

            #[inline]
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

            #[inline]
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

        impl Integer for Option<NonZero<$t>> {
            #[inline]
            fn read<const BITS: u32, R: BitRead + ?Sized>(reader: &mut R) -> io::Result<Self>
            where
                Self: Sized,
            {
                <$t as Integer>::read::<BITS, R>(reader).map(NonZero::new)
            }

            #[inline]
            fn read_var<const MAX: u32, R>(reader: &mut R, count: BitCount<MAX>) -> io::Result<Self>
            where
                R: BitRead + ?Sized,
                Self: Sized,
            {
                <$t as Integer>::read_var::<MAX, R>(reader, count).map(NonZero::new)
            }

            #[inline]
            fn write<const BITS: u32, W: BitWrite + ?Sized>(
                self,
                writer: &mut W,
            ) -> io::Result<()> {
                <$t as Integer>::write::<BITS, W>(self.map(|n| n.get()).unwrap_or(0), writer)
            }

            #[inline]
            fn write_var<const MAX: u32, W: BitWrite + ?Sized>(
                self,
                writer: &mut W,
                count: BitCount<MAX>,
            ) -> io::Result<()> {
                <$t as Integer>::write_var::<MAX, W>(
                    self.map(|n| n.get()).unwrap_or(0),
                    writer,
                    count,
                )
            }
        }
    };
}

/// This trait extends many common signed integer types
/// so that they can be used with the bitstream handling traits.
///
/// This trait was formerly named `SignedNumeric` in 2.X.X code.
/// If backwards-compatibility is needed one can
/// import `SignedInteger` as `SignedNumeric`.
pub trait SignedInteger: Numeric + Into<crate::write::SignedValue> {
    /// The unsigned variant of ourself
    type Unsigned: UnsignedInteger<Signed = Self>;

    /// Returns true if this value is negative
    ///
    /// # Example
    /// ```
    /// use bitstream_io::SignedInteger;
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
    /// use bitstream_io::SignedInteger;
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
    /// use bitstream_io::SignedInteger;
    /// assert_eq!((-1i8).as_negative(8), 0b01111111u8);
    /// ```
    fn as_negative(self, bits: u32) -> Self::Unsigned;

    /// Given a negative value and a certain number of bits,
    /// returns this value as a twos-complement positive number.
    ///
    /// # Example
    /// ```
    /// use bitstream_io::SignedInteger;
    /// assert_eq!((-1i8).as_negative_fixed::<8>(), 0b01111111u8);
    /// ```
    fn as_negative_fixed<const BITS: u32>(self) -> Self::Unsigned;
}

macro_rules! define_signed_integer {
    ($t:ty, $u:ty) => {
        define_numeric!($t);

        impl SignedInteger for $t {
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

define_unsigned_integer!(u8, i8);
define_unsigned_integer!(u16, i16);
define_unsigned_integer!(u32, i32);
define_unsigned_integer!(u64, i64);
define_unsigned_integer!(u128, i128);

define_signed_integer!(i8, u8);
define_signed_integer!(i16, u16);
define_signed_integer!(i32, u32);
define_signed_integer!(i64, u64);
define_signed_integer!(i128, u128);

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
    /// repleneshing it from the given reader if necessary
    fn pop_bit_refill<R>(
        reader: &mut R,
        queue_value: &mut u8,
        queue_bits: &mut u32,
    ) -> io::Result<bool>
    where
        R: io::Read;

    /// Pops the next unary value from the source until
    /// `STOP_BIT` is encountered, replenishing it from the given
    /// closure if necessary.
    ///
    /// `STOP_BIT` must be 0 or 1.
    fn pop_unary<const STOP_BIT: u8, R>(
        reader: &mut R,
        queue_value: &mut u8,
        queue_bits: &mut u32,
    ) -> io::Result<u32>
    where
        R: io::Read;

    /// Pushes the next bit into the queue,
    /// and returns `Some` value if the queue is full.
    fn push_bit_flush(queue_value: &mut u8, queue_bits: &mut u32, bit: bool) -> Option<u8>;

    /// For performing bulk reads from a bit source to an output type.
    fn read_bits<const MAX: u32, R, U>(
        reader: &mut R,
        queue_value: &mut u8,
        queue_bits: &mut u32,
        count: BitCount<MAX>,
    ) -> io::Result<U>
    where
        R: io::Read,
        U: UnsignedInteger;

    /// For performing bulk reads from a bit source to an output type.
    fn read_bits_fixed<const BITS: u32, R, U>(
        reader: &mut R,
        queue_value: &mut u8,
        queue_bits: &mut u32,
    ) -> io::Result<U>
    where
        R: io::Read,
        U: UnsignedInteger;

    /// For performing bulk writes of a type to a bit sink.
    fn write_bits<const MAX: u32, W, U>(
        writer: &mut W,
        queue_value: &mut u8,
        queue_bits: &mut u32,
        count: BitCount<MAX>,
        value: U,
    ) -> io::Result<()>
    where
        W: io::Write,
        U: UnsignedInteger;

    /// For performing bulk writes of a constant value to a bit sink.
    fn write_bits_const<const BITS: u32, const VALUE: u32, W>(
        writer: &mut W,
        queue_value: &mut u8,
        queue_bits: &mut u32,
    ) -> io::Result<()>
    where
        W: io::Write;

    /// For performing bulk writes of a type to a bit sink.
    fn write_bits_fixed<const BITS: u32, W, U>(
        writer: &mut W,
        queue_value: &mut u8,
        queue_bits: &mut u32,
        value: U,
    ) -> io::Result<()>
    where
        W: io::Write,
        U: UnsignedInteger;

    /// Reads signed value from reader in this endianness
    fn read_signed<const MAX: u32, R, S>(r: &mut R, bits: BitCount<MAX>) -> io::Result<S>
    where
        R: BitRead,
        S: SignedInteger;

    /// Reads signed value from reader in this endianness
    fn read_signed_fixed<R, const B: u32, S>(r: &mut R) -> io::Result<S>
    where
        R: BitRead,
        S: SignedInteger;

    /// Writes signed value to writer in this endianness
    fn write_signed<const MAX: u32, W, S>(
        w: &mut W,
        bits: BitCount<MAX>,
        value: S,
    ) -> io::Result<()>
    where
        W: BitWrite,
        S: SignedInteger;

    /// Writes signed value to writer in this endianness
    fn write_signed_fixed<W, const B: u32, S>(w: &mut W, value: S) -> io::Result<()>
    where
        W: BitWrite,
        S: SignedInteger;

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

#[inline(always)]
fn read_byte<R>(mut reader: R) -> io::Result<u8>
where
    R: io::Read,
{
    let mut byte = 0;
    reader
        .read_exact(core::slice::from_mut(&mut byte))
        .map(|()| byte)
}

#[inline(always)]
fn write_byte<W>(mut writer: W, byte: u8) -> io::Result<()>
where
    W: io::Write,
{
    writer.write_all(core::slice::from_ref(&byte))
}

// These "read_bits" and "write_bits" functions are
// to be used by the endianness traits to fill in their closures
// and build specialized reading and writing routines
// that shift and consume bits in the proper directions.
//
// So while they have a lot of arguments, they're not intended
// for public consumption.

/// A number of bits to be consumed or written, with a known maximum
#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq)]
pub struct BitCount<const MAX: u32> {
    // The amount of bits may be less than or equal to the maximum,
    // but never more.
    bits: u32,
}

impl<const MAX: u32> BitCount<MAX> {
    /// The largest possible BitCount maximum value
    ///
    /// This corresponds to the largest unsigned integer
    /// type supported.
    const MAX: u32 = u128::BITS_SIZE;

    /// Builds a bit count from a constant number
    /// of bits, which must not be greater than `MAX`
    /// or greater than the largest supported type.
    ///
    /// Intended to be used for defining constants.
    ///
    /// Use `TryFrom` to conditionally build
    /// counts from values at runtime.
    ///
    /// # Examples
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
    ///
    /// ```rust,compile_fail
    /// use bitstream_io::BitCount;
    /// // trying to build a count of 10 with a maximum of 129
    /// // fails to compile at all
    /// let count = BitCount::<129>::new::<10>();
    /// ```
    pub const fn new<const BITS: u32>() -> Self {
        const {
            assert!(MAX <= BitCount::<BITS>::MAX, "MAX must be <= BitCount::MAX");
            assert!(BITS <= MAX, "BITS must be <= MAX");
        }

        Self { bits: BITS }
    }

    /// Add a number of bits to our count,
    /// returning a new count with a new maximum.
    ///
    /// Returns `None` if the new count goes above our new maximum.
    /// A compile-time error occurs if `NEW_MAX` is larger than
    /// the largest supported type.
    ///
    /// # Examples
    ///
    /// ```
    /// use bitstream_io::BitCount;
    ///
    /// let count = BitCount::<2>::new::<1>();
    /// // adding 2 to 1 and increasing the max to 3 yields a new count of 3
    /// assert_eq!(count.checked_add::<3>(2), Some(BitCount::<3>::new::<3>()));
    /// // adding 2 to 1 without increasing the max yields None
    /// assert_eq!(count.checked_add::<2>(2), None);
    /// ```
    ///
    /// ```rust,compile_fail
    /// use bitstream_io::BitCount;
    ///
    /// let count = BitCount::<2>::new::<1>();
    /// // a new maximum of 129 is larger than our largest supported type
    /// let count2 = count.checked_add::<129>(1);
    /// ```
    #[inline]
    pub const fn checked_add<const NEW_MAX: u32>(self, bits: u32) -> Option<BitCount<NEW_MAX>> {
        const {
            assert!(
                NEW_MAX <= BitCount::<NEW_MAX>::MAX,
                "NEW_MAX must be <= BitCount::MAX"
            );
        }

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
    /// A compile-time error occurs if one tries to
    /// use a maximum bit count larger than the largest
    /// supported type.
    ///
    /// # Examples
    /// ```
    /// use bitstream_io::BitCount;
    ///
    /// let count = BitCount::<5>::new::<5>();
    /// // muliplying 5 bits by 2 with a new max of 10 is ok
    /// assert_eq!(
    ///     count.try_map::<10, _>(|i| i.checked_mul(2)),
    ///     Some(BitCount::<10>::new::<10>()),
    /// );
    /// // multiplying 5 bits by 3 with a new max of 10 overflows
    /// assert_eq!(count.try_map::<10, _>(|i| i.checked_mul(3)), None);
    /// ```
    ///
    /// ```rust,compile_fail
    /// use bitstream_io::BitCount;
    ///
    /// // 129 bits is larger than the largest supported type
    /// let count = BitCount::<5>::new::<5>();
    /// let new_count = count.try_map::<129, _>(|i| i).unwrap();
    /// ```
    #[inline]
    pub fn try_map<const NEW_MAX: u32, F>(self, f: F) -> Option<BitCount<NEW_MAX>>
    where
        F: FnOnce(u32) -> Option<u32>,
    {
        const {
            assert!(
                NEW_MAX <= BitCount::<NEW_MAX>::MAX,
                "NEW_MAX must be <= BitCount::MAX"
            );
        }

        f(self.bits)
            .filter(|bits| *bits <= NEW_MAX)
            .map(|bits| BitCount { bits })
    }
}

impl<const MAX: u32> core::convert::TryFrom<u32> for BitCount<MAX> {
    type Error = u32;

    /// Attempts to convert a `u32` bit count to a `BitCount`
    ///
    /// Attempting a bit maximum bit count larger than the
    /// largest supported type is a compile-time error
    ///
    /// # Examples
    /// ```
    /// use bitstream_io::BitCount;
    /// use std::convert::TryInto;
    ///
    /// assert_eq!(8u32.try_into(), Ok(BitCount::<8>::new::<8>()));
    /// assert_eq!(9u32.try_into(), Err::<BitCount<8>, _>(9));
    /// ```
    ///
    /// ```rust,compile_fail
    /// use bitstream_io::BitCount;
    /// use std::convert::TryInto;
    ///
    /// // largest bit count is 128
    /// assert_eq!(129u32.try_into(), Err::<BitCount<129>, _>(129));
    /// ```
    fn try_from(bits: u32) -> Result<Self, Self::Error> {
        const {
            assert!(MAX <= BitCount::<MAX>::MAX, "MAX must be <= BitCount::MAX");
        }

        (bits <= MAX).then_some(Self { bits }).ok_or(bits)
    }
}

impl BitCount<{ u128::BITS_SIZE }> {
    /// Builds a bit count where the maximum bits is unknown.
    ///
    /// In this case, `u128::BITS_SIZE` is assumed,
    /// because that's the largest type supported.
    ///
    /// # Example
    /// ```
    /// use bitstream_io::BitCount;
    /// assert_eq!(BitCount::unknown(5), BitCount::<128>::new::<5>());
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

impl BigEndian {
    // checked in the sense that we've verified
    // the output type is large enough to hold the
    // requested number of bits
    #[inline]
    fn read_bits_checked<const MAX: u32, R, U>(
        reader: &mut R,
        queue: &mut u8,
        queue_bits: &mut u32,
        BitCount { bits }: BitCount<MAX>,
    ) -> io::Result<U>
    where
        R: io::Read,
        U: UnsignedInteger,
    {
        // reads a whole value with the given number of
        // bytes in our endianness, where the number of bytes
        // must be less than or equal to the type's size in bytes
        #[inline(always)]
        fn read_bytes<R, U>(reader: &mut R, bytes: usize) -> io::Result<U>
        where
            R: io::Read,
            U: UnsignedInteger,
        {
            let mut buf = U::buffer();
            reader
                .read_exact(&mut buf.as_mut()[(mem::size_of::<U>() - bytes)..])
                .map(|()| U::from_be_bytes(buf))
        }

        if bits <= *queue_bits {
            // all bits in queue, so no byte needed
            let value = queue.shr_default(u8::BITS_SIZE - bits);
            *queue = queue.shl_default(bits);
            *queue_bits -= bits;
            Ok(U::from_u8(value))
        } else {
            // at least one byte needed

            // bits needed beyond what's in the queue
            let needed_bits = bits - *queue_bits;

            match (needed_bits / 8, needed_bits % 8) {
                (0, needed) => {
                    // only one additional byte needed,
                    // which we share between our returned value
                    // and the bit queue
                    let next_byte = read_byte(reader)?;

                    Ok(U::from_u8(
                        mem::replace(queue, next_byte.shl_default(needed)).shr_default(
                            u8::BITS_SIZE - mem::replace(queue_bits, u8::BITS_SIZE - needed),
                        ),
                    )
                    .shl_default(needed)
                        | U::from_u8(next_byte.shr_default(u8::BITS_SIZE - needed)))
                }
                (bytes, 0) => {
                    // exact number of bytes needed beyond what's
                    // available in the queue
                    // so read a whole value from the reader
                    // and prepend what's left of our queue onto it

                    Ok(U::from_u8(
                        mem::take(queue).shr_default(u8::BITS_SIZE - mem::take(queue_bits)),
                    )
                    .shl_default(needed_bits)
                        | read_bytes(reader, bytes as usize)?)
                }
                (bytes, needed) => {
                    // read a whole value from the reader
                    // prepend what's in the queue at the front of it
                    // *and* append a partial byte at the end of it
                    // while also updating the queue and its bit count

                    let whole: U = read_bytes(reader, bytes as usize)?;
                    let next_byte = read_byte(reader)?;

                    Ok(U::from_u8(
                        mem::replace(queue, next_byte.shl_default(needed)).shr_default(
                            u8::BITS_SIZE - mem::replace(queue_bits, u8::BITS_SIZE - needed),
                        ),
                    )
                    .shl_default(needed_bits)
                        | whole.shl_default(needed)
                        | U::from_u8(next_byte.shr_default(u8::BITS_SIZE - needed)))
                }
            }
        }
    }

    // checked in the sense that we've verified
    // the input type is large enough to hold the
    // requested number of bits and that the value is
    // not too large for those bits
    #[inline]
    fn write_bits_checked<const MAX: u32, W, U>(
        writer: &mut W,
        queue_value: &mut u8,
        queue_bits: &mut u32,
        BitCount { bits }: BitCount<MAX>,
        value: U,
    ) -> io::Result<()>
    where
        W: io::Write,
        U: UnsignedInteger,
    {
        fn write_bytes<W, U>(writer: &mut W, bytes: usize, value: U) -> io::Result<()>
        where
            W: io::Write,
            U: UnsignedInteger,
        {
            let buf = U::to_be_bytes(value);
            writer.write_all(&buf.as_ref()[(mem::size_of::<U>() - bytes)..])
        }

        // the amount of available bits in the queue
        let available_bits = u8::BITS_SIZE - *queue_bits;

        if bits < available_bits {
            // all bits fit in queue, so no write needed
            *queue_value = queue_value.shl_default(bits) | U::to_u8(value);
            *queue_bits += bits;
            Ok(())
        } else {
            // at least one byte needs to be written

            // bits beyond what can fit in the queue
            let excess_bits = bits - available_bits;

            match (excess_bits / 8, excess_bits % 8) {
                (0, excess) => {
                    // only one byte to be written,
                    // while the excess bits are shared
                    // between the written byte and the bit queue

                    *queue_bits = excess;

                    write_byte(
                        writer,
                        mem::replace(
                            queue_value,
                            U::to_u8(value & U::ALL.shr_default(U::BITS_SIZE - excess)),
                        )
                        .shl_default(available_bits)
                            | U::to_u8(value.shr_default(excess)),
                    )
                }
                (bytes, 0) => {
                    // no excess bytes beyond what can fit the queue
                    // so write a whole byte and
                    // the remainder of the whole value

                    *queue_bits = 0;

                    write_byte(
                        writer.by_ref(),
                        mem::take(queue_value).shl_default(available_bits)
                            | U::to_u8(value.shr_default(bytes * 8)),
                    )?;

                    write_bytes(writer, bytes as usize, value)
                }
                (bytes, excess) => {
                    // write what's in the queue along
                    // with the head of our whole value,
                    // write the middle section of our whole value,
                    // while also replacing the queue with
                    // the tail of our whole value

                    *queue_bits = excess;

                    write_byte(
                        writer.by_ref(),
                        mem::replace(
                            queue_value,
                            U::to_u8(value & U::ALL.shr_default(U::BITS_SIZE - excess)),
                        )
                        .shl_default(available_bits)
                            | U::to_u8(value.shr_default(excess + bytes * 8)),
                    )?;

                    write_bytes(writer, bytes as usize, value.shr_default(excess))
                }
            }
        }
    }
}

impl Endianness for BigEndian {
    #[inline]
    fn push_bit_flush(queue_value: &mut u8, queue_bits: &mut u32, bit: bool) -> Option<u8> {
        *queue_value = (*queue_value << 1) | u8::from(bit);
        *queue_bits = (*queue_bits + 1) % 8;
        (*queue_bits == 0).then(|| mem::take(queue_value))
    }

    #[inline]
    fn read_bits<const MAX: u32, R, U>(
        reader: &mut R,
        queue_value: &mut u8,
        queue_bits: &mut u32,
        count @ BitCount { bits }: BitCount<MAX>,
    ) -> io::Result<U>
    where
        R: io::Read,
        U: UnsignedInteger,
    {
        if MAX <= U::BITS_SIZE || bits <= U::BITS_SIZE {
            Self::read_bits_checked::<MAX, R, U>(reader, queue_value, queue_bits, count)
        } else {
            Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "excessive bits for type read",
            ))
        }
    }

    #[inline]
    fn read_bits_fixed<const BITS: u32, R, U>(
        reader: &mut R,
        queue_value: &mut u8,
        queue_bits: &mut u32,
    ) -> io::Result<U>
    where
        R: io::Read,
        U: UnsignedInteger,
    {
        const {
            assert!(BITS <= U::BITS_SIZE, "excessive bits for type read");
        }

        Self::read_bits_checked::<BITS, R, U>(
            reader,
            queue_value,
            queue_bits,
            BitCount::new::<BITS>(),
        )
    }

    /// For performing bulk writes of a type to a bit sink.
    fn write_bits<const MAX: u32, W, U>(
        writer: &mut W,
        queue_value: &mut u8,
        queue_bits: &mut u32,
        count @ BitCount { bits }: BitCount<MAX>,
        value: U,
    ) -> io::Result<()>
    where
        W: io::Write,
        U: UnsignedInteger,
    {
        if MAX <= U::BITS_SIZE || bits <= U::BITS_SIZE {
            if bits == 0 {
                Ok(())
            } else if value <= U::ALL >> (U::BITS_SIZE - bits) {
                Self::write_bits_checked::<MAX, W, U>(writer, queue_value, queue_bits, count, value)
            } else {
                Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    "excessive value for bits written",
                ))
            }
        } else {
            Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "excessive bits for type written",
            ))
        }
    }

    /// For performing bulk writes of a constant value to a bit sink.
    fn write_bits_const<const BITS: u32, const VALUE: u32, W>(
        writer: &mut W,
        queue_value: &mut u8,
        queue_bits: &mut u32,
    ) -> io::Result<()>
    where
        W: io::Write,
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
            Self::write_bits_checked::<BITS, W, u32>(
                writer,
                queue_value,
                queue_bits,
                BitCount::new::<BITS>(),
                VALUE,
            )
        }
    }

    /// For performing bulk writes of a type to a bit sink.
    fn write_bits_fixed<const BITS: u32, W, U>(
        writer: &mut W,
        queue_value: &mut u8,
        queue_bits: &mut u32,
        value: U,
    ) -> io::Result<()>
    where
        W: io::Write,
        U: UnsignedInteger,
    {
        const {
            assert!(BITS <= U::BITS_SIZE, "excessive bits for type written");
        }

        if BITS == 0 {
            Ok(())
        } else if value <= (U::ALL >> (U::BITS_SIZE - BITS)) {
            Self::write_bits_checked::<BITS, W, U>(
                writer,
                queue_value,
                queue_bits,
                BitCount::new::<BITS>(),
                value,
            )
        } else {
            Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "excessive value for bits written",
            ))
        }
    }

    #[inline]
    fn pop_bit_refill<R>(
        reader: &mut R,
        queue_value: &mut u8,
        queue_bits: &mut u32,
    ) -> io::Result<bool>
    where
        R: io::Read,
    {
        Ok(if *queue_bits == 0 {
            let value = read_byte(reader)?;
            let msb = value & u8::MSB_BIT;
            *queue_value = value << 1;
            *queue_bits = u8::BITS_SIZE - 1;
            msb
        } else {
            let msb = *queue_value & u8::MSB_BIT;
            *queue_value <<= 1;
            *queue_bits -= 1;
            msb
        } != 0)
    }

    #[inline]
    fn pop_unary<const STOP_BIT: u8, R>(
        reader: &mut R,
        queue_value: &mut u8,
        queue_bits: &mut u32,
    ) -> io::Result<u32>
    where
        R: io::Read,
    {
        const {
            assert!(matches!(STOP_BIT, 0 | 1), "stop bit must be 0 or 1");
        }

        match STOP_BIT {
            0 => find_unary(
                reader,
                queue_value,
                queue_bits,
                |v| v.leading_ones(),
                |q| *q,
                |v, b| v.checked_shl(b),
            ),
            1 => find_unary(
                reader,
                queue_value,
                queue_bits,
                |v| v.leading_zeros(),
                |_| u8::BITS_SIZE,
                |v, b| v.checked_shl(b),
            ),
            _ => unreachable!(),
        }
    }

    fn read_signed<const MAX: u32, R, S>(
        r: &mut R,
        count @ BitCount { bits }: BitCount<MAX>,
    ) -> io::Result<S>
    where
        R: BitRead,
        S: SignedInteger,
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
        S: SignedInteger,
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
        S: SignedInteger,
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
        S: SignedInteger,
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

impl LittleEndian {
    // checked in the sense that we've verified
    // the output type is large enough to hold the
    // requested number of bits
    #[inline]
    fn read_bits_checked<const MAX: u32, R, U>(
        reader: &mut R,
        queue: &mut u8,
        queue_bits: &mut u32,
        BitCount { bits }: BitCount<MAX>,
    ) -> io::Result<U>
    where
        R: io::Read,
        U: UnsignedInteger,
    {
        // reads a whole value with the given number of
        // bytes in our endianness, where the number of bytes
        // must be less than or equal to the type's size in bytes
        #[inline(always)]
        fn read_bytes<R, U>(reader: &mut R, bytes: usize) -> io::Result<U>
        where
            R: io::Read,
            U: UnsignedInteger,
        {
            let mut buf = U::buffer();
            reader
                .read_exact(&mut buf.as_mut()[0..bytes])
                .map(|()| U::from_le_bytes(buf))
        }

        if bits <= *queue_bits {
            // all bits in queue, so no byte needed
            let value = *queue & u8::ALL.shr_default(u8::BITS_SIZE - bits);
            *queue = queue.shr_default(bits);
            *queue_bits -= bits;
            Ok(U::from_u8(value))
        } else {
            // at least one byte needed

            // bits needed beyond what's in the queue
            let needed_bits = bits - *queue_bits;

            match (needed_bits / 8, needed_bits % 8) {
                (0, needed) => {
                    // only one additional byte needed,
                    // which we share between our returned value
                    // and the bit queue
                    let next_byte = read_byte(reader)?;

                    Ok(
                        U::from_u8(mem::replace(queue, next_byte.shr_default(needed)))
                            | (U::from_u8(next_byte & (u8::ALL >> (u8::BITS_SIZE - needed)))
                                << mem::replace(queue_bits, u8::BITS_SIZE - needed)),
                    )
                }
                (bytes, 0) => {
                    // exact number of bytes needed beyond what's
                    // available in the queue

                    // so read a whole value from the reader
                    // and prepend what's left of our queue onto it

                    Ok(U::from_u8(mem::take(queue))
                        | (read_bytes::<R, U>(reader, bytes as usize)? << mem::take(queue_bits)))
                }
                (bytes, needed) => {
                    // read a whole value from the reader
                    // prepend what's in the queue at the front of it
                    // *and* append a partial byte at the end of it
                    // while also updating the queue and its bit count

                    let whole: U = read_bytes(reader, bytes as usize)?;
                    let next_byte = read_byte(reader)?;

                    Ok(
                        U::from_u8(mem::replace(queue, next_byte.shr_default(needed)))
                            | (whole << *queue_bits)
                            | (U::from_u8(next_byte & (u8::ALL >> (u8::BITS_SIZE - needed)))
                                << (mem::replace(queue_bits, u8::BITS_SIZE - needed) + bytes * 8)),
                    )
                }
            }
        }
    }

    // checked in the sense that we've verified
    // the input type is large enough to hold the
    // requested number of bits and that the value is
    // not too large for those bits
    #[inline]
    fn write_bits_checked<const MAX: u32, W, U>(
        writer: &mut W,
        queue_value: &mut u8,
        queue_bits: &mut u32,
        BitCount { bits }: BitCount<MAX>,
        value: U,
    ) -> io::Result<()>
    where
        W: io::Write,
        U: UnsignedInteger,
    {
        fn write_bytes<W, U>(writer: &mut W, bytes: usize, value: U) -> io::Result<()>
        where
            W: io::Write,
            U: UnsignedInteger,
        {
            let buf = U::to_le_bytes(value);
            writer.write_all(&buf.as_ref()[0..bytes])
        }

        // the amount of available bits in the queue
        let available_bits = u8::BITS_SIZE - *queue_bits;

        if bits < available_bits {
            // all bits fit in queue, so no write needed
            *queue_value |= U::to_u8(value.shl_default(*queue_bits));
            *queue_bits += bits;
            Ok(())
        } else {
            // at least one byte needs to be written

            // bits beyond what can fit in the queue
            let excess_bits = bits - available_bits;

            match (excess_bits / 8, excess_bits % 8) {
                (0, excess) => {
                    // only one byte to be written,
                    // while the excess bits are shared
                    // between the written byte and the bit queue

                    write_byte(
                        writer,
                        mem::replace(queue_value, U::to_u8(value.shr_default(available_bits)))
                            | U::to_u8(
                                (value << mem::replace(queue_bits, excess)) & U::from_u8(u8::ALL),
                            ),
                    )
                }
                (bytes, 0) => {
                    // no excess bytes beyond what can fit the queue
                    // so write a whole byte and
                    // the remainder of the whole value

                    write_byte(
                        writer.by_ref(),
                        mem::take(queue_value)
                            | U::to_u8((value << mem::take(queue_bits)) & U::from_u8(u8::ALL)),
                    )?;

                    write_bytes(writer, bytes as usize, value >> available_bits)
                }
                (bytes, excess) => {
                    // write what's in the queue along
                    // with the head of our whole value,
                    // write the middle section of our whole value,
                    // while also replacing the queue with
                    // the tail of our whole value

                    write_byte(
                        writer.by_ref(),
                        mem::replace(
                            queue_value,
                            U::to_u8(value.shr_default(available_bits + bytes * 8)),
                        ) | U::to_u8(
                            (value << mem::replace(queue_bits, excess)) & U::from_u8(u8::ALL),
                        ),
                    )?;

                    write_bytes(writer, bytes as usize, value >> available_bits)
                }
            }
        }
    }
}

impl Endianness for LittleEndian {
    #[inline]
    fn push_bit_flush(queue_value: &mut u8, queue_bits: &mut u32, bit: bool) -> Option<u8> {
        *queue_value |= u8::from(bit) << *queue_bits;
        *queue_bits = (*queue_bits + 1) % 8;
        (*queue_bits == 0).then(|| mem::take(queue_value))
    }

    #[inline]
    fn read_bits<const MAX: u32, R, U>(
        reader: &mut R,
        queue_value: &mut u8,
        queue_bits: &mut u32,
        count @ BitCount { bits }: BitCount<MAX>,
    ) -> io::Result<U>
    where
        R: io::Read,
        U: UnsignedInteger,
    {
        if MAX <= U::BITS_SIZE || bits <= U::BITS_SIZE {
            Self::read_bits_checked::<MAX, R, U>(reader, queue_value, queue_bits, count)
        } else {
            Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "excessive bits for type read",
            ))
        }
    }

    #[inline]
    fn read_bits_fixed<const BITS: u32, R, U>(
        reader: &mut R,
        queue_value: &mut u8,
        queue_bits: &mut u32,
    ) -> io::Result<U>
    where
        R: io::Read,
        U: UnsignedInteger,
    {
        const {
            assert!(BITS <= U::BITS_SIZE, "excessive bits for type read");
        }

        Self::read_bits_checked::<BITS, R, U>(
            reader,
            queue_value,
            queue_bits,
            BitCount::new::<BITS>(),
        )
    }

    /// For performing bulk writes of a type to a bit sink.
    fn write_bits<const MAX: u32, W, U>(
        writer: &mut W,
        queue_value: &mut u8,
        queue_bits: &mut u32,
        count @ BitCount { bits }: BitCount<MAX>,
        value: U,
    ) -> io::Result<()>
    where
        W: io::Write,
        U: UnsignedInteger,
    {
        if MAX <= U::BITS_SIZE || bits <= U::BITS_SIZE {
            if bits == 0 {
                Ok(())
            } else if value <= U::ALL >> (U::BITS_SIZE - bits) {
                Self::write_bits_checked::<MAX, W, U>(writer, queue_value, queue_bits, count, value)
            } else {
                Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    "excessive value for bits written",
                ))
            }
        } else {
            Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "excessive bits for type written",
            ))
        }
    }

    /// For performing bulk writes of a constant value to a bit sink.
    fn write_bits_const<const BITS: u32, const VALUE: u32, W>(
        writer: &mut W,
        queue_value: &mut u8,
        queue_bits: &mut u32,
    ) -> io::Result<()>
    where
        W: io::Write,
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
            Self::write_bits_checked::<BITS, W, u32>(
                writer,
                queue_value,
                queue_bits,
                BitCount::new::<BITS>(),
                VALUE,
            )
        }
    }

    /// For performing bulk writes of a type to a bit sink.
    fn write_bits_fixed<const BITS: u32, W, U>(
        writer: &mut W,
        queue_value: &mut u8,
        queue_bits: &mut u32,
        value: U,
    ) -> io::Result<()>
    where
        W: io::Write,
        U: UnsignedInteger,
    {
        const {
            assert!(BITS <= U::BITS_SIZE, "excessive bits for type written");
        }

        if BITS == 0 {
            Ok(())
        } else if value <= (U::ALL >> (U::BITS_SIZE - BITS)) {
            Self::write_bits_checked::<BITS, W, U>(
                writer,
                queue_value,
                queue_bits,
                BitCount::new::<BITS>(),
                value,
            )
        } else {
            Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "excessive value for bits written",
            ))
        }
    }

    #[inline]
    fn pop_bit_refill<R>(
        reader: &mut R,
        queue_value: &mut u8,
        queue_bits: &mut u32,
    ) -> io::Result<bool>
    where
        R: io::Read,
    {
        Ok(if *queue_bits == 0 {
            let value = read_byte(reader)?;
            let lsb = value & u8::LSB_BIT;
            *queue_value = value >> 1;
            *queue_bits = u8::BITS_SIZE - 1;
            lsb
        } else {
            let lsb = *queue_value & u8::LSB_BIT;
            *queue_value >>= 1;
            *queue_bits -= 1;
            lsb
        } != 0)
    }

    #[inline]
    fn pop_unary<const STOP_BIT: u8, R>(
        reader: &mut R,
        queue_value: &mut u8,
        queue_bits: &mut u32,
    ) -> io::Result<u32>
    where
        R: io::Read,
    {
        const {
            assert!(matches!(STOP_BIT, 0 | 1), "stop bit must be 0 or 1");
        }

        match STOP_BIT {
            0 => find_unary(
                reader,
                queue_value,
                queue_bits,
                |v| v.trailing_ones(),
                |q| *q,
                |v, b| v.checked_shr(b),
            ),
            1 => find_unary(
                reader,
                queue_value,
                queue_bits,
                |v| v.trailing_zeros(),
                |_| u8::BITS_SIZE,
                |v, b| v.checked_shr(b),
            ),
            _ => unreachable!(),
        }
    }

    fn read_signed<const MAX: u32, R, S>(
        r: &mut R,
        count @ BitCount { bits }: BitCount<MAX>,
    ) -> io::Result<S>
    where
        R: BitRead,
        S: SignedInteger,
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
        S: SignedInteger,
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
        S: SignedInteger,
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
        S: SignedInteger,
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
fn find_unary<R>(
    reader: &mut R,
    queue_value: &mut u8,
    queue_bits: &mut u32,
    leading_bits: impl Fn(u8) -> u32,
    max_bits: impl Fn(&mut u32) -> u32,
    checked_shift: impl Fn(u8, u32) -> Option<u8>,
) -> io::Result<u32>
where
    R: io::Read,
{
    let mut acc = 0;

    loop {
        match leading_bits(*queue_value) {
            bits if bits == max_bits(queue_bits) => {
                // all bits exhausted
                // fetch another byte and keep going
                acc += *queue_bits;
                *queue_value = read_byte(reader.by_ref())?;
                *queue_bits = u8::BITS_SIZE;
            }
            bits => match checked_shift(*queue_value, bits + 1) {
                Some(value) => {
                    // fetch part of source byte
                    *queue_value = value;
                    *queue_bits -= bits + 1;
                    break Ok(acc + bits);
                }
                None => {
                    // fetch all of source byte
                    *queue_value = 0;
                    *queue_bits = 0;
                    break Ok(acc + bits);
                }
            },
        }
    }
}
