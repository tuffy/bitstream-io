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

use core::ops::{
    BitAnd, BitOr, BitOrAssign, BitXor, ControlFlow, Not, Rem, RemAssign, Shl, ShlAssign, Shr,
    ShrAssign, Sub,
};
use core::{fmt::Debug, marker::PhantomData, mem};
#[cfg(feature = "std")]
use std::io;

pub mod huffman;
pub mod read;
pub mod write;
pub use read::{
    BitRead, BitReader, ByteRead, ByteReader, FromBitStream, FromBitStreamWith, FromByteStream,
    FromByteStreamWith,
};
pub use write::{
    BitCounter, BitRecorder, BitWrite, BitWriter, ByteWrite, ByteWriter, ToBitStream,
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
    /// Creates a new `BitSource` with the given bits and value.
    ///
    /// # Errors
    ///
    /// Returns an error if the bits are larger than the given
    /// type, or if the value would not fit into the given number of bits.
    fn new_source<U>(bits: u32, value: U) -> io::Result<BitSourceOnce<Self, U>>
    where
        U: UnsignedNumeric;

    /// Creates a new `BitSource` with the given bits and value.
    ///
    /// # Errors
    ///
    /// Returns an error if the value would not fit into
    /// the given number of bits.
    /// A compile-time error occurs if the number of bits is
    /// larger than the value.
    fn new_source_fixed<const BITS: u32, U>(value: U) -> io::Result<BitSourceOnce<Self, U>>
    where
        U: UnsignedNumeric;

    /// Pops the next bit from the queue, if available.
    fn pop_bit_once<U>(queue: &mut BitSourceOnce<Self, U>) -> Option<bool>
    where
        U: UnsignedNumeric;

    /// Pops the next bit from the queue,
    /// repleneshing it from the given closure if necessary
    fn pop_bit_refill<U, F, E>(
        queue: &mut BitSourceRefill<Self, U>,
        read_val: F,
    ) -> Result<bool, E>
    where
        U: UnsignedNumeric,
        F: FnOnce() -> Result<U, E>;

    /// Pops the next unary value from the source until
    /// `STOP_BIT` is encountered, replenishing it from the given
    /// closure if necessary.
    ///
    /// `STOP_BIT` must be 0 or 1.
    fn pop_unary<const STOP_BIT: u8, U, F, E>(
        queue: &mut BitSourceRefill<Self, U>,
        read_val: F,
    ) -> Result<u32, E>
    where
        U: UnsignedNumeric,
        F: FnMut() -> Result<U, E>;

    /// Pushes the next bit into the queue,
    /// and returns `Some` value if the queue is full.
    fn push_bit_flush<U>(queue: &mut BitSinkFlush<Self, U>, bit: bool) -> Option<U>
    where
        U: UnsignedNumeric;

    /// Pushes the next bit into the queue,
    /// returning a whole value once the sink is full.
    fn push_bit_once<U>(
        queue: BitSinkOnce<Self, U>,
        bit: bool,
    ) -> ControlFlow<U, BitSinkOnce<Self, U>>
    where
        U: UnsignedNumeric;

    /// Pushes the next bit into the queue,
    /// returning a whole value once the sink is full.
    fn push_bit_once_fixed<const B: u32, U>(
        queue: BitSinkOnceFixed<B, Self, U>,
        bit: bool,
    ) -> ControlFlow<U, BitSinkOnceFixed<B, Self, U>>
    where
        U: UnsignedNumeric;

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
    fn new_source<U>(bits: u32, value: U) -> io::Result<BitSourceOnce<Self, U>>
    where
        U: UnsignedNumeric,
    {
        if value
            <= (U::ALL
                >> U::BITS_SIZE.checked_sub(bits).ok_or(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    "excessive bits for type written",
                ))?)
        {
            Ok(BitSourceOnce {
                phantom: PhantomData,
                value: value << (U::BITS_SIZE - bits),
                bits,
            })
        } else {
            Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "excessive value for bits written",
            ))
        }
    }

    fn new_source_fixed<const BITS: u32, U>(value: U) -> io::Result<BitSourceOnce<Self, U>>
    where
        U: UnsignedNumeric,
    {
        const {
            assert!(BITS <= U::BITS_SIZE, "excessive bits for type written");
        }

        if value <= (U::ALL >> (U::BITS_SIZE - BITS)) {
            Ok(BitSourceOnce {
                phantom: PhantomData,
                value: value << (U::BITS_SIZE - BITS),
                bits: BITS,
            })
        } else {
            Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "excessive value for bits written",
            ))
        }
    }

    fn pop_bit_once<U>(queue: &mut BitSourceOnce<Self, U>) -> Option<bool>
    where
        U: UnsignedNumeric,
    {
        if queue.is_empty() {
            None
        } else {
            let msb = queue.value & U::MSB_BIT;
            queue.value <<= 1;
            queue.bits -= 1;
            Some(msb != U::ZERO)
        }
    }

    fn pop_bit_refill<U, F, E>(queue: &mut BitSourceRefill<Self, U>, read_val: F) -> Result<bool, E>
    where
        U: UnsignedNumeric,
        F: FnOnce() -> Result<U, E>,
    {
        Ok(if queue.is_empty() {
            let value = read_val()?;
            let msb = value & U::MSB_BIT;
            queue.value = value << 1;
            queue.bits = U::BITS_SIZE - 1;
            msb
        } else {
            let msb = queue.value & U::MSB_BIT;
            queue.value <<= 1;
            queue.bits -= 1;
            msb
        } != U::ZERO)
    }

    fn pop_unary<const STOP_BIT: u8, U, F, E>(
        queue: &mut BitSourceRefill<Self, U>,
        read_val: F,
    ) -> Result<u32, E>
    where
        U: UnsignedNumeric,
        F: FnMut() -> Result<U, E>,
    {
        const {
            assert!(matches!(STOP_BIT, 0 | 1), "stop bit must be 0 or 1");
        }

        match STOP_BIT {
            0 => queue.find_unary(
                |v| v.leading_ones(),
                |q| q.bits,
                |v, b| v.checked_shl(b),
                read_val,
            ),
            1 => queue.find_unary(
                |v| v.leading_zeros(),
                |_| U::BITS_SIZE,
                |v, b| v.checked_shl(b),
                read_val,
            ),
            _ => unreachable!(),
        }
    }

    #[inline]
    fn push_bit_flush<U>(queue: &mut BitSinkFlush<Self, U>, bit: bool) -> Option<U>
    where
        U: UnsignedNumeric,
    {
        queue.value = if bit { U::LSB_BIT } else { U::ZERO } | (queue.value << 1);
        queue.bits = (queue.bits + 1) % U::BITS_SIZE;
        queue.is_empty().then(|| mem::take(&mut queue.value))
    }

    #[inline]
    fn push_bit_once<U>(
        mut queue: BitSinkOnce<Self, U>,
        bit: bool,
    ) -> ControlFlow<U, BitSinkOnce<Self, U>>
    where
        U: UnsignedNumeric,
    {
        queue.value = if bit { U::LSB_BIT } else { U::ZERO } | (queue.value << 1);
        queue.bits += 1;
        if queue.bits == queue.total_bits {
            ControlFlow::Break(queue.value)
        } else {
            ControlFlow::Continue(queue)
        }
    }

    #[inline]
    fn push_bit_once_fixed<const B: u32, U>(
        mut queue: BitSinkOnceFixed<B, Self, U>,
        bit: bool,
    ) -> ControlFlow<U, BitSinkOnceFixed<B, Self, U>>
    where
        U: UnsignedNumeric,
    {
        queue.value = if bit { U::LSB_BIT } else { U::ZERO } | (queue.value << 1);
        queue.bits += 1;
        if queue.bits == B {
            ControlFlow::Break(queue.value)
        } else {
            ControlFlow::Continue(queue)
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
    fn new_source<U>(bits: u32, value: U) -> io::Result<BitSourceOnce<Self, U>>
    where
        U: UnsignedNumeric,
    {
        if value
            <= (U::ALL
                >> U::BITS_SIZE.checked_sub(bits).ok_or(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    "excessive bits for type written",
                ))?)
        {
            Ok(BitSourceOnce {
                phantom: PhantomData,
                value,
                bits,
            })
        } else {
            Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "excessive value for bits written",
            ))
        }
    }

    fn new_source_fixed<const BITS: u32, U>(value: U) -> io::Result<BitSourceOnce<Self, U>>
    where
        U: UnsignedNumeric,
    {
        const {
            assert!(BITS <= U::BITS_SIZE, "excessive bits for type written");
        }

        if value <= (U::ALL >> (U::BITS_SIZE - BITS)) {
            Ok(BitSourceOnce {
                phantom: PhantomData,
                value,
                bits: BITS,
            })
        } else {
            Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "excessive value for bits written",
            ))
        }
    }

    fn pop_bit_once<U>(queue: &mut BitSourceOnce<Self, U>) -> Option<bool>
    where
        U: UnsignedNumeric,
    {
        if queue.is_empty() {
            None
        } else {
            let lsb = queue.value & U::LSB_BIT;
            queue.value >>= 1;
            queue.bits -= 1;
            Some(lsb != U::ZERO)
        }
    }

    fn pop_bit_refill<U, F, E>(queue: &mut BitSourceRefill<Self, U>, read_val: F) -> Result<bool, E>
    where
        U: UnsignedNumeric,
        F: FnOnce() -> Result<U, E>,
    {
        Ok(if queue.is_empty() {
            let value = read_val()?;
            let lsb = value & U::LSB_BIT;
            queue.value = value >> 1;
            queue.bits = U::BITS_SIZE - 1;
            lsb
        } else {
            let lsb = queue.value & U::LSB_BIT;
            queue.value >>= 1;
            queue.bits -= 1;
            lsb
        } != U::ZERO)
    }

    fn pop_unary<const STOP_BIT: u8, U, F, E>(
        queue: &mut BitSourceRefill<Self, U>,
        read_val: F,
    ) -> Result<u32, E>
    where
        U: UnsignedNumeric,
        F: FnMut() -> Result<U, E>,
    {
        // FIXME - optimize this for different endianness-es

        const {
            assert!(matches!(STOP_BIT, 0 | 1), "stop bit must be 0 or 1");
        }

        match STOP_BIT {
            0 => queue.find_unary(
                |v| v.trailing_ones(),
                |q| q.bits,
                |v, b| v.checked_shr(b),
                read_val,
            ),
            1 => queue.find_unary(
                |v| v.trailing_zeros(),
                |_| U::BITS_SIZE,
                |v, b| v.checked_shr(b),
                read_val,
            ),
            _ => unreachable!(),
        }
    }

    #[inline]
    fn push_bit_flush<U>(queue: &mut BitSinkFlush<Self, U>, bit: bool) -> Option<U>
    where
        U: UnsignedNumeric,
    {
        queue.value = if bit { U::MSB_BIT } else { U::ZERO } | (queue.value >> 1);
        queue.bits = (queue.bits + 1) % U::BITS_SIZE;
        queue.is_empty().then(|| mem::take(&mut queue.value))
    }

    fn push_bit_once<U>(
        mut queue: BitSinkOnce<Self, U>,
        bit: bool,
    ) -> ControlFlow<U, BitSinkOnce<Self, U>>
    where
        U: UnsignedNumeric,
    {
        queue.value = if bit { U::MSB_BIT } else { U::ZERO } | (queue.value >> 1);
        queue.bits += 1;
        if queue.bits == queue.total_bits {
            ControlFlow::Break(queue.value >> (U::BITS_SIZE - queue.total_bits))
        } else {
            ControlFlow::Continue(queue)
        }
    }

    #[inline]
    fn push_bit_once_fixed<const B: u32, U>(
        mut queue: BitSinkOnceFixed<B, Self, U>,
        bit: bool,
    ) -> ControlFlow<U, BitSinkOnceFixed<B, Self, U>>
    where
        U: UnsignedNumeric,
    {
        queue.value = if bit { U::MSB_BIT } else { U::ZERO } | (queue.value >> 1);
        queue.bits += 1;
        if queue.bits == B {
            ControlFlow::Break(queue.value >> (U::BITS_SIZE - B))
        } else {
            ControlFlow::Continue(queue)
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

/// A source for bits to be read from and refilled when full
///
/// This is useful to attach to bitstream readers so that
/// the partial byte can be refilled from the input stream.
#[derive(Clone, Debug)]
pub struct BitSourceRefill<E: Endianness, U: UnsignedNumeric> {
    phantom: PhantomData<E>,
    // the current value in the source
    value: U,
    // the bits remaining in the source
    bits: u32,
}

impl<E: Endianness, U: UnsignedNumeric> Default for BitSourceRefill<E, U> {
    fn default() -> Self {
        Self {
            phantom: PhantomData,
            value: U::default(),
            bits: 0,
        }
    }
}

impl<E: Endianness, U: UnsignedNumeric> BitSourceRefill<E, U> {
    /// Returns true if source is empty.
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.bits == 0
    }

    /// Pops the next bit from the source,
    /// replenishing it from the given closure if necessary.
    #[inline(always)]
    pub fn pop_bit<F, G>(&mut self, read_val: F) -> Result<bool, G>
    where
        F: FnOnce() -> Result<U, G>,
    {
        E::pop_bit_refill(self, read_val)
    }

    /// Pops the next unary value from the source until
    /// `STOP_BIT` is encountered, replenishing it from the given
    /// closure if necessary.
    ///
    /// `STOP_BIT` must be 0 or 1.
    #[inline(always)]
    pub fn pop_unary<const STOP_BIT: u8, F, G>(&mut self, read_val: F) -> Result<u32, G>
    where
        F: FnMut() -> Result<U, G>,
    {
        E::pop_unary::<STOP_BIT, U, F, G>(self, read_val)
    }

    /// Empties queue of all values
    #[inline]
    pub fn clear(&mut self) {
        self.value = U::default();
        self.bits = 0;
    }

    /// Returns total bits in the sink
    pub fn len(&self) -> u32 {
        self.bits
    }

    fn find_unary<L, M, S, F, G>(
        &mut self,
        leading_bits: L,
        max_bits: M,
        checked_shift: S,
        mut read_val: F,
    ) -> Result<u32, G>
    where
        L: Fn(U) -> u32,
        M: Fn(&Self) -> u32,
        S: Fn(U, u32) -> Option<U>,
        F: FnMut() -> Result<U, G>,
    {
        let mut acc = 0;

        loop {
            match leading_bits(self.value) {
                bits if bits == max_bits(self) => {
                    // all bits exhausted
                    // fetch another byte and keep going
                    acc += self.bits;
                    self.value = read_val()?;
                    self.bits = U::BITS_SIZE;
                }
                bits => match checked_shift(self.value, bits + 1) {
                    Some(value) => {
                        // fetch part of source byte
                        self.value = value;
                        self.bits -= bits + 1;
                        break Ok(acc + bits);
                    }
                    None => {
                        // fetch all of source byte
                        self.value = U::default();
                        self.bits = 0;
                        break Ok(acc + bits);
                    }
                },
            }
        }
    }
}

/// A source for bits to be read from until depleted.
///
/// This is useful to for bitstream writers so that
/// partial bits can be pulled from an input value until empty.
pub struct BitSourceOnce<E: Endianness, U: UnsignedNumeric> {
    phantom: PhantomData<E>,
    // the current value in the source
    value: U,
    // the bits remaining in the source
    bits: u32,
}

impl<E: Endianness, U: UnsignedNumeric> BitSourceOnce<E, U> {
    /// Creates a new `BitSource` with the given bits and value.
    ///
    /// # Errors
    ///
    /// Returns an error if the bits are larger than the given
    /// type, or if the value would not fit into the given number of bits.
    #[inline(always)]
    pub fn new(bits: u32, value: U) -> io::Result<Self> {
        E::new_source(bits, value)
    }

    /// Creates a new `BitSource` with the given bits and value.
    ///
    /// # Errors
    ///
    /// Returns an error if the value would not fit into
    /// the given number of bits.
    /// A compile-time error occurs if the number of bits is
    /// larger than the value.
    #[inline(always)]
    pub fn new_fixed<const BITS: u32>(value: U) -> io::Result<Self> {
        E::new_source_fixed::<BITS, U>(value)
    }

    /// Returns true if source is empty.
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.bits == 0
    }

    /// Pops the next bit from the source, if available.
    #[inline(always)]
    pub fn pop_bit(&mut self) -> Option<bool> {
        E::pop_bit_once(self)
    }
}

/// A target for bits to be written into and flushed when full
///
/// This is useful to for bitstream writers so that
/// whole bytes can be flushed to the stream when full.
#[derive(Clone, Debug)]
pub struct BitSinkFlush<E: Endianness, U: UnsignedNumeric> {
    phantom: PhantomData<E>,
    value: U,
    bits: u32,
}

impl<E: Endianness, U: UnsignedNumeric> Default for BitSinkFlush<E, U> {
    fn default() -> Self {
        Self {
            phantom: PhantomData,
            value: U::default(),
            bits: 0,
        }
    }
}

impl<E: Endianness, U: UnsignedNumeric> BitSinkFlush<E, U> {
    /// Returns true if sink is empty.
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.bits == 0
    }

    /// Pushes the next bit into the sink,
    /// returning a whole value once the sink is full.
    #[inline(always)]
    pub fn push_bit(&mut self, bit: bool) -> Option<U> {
        E::push_bit_flush(self, bit)
    }
}

/// A target for bits to be written into and unpacked once full
///
/// This is useful for bitstream readers to build a whole value
/// from a series of stream bits.
#[derive(Clone, Debug)]
pub struct BitSinkOnce<E: Endianness, U: UnsignedNumeric> {
    phantom: PhantomData<E>,
    // our accumulated value
    value: U,
    // the number of bits pushed into the sink thus far
    bits: u32,
    // the total number of bits the sink can contain
    total_bits: u32,
}

impl<E: Endianness, U: UnsignedNumeric> BitSinkOnce<E, U> {
    /// Builds a new sink large enough for the given number of bits.
    ///
    /// # Errors
    ///
    /// Returns an error if bits is larger than the type can contain.
    pub fn new(bits: u32) -> io::Result<Self> {
        if bits <= U::BITS_SIZE {
            Ok(Self {
                phantom: PhantomData,
                value: U::default(),
                bits: 0,
                total_bits: bits,
            })
        } else {
            Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "excessive bits for type read",
            ))
        }
    }

    /// Pushes the next bit into the sink,
    /// returning a whole value once the sink is full.
    #[inline(always)]
    pub fn push_bit(self, bit: bool) -> ControlFlow<U, Self> {
        E::push_bit_once(self, bit)
    }
}

/// A target for bits to be written into and unpacked once full
///
/// This is useful for bitstream readers to build a whole value
/// from a series of stream bits.
#[derive(Clone, Debug)]
pub struct BitSinkOnceFixed<const B: u32, E: Endianness, U: UnsignedNumeric> {
    phantom: PhantomData<E>,
    // our accumulated value
    value: U,
    // the number of bits pushed into the sink thus far
    bits: u32,
}

impl<const B: u32, E: Endianness, U: UnsignedNumeric> BitSinkOnceFixed<B, E, U> {
    /// Builds a new sink large enough for the given number of bits.
    ///
    /// # Errors
    ///
    /// A compile-time error occurs if `B` is larger than the type
    /// can contain.
    pub fn new() -> Self {
        const {
            assert!(B <= U::BITS_SIZE, "excessive bits for type read");
        }

        Self {
            phantom: PhantomData,
            value: U::default(),
            bits: 0,
        }
    }

    /// Pushes the next bit into the sink,
    /// returning a whole value once the sink is full.
    #[inline(always)]
    pub fn push_bit(self, bit: bool) -> ControlFlow<U, Self> {
        E::push_bit_once_fixed(self, bit)
    }
}
