// Copyright 2017 Brian Langenberger
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Traits and implementations for reading bits from a stream.
//!
//! ## Example
//!
//! Reading the initial STREAMINFO block from a FLAC file,
//! as documented in its
//! [specification](https://xiph.org/flac/format.html#stream).
//!
//! ```
//! use std::io::{Cursor, Read};
//! use bitstream_io::{BitRead, BitReader, BigEndian, FromBitStream};
//!
//! #[derive(Debug, PartialEq, Eq)]
//! struct BlockHeader {
//!     last_block: bool,  // 1 bit
//!     block_type: u8,    // 7 bits
//!     block_size: u32,   // 24 bits
//! }
//!
//! impl FromBitStream for BlockHeader {
//!     type Error = std::io::Error;
//!
//!     fn from_reader<R: BitRead + ?Sized>(r: &mut R) -> std::io::Result<Self> {
//!         Ok(Self {
//!             last_block: r.read_bit()?,
//!             block_type: r.read::<7, _>()?,
//!             block_size: r.read::<24, _>()?,
//!         })
//!     }
//! }
//!
//! #[derive(Debug, PartialEq, Eq)]
//! struct Streaminfo {
//!     minimum_block_size: u16,  // 16 bits
//!     maximum_block_size: u16,  // 16 bits
//!     minimum_frame_size: u32,  // 24 bits
//!     maximum_frame_size: u32,  // 24 bits
//!     sample_rate: u32,         // 20 bits
//!     channels: u8,             // 3 bits
//!     bits_per_sample: u8,      // 5 bits
//!     total_samples: u64,       // 36 bits
//!     md5: [u8; 16],            // 16 bytes
//! }
//!
//! impl FromBitStream for Streaminfo {
//!     type Error = std::io::Error;
//!
//!     fn from_reader<R: BitRead + ?Sized>(r: &mut R) -> std::io::Result<Self> {
//!         Ok(Self {
//!             minimum_block_size: r.read_to()?,
//!             maximum_block_size: r.read_to()?,
//!             minimum_frame_size: r.read::<24, _>()?,
//!             maximum_frame_size: r.read::<24, _>()?,
//!             sample_rate:        r.read::<20, _>()?,
//!             channels:           r.read::<3, u8>()? + 1,
//!             bits_per_sample:    r.read::<5, u8>()? + 1,
//!             total_samples:      r.read::<36, _>()?,
//!             md5:                r.read_to()?,
//!         })
//!     }
//! }
//!
//! #[derive(Debug, PartialEq, Eq)]
//! struct VorbisComment {
//!     vendor: String,
//!     comment: Vec<String>,
//! }
//!
//! impl FromBitStream for VorbisComment {
//!    type Error = Box<dyn std::error::Error>;
//!
//!    fn from_reader<R: BitRead + ?Sized>(r: &mut R) -> Result<Self, Self::Error> {
//!        use bitstream_io::LE;
//!
//!        fn read_entry<R: BitRead + ?Sized>(
//!            r: &mut R,
//!        ) -> Result<String, Box<dyn std::error::Error>> {
//!            use std::convert::TryInto;
//!            let size = r.read_as_to::<LE, u32>()?.try_into()?;
//!            Ok(String::from_utf8(r.read_to_vec(size)?)?)
//!        }
//!
//!        Ok(Self {
//!            vendor: read_entry(r)?,
//!            comment: (0..r.read_as_to::<LE, u32>()?)
//!                .map(|_| read_entry(r))
//!                .collect::<Result<Vec<_>, _>>()?,
//!        })
//!    }
//! }
//!
//! // test FLAC file data
//! let flac: Vec<u8> = vec![0x66,0x4c,0x61,0x43,0x00,0x00,0x00,0x22,
//!                          0x10,0x00,0x10,0x00,0x00,0x06,0x06,0x00,
//!                          0x21,0x62,0x0a,0xc4,0x42,0xf0,0x00,0x04,
//!                          0xa6,0xcc,0xfa,0xf2,0x69,0x2f,0xfd,0xec,
//!                          0x2d,0x5b,0x30,0x01,0x76,0xb4,0x62,0x88,
//!                          0x7d,0x92,0x04,0x00,0x00,0x7a,0x20,0x00,
//!                          0x00,0x00,0x72,0x65,0x66,0x65,0x72,0x65,
//!                          0x6e,0x63,0x65,0x20,0x6c,0x69,0x62,0x46,
//!                          0x4c,0x41,0x43,0x20,0x31,0x2e,0x31,0x2e,
//!                          0x34,0x20,0x32,0x30,0x30,0x37,0x30,0x32,
//!                          0x31,0x33,0x04,0x00,0x00,0x00,0x16,0x00,
//!                          0x00,0x00,0x74,0x69,0x74,0x6c,0x65,0x3d,
//!                          0x32,0x63,0x68,0x20,0x34,0x34,0x31,0x30,
//!                          0x30,0x20,0x20,0x31,0x36,0x62,0x69,0x74,
//!                          0x10,0x00,0x00,0x00,0x61,0x6c,0x62,0x75,
//!                          0x6d,0x3d,0x54,0x65,0x73,0x74,0x20,0x41,
//!                          0x6c,0x62,0x75,0x6d,0x0f,0x00,0x00,0x00,
//!                          0x61,0x72,0x74,0x69,0x73,0x74,0x3d,0x41,
//!                          0x73,0x73,0x6f,0x72,0x74,0x65,0x64,0x0d,
//!                          0x00,0x00,0x00,0x74,0x72,0x61,0x63,0x6b,
//!                          0x6e,0x75,0x6d,0x62,0x65,0x72,0x3d,0x31];
//!
//! let mut cursor = Cursor::new(&flac);
//!
//! let mut reader = BitReader::endian(&mut cursor, BigEndian);
//!
//! // stream marker
//! assert_eq!(&reader.read_to::<[u8; 4]>().unwrap(), b"fLaC");
//!
//! // metadata block header
//! assert_eq!(
//!     reader.parse::<BlockHeader>().unwrap(),
//!     BlockHeader { last_block: false, block_type: 0, block_size: 34 }
//! );
//!
//! // STREAMINFO block
//! assert_eq!(
//!     reader.parse::<Streaminfo>().unwrap(),
//!     Streaminfo {
//!         minimum_block_size: 4096,
//!         maximum_block_size: 4096,
//!         minimum_frame_size: 1542,
//!         maximum_frame_size: 8546,
//!         sample_rate: 44100,
//!         channels: 2,
//!         bits_per_sample: 16,
//!         total_samples: 304844,
//!         md5: *b"\xFA\xF2\x69\x2F\xFD\xEC\x2D\x5B\x30\x01\x76\xB4\x62\x88\x7D\x92",
//!     }
//! );
//!
//! // metadata block header
//! assert_eq!(
//!     reader.parse::<BlockHeader>().unwrap(),
//!     BlockHeader { last_block: false, block_type: 4, block_size: 122 }
//! );
//!
//! // VORBIS_COMMENT block
//! assert_eq!(
//!    reader.parse::<VorbisComment>().unwrap(),
//!    VorbisComment {
//!        vendor: "reference libFLAC 1.1.4 20070213".to_string(),
//!        comment: vec![
//!            "title=2ch 44100  16bit".to_string(),
//!            "album=Test Album".to_string(),
//!            "artist=Assorted".to_string(),
//!            "tracknumber=1".to_string(),
//!        ],
//!    }
//! );

#![warn(missing_docs)]

#[cfg(not(feature = "std"))]
use core2::io;

use alloc::{vec, vec::Vec};
#[cfg(feature = "std")]
use std::io;

use super::{
    BitCount, BitSourceRefill, Endianness, Integer, PhantomData, Primitive, SignedNumeric,
    UnsignedNumeric,
};

/// A trait for anything that can read a variable number of
/// potentially un-aligned values from an input stream
pub trait BitRead {
    /// Reads a single bit from the stream.
    /// `true` indicates 1, `false` indicates 0
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    fn read_bit(&mut self) -> io::Result<bool> {
        self.read_unsigned::<1, u8>().map(|b| b == 1)
    }

    /// Reads a signed or unsigned value from the stream with
    /// the given constant number of bits.
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    /// A compile-time error occurs if the given number of bits
    /// is larger than the output type.
    #[inline]
    fn read<const BITS: u32, I>(&mut self) -> io::Result<I>
    where
        I: Integer,
    {
        I::read_in::<BITS, _>(self)
    }

    /// Reads a signed or unsigned value from the stream with
    /// the given variable number of bits.
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    /// Also returns an error if the output type is too small
    /// to hold the requested number of bits.
    #[inline]
    fn read_var<I>(&mut self, bits: u32) -> io::Result<I>
    where
        I: Integer + Sized,
    {
        I::read(self, BitCount::unknown(bits))
    }

    /// Given a desired maximum value for a bit count,
    /// reads the necessary bits to fill up to that amount.
    ///
    /// For example, if the maximum bit count is 15 - or `0b1111` -
    /// reads a 4-bit unsigned value from the stream and returns a `BitCount`
    /// which can be used in subsequent reads.
    ///
    /// Note that `MAX` must be greater than 0, and `MAX + 1` must be
    /// an exact power of two.
    ///
    /// # Errors
    ///
    /// Passes along an I/O error from the underlying stream.
    ///
    /// # Examples
    ///
    /// ```
    /// use bitstream_io::{BigEndian, BitReader, BitRead};
    ///
    /// let bytes: &[u8] = &[0b10011110];
    /// let mut r = BitReader::endian(bytes, BigEndian);
    /// let count = r.read::<3, u32>().unwrap();
    /// assert_eq!(count, 0b100);
    /// // need to verify count is not larger than u8 at runtime
    /// assert_eq!(r.read_var::<u8>(count).unwrap(), 0b1111);
    /// ```
    ///
    /// ```
    /// use bitstream_io::{BigEndian, BitReader, BitRead};
    ///
    /// let bytes: &[u8] = &[0b10011110];
    /// let mut r = BitReader::endian(bytes, BigEndian);
    /// let count = r.read_count::<0b111>().unwrap();
    /// // size of count is known at compile-time, so no runtime check needed
    /// assert_eq!(r.read_counted::<0b111, u8>(count).unwrap(), 0b1111);
    /// ```
    fn read_count<const MAX: u32>(&mut self) -> io::Result<BitCount<MAX>> {
        const {
            assert!(MAX > 0, "MAX value must be > 0");
        }

        const {
            assert!(
                MAX == u32::MAX || (MAX + 1).is_power_of_two(),
                "MAX should fill some whole number of bits ('0b111', '0b1111', etc.)"
            )
        }

        self.read_unsigned_var((MAX + 1).ilog2())
            .map(|bits| BitCount { bits })
    }

    /// Reads a signed or unsigned value from the stream with
    /// the given number of bits.
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    /// Also returns an error if the output type is too small
    /// to hold the requested number of bits.
    #[inline(always)]
    fn read_counted<const MAX: u32, I>(&mut self, bits: BitCount<MAX>) -> io::Result<I>
    where
        I: Integer + Sized,
    {
        I::read(self, bits)
    }

    /// Reads an unsigned value from the stream with
    /// the given number of bits.
    ///
    /// # Examples
    /// ```
    /// use std::io::{Read, Cursor};
    /// use bitstream_io::{BigEndian, BitReader, BitRead};
    /// let data = [0b10110111];
    /// let mut reader = BitReader::endian(Cursor::new(&data), BigEndian);
    /// assert_eq!(reader.read_unsigned::<1, u8>().unwrap(), 0b1);
    /// assert_eq!(reader.read_unsigned::<2, u8>().unwrap(), 0b01);
    /// assert_eq!(reader.read_unsigned::<5, u8>().unwrap(), 0b10111);
    /// ```
    ///
    /// ```
    /// use std::io::{Read, Cursor};
    /// use bitstream_io::{LittleEndian, BitReader, BitRead};
    /// let data = [0b10110111];
    /// let mut reader = BitReader::endian(Cursor::new(&data), LittleEndian);
    /// assert_eq!(reader.read_unsigned::<1, u8>().unwrap(), 0b1);
    /// assert_eq!(reader.read_unsigned::<2, u8>().unwrap(), 0b11);
    /// assert_eq!(reader.read_unsigned::<5, u8>().unwrap(), 0b10110);
    /// ```
    ///
    /// ```
    /// use std::io::{Read, Cursor};
    /// use bitstream_io::{BigEndian, BitReader, BitRead};
    /// let data = [0;10];
    /// let mut reader = BitReader::endian(Cursor::new(&data), BigEndian);
    /// assert!(reader.read_unsigned_var::<u8>(9).is_err());    // can't read  9 bits to u8
    /// assert!(reader.read_unsigned_var::<u16>(17).is_err());  // can't read 17 bits to u16
    /// assert!(reader.read_unsigned_var::<u32>(33).is_err());  // can't read 33 bits to u32
    /// assert!(reader.read_unsigned_var::<u64>(65).is_err());  // can't read 65 bits to u64
    /// ```
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    /// Also returns an error if the output type is too small
    /// to hold the requested number of bits.
    #[inline(always)]
    fn read_unsigned_var<U>(&mut self, bits: u32) -> io::Result<U>
    where
        U: UnsignedNumeric,
    {
        self.read_unsigned_counted(BitCount::unknown(bits))
    }

    /// Reads an unsigned value from the stream with
    /// the given constant number of bits.
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    /// A compile-time error occurs if the given number of bits
    /// is larger than the output type.
    fn read_unsigned<const BITS: u32, U>(&mut self) -> io::Result<U>
    where
        U: UnsignedNumeric,
    {
        self.read_unsigned_var(BITS)
    }

    /// Reads an unsigned value from the stream with
    /// the given number of bits.
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    /// Also returns an error if the output type is too small
    /// to hold the requested number of bits.
    fn read_unsigned_counted<const MAX: u32, U>(&mut self, bits: BitCount<MAX>) -> io::Result<U>
    where
        U: UnsignedNumeric;

    /// Reads a twos-complement signed value from the stream with
    /// the given constant number of bits.
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    /// A compile-time error occurs if the number of bits is 0,
    /// since one bit is always needed for the sign.
    /// A compile-time error occurs if the given number of bits
    /// is larger than the output type.
    fn read_signed<const BITS: u32, S>(&mut self) -> io::Result<S>
    where
        S: SignedNumeric,
    {
        self.read_signed_var(BITS)
    }

    /// Reads a twos-complement signed value from the stream with
    /// the given number of bits.
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    /// Returns an error if the number of bits is 0,
    /// since one bit is always needed for the sign.
    /// Also returns an error if the output type is too small
    /// to hold the requested number of bits.
    ///
    /// # Examples
    /// ```
    /// use std::io::{Read, Cursor};
    /// use bitstream_io::{BigEndian, BitReader, BitRead};
    /// let data = [0b10110111];
    /// let mut reader = BitReader::endian(Cursor::new(&data), BigEndian);
    /// assert_eq!(reader.read_signed::<4, i8>().unwrap(), -5);
    /// assert_eq!(reader.read_signed::<4, i8>().unwrap(), 7);
    /// ```
    ///
    /// ```
    /// use std::io::{Read, Cursor};
    /// use bitstream_io::{LittleEndian, BitReader, BitRead};
    /// let data = [0b10110111];
    /// let mut reader = BitReader::endian(Cursor::new(&data), LittleEndian);
    /// assert_eq!(reader.read_signed::<4, i8>().unwrap(), 7);
    /// assert_eq!(reader.read_signed::<4, i8>().unwrap(), -5);
    /// ```
    ///
    /// ```
    /// use std::io::{Read, Cursor};
    /// use bitstream_io::{BigEndian, BitReader, BitRead};
    /// let data = [0;10];
    /// let mut r = BitReader::endian(Cursor::new(&data), BigEndian);
    /// assert!(r.read_signed_var::<i8>(9).is_err());   // can't read 9 bits to i8
    /// assert!(r.read_signed_var::<i16>(17).is_err()); // can't read 17 bits to i16
    /// assert!(r.read_signed_var::<i32>(33).is_err()); // can't read 33 bits to i32
    /// assert!(r.read_signed_var::<i64>(65).is_err()); // can't read 65 bits to i64
    /// ```
    fn read_signed_var<S>(&mut self, bits: u32) -> io::Result<S>
    where
        S: SignedNumeric,
    {
        self.read_signed_counted(BitCount::unknown(bits))
    }

    /// Reads a twos-complement signed value from the stream with
    /// the given number of bits.
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    /// Returns an error if the number of bits is 0,
    /// since one bit is always needed for the sign.
    /// Also returns an error if the output type is too small
    /// to hold the requested number of bits.
    fn read_signed_counted<const MAX: u32, S>(&mut self, bits: BitCount<MAX>) -> io::Result<S>
    where
        S: SignedNumeric;

    /// Reads whole value from the stream whose size in bits is equal
    /// to its type's size.
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    fn read_to<V>(&mut self) -> io::Result<V>
    where
        V: Primitive;

    /// Reads whole value from the stream whose size in bits is equal
    /// to its type's size in an endianness that may be different
    /// from the stream's endianness.
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    fn read_as_to<F, V>(&mut self) -> io::Result<V>
    where
        F: Endianness,
        V: Primitive;

    /// Skips the given number of bits in the stream.
    /// Since this method does not need an accumulator,
    /// it may be slightly faster than reading to an empty variable.
    /// In addition, since there is no accumulator,
    /// there is no upper limit on the number of bits
    /// which may be skipped.
    /// These bits are still read from the stream, however,
    /// and are never skipped via a `seek` method.
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    fn skip(&mut self, bits: u32) -> io::Result<()> {
        (0..bits).try_for_each(|_| self.read_bit().map(|_| ()))
    }

    /// Completely fills the given buffer with whole bytes.
    /// If the stream is already byte-aligned, it will map
    /// to a faster `read_exact` call.  Otherwise it will read
    /// bytes individually in 8-bit increments.
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    fn read_bytes(&mut self, buf: &mut [u8]) -> io::Result<()> {
        for b in buf.iter_mut() {
            *b = self.read_unsigned::<8, _>()?;
        }
        Ok(())
    }

    /// Completely fills a whole buffer with bytes and returns it.
    /// If the stream is already byte-aligned, it will map
    /// to a faster `read_exact` call.  Otherwise it will read
    /// bytes individually in 8-bit increments.
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    #[inline(always)]
    #[deprecated(since = "1.8.0", note = "use read_to() method instead")]
    fn read_to_bytes<const SIZE: usize>(&mut self) -> io::Result<[u8; SIZE]> {
        self.read_to()
    }

    /// Completely fills a vector of bytes and returns it.
    /// If the stream is already byte-aligned, it will map
    /// to a faster `read_exact` call.  Otherwise it will read
    /// bytes individually in 8-bit increments.
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    fn read_to_vec(&mut self, bytes: usize) -> io::Result<Vec<u8>> {
        read_to_vec(|buf| self.read_bytes(buf), bytes)
    }

    /// Counts the number of bits in the stream until `STOP_BIT`
    /// and returns the amount read.
    /// `STOP_BIT` must be 0 or 1.
    /// Because this field is variably-sized and may be large,
    /// its output is always a `u32` type.
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    /// May panic if the number of bits exceeds `u32`.
    fn read_unary<const STOP_BIT: u8>(&mut self) -> io::Result<u32> {
        const {
            assert!(matches!(STOP_BIT, 0 | 1), "stop bit must be 0 or 1");
        }

        // a simple implementation which works anywhere
        let mut unary = 0;
        while self.read::<1, u8>()? != STOP_BIT {
            unary += 1;
        }
        Ok(unary)
    }

    /// Parses and returns complex type
    fn parse<F: FromBitStream>(&mut self) -> Result<F, F::Error> {
        F::from_reader(self)
    }

    /// Parses and returns complex type with context
    fn parse_with<'a, F: FromBitStreamWith<'a>>(
        &mut self,
        context: &F::Context,
    ) -> Result<F, F::Error> {
        F::from_reader(self, context)
    }

    /// Returns true if the stream is aligned at a whole byte.
    fn byte_aligned(&self) -> bool;

    /// Throws away all unread bit values until the next whole byte.
    /// Does nothing if the stream is already aligned.
    fn byte_align(&mut self);

    /// Given a compiled Huffman tree, reads bits from the stream
    /// until the next symbol is encountered.
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    #[inline]
    fn read_huffman<T>(&mut self) -> io::Result<T::Output>
    where
        T: crate::huffman::FromBits,
    {
        T::from_bits(|| self.read_bit())
    }
}

/// A trait for anything that can read a variable number of
/// potentially un-aligned values from an input stream.
///
/// This is a trait largely compatible with older code
/// from the 2.X.X version and earlier,
/// which one can use with a named import as needed.
///
/// New code should prefer the regular `BitRead` trait.
///
/// # Example
/// ```
/// use bitstream_io::BitRead2 as BitRead;
/// ```
pub trait BitRead2 {
    /// Reads a single bit from the stream.
    /// `true` indicates 1, `false` indicates 0
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    fn read_bit(&mut self) -> io::Result<bool>;

    /// Reads an unsigned value from the stream with
    /// the given number of bits.
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    /// Also returns an error if the output type is too small
    /// to hold the requested number of bits.
    fn read<I>(&mut self, bits: u32) -> io::Result<I>
    where
        I: Integer + Sized;

    /// Reads an unsigned value from the stream with
    /// the given constant number of bits.
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    /// A compile-time error occurs if the given number of bits
    /// is larger than the output type.
    fn read_in<const BITS: u32, I>(&mut self) -> io::Result<I>
    where
        I: Integer,
    {
        self.read(BITS)
    }

    /// Reads a twos-complement signed value from the stream with
    /// the given number of bits.
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    /// Returns an error if the number of bits is 0,
    /// since one bit is always needed for the sign.
    /// Also returns an error if the output type is too small
    /// to hold the requested number of bits.
    fn read_signed<S>(&mut self, bits: u32) -> io::Result<S>
    where
        S: SignedNumeric;

    /// Reads a twos-complement signed value from the stream with
    /// the given constant number of bits.
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    /// A compile-time error occurs if the number of bits is 0,
    /// since one bit is always needed for the sign.
    /// A compile-time error occurs if the given number of bits
    /// is larger than the output type.
    fn read_signed_in<const BITS: u32, S>(&mut self) -> io::Result<S>
    where
        S: SignedNumeric,
    {
        self.read_signed(BITS)
    }

    /// Reads whole value from the stream whose size in bits is equal
    /// to its type's size.
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    fn read_to<V>(&mut self) -> io::Result<V>
    where
        V: Primitive;

    /// Reads whole value from the stream whose size in bits is equal
    /// to its type's size in an endianness that may be different
    /// from the stream's endianness.
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    fn read_as_to<F, V>(&mut self) -> io::Result<V>
    where
        F: Endianness,
        V: Primitive;

    /// Skips the given number of bits in the stream.
    /// Since this method does not need an accumulator,
    /// it may be slightly faster than reading to an empty variable.
    /// In addition, since there is no accumulator,
    /// there is no upper limit on the number of bits
    /// which may be skipped.
    /// These bits are still read from the stream, however,
    /// and are never skipped via a `seek` method.
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    fn skip(&mut self, bits: u32) -> io::Result<()>;

    /// Completely fills the given buffer with whole bytes.
    /// If the stream is already byte-aligned, it will map
    /// to a faster `read_exact` call.  Otherwise it will read
    /// bytes individually in 8-bit increments.
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    fn read_bytes(&mut self, buf: &mut [u8]) -> io::Result<()> {
        for b in buf.iter_mut() {
            *b = self.read_in::<8, _>()?;
        }
        Ok(())
    }

    /// Completely fills a whole buffer with bytes and returns it.
    /// If the stream is already byte-aligned, it will map
    /// to a faster `read_exact` call.  Otherwise it will read
    /// bytes individually in 8-bit increments.
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    #[inline(always)]
    #[deprecated(since = "1.8.0", note = "use read_to() method instead")]
    fn read_to_bytes<const SIZE: usize>(&mut self) -> io::Result<[u8; SIZE]> {
        self.read_to()
    }

    /// Completely fills a vector of bytes and returns it.
    /// If the stream is already byte-aligned, it will map
    /// to a faster `read_exact` call.  Otherwise it will read
    /// bytes individually in 8-bit increments.
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    fn read_to_vec(&mut self, bytes: usize) -> io::Result<Vec<u8>> {
        read_to_vec(|buf| self.read_bytes(buf), bytes)
    }

    /// Counts the number of 1 bits in the stream until the next
    /// 0 bit and returns the amount read.
    /// Because this field is variably-sized and may be large,
    /// its output is always a `u32` type.
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    fn read_unary0(&mut self) -> io::Result<u32> {
        let mut unary = 0;
        while self.read_bit()? {
            unary += 1;
        }
        Ok(unary)
    }

    /// Counts the number of 0 bits in the stream until the next
    /// 1 bit and returns the amount read.
    /// Because this field is variably-sized and may be large,
    /// its output is always a `u32` type.
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    fn read_unary1(&mut self) -> io::Result<u32> {
        let mut unary = 0;
        while !(self.read_bit()?) {
            unary += 1;
        }
        Ok(unary)
    }

    /// Parses and returns complex type
    fn parse<F: FromBitStream>(&mut self) -> Result<F, F::Error>
    where
        Self: BitRead,
    {
        F::from_reader(self)
    }

    /// Parses and returns complex type with context
    fn parse_with<'a, F: FromBitStreamWith<'a>>(
        &mut self,
        context: &F::Context,
    ) -> Result<F, F::Error>
    where
        Self: BitRead,
    {
        F::from_reader(self, context)
    }

    /// Returns true if the stream is aligned at a whole byte.
    fn byte_aligned(&self) -> bool;

    /// Throws away all unread bit values until the next whole byte.
    /// Does nothing if the stream is already aligned.
    fn byte_align(&mut self);
}

impl<R: BitRead> BitRead2 for R {
    #[inline(always)]
    fn read_bit(&mut self) -> io::Result<bool> {
        BitRead::read_bit(self)
    }

    #[inline(always)]
    fn read<I>(&mut self, bits: u32) -> io::Result<I>
    where
        I: Integer + Sized,
    {
        self.read_var(bits)
    }

    #[inline(always)]
    fn read_in<const BITS: u32, I>(&mut self) -> io::Result<I>
    where
        I: Integer,
    {
        BitRead::read::<BITS, I>(self)
    }

    #[inline(always)]
    fn read_signed<S>(&mut self, bits: u32) -> io::Result<S>
    where
        S: SignedNumeric,
    {
        self.read_signed_var(bits)
    }

    #[inline(always)]
    fn read_signed_in<const BITS: u32, S>(&mut self) -> io::Result<S>
    where
        S: SignedNumeric,
    {
        BitRead::read_signed::<BITS, S>(self)
    }

    #[inline(always)]
    fn read_to<V>(&mut self) -> io::Result<V>
    where
        V: Primitive,
    {
        BitRead::read_to::<V>(self)
    }

    #[inline(always)]
    fn read_as_to<F, V>(&mut self) -> io::Result<V>
    where
        F: Endianness,
        V: Primitive,
    {
        BitRead::read_as_to::<F, V>(self)
    }

    #[inline(always)]
    fn skip(&mut self, bits: u32) -> io::Result<()> {
        BitRead::skip(self, bits)
    }

    #[inline(always)]
    fn read_bytes(&mut self, buf: &mut [u8]) -> io::Result<()> {
        BitRead::read_bytes(self, buf)
    }

    #[inline(always)]
    fn read_unary0(&mut self) -> io::Result<u32> {
        self.read_unary::<0>()
    }

    #[inline(always)]
    fn read_unary1(&mut self) -> io::Result<u32> {
        self.read_unary::<1>()
    }

    #[inline(always)]
    fn byte_aligned(&self) -> bool {
        BitRead::byte_aligned(self)
    }

    #[inline(always)]
    fn byte_align(&mut self) {
        BitRead::byte_align(self)
    }
}

/// For reading non-aligned bits from a stream of bytes in a given endianness.
///
/// This will read exactly as many whole bytes needed to return
/// the requested number of bits.  It may cache up to a single partial byte
/// but no more.
#[derive(Clone, Debug)]
pub struct BitReader<R, E: Endianness> {
    reader: R,
    bitqueue: BitSourceRefill<E, u8>,
}

impl<R, E: Endianness> BitReader<R, E> {
    /// Wraps a BitReader around something that implements `Read`
    pub fn new(reader: R) -> BitReader<R, E> {
        BitReader {
            reader,
            bitqueue: BitSourceRefill::default(),
        }
    }

    /// Wraps a BitReader around something that implements `Read`
    /// with the given endianness.
    pub fn endian(reader: R, _endian: E) -> BitReader<R, E> {
        BitReader {
            reader,
            bitqueue: BitSourceRefill::default(),
        }
    }

    /// Unwraps internal reader and disposes of BitReader.
    ///
    /// # Warning
    ///
    /// Any unread partial bits are discarded.
    #[inline]
    pub fn into_reader(self) -> R {
        self.reader
    }
}

impl<R: io::Read, E: Endianness> BitReader<R, E> {
    /// If stream is byte-aligned, provides mutable reference
    /// to internal reader.  Otherwise returns `None`
    #[inline]
    pub fn reader(&mut self) -> Option<&mut R> {
        if BitRead::byte_aligned(self) {
            Some(&mut self.reader)
        } else {
            None
        }
    }

    /// Converts `BitReader` to `ByteReader` in the same endianness.
    ///
    /// # Warning
    ///
    /// Any unread partial bits are discarded.
    #[inline]
    pub fn into_bytereader(self) -> ByteReader<R, E> {
        ByteReader::new(self.into_reader())
    }

    /// If stream is byte-aligned, provides temporary `ByteReader`
    /// in the same endianness.  Otherwise returns `None`
    ///
    /// # Warning
    ///
    /// Any reader bits left over when `ByteReader` is dropped are lost.
    #[inline]
    pub fn bytereader(&mut self) -> Option<ByteReader<&mut R, E>> {
        self.reader().map(ByteReader::new)
    }
}

impl<R: io::Read, E: Endianness> BitRead for BitReader<R, E> {
    /// # Examples
    ///
    /// ```
    /// use std::io::{Read, Cursor};
    /// use bitstream_io::{BigEndian, BitReader, BitRead};
    /// let data = [0b10110111];
    /// let mut reader = BitReader::endian(Cursor::new(&data), BigEndian);
    /// assert_eq!(reader.read_bit().unwrap(), true);
    /// assert_eq!(reader.read_bit().unwrap(), false);
    /// assert_eq!(reader.read_bit().unwrap(), true);
    /// assert_eq!(reader.read_bit().unwrap(), true);
    /// assert_eq!(reader.read_bit().unwrap(), false);
    /// assert_eq!(reader.read_bit().unwrap(), true);
    /// assert_eq!(reader.read_bit().unwrap(), true);
    /// assert_eq!(reader.read_bit().unwrap(), true);
    /// ```
    ///
    /// ```
    /// use std::io::{Read, Cursor};
    /// use bitstream_io::{LittleEndian, BitReader, BitRead};
    /// let data = [0b10110111];
    /// let mut reader = BitReader::endian(Cursor::new(&data), LittleEndian);
    /// assert_eq!(reader.read_bit().unwrap(), true);
    /// assert_eq!(reader.read_bit().unwrap(), true);
    /// assert_eq!(reader.read_bit().unwrap(), true);
    /// assert_eq!(reader.read_bit().unwrap(), false);
    /// assert_eq!(reader.read_bit().unwrap(), true);
    /// assert_eq!(reader.read_bit().unwrap(), true);
    /// assert_eq!(reader.read_bit().unwrap(), false);
    /// assert_eq!(reader.read_bit().unwrap(), true);
    /// ```
    #[inline(always)]
    fn read_bit(&mut self) -> io::Result<bool> {
        let Self { bitqueue, reader } = self;
        bitqueue.pop_bit(|| read_byte(reader))
    }

    #[inline(always)]
    fn read_unsigned_counted<const BITS: u32, U>(&mut self, bits: BitCount<BITS>) -> io::Result<U>
    where
        U: UnsignedNumeric,
    {
        let Self { bitqueue, reader } = self;
        E::read_bits(bitqueue, bits, || read_byte(reader.by_ref()))
    }

    /// # Examples
    /// ```
    /// use std::io::{Read, Cursor};
    /// use bitstream_io::{BigEndian, BitReader, BitRead};
    /// let data = [0b10110111];
    /// let mut reader = BitReader::endian(Cursor::new(&data), BigEndian);
    /// assert_eq!(reader.read_unsigned::<1, u8>().unwrap(), 0b1);
    /// assert_eq!(reader.read_unsigned::<2, u8>().unwrap(), 0b01);
    /// assert_eq!(reader.read_unsigned::<5, u8>().unwrap(), 0b10111);
    /// ```
    ///
    /// ```
    /// use std::io::{Read, Cursor};
    /// use bitstream_io::{LittleEndian, BitReader, BitRead};
    /// let data = [0b10110111];
    /// let mut reader = BitReader::endian(Cursor::new(&data), LittleEndian);
    /// assert_eq!(reader.read_unsigned::<1, u8>().unwrap(), 0b1);
    /// assert_eq!(reader.read_unsigned::<2, u8>().unwrap(), 0b11);
    /// assert_eq!(reader.read_unsigned::<5, u8>().unwrap(), 0b10110);
    /// ```
    #[inline]
    fn read_unsigned<const BITS: u32, U>(&mut self) -> io::Result<U>
    where
        U: UnsignedNumeric,
    {
        let Self { bitqueue, reader } = self;
        E::read_bits_fixed::<BITS, U, _, _>(bitqueue, || read_byte(reader.by_ref()))
    }

    #[inline(always)]
    fn read_signed_counted<const BITS: u32, S>(&mut self, bits: BitCount<BITS>) -> io::Result<S>
    where
        S: SignedNumeric,
    {
        E::read_signed(self, bits)
    }

    /// # Examples
    /// ```
    /// use std::io::{Read, Cursor};
    /// use bitstream_io::{BigEndian, BitReader, BitRead};
    /// let data = [0b10110111];
    /// let mut reader = BitReader::endian(Cursor::new(&data), BigEndian);
    /// assert_eq!(reader.read_signed::<4, i8>().unwrap(), -5);
    /// assert_eq!(reader.read_signed::<4, i8>().unwrap(), 7);
    /// ```
    ///
    /// ```
    /// use std::io::{Read, Cursor};
    /// use bitstream_io::{LittleEndian, BitReader, BitRead};
    /// let data = [0b10110111];
    /// let mut reader = BitReader::endian(Cursor::new(&data), LittleEndian);
    /// assert_eq!(reader.read_signed::<4, i8>().unwrap(), 7);
    /// assert_eq!(reader.read_signed::<4, i8>().unwrap(), -5);
    /// ```
    #[inline]
    fn read_signed<const BITS: u32, S>(&mut self) -> io::Result<S>
    where
        S: SignedNumeric,
    {
        const {
            assert!(BITS > 0, "signed reads need at least 1 bit for sign");
            assert!(BITS <= S::BITS_SIZE, "excessive bits for type read");
        }
        E::read_signed_fixed::<_, BITS, S>(self)
    }

    #[inline]
    fn read_to<V>(&mut self) -> io::Result<V>
    where
        V: Primitive,
    {
        E::read_primitive(self)
    }

    #[inline]
    fn read_as_to<F, V>(&mut self) -> io::Result<V>
    where
        F: Endianness,
        V: Primitive,
    {
        F::read_primitive(self)
    }

    /// # Examples
    /// ```
    /// use std::io::{Read, Cursor};
    /// use bitstream_io::{BigEndian, BitReader, BitRead};
    /// let data = [0b10110111];
    /// let mut reader = BitReader::endian(Cursor::new(&data), BigEndian);
    /// assert!(reader.skip(3).is_ok());
    /// assert_eq!(reader.read::<5, u8>().unwrap(), 0b10111);
    /// ```
    ///
    /// ```
    /// use std::io::{Read, Cursor};
    /// use bitstream_io::{LittleEndian, BitReader, BitRead};
    /// let data = [0b10110111];
    /// let mut reader = BitReader::endian(Cursor::new(&data), LittleEndian);
    /// assert!(reader.skip(3).is_ok());
    /// assert_eq!(reader.read::<5, u8>().unwrap(), 0b10110);
    /// ```
    fn skip(&mut self, bits: u32) -> io::Result<()> {
        if BitRead::byte_aligned(self) && bits % 8 == 0 {
            skip_aligned(self.reader.by_ref(), bits / 8)
        } else {
            (0..bits).try_for_each(|_| BitRead::read_bit(self).map(|_| ()))
        }
    }

    /// # Example
    /// ```
    /// use std::io::{Read, Cursor};
    /// use bitstream_io::{BigEndian, BitReader, BitRead};
    /// let data = b"foobar";
    /// let mut reader = BitReader::endian(Cursor::new(data), BigEndian);
    /// assert!(reader.skip(24).is_ok());
    /// let mut buf = [0;3];
    /// assert!(reader.read_bytes(&mut buf).is_ok());
    /// assert_eq!(&buf, b"bar");
    /// ```
    fn read_bytes(&mut self, buf: &mut [u8]) -> io::Result<()> {
        if BitRead::byte_aligned(self) {
            self.reader.read_exact(buf)
        } else {
            for b in buf.iter_mut() {
                *b = self.read_unsigned::<8, _>()?;
            }
            Ok(())
        }
    }

    fn read_unary<const STOP_BIT: u8>(&mut self) -> io::Result<u32> {
        let Self {
            bitqueue,
            ref mut reader,
        } = self;
        bitqueue.pop_unary::<STOP_BIT, _, _>(|| read_byte(reader.by_ref()))
    }

    /// # Example
    /// ```
    /// use std::io::{Read, Cursor};
    /// use bitstream_io::{BigEndian, BitReader, BitRead};
    /// let data = [0];
    /// let mut reader = BitReader::endian(Cursor::new(&data), BigEndian);
    /// assert_eq!(reader.byte_aligned(), true);
    /// assert!(reader.skip(1).is_ok());
    /// assert_eq!(reader.byte_aligned(), false);
    /// assert!(reader.skip(7).is_ok());
    /// assert_eq!(reader.byte_aligned(), true);
    /// ```
    #[inline]
    fn byte_aligned(&self) -> bool {
        self.bitqueue.is_empty()
    }

    /// # Example
    /// ```
    /// use std::io::{Read, Cursor};
    /// use bitstream_io::{BigEndian, BitReader, BitRead};
    /// let data = [0x00, 0xFF];
    /// let mut reader = BitReader::endian(Cursor::new(&data), BigEndian);
    /// assert_eq!(reader.read::<4, u8>().unwrap(), 0);
    /// reader.byte_align();
    /// assert_eq!(reader.read::<8, u8>().unwrap(), 0xFF);
    /// ```
    #[inline]
    fn byte_align(&mut self) {
        self.bitqueue.clear()
    }
}

impl<R, E> BitReader<R, E>
where
    E: Endianness,
    R: io::Read + io::Seek,
{
    /// # Example
    /// ```
    /// use std::io::{Read, Cursor, SeekFrom};
    /// use bitstream_io::{BigEndian, BitReader, BitRead};
    /// let data = [0x00, 0xFF];
    /// let mut reader = BitReader::endian(Cursor::new(&data), BigEndian);
    /// assert_eq!(reader.position_in_bits().unwrap(), 0);
    ///
    /// let pos = reader.seek_bits(SeekFrom::Start(5)).unwrap();
    /// assert!(pos == 5 && 5 == reader.position_in_bits().unwrap());
    ///
    /// let pos = reader.seek_bits(SeekFrom::Current(-2)).unwrap();
    /// assert!(pos == 3 && 3 == reader.position_in_bits().unwrap());    ///
    ///
    /// let pos = reader.seek_bits(SeekFrom::End(5)).unwrap();
    /// assert!(pos == 11 && 11 == reader.position_in_bits().unwrap());
    /// ```
    pub fn seek_bits(&mut self, from: io::SeekFrom) -> io::Result<u64> {
        match from {
            io::SeekFrom::Start(from_start_pos) => {
                let (bytes, bits) = (from_start_pos / 8, (from_start_pos % 8) as u32);
                BitRead::byte_align(self);
                self.reader.seek(io::SeekFrom::Start(bytes))?;
                BitRead::skip(self, bits)?;
                Ok(from_start_pos)
            }
            io::SeekFrom::End(from_end_pos) => {
                let reader_end = self.reader.seek(io::SeekFrom::End(0))?;
                let new_pos = (reader_end * 8) as i64 - from_end_pos;
                assert!(new_pos >= 0, "The final position should be greater than 0");
                self.seek_bits(io::SeekFrom::Start(new_pos as u64))
            }
            io::SeekFrom::Current(offset) => {
                let new_pos = self.position_in_bits()? as i64 + offset;
                assert!(new_pos >= 0, "The final position should be greater than 0");
                self.seek_bits(io::SeekFrom::Start(new_pos as u64))
            }
        }
    }

    /// # Example
    /// ```
    /// use std::fs::read;
    /// use std::io::{Read, Cursor, SeekFrom};
    /// use bitstream_io::{BigEndian, BitReader, BitRead};
    /// let data = [0x00, 0xFF];
    /// let mut reader = BitReader::endian(Cursor::new(&data), BigEndian);
    /// assert_eq!(reader.position_in_bits().unwrap(), 0);
    ///
    /// let _: i32 = reader.read_signed::<5, _>().unwrap();
    /// assert_eq!(reader.position_in_bits().unwrap(), 5);
    ///
    /// reader.read_bit().unwrap();
    /// assert_eq!(reader.position_in_bits().unwrap(), 6);
    /// ```
    #[inline]
    pub fn position_in_bits(&mut self) -> io::Result<u64> {
        let bytes = self.reader.stream_position()?;
        Ok(bytes * 8 - (self.bitqueue.len() as u64))
    }
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

fn skip_aligned<R>(reader: R, bytes: u32) -> io::Result<()>
where
    R: io::Read,
{
    fn skip_chunks<const SIZE: usize, R>(mut reader: R, mut bytes: usize) -> io::Result<()>
    where
        R: io::Read,
    {
        let mut buf = [0; SIZE];
        while bytes > 0 {
            let to_read = bytes.min(SIZE);
            reader.read_exact(&mut buf[0..to_read])?;
            bytes -= to_read;
        }
        Ok(())
    }

    match bytes {
        0..256 => skip_chunks::<8, R>(reader, bytes as usize),
        256..1024 => skip_chunks::<256, R>(reader, bytes as usize),
        1024..4096 => skip_chunks::<1024, R>(reader, bytes as usize),
        _ => skip_chunks::<4096, R>(reader, bytes as usize),
    }
}

/// A trait for anything that can read aligned values from an input stream
pub trait ByteRead {
    /// Reads whole numeric value from stream
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    ///
    /// # Examples
    /// ```
    /// use std::io::{Read, Cursor};
    /// use bitstream_io::{BigEndian, ByteReader, ByteRead};
    /// let data = [0b00000000, 0b11111111];
    /// let mut reader = ByteReader::endian(Cursor::new(&data), BigEndian);
    /// assert_eq!(reader.read::<u16>().unwrap(), 0b0000000011111111);
    /// ```
    ///
    /// ```
    /// use std::io::{Read, Cursor};
    /// use bitstream_io::{LittleEndian, ByteReader, ByteRead};
    /// let data = [0b00000000, 0b11111111];
    /// let mut reader = ByteReader::endian(Cursor::new(&data), LittleEndian);
    /// assert_eq!(reader.read::<u16>().unwrap(), 0b1111111100000000);
    /// ```
    fn read<V>(&mut self) -> Result<V, io::Error>
    where
        V: Primitive;

    /// Reads whole numeric value from stream in a potentially different endianness
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    ///
    /// # Examples
    /// ```
    /// use std::io::{Read, Cursor};
    /// use bitstream_io::{BigEndian, ByteReader, ByteRead, LittleEndian};
    /// let data = [0b00000000, 0b11111111];
    /// let mut reader = ByteReader::endian(Cursor::new(&data), BigEndian);
    /// assert_eq!(reader.read_as::<LittleEndian, u16>().unwrap(), 0b1111111100000000);
    /// ```
    ///
    /// ```
    /// use std::io::{Read, Cursor};
    /// use bitstream_io::{BigEndian, ByteReader, ByteRead, LittleEndian};
    /// let data = [0b00000000, 0b11111111];
    /// let mut reader = ByteReader::endian(Cursor::new(&data), LittleEndian);
    /// assert_eq!(reader.read_as::<BigEndian, u16>().unwrap(), 0b0000000011111111);
    /// ```
    fn read_as<F, V>(&mut self) -> Result<V, io::Error>
    where
        F: Endianness,
        V: Primitive;

    /// Completely fills the given buffer with whole bytes.
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    fn read_bytes(&mut self, buf: &mut [u8]) -> io::Result<()> {
        for b in buf.iter_mut() {
            *b = self.read()?;
        }
        Ok(())
    }

    /// Completely fills a whole buffer with bytes and returns it.
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    #[inline(always)]
    #[deprecated(since = "1.8.0", note = "use read() method instead")]
    fn read_to_bytes<const SIZE: usize>(&mut self) -> io::Result<[u8; SIZE]> {
        self.read()
    }

    /// Completely fills a vector of bytes and returns it.
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    fn read_to_vec(&mut self, bytes: usize) -> io::Result<Vec<u8>> {
        read_to_vec(|buf| self.read_bytes(buf), bytes)
    }

    /// Skips the given number of bytes in the stream.
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    fn skip(&mut self, bytes: u32) -> io::Result<()>;

    /// Parses and returns complex type
    fn parse<F: FromByteStream>(&mut self) -> Result<F, F::Error> {
        F::from_reader(self)
    }

    /// Parses and returns complex type with context
    fn parse_with<'a, F: FromByteStreamWith<'a>>(
        &mut self,
        context: &F::Context,
    ) -> Result<F, F::Error> {
        F::from_reader(self, context)
    }

    /// Returns mutable reference to underlying reader
    fn reader_ref(&mut self) -> &mut dyn io::Read;
}

/// For reading aligned bytes from a stream of bytes in a given endianness.
///
/// This only reads aligned values and maintains no internal state.
#[derive(Debug)]
pub struct ByteReader<R: io::Read, E: Endianness> {
    phantom: PhantomData<E>,
    reader: R,
}

impl<R: io::Read, E: Endianness> ByteReader<R, E> {
    /// Wraps a ByteReader around something that implements `Read`
    pub fn new(reader: R) -> ByteReader<R, E> {
        ByteReader {
            phantom: PhantomData,
            reader,
        }
    }

    /// Wraps a ByteReader around something that implements `Read`
    /// with the given endianness.
    pub fn endian(reader: R, _endian: E) -> ByteReader<R, E> {
        ByteReader {
            phantom: PhantomData,
            reader,
        }
    }

    /// Unwraps internal reader and disposes of `ByteReader`.
    #[inline]
    pub fn into_reader(self) -> R {
        self.reader
    }

    /// Provides mutable reference to internal reader
    #[inline]
    pub fn reader(&mut self) -> &mut R {
        &mut self.reader
    }

    /// Converts `ByteReader` to `BitReader` in the same endianness.
    #[inline]
    pub fn into_bitreader(self) -> BitReader<R, E> {
        BitReader::new(self.into_reader())
    }

    /// Provides temporary `BitReader` in the same endianness.
    ///
    /// # Warning
    ///
    /// Any unread bits left over when `BitReader` is dropped are lost.
    #[inline]
    pub fn bitreader(&mut self) -> BitReader<&mut R, E> {
        BitReader::new(self.reader())
    }
}

impl<R: io::Read, E: Endianness> ByteRead for ByteReader<R, E> {
    #[inline]
    fn read<V>(&mut self) -> Result<V, io::Error>
    where
        V: Primitive,
    {
        E::read_numeric(&mut self.reader)
    }

    #[inline]
    fn read_as<F, V>(&mut self) -> Result<V, io::Error>
    where
        F: Endianness,
        V: Primitive,
    {
        F::read_numeric(&mut self.reader)
    }

    #[inline]
    fn read_bytes(&mut self, buf: &mut [u8]) -> io::Result<()> {
        self.reader.read_exact(buf)
    }

    #[inline]
    fn skip(&mut self, bytes: u32) -> io::Result<()> {
        skip_aligned(&mut self.reader, bytes)
    }

    #[inline]
    fn reader_ref(&mut self) -> &mut dyn io::Read {
        &mut self.reader
    }
}

/// Implemented by complex types that don't require any additional context
/// to parse themselves from a reader.  Analagous to `FromStr`.
///
/// # Example
/// ```
/// use std::io::{Cursor, Read};
/// use bitstream_io::{BigEndian, BitRead, BitReader, FromBitStream};
///
/// #[derive(Debug, PartialEq, Eq)]
/// struct BlockHeader {
///     last_block: bool,
///     block_type: u8,
///     block_size: u32,
/// }
///
/// impl FromBitStream for BlockHeader {
///     type Error = std::io::Error;
///
///     fn from_reader<R: BitRead + ?Sized>(r: &mut R) -> std::io::Result<Self> {
///         Ok(Self {
///             last_block: r.read_bit()?,
///             block_type: r.read::<7, _>()?,
///             block_size: r.read::<24, _>()?,
///         })
///     }
/// }
///
/// let mut reader = BitReader::endian(Cursor::new(b"\x04\x00\x00\x7A"), BigEndian);
/// assert_eq!(
///     reader.parse::<BlockHeader>().unwrap(),
///     BlockHeader { last_block: false, block_type: 4, block_size: 122 }
/// );
/// ```
pub trait FromBitStream {
    /// Error generated during parsing, such as `io::Error`
    type Error;

    /// Parse Self from reader
    fn from_reader<R: BitRead + ?Sized>(r: &mut R) -> Result<Self, Self::Error>
    where
        Self: Sized;
}

/// Implemented by complex types that require some immutable context
/// to parse themselves from a reader.
///
/// # Example
/// ```
/// use std::io::{Cursor, Read};
/// use bitstream_io::{BigEndian, BitRead, BitReader, FromBitStreamWith};
///
/// #[derive(Default)]
/// struct Streaminfo {
///     minimum_block_size: u16,
///     maximum_block_size: u16,
///     minimum_frame_size: u32,
///     maximum_frame_size: u32,
///     sample_rate: u32,
///     channels: u8,
///     bits_per_sample: u8,
///     total_samples: u64,
///     md5: [u8; 16],
/// }
///
/// #[derive(Debug, PartialEq, Eq)]
/// struct FrameHeader {
///     variable_block_size: bool,
///     block_size: u32,
///     sample_rate: u32,
///     channel_assignment: u8,
///     sample_size: u8,
///     frame_number: u64,
///     crc8: u8,
/// }
///
/// impl FromBitStreamWith<'_> for FrameHeader {
///     type Context = Streaminfo;
///
///     type Error = FrameHeaderError;
///
///     fn from_reader<R: BitRead + ?Sized>(
///         r: &mut R,
///         streaminfo: &Streaminfo,
///     ) -> Result<Self, Self::Error> {
///         if r.read::<14, u16>()? != 0b11111111111110 {
///             return Err(FrameHeaderError::InvalidSync);
///         }
///
///         if r.read_bit()? != false {
///             return Err(FrameHeaderError::InvalidReservedBit);
///         }
///
///         let variable_block_size = r.read_bit()?;
///
///         let block_size_bits = r.read::<4, u8>()?;
///
///         let sample_rate_bits = r.read::<4, u8>()?;
///
///         let channel_assignment = r.read::<4, u8>()?;
///
///         let sample_size = match r.read::<3, u8>()? {
///             0b000 => streaminfo.bits_per_sample,
///             0b001 => 8,
///             0b010 => 12,
///             0b011 => return Err(FrameHeaderError::InvalidSampleSize),
///             0b100 => 16,
///             0b101 => 20,
///             0b110 => 24,
///             0b111 => 32,
///             _ => unreachable!(),
///         };
///
///         if r.read_bit()? != false {
///             return Err(FrameHeaderError::InvalidReservedBit);
///         }
///
///         let frame_number = read_utf8(r)?;
///
///         Ok(FrameHeader {
///             variable_block_size,
///             block_size: match block_size_bits {
///                 0b0000 => return Err(FrameHeaderError::InvalidBlockSize),
///                 0b0001 => 192,
///                 n @ 0b010..=0b0101 => 576 * (1 << (n - 2)),
///                 0b0110 => r.read::<8, u32>()? + 1,
///                 0b0111 => r.read::<16, u32>()? + 1,
///                 n @ 0b1000..=0b1111 => 256 * (1 << (n - 8)),
///                 _ => unreachable!(),
///             },
///             sample_rate: match sample_rate_bits {
///                 0b0000 => streaminfo.sample_rate,
///                 0b0001 => 88200,
///                 0b0010 => 176400,
///                 0b0011 => 192000,
///                 0b0100 => 8000,
///                 0b0101 => 16000,
///                 0b0110 => 22050,
///                 0b0111 => 24000,
///                 0b1000 => 32000,
///                 0b1001 => 44100,
///                 0b1010 => 48000,
///                 0b1011 => 96000,
///                 0b1100 => r.read::<8, u32>()? * 1000,
///                 0b1101 => r.read::<16, u32>()?,
///                 0b1110 => r.read::<16, u32>()? * 10,
///                 0b1111 => return Err(FrameHeaderError::InvalidSampleRate),
///                 _ => unreachable!(),
///             },
///             channel_assignment,
///             sample_size,
///             frame_number,
///             crc8: r.read::<8, _>()?
///         })
///     }
/// }
///
/// #[derive(Debug)]
/// enum FrameHeaderError {
///     Io(std::io::Error),
///     InvalidSync,
///     InvalidReservedBit,
///     InvalidSampleSize,
///     InvalidBlockSize,
///     InvalidSampleRate,
/// }
///
/// impl From<std::io::Error> for FrameHeaderError {
///     fn from(err: std::io::Error) -> Self {
///         Self::Io(err)
///     }
/// }
///
/// fn read_utf8<R: BitRead + ?Sized>(r: &mut R) -> Result<u64, std::io::Error> {
///     r.read::<8, _>()  // left unimplimented in this example
/// }
///
/// let mut reader = BitReader::endian(Cursor::new(b"\xFF\xF8\xC9\x18\x00\xC2"), BigEndian);
/// assert_eq!(
///     reader.parse_with::<FrameHeader>(&Streaminfo::default()).unwrap(),
///     FrameHeader {
///         variable_block_size: false,
///         block_size: 4096,
///         sample_rate: 44100,
///         channel_assignment: 1,
///         sample_size: 16,
///         frame_number: 0,
///         crc8: 0xC2,
///     }
/// );
/// ```
///
/// # Example with lifetime-contrained `Context`
///
/// In some cases, the `Context` can depend on a reference to another `struct`.
///
/// ```
/// use std::io::{Cursor, Read};
/// use bitstream_io::{BigEndian, BitRead, BitReader, FromBitStreamWith};
///
/// #[derive(Default)]
/// struct ModeParameters {
///     size_len: u8,
///     index_len: u8,
///     index_delta_len: u8,
///     // ...
/// }
///
/// struct AuHeaderParseContext<'a> {
///     params: &'a ModeParameters,
///     base_index: Option<u32>,
/// }
///
/// #[derive(Debug, PartialEq, Eq)]
/// struct AuHeader {
///     size: u32,
///     index: u32,
///     // ...
/// }
///
/// impl<'a> FromBitStreamWith<'a> for AuHeader {
///     type Context = AuHeaderParseContext<'a>;
///
///     type Error = AuHeaderError;
///
///     fn from_reader<R: BitRead + ?Sized>(
///         r: &mut R,
///         ctx: &AuHeaderParseContext<'a>,
///     ) -> Result<Self, Self::Error> {
///         let size = r.read_var::<u32>(ctx.params.size_len as u32)?;
///         let index = match ctx.base_index {
///             None => r.read_var::<u32>(ctx.params.index_len as u32)?,
///             Some(base_index) => {
///                 base_index
///                 + 1
///                 + r.read_var::<u32>(ctx.params.index_delta_len as u32)?
///             }
///         };
///
///         Ok(AuHeader {
///             size,
///             index,
///             // ...
///         })
///     }
/// }
///
/// #[derive(Debug)]
/// enum AuHeaderError {
///     Io(std::io::Error),
/// }
///
/// impl From<std::io::Error> for AuHeaderError {
///     fn from(err: std::io::Error) -> Self {
///         Self::Io(err)
///     }
/// }
///
/// let mut reader = BitReader::endian(Cursor::new(b"\xFF\xEA\xFF\x10"), BigEndian);
///
/// let mode_params = ModeParameters {
///     size_len: 10,
///     index_len: 6,
///     index_delta_len: 2,
///     // ...
/// };
///
/// let mut ctx = AuHeaderParseContext {
///     params: &mode_params,
///     base_index: None,
/// };
///
/// let header1 = reader.parse_with::<AuHeader>(&ctx).unwrap();
/// assert_eq!(
///     header1,
///     AuHeader {
///         size: 1023,
///         index: 42,
///     }
/// );
///
/// ctx.base_index = Some(header1.index);
///
/// assert_eq!(
///     reader.parse_with::<AuHeader>(&ctx).unwrap(),
///     AuHeader {
///         size: 1020,
///         index: 44,
///     }
/// );
/// ```
pub trait FromBitStreamWith<'a> {
    /// Some context to use when parsing
    type Context: 'a;

    /// Error generated during parsing, such as `io::Error`
    type Error;

    /// Parse Self from reader with the given context
    fn from_reader<R: BitRead + ?Sized>(
        r: &mut R,
        context: &Self::Context,
    ) -> Result<Self, Self::Error>
    where
        Self: Sized;
}

/// Implemented by complex types that don't require any additional context
/// to parse themselves from a reader.  Analagous to `FromStr`.
pub trait FromByteStream {
    /// Error generated during parsing, such as `io::Error`
    type Error;

    /// Parse Self from reader
    fn from_reader<R: ByteRead + ?Sized>(r: &mut R) -> Result<Self, Self::Error>
    where
        Self: Sized;
}

/// Implemented by complex types that require some additional context
/// to parse themselves from a reader.  Analagous to `FromStr`.
pub trait FromByteStreamWith<'a> {
    /// Some context to use when parsing
    type Context: 'a;

    /// Error generated during parsing, such as `io::Error`
    type Error;

    /// Parse Self from reader
    fn from_reader<R: ByteRead + ?Sized>(
        r: &mut R,
        context: &Self::Context,
    ) -> Result<Self, Self::Error>
    where
        Self: Sized;
}

fn read_to_vec(
    mut read: impl FnMut(&mut [u8]) -> io::Result<()>,
    bytes: usize,
) -> io::Result<Vec<u8>> {
    const MAX_CHUNK: usize = 4096;

    match bytes {
        0 => Ok(Vec::new()),
        bytes if bytes <= MAX_CHUNK => {
            let mut buf = vec![0; bytes];
            read(&mut buf)?;
            Ok(buf)
        }
        mut bytes => {
            let mut whole = Vec::with_capacity(MAX_CHUNK);
            let mut chunk: [u8; MAX_CHUNK] = [0; MAX_CHUNK];
            while bytes > 0 {
                let chunk_size = bytes.min(MAX_CHUNK);
                let chunk = &mut chunk[0..chunk_size];
                read(chunk)?;
                whole.extend_from_slice(chunk);
                bytes -= chunk_size;
            }
            Ok(whole)
        }
    }
}
