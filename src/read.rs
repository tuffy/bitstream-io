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
//! use bitstream_io::{BE, BitReader};
//!
//! let flac: Vec<u8> = vec![0x66,0x4C,0x61,0x43,0x00,0x00,0x00,0x22,
//!                          0x10,0x00,0x10,0x00,0x00,0x06,0x06,0x00,
//!                          0x21,0x62,0x0A,0xC4,0x42,0xF0,0x00,0x04,
//!                          0xA6,0xCC,0xFA,0xF2,0x69,0x2F,0xFD,0xEC,
//!                          0x2D,0x5B,0x30,0x01,0x76,0xB4,0x62,0x88,
//!                          0x7D,0x92];
//!
//! let mut cursor = Cursor::new(&flac);
//! {
//!     let mut reader = BitReader::<BE>::new(&mut cursor);
//!
//!     // stream marker
//!     let mut file_header: [u8; 4] = [0, 0, 0, 0];
//!     reader.read_bytes(&mut file_header).unwrap();
//!     assert_eq!(&file_header, b"fLaC");
//!
//!     // metadata block header
//!     let last_block: bool = reader.read_bit().unwrap();
//!     let block_type: u8 = reader.read(7).unwrap();
//!     let block_size: u32 = reader.read(24).unwrap();
//!     assert_eq!(last_block, false);
//!     assert_eq!(block_type, 0);
//!     assert_eq!(block_size, 34);
//!
//!     // STREAMINFO block
//!     let minimum_block_size: u16 = reader.read(16).unwrap();
//!     let maximum_block_size: u16 = reader.read(16).unwrap();
//!     let minimum_frame_size: u32 = reader.read(24).unwrap();
//!     let maximum_frame_size: u32 = reader.read(24).unwrap();
//!     let sample_rate: u32 = reader.read(20).unwrap();
//!     let channels = reader.read::<u8>(3).unwrap() + 1;
//!     let bits_per_sample = reader.read::<u8>(5).unwrap() + 1;
//!     let total_samples: u64 = reader.read(36).unwrap();
//!     assert_eq!(minimum_block_size, 4096);
//!     assert_eq!(maximum_block_size, 4096);
//!     assert_eq!(minimum_frame_size, 1542);
//!     assert_eq!(maximum_frame_size, 8546);
//!     assert_eq!(sample_rate, 44100);
//!     assert_eq!(channels, 2);
//!     assert_eq!(bits_per_sample, 16);
//!     assert_eq!(total_samples, 304844);
//! }
//!
//! // STREAMINFO's MD5 sum
//!
//! // Note that the wrapped reader can be used once bitstream reading
//! // is finished at exactly the position one would expect.
//!
//! let mut md5 = [0; 16];
//! cursor.read_exact(&mut md5).unwrap();
//! assert_eq!(&md5,
//!     b"\xFA\xF2\x69\x2F\xFD\xEC\x2D\x5B\x30\x01\x76\xB4\x62\x88\x7D\x92");
//! ```

#![warn(missing_docs)]

use std::io;

use super::{Numeric, SignedNumeric, BitQueue,
            Endianness, BigEndian, LittleEndian};
use huffman::ReadHuffmanTree;

/// For reading non-aligned bits from a stream of bytes in a given endianness.
///
/// This will read exactly as many whole bytes needed to return
/// the requested number of bits.  It may cache up to a single partial byte
/// but no more.
pub struct BitReader<'a, E: Endianness> {
    reader: &'a mut io::Read,
    reader_pos: u64,
    bitqueue: BitQueue<E,u8>
}

impl<'a, E: Endianness> BitReader<'a, E> {
    /// Wraps a BitReader around something that implements `Read`
    pub fn new(reader: &mut io::Read) -> BitReader<E> {
        BitReader{reader: reader, reader_pos: 0, bitqueue: BitQueue::new()}
    }

    pub fn position(&self) -> u64 {
        self.reader_pos
    }

    /// Reads a single bit from the stream.
    /// `true` indicates 1, `false` indicates 0
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::io::{Read, Cursor};
    /// use bitstream_io::{BigEndian, BitReader};
    /// let data = [0b10110111];
    /// let mut cursor = Cursor::new(&data);
    /// let mut reader = BitReader::<BigEndian>::new(&mut cursor);
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
    /// use bitstream_io::{LittleEndian, BitReader};
    /// let data = [0b10110111];
    /// let mut cursor = Cursor::new(&data);
    /// let mut reader = BitReader::<LittleEndian>::new(&mut cursor);
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
    pub fn read_bit(&mut self) -> Result<bool, io::Error> {
        if self.bitqueue.is_empty() {
            let b = self.read_byte()?;
            self.bitqueue.set(b, 8);
        }
        Ok(self.bitqueue.pop(1) == 1)
    }

    /// Reads an unsigned value from the stream with
    /// the given number of bits.
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    /// Also returns an error if the output type is too small
    /// to hold the requested number of bits.
    ///
    /// # Examples
    /// ```
    /// use std::io::{Read, Cursor};
    /// use bitstream_io::{BigEndian, BitReader};
    /// let data = [0b10110111];
    /// let mut cursor = Cursor::new(&data);
    /// let mut reader = BitReader::<BigEndian>::new(&mut cursor);
    /// assert_eq!(reader.read::<u8>(1).unwrap(), 0b1);
    /// assert_eq!(reader.read::<u8>(2).unwrap(), 0b01);
    /// assert_eq!(reader.read::<u8>(5).unwrap(), 0b10111);
    /// ```
    ///
    /// ```
    /// use std::io::{Read, Cursor};
    /// use bitstream_io::{LittleEndian, BitReader};
    /// let data = [0b10110111];
    /// let mut cursor = Cursor::new(&data);
    /// let mut reader = BitReader::<LittleEndian>::new(&mut cursor);
    /// assert_eq!(reader.read::<u8>(1).unwrap(), 0b1);
    /// assert_eq!(reader.read::<u8>(2).unwrap(), 0b11);
    /// assert_eq!(reader.read::<u8>(5).unwrap(), 0b10110);
    /// ```
    ///
    /// ```
    /// use std::io::{Read, Cursor};
    /// use bitstream_io::{BigEndian, BitReader};
    /// let data = [0;10];
    /// let mut cursor = Cursor::new(&data);
    /// let mut reader = BitReader::<BigEndian>::new(&mut cursor);
    /// assert!(reader.read::<u8>(9).is_err());    // can't read  9 bits to u8
    /// assert!(reader.read::<u16>(17).is_err());  // can't read 17 bits to u16
    /// assert!(reader.read::<u32>(33).is_err());  // can't read 33 bits to u32
    /// assert!(reader.read::<u64>(65).is_err());  // can't read 65 bits to u64
    /// ```
    pub fn read<U>(&mut self, mut bits: u32) -> Result<U, io::Error>
        where U: Numeric {

        if bits <= U::bits_size() {
            let bitqueue_len = self.bitqueue.len();
            if bits <= bitqueue_len {
                Ok(U::from_u8(self.bitqueue.pop(bits)))
            } else {
                let mut acc = BitQueue::from_value(
                    U::from_u8(self.bitqueue.pop(bitqueue_len)),
                    bitqueue_len);
                bits -= bitqueue_len;

                self.read_aligned(bits / 8, &mut acc)
                    .and_then(|()| self.read_unaligned(bits % 8, &mut acc))
                    .map(|()| acc.value())
            }
        } else {
            Err(io::Error::new(io::ErrorKind::InvalidInput,
                               "excessive bits for type read"))
        }
    }

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
    ///
    /// # Examples
    /// ```
    /// use std::io::{Read, Cursor};
    /// use bitstream_io::{BigEndian, BitReader};
    /// let data = [0b10110111];
    /// let mut cursor = Cursor::new(&data);
    /// let mut reader = BitReader::<BigEndian>::new(&mut cursor);
    /// assert!(reader.skip(3).is_ok());
    /// assert_eq!(reader.read::<u8>(5).unwrap(), 0b10111);
    /// ```
    ///
    /// ```
    /// use std::io::{Read, Cursor};
    /// use bitstream_io::{LittleEndian, BitReader};
    /// let data = [0b10110111];
    /// let mut cursor = Cursor::new(&data);
    /// let mut reader = BitReader::<LittleEndian>::new(&mut cursor);
    /// assert!(reader.skip(3).is_ok());
    /// assert_eq!(reader.read::<u8>(5).unwrap(), 0b10110);
    /// ```
    pub fn skip(&mut self, mut bits: u32) -> Result<(), io::Error> {
        use std::cmp::min;

        let to_drop = min(self.bitqueue.len(), bits);
        if to_drop != 0 {
            self.bitqueue.drop(to_drop);
            bits -= to_drop;
        }

        self.skip_aligned(bits / 8)
            .and_then(|()| self.skip_unaligned(bits % 8))
    }

    /// Completely fills the given buffer with whole bytes.
    /// If the stream is already byte-aligned, it will typically map
    /// to a faster `read_exact` call.  Otherwise it will read
    /// bytes individually in 8-bit increments.
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    ///
    /// # Example
    /// ```
    /// use std::io::{Read, Cursor};
    /// use bitstream_io::{BigEndian, BitReader};
    /// let data = b"foobar";
    /// let mut cursor = Cursor::new(&data);
    /// let mut reader = BitReader::<BigEndian>::new(&mut cursor);
    /// assert!(reader.skip(24).is_ok());
    /// let mut buf = [0;3];
    /// assert!(reader.read_bytes(&mut buf).is_ok());
    /// assert_eq!(&buf, b"bar");
    /// ```
    pub fn read_bytes(&mut self, buf: &mut [u8]) -> Result<(), io::Error> {
        if self.byte_aligned() {
            let result = self.reader.read_exact(buf);
            if result.is_ok() {
                self.reader_pos += buf.len() as u64;
            }
            result
        } else {
            for b in buf.iter_mut() {
                *b = self.read::<u8>(8)?;
            }
            Ok(())
        }
    }

    /// Counts the number of 1 bits in the stream until the next
    /// 0 bit and returns the amount read.
    /// Because this field is variably-sized and may be large,
    /// its output is always a `u32` type.
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    ///
    /// # Examples
    /// ```
    /// use std::io::{Read, Cursor};
    /// use bitstream_io::{BigEndian, BitReader};
    /// let data = [0b01110111, 0b11111110];
    /// let mut cursor = Cursor::new(&data);
    /// let mut reader = BitReader::<BigEndian>::new(&mut cursor);
    /// assert_eq!(reader.read_unary0().unwrap(), 0);
    /// assert_eq!(reader.read_unary0().unwrap(), 3);
    /// assert_eq!(reader.read_unary0().unwrap(), 10);
    /// ```
    ///
    /// ```
    /// use std::io::{Read, Cursor};
    /// use bitstream_io::{LittleEndian, BitReader};
    /// let data = [0b11101110, 0b01111111];
    /// let mut cursor = Cursor::new(&data);
    /// let mut reader = BitReader::<LittleEndian>::new(&mut cursor);
    /// assert_eq!(reader.read_unary0().unwrap(), 0);
    /// assert_eq!(reader.read_unary0().unwrap(), 3);
    /// assert_eq!(reader.read_unary0().unwrap(), 10);
    /// ```
    pub fn read_unary0(&mut self) -> Result<u32, io::Error> {
        if self.bitqueue.is_empty() {
            self.read_aligned_unary(0b11111111)
                .map(|u| u + self.bitqueue.pop_1())
        } else if self.bitqueue.all_1() {
            let base = self.bitqueue.len();
            self.bitqueue.clear();
            self.read_aligned_unary(0b11111111)
                .map(|u| base + u + self.bitqueue.pop_1())
        } else {
            Ok(self.bitqueue.pop_1())
        }
    }

    /// Counts the number of 0 bits in the stream until the next
    /// 1 bit and returns the amount read.
    /// Because this field is variably-sized and may be large,
    /// its output is always a `u32` type.
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    ///
    /// # Examples
    /// ```
    /// use std::io::{Read, Cursor};
    /// use bitstream_io::{BigEndian, BitReader};
    /// let data = [0b10001000, 0b00000001];
    /// let mut cursor = Cursor::new(&data);
    /// let mut reader = BitReader::<BigEndian>::new(&mut cursor);
    /// assert_eq!(reader.read_unary1().unwrap(), 0);
    /// assert_eq!(reader.read_unary1().unwrap(), 3);
    /// assert_eq!(reader.read_unary1().unwrap(), 10);
    /// ```
    ///
    /// ```
    /// use std::io::{Read, Cursor};
    /// use bitstream_io::{LittleEndian, BitReader};
    /// let data = [0b00010001, 0b10000000];
    /// let mut cursor = Cursor::new(&data);
    /// let mut reader = BitReader::<LittleEndian>::new(&mut cursor);
    /// assert_eq!(reader.read_unary1().unwrap(), 0);
    /// assert_eq!(reader.read_unary1().unwrap(), 3);
    /// assert_eq!(reader.read_unary1().unwrap(), 10);
    /// ```
    pub fn read_unary1(&mut self) -> Result<u32, io::Error> {
        if self.bitqueue.is_empty() {
            self.read_aligned_unary(0b00000000)
                .map(|u| u + self.bitqueue.pop_0())
        } else if self.bitqueue.all_0() {
            let base = self.bitqueue.len();
            self.bitqueue.clear();
            self.read_aligned_unary(0b00000000)
                .map(|u| base + u + self.bitqueue.pop_0())
        } else {
            Ok(self.bitqueue.pop_0())
        }
    }

    /// Returns true if the stream is aligned at a whole byte.
    ///
    /// # Example
    /// ```
    /// use std::io::{Read, Cursor};
    /// use bitstream_io::{BigEndian, BitReader};
    /// let data = [0];
    /// let mut cursor = Cursor::new(&data);
    /// let mut reader = BitReader::<BigEndian>::new(&mut cursor);
    /// assert_eq!(reader.byte_aligned(), true);
    /// assert!(reader.skip(1).is_ok());
    /// assert_eq!(reader.byte_aligned(), false);
    /// assert!(reader.skip(7).is_ok());
    /// assert_eq!(reader.byte_aligned(), true);
    /// ```
    #[inline(always)]
    pub fn byte_aligned(&self) -> bool {
        self.bitqueue.is_empty()
    }

    /// Throws away all unread bit values until the next whole byte.
    /// Does nothing if the stream is already aligned.
    ///
    /// # Example
    /// ```
    /// use std::io::{Read, Cursor};
    /// use bitstream_io::{BigEndian, BitReader};
    /// let data = [0x00, 0xFF];
    /// let mut cursor = Cursor::new(&data);
    /// let mut reader = BitReader::<BigEndian>::new(&mut cursor);
    /// assert_eq!(reader.read::<u8>(4).unwrap(), 0);
    /// reader.byte_align();
    /// assert_eq!(reader.read::<u8>(8).unwrap(), 0xFF);
    /// ```
    #[inline(always)]
    pub fn byte_align(&mut self) {
        self.bitqueue.clear()
    }

    /// Given a compiled Huffman tree, reads bits from the stream
    /// until the next symbol is encountered.
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    ///
    /// # Example
    /// ```
    /// use std::io::{Read, Cursor};
    /// use bitstream_io::{BigEndian, BitReader};
    /// use bitstream_io::huffman::compile_read_tree;
    /// let tree = compile_read_tree(
    ///     vec![('a', vec![0]),
    ///          ('b', vec![1, 0]),
    ///          ('c', vec![1, 1, 0]),
    ///          ('d', vec![1, 1, 1])]).unwrap();
    /// let data = [0b10110111];
    /// let mut cursor = Cursor::new(&data);
    /// let mut reader = BitReader::<BigEndian>::new(&mut cursor);
    /// assert_eq!(reader.read_huffman(&tree).unwrap(), 'b');
    /// assert_eq!(reader.read_huffman(&tree).unwrap(), 'c');
    /// assert_eq!(reader.read_huffman(&tree).unwrap(), 'd');
    /// ```
    pub fn read_huffman<T>(&mut self, tree: &[ReadHuffmanTree<E, T>]) -> Result<T, io::Error>
        where T: Clone {

        let mut result: &ReadHuffmanTree<E, T> = &tree[self.bitqueue.to_state()];
        loop {
            match result {
                &ReadHuffmanTree::Done(ref value, ref queue_val, ref queue_bits, _) => {
                    self.bitqueue.set(*queue_val, *queue_bits);
                    return Ok(value.clone())
                }
                &ReadHuffmanTree::Continue(ref tree) => {
                    result = &tree[self.read_byte()? as usize];
                }
                &ReadHuffmanTree::InvalidState => {panic!("invalid state");}
            }
        }
    }

    /// Consumes reader and returns any un-read partial byte
    /// as a `(bits, value)` tuple.
    ///
    /// # Examples
    /// ```
    /// use std::io::{Read, Cursor};
    /// use bitstream_io::{BigEndian, BitReader};
    /// let data = [0b1010_0101, 0b0101_1010];
    /// let mut cursor = Cursor::new(&data);
    /// let mut reader = BitReader::<BigEndian>::new(&mut cursor);
    /// assert_eq!(reader.read::<u16>(9).unwrap(), 0b1010_0101_0);
    /// let (bits, value) = reader.into_unread();
    /// assert_eq!(bits, 7);
    /// assert_eq!(value, 0b101_1010);
    /// ```
    ///
    /// ```
    /// use std::io::{Read, Cursor};
    /// use bitstream_io::{BigEndian, BitReader};
    /// let data = [0b1010_0101, 0b0101_1010];
    /// let mut cursor = Cursor::new(&data);
    /// let mut reader = BitReader::<BigEndian>::new(&mut cursor);
    /// assert_eq!(reader.read::<u16>(8).unwrap(), 0b1010_0101);
    /// let (bits, value) = reader.into_unread();
    /// assert_eq!(bits, 0);
    /// assert_eq!(value, 0);
    /// ```
    #[inline(always)]
    pub fn into_unread(self) -> (u32, u8) {
        (self.bitqueue.len(), self.bitqueue.value())
    }

    #[inline]
    fn read_byte(&mut self) -> Result<u8, io::Error> {
        let mut buf = [0; 1];
        let result = self.reader.read_exact(&mut buf).map(|()| buf[0]);
        if result.is_ok() {
            self.reader_pos += 1;
        }
        result
    }

    fn read_aligned<N>(&mut self, bytes: u32, acc: &mut BitQueue<E, N>) -> Result<(), io::Error>
        where N: Numeric {

        // 64-bit types are the maximum supported
        debug_assert!(bytes <= 8);

        let mut buf = [0; 8];
        let result = self.reader.read_exact(&mut buf[0..bytes as usize])
            .map(|()| {for b in &buf[0..bytes as usize]
                {acc.push(8, N::from_u8(*b))}});
        if result.is_ok() {
            self.reader_pos += bytes as u64;
        }
        result
    }

    fn skip_aligned(&mut self, mut bytes: u32) -> Result<(), io::Error> {
        use std::cmp::min;

        /*skip 8 bytes at a time (unlike with read_aligned, bytes may be larger than any native type) */
        let mut buf = [0; 8];
        while bytes > 0 {
            let to_read = min(8, bytes);
            self.reader.read_exact(&mut buf[0..to_read as usize])?;
            bytes -= to_read;
            self.reader_pos += to_read as u64;
        }
        Ok(())
    }

    #[inline]
    fn read_unaligned<N>(&mut self, bits: u32, acc: &mut BitQueue<E, N>) -> Result<(), io::Error>
        where N: Numeric {
        debug_assert!(bits <= 8);

        if bits > 0 {
            self.read_byte().map(|byte| {
                self.bitqueue.set(byte, 8);
                acc.push(bits, N::from_u8(self.bitqueue.pop(bits)))
            })
        } else {
            Ok(())
        }
    }

    #[inline]
    fn skip_unaligned(&mut self, bits: u32) -> Result<(), io::Error> {
        debug_assert!(bits <= 8);

        if bits > 0 {
            let byte = self.read_byte()?;
            self.bitqueue.set(byte, 8);
            self.bitqueue.pop(bits);
        }
        Ok(())
    }

    #[inline]
    fn read_aligned_unary(&mut self, continue_val: u8) -> Result<u32, io::Error> {
        let mut acc = 0;
        let mut byte = self.read_byte()?;
        while byte == continue_val {
            acc += 8;
            byte = self.read_byte()?;
        }
        self.bitqueue.set(byte, 8);
        Ok(acc)
    }
}

impl<'a> BitReader<'a, BigEndian> {
    /// Reads a twos-complement signed value from the stream with
    /// the given number of bits.
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    /// Also returns an error if the output type is too small
    /// to hold the requested number of bits.
    ///
    /// # Examples
    /// ```
    /// use std::io::{Read, Cursor};
    /// use bitstream_io::{BigEndian, BitReader};
    /// let data = [0b10110111];
    /// let mut cursor = Cursor::new(&data);
    /// let mut reader = BitReader::<BigEndian>::new(&mut cursor);
    /// assert_eq!(reader.read_signed::<i8>(4).unwrap(), -5);
    /// assert_eq!(reader.read_signed::<i8>(4).unwrap(), 7);
    /// ```
    ///
    /// ```
    /// use std::io::{Read, Cursor};
    /// use bitstream_io::{BigEndian, BitReader};
    /// let data = [0;10];
    /// let mut cursor = Cursor::new(&data);
    /// let mut r = BitReader::<BigEndian>::new(&mut cursor);
    /// assert!(r.read_signed::<i8>(9).is_err());   // can't read 9 bits to i8
    /// assert!(r.read_signed::<i16>(17).is_err()); // can't read 17 bits to i16
    /// assert!(r.read_signed::<i32>(33).is_err()); // can't read 33 bits to i32
    /// assert!(r.read_signed::<i64>(65).is_err()); // can't read 65 bits to i64
    /// ```
    pub fn read_signed<S>(&mut self, bits: u32) -> Result<S, io::Error>
        where S: SignedNumeric {

        if bits <= S::bits_size() {
            let is_negative = self.read_bit()?;
            let unsigned = self.read::<S>(bits - 1)?;
            Ok(if is_negative {unsigned.as_negative(bits)} else {unsigned})
        } else {
            Err(io::Error::new(io::ErrorKind::InvalidInput,
                               "excessive bits for type read"))
        }
    }
}

impl<'a> BitReader<'a, LittleEndian> {
    /// Reads a twos-complement signed value from the stream with
    /// the given number of bits.
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    /// Also returns an error if the output type is too small
    /// to hold the requested number of bits.
    ///
    /// # Examples
    /// ```
    /// use std::io::{Read, Cursor};
    /// use bitstream_io::{LittleEndian, BitReader};
    /// let data = [0b10110111];
    /// let mut cursor = Cursor::new(&data);
    /// let mut reader = BitReader::<LittleEndian>::new(&mut cursor);
    /// assert_eq!(reader.read_signed::<i8>(4).unwrap(), 7);
    /// assert_eq!(reader.read_signed::<i8>(4).unwrap(), -5);
    /// ```
    ///
    /// ```
    /// use std::io::{Read, Cursor};
    /// use bitstream_io::{LittleEndian, BitReader};
    /// let data = [0;10];
    /// let mut cursor = Cursor::new(&data);
    /// let mut r = BitReader::<LittleEndian>::new(&mut cursor);
    /// assert!(r.read_signed::<i8>(9).is_err());   // can't read 9 bits to i8
    /// assert!(r.read_signed::<i16>(17).is_err()); // can't read 17 bits to i16
    /// assert!(r.read_signed::<i32>(33).is_err()); // can't read 33 bits to i32
    /// assert!(r.read_signed::<i64>(65).is_err()); // can't read 65 bits to i64
    /// ```
    pub fn read_signed<S>(&mut self, bits: u32) -> Result<S, io::Error>
        where S: SignedNumeric {

        if bits <= S::bits_size() {
            let unsigned = self.read::<S>(bits - 1)?;
            let is_negative = self.read_bit()?;
            Ok(if is_negative {unsigned.as_negative(bits)} else {unsigned})
        } else {
            Err(io::Error::new(io::ErrorKind::InvalidInput,
                               "excessive bits for type read"))
        }
    }
}
