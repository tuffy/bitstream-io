// Copyright 2017 Brian Langenberger
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Traits and implementations for writing bits to a stream.
//!
//! ## Example
//! ```
//! use std::io::Write;
//! use bitstream_io::{BitWrite, BitWriterBE};
//!
//! let mut flac: Vec<u8> = Vec::new();
//! {
//!     let mut writer = BitWriterBE::new(&mut flac);
//!     writer.write_bytes(b"fLaC").unwrap();
//!
//!     let last_block: u8 = 0;
//!     let block_type: u8 = 0;
//!     let block_size: u32 = 34;
//!     writer.write(1, last_block).unwrap();
//!     writer.write(7, block_type).unwrap();
//!     writer.write(24, block_size).unwrap();
//!
//!     let minimum_block_size: u16 = 4096;
//!     let maximum_block_size: u16 = 4096;
//!     let minimum_frame_size: u32 = 1542;
//!     let maximum_frame_size: u32 = 8546;
//!     let sample_rate: u32 = 44100;
//!     let channels: u8 = 2;
//!     let bits_per_sample: u8 = 16;
//!     let total_samples: u64 = 304844;
//!     writer.write(16, minimum_block_size).unwrap();
//!     writer.write(16, maximum_block_size).unwrap();
//!     writer.write(24, minimum_frame_size).unwrap();
//!     writer.write(24, maximum_frame_size).unwrap();
//!     writer.write(20, sample_rate).unwrap();
//!     writer.write(3, channels - 1).unwrap();
//!     writer.write(5, bits_per_sample - 1).unwrap();
//!     writer.write(36, total_samples).unwrap();
//! }
//!
//! // the wrapped writer can be used once bitstream writing is finished
//! // at exactly the position one would expect
//! flac.write_all(
//!     b"\xFA\xF2\x69\x2F\xFD\xEC\x2D\x5B\x30\x01\x76\xB4\x62\x88\x7D\x92")
//!       .unwrap();
//!
//! assert_eq!(flac, vec![0x66,0x4C,0x61,0x43,0x00,0x00,0x00,0x22,
//!                       0x10,0x00,0x10,0x00,0x00,0x06,0x06,0x00,
//!                       0x21,0x62,0x0A,0xC4,0x42,0xF0,0x00,0x04,
//!                       0xA6,0xCC,0xFA,0xF2,0x69,0x2F,0xFD,0xEC,
//!                       0x2D,0x5B,0x30,0x01,0x76,0xB4,0x62,0x88,
//!                       0x7D,0x92]);
//! ```

use std::io;

use super::{Numeric, SignedNumeric, BitQueue, BitQueueBE, BitQueueLE};
use huffman::{WriteHuffmanTreeBE, WriteHuffmanTreeLE};

/// For writing bit values to an underlying stream in a given endianness.
///
/// Because this only writes whole bytes to the underlying stream,
/// it is important that output is byte-aligned before the bitstream
/// writer's lifetime ends.
/// **Partial bytes will be lost** if the writer is disposed of
/// before they can be written.
pub trait BitWrite {
    /// Writes an unsigned value to the stream using the given
    /// number of bits.  This method assumes that value's type
    /// is sufficiently large to hold those bits.
    fn write<U>(&mut self, bits: u32, value: U) -> Result<(), io::Error>
        where U: Numeric;

    /// Writes a twos-complement signed value to the stream
    /// with the given number of bits.  This method assumes
    /// that value's type is sufficiently large to hold those bits.
    fn write_signed<S>(&mut self, bits: u32, value: S) -> Result<(), io::Error>
        where S: SignedNumeric;

    /// Writes the entirety of a byte buffer to the stream.
    /// If the stream is already byte-aligned, it will often
    /// map to a faster `write_all` call.  Otherwise it will
    /// write bytes individually in 8-bit increments.
    fn write_bytes(&mut self, buf: &[u8]) -> Result<(), io::Error>;

    /// Writes `value` number of 1 bits to the stream
    /// and then writes a 0 bit.  This field is variably-sized.
    fn write_unary0(&mut self, mut value: u32) -> Result<(), io::Error> {
        /*FIXME - optimize this*/
        while value > 8 {
            self.write(8, 0xFFu8)?;
            value -= 8;
        }
        if value > 0 {
            self.write(value, (1 << value) - 1)?;
        }
        self.write(1, 0u8)
    }

    /// Writes `value` number of 0 bits to the stream
    /// and then writes a 1 bit.  This field is variably-sized.
    fn write_unary1(&mut self, mut value: u32) -> Result<(), io::Error> {
        /*FIXME - optimize this*/
        while value > 8 {
            self.write(8, 0u8)?;
            value -= 8;
        }
        if value > 0 {
            self.write(value, 0)?;
        }
        self.write(1, 1u8)
    }

    /// Returns true if the stream is aligned at a whole byte.
    fn byte_aligned(&self) -> bool;

    /// Pads the stream with 0 bits until is aligned at a whole byte.
    /// Does nothing if the stream is already aligned.
    fn byte_align(&mut self) -> Result<(), io::Error> {
        while !self.byte_aligned() {
            self.write(1, 0u8)?;
        }
        Ok(())
    }

}

/// A wrapper for writing values to a big-endian stream.
pub struct BitWriterBE<'a> {
    writer: &'a mut io::Write,
    bitqueue: BitQueueBE<u8>,
    byte_buf: Vec<u8>
}

impl<'a> BitWriterBE<'a> {
    /// Wraps a big-endian writer around a `Write` reference.
    ///
    /// Because this is liable to make many small writes
    /// in the course of normal operation, a `BufWrite` is preferable
    /// for better performance.
    pub fn new(writer: &mut io::Write) -> BitWriterBE {
        BitWriterBE{writer: writer,
                    bitqueue: BitQueueBE::new(),
                    byte_buf: Vec::new()}
    }

    /// Given a compiled Huffman tree, writes value to the stream
    /// with the corresponding bits for that value.
    /// Panics of the value is not found in the tree.
    pub fn write_huffman<T>(&mut self,
                            tree: &WriteHuffmanTreeBE<T>,
                            value: T) -> Result<(), io::Error>
        where T: Ord + Copy {
        let (bits, value) = tree.get(value);
        self.write(bits, value)
    }
}

impl<'a> BitWrite for BitWriterBE<'a> {
    fn write<U>(&mut self, bits: u32, value: U) -> Result<(), io::Error>
        where U: Numeric {
        let mut acc = BitQueueBE::from_value(value, bits);
        write_unaligned(&mut self.writer, &mut acc, &mut self.bitqueue)
        .and_then(|()|
            write_aligned(&mut self.writer, &mut self.byte_buf, &mut acc))
        .and_then(|()| Ok(self.bitqueue.push(acc.len(), acc.value().to_u8())))
    }

    fn write_signed<S>(&mut self, bits: u32, value: S) -> Result<(), io::Error>
        where S: SignedNumeric {
        if value.is_negative() {
            self.write(1, 1u8)
                .and_then(|()| self.write(bits - 1, value.as_unsigned(bits)))
        } else {
            self.write(1, 0u8)
                .and_then(|()| self.write(bits - 1, value))
        }
    }

    fn write_bytes(&mut self, buf: &[u8]) -> Result<(), io::Error> {
        if self.byte_aligned() {
            self.writer.write_all(buf)
        } else {
            for b in buf {
                self.write(8, *b)?;
            }
            Ok(())
        }
    }

    #[inline]
    fn byte_aligned(&self) -> bool {
        self.bitqueue.is_empty()
    }
}

/// A wrapper for writing values to a little-endian stream.
pub struct BitWriterLE<'a> {
    writer: &'a mut io::Write,
    bitqueue: BitQueueLE<u8>,
    byte_buf: Vec<u8>
}

impl<'a> BitWriterLE<'a> {
    /// Wraps a little-endian writer around a `Write` reference.
    ///
    /// Because this is liable to make many small writes
    /// in the course of normal operation, a `BufWrite` is preferable
    /// for better performance.
    pub fn new(writer: &mut io::Write) -> BitWriterLE {
        BitWriterLE{writer: writer,
                    bitqueue: BitQueueLE::new(),
                    byte_buf: Vec::new()}
    }

    /// Given a compiled Huffman tree, writes value to the stream
    /// with the corresponding bits for that value.
    /// Panics of the value is not found in the tree.
    pub fn write_huffman<T>(&mut self,
                            tree: &WriteHuffmanTreeLE<T>,
                            value: T) -> Result<(), io::Error>
        where T: Ord + Copy {
        let (bits, value) = tree.get(value);
        self.write(bits, value)
    }
}

impl<'a> BitWrite for BitWriterLE<'a> {
    fn write<U>(&mut self, bits: u32, value: U) -> Result<(), io::Error>
        where U: Numeric {
        let mut acc = BitQueueLE::from_value(value, bits);
        write_unaligned(&mut self.writer, &mut acc, &mut self.bitqueue)
        .and_then(|()|
            write_aligned(&mut self.writer, &mut self.byte_buf, &mut acc))
        .and_then(|()| Ok(self.bitqueue.push(acc.len(), acc.value().to_u8())))
    }

    fn write_signed<S>(&mut self, bits: u32, value: S) -> Result<(), io::Error>
        where S: SignedNumeric {
        if value.is_negative() {
            self.write(bits - 1, value.as_unsigned(bits))
                .and_then(|()| self.write(1, 1u8))
        } else {
            self.write(bits - 1, value)
                .and_then(|()| self.write(1, 0u8))
        }
    }

    fn write_bytes(&mut self, buf: &[u8]) -> Result<(), io::Error> {
        if self.byte_aligned() {
            self.writer.write_all(buf)
        } else {
            for b in buf {
                self.write(8, *b)?;
            }
            Ok(())
        }
    }

    #[inline]
    fn byte_aligned(&self) -> bool {
        self.bitqueue.is_empty()
    }
}

fn write_unaligned<N>(writer: &mut io::Write,
                      acc: &mut BitQueue<N>,
                      rem: &mut BitQueue<u8>) -> Result<(), io::Error>
    where N: Numeric {

    if rem.is_empty() {
        Ok(())
    } else {
        use std::cmp::min;
        let bits_to_transfer = min(8 - rem.len(), acc.len());
        rem.push(bits_to_transfer, acc.pop(bits_to_transfer).to_u8());
        if rem.len() == 8 {
            let buf: [u8;1] = [rem.pop(8)];
            writer.write_all(&buf)
        } else {
            Ok(())
        }
    }
}

fn write_aligned<N>(writer: &mut io::Write,
                    byte_buf: &mut Vec<u8>,
                    acc: &mut BitQueue<N>) -> Result<(), io::Error>
    where N: Numeric {
    let bytes_to_write = (acc.len() / 8) as usize;
    if bytes_to_write > 0 {
        byte_buf.clear();
        byte_buf.extend((0..bytes_to_write).map(|_| acc.pop(8).to_u8()));
        writer.write_all(&byte_buf)
    } else {
        Ok(())
    }
}
