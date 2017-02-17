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
//! ```
//! use std::io::Cursor;
//! use std::io::Read;
//! use bitstream_io::{BitRead, BitReaderBE};
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
//!     let mut reader = BitReaderBE::new(&mut cursor);
//!     let mut file_header: [u8; 4] = [0, 0, 0, 0];
//!     reader.read_bytes(&mut file_header).unwrap();
//!     assert_eq!(&file_header, b"fLaC");
//!
//!     let last_block: u8 = reader.read(1).unwrap();
//!     let block_type: u8 = reader.read(7).unwrap();
//!     let block_size: u32 = reader.read(24).unwrap();
//!     assert_eq!(last_block, 0);
//!     assert_eq!(block_type, 0);
//!     assert_eq!(block_size, 34);
//!
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
//! // the wrapped reader can be used once bitstream reading is finished
//! // at exactly the position one would expect
//! let mut md5: [u8; 16] = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
//! cursor.read_exact(&mut md5).unwrap();
//! assert_eq!(&md5,
//!     b"\xFA\xF2\x69\x2F\xFD\xEC\x2D\x5B\x30\x01\x76\xB4\x62\x88\x7D\x92");
//! ```

use std::io;

use super::{Numeric, SignedNumeric, BitQueueBE, BitQueueLE, BitQueue};

/// For reading bit values from an underlying stream in a given endianness.
pub trait BitRead {
    /// Reads an unsigned value from the stream with
    /// the given number of bits.  This method assumes
    /// that the programmer is using an output type
    /// sufficiently large to hold those bits.
    fn read<U>(&mut self, bits: u32) -> Result<U, io::Error>
        where U: Numeric;

    /// Reads a twos-complement signed value from the stream with
    /// the given number of bits.  This method assumes
    /// that the programmer is using an output type
    /// sufficiently large to hold those bits.
    fn read_signed<S>(&mut self, bits: u32) -> Result<S, io::Error>
        where S: SignedNumeric;

    /// Skips the given number of bits in the stream.
    /// Since this method does not need an accumulator,
    /// it may be slightly faster than reading to an empty variable.
    /// In addition, since there is no accumulator,
    /// there is no upper limit on the number of bits
    /// which may be skipped.
    /// These bits are still read from the stream, however,
    /// and are never skipped via a `seek` method.
    fn skip(&mut self, bits: u32) -> Result<(), io::Error>;

    /// Completely fills the given buffer with whole bytes.
    /// If the stream is already byte-aligned, it will map
    /// to a faster `read_exact` call.  Otherwise it will read
    /// bytes individually in 8-bit increments.
    fn read_bytes(&mut self, buf: &mut [u8]) -> Result<(), io::Error>;

    /// Counts the number of 1 bits in the stream until the next
    /// 0 bit and returns the amount read.
    /// Because this field is variably-sized and may be large,
    /// its output is always a `u32` type.
    fn read_unary0(&mut self) -> Result<u32, io::Error> {
        /*FIXME - optimize this*/
        let mut acc = 0;
        while self.read::<u8>(1)? != 0 {
            acc += 1;
        }
        Ok(acc)
    }

    /// Counts the number of 0 bits in the stream until the next
    /// 1 bit and returns the amount read.
    /// Because this field is variably-sized and may be large,
    /// its output is always a `u32` type.
    fn read_unary1(&mut self) -> Result<u32, io::Error> {
        /*FIXME - optimize this*/
        let mut acc = 0;
        while self.read::<u8>(1)? != 1 {
            acc += 1;
        }
        Ok(acc)
    }

    /// Returns true if the stream is aligned at a whole byte.
    fn byte_aligned(&self) -> bool;

    /// Throws away all unread bit values until the next whole byte.
    fn byte_align(&mut self);

    /*FIXME - add support for reading Huffman codes*/
}

/// A wrapper for reading values from a big-endian stream.
pub struct BitReaderBE<'a> {
    reader: &'a mut io::BufRead,
    bitqueue: BitQueueBE<u8>
}

impl<'a> BitReaderBE<'a> {
    /// Wraps a big-endian reader around a `BufRead` reference.
    ///
    /// A `BufRead` is required because this reader is liable
    /// to make many small reads to the stream in normal operation,
    /// so reading from the buffer directly is preferable
    /// to making many calls to `read_exact`.
    pub fn new(reader: &mut io::BufRead) -> BitReaderBE {
        BitReaderBE{reader: reader, bitqueue: BitQueueBE::new()}
    }
}

impl<'a> BitRead for BitReaderBE<'a> {
    fn read<U>(&mut self, mut bits: u32) -> Result<U, io::Error>
        where U: Numeric {
        use std::cmp::min;
        let mut acc: BitQueueBE<U> = BitQueueBE::new();

        /*transfer un-processed bits from queue to accumulator*/
        let queue_len = self.bitqueue.len();
        if queue_len > 0 {
            let to_transfer = min(queue_len, bits);
            acc.push(to_transfer, U::from_u8(self.bitqueue.pop(to_transfer)));
            bits -= to_transfer;
        }

        read_aligned(&mut self.reader, bits / 8, &mut acc)
        .and_then(|()| read_unaligned(&mut self.reader,
                                      bits % 8,
                                      &mut acc,
                                      &mut self.bitqueue))
        .map(|()| acc.value())
    }

    fn skip(&mut self, mut bits: u32) -> Result<(), io::Error> {
        use std::cmp::min;

        let queue_len = self.bitqueue.len();
        if queue_len > 0 {
            let to_drop = min(queue_len, bits);
            self.bitqueue.pop(to_drop);
            bits -= to_drop;
        }

        skip_aligned(&mut self.reader, bits / 8)
        .and_then(|()| skip_unaligned(&mut self.reader,
                                      bits % 8,
                                      &mut self.bitqueue))
    }

    fn read_signed<S>(&mut self, bits: u32) -> Result<S, io::Error>
        where S: SignedNumeric {
        debug_assert!(bits >= 1);
        let sign = self.read::<S>(1)?;
        let unsigned = self.read::<S>(bits - 1)?;
        Ok(if sign.is_zero() {unsigned} else{unsigned.as_negative(bits)})
    }

    fn read_bytes(&mut self, buf: &mut [u8]) -> Result<(), io::Error> {
        if self.byte_aligned() {
            self.reader.read_exact(buf)
        } else {
            for b in buf.iter_mut() {
                *b = self.read::<u8>(8)?;
            }
            Ok(())
        }
    }

    #[inline]
    fn byte_aligned(&self) -> bool {
        self.bitqueue.is_empty()
    }

    #[inline]
    fn byte_align(&mut self) {
        self.bitqueue.clear()
    }
}

/// A wrapper for reading values from a little-endian stream.
pub struct BitReaderLE<'a> {
    reader: &'a mut io::BufRead,
    bitqueue: BitQueueLE<u8>
}

impl<'a> BitReaderLE<'a> {
    /// Wraps a little-endian reader around a `BufRead` reference.
    ///
    /// A `BufRead` is required because this reader is liable
    /// to make many small reads to the stream in normal operation,
    /// so reading from the buffer directly is preferable
    /// to making many calls to `read_exact`.
    pub fn new(reader: &mut io::BufRead) -> BitReaderLE {
        BitReaderLE{reader: reader, bitqueue: BitQueueLE::new()}
    }
}

impl<'a> BitRead for BitReaderLE<'a> {
    fn read<U>(&mut self, mut bits: u32) -> Result<U, io::Error>
        where U: Numeric {
        use std::cmp::min;

        let mut acc: BitQueueLE<U> = BitQueueLE::new();

        /*transfer un-processed bits from queue to accumulator*/
        let queue_len = self.bitqueue.len();
        if queue_len > 0 {
            let to_transfer = min(queue_len, bits);
            acc.push(to_transfer, U::from_u8(self.bitqueue.pop(to_transfer)));
            bits -= to_transfer;
        }

        read_aligned(&mut self.reader, bits / 8, &mut acc)
        .and_then(|()| read_unaligned(&mut self.reader,
                                      bits % 8,
                                      &mut acc,
                                      &mut self.bitqueue))
        .map(|()| acc.value())
    }

    fn skip(&mut self, mut bits: u32) -> Result<(), io::Error> {
        use std::cmp::min;

        let queue_len = self.bitqueue.len();
        if queue_len > 0 {
            let to_drop = min(queue_len, bits);
            self.bitqueue.pop(to_drop);
            bits -= to_drop;
        }

        skip_aligned(&mut self.reader, bits / 8)
        .and_then(|()| skip_unaligned(&mut self.reader,
                                      bits % 8,
                                      &mut self.bitqueue))
    }

    fn read_signed<S>(&mut self, bits: u32) -> Result<S, io::Error>
        where S: SignedNumeric {
        debug_assert!(bits >= 1);
        let unsigned = self.read::<S>(bits - 1)?;
        let sign = self.read::<S>(1)?;
        Ok(if sign.is_zero() {unsigned} else {unsigned.as_negative(bits)})
    }

    fn read_bytes(&mut self, buf: &mut [u8]) -> Result<(), io::Error> {
        if self.byte_aligned() {
            self.reader.read_exact(buf)
        } else {
            for b in buf.iter_mut() {
                *b = self.read::<u8>(8)?;
            }
            Ok(())
        }
    }

    #[inline]
    fn byte_aligned(&self) -> bool {
        self.bitqueue.is_empty()
    }

    #[inline]
    fn byte_align(&mut self) {
        self.bitqueue.clear()
    }
}

fn read_aligned<N>(reader: &mut io::BufRead,
                   mut bytes: u32,
                   acc: &mut BitQueue<N>) -> Result<(), io::Error>
    where N: Numeric {
    use std::cmp::min;

    while bytes > 0 {
        let processed = {
            let buf = reader.fill_buf()?;
            let to_process = min(bytes as usize, buf.len());
            for b in &buf[0..to_process] {
                acc.push(8, N::from_u8(*b));
            }
            to_process
        };
        if processed > 0 {
            reader.consume(processed);
            bytes -= processed as u32;
        } else {
            return Err(io::Error::new(
                io::ErrorKind::UnexpectedEof, "EOF in stream"));
        }
    }
    Ok(())
}

fn read_unaligned<N>(reader: &mut io::BufRead,
                     bits: u32,
                     acc: &mut BitQueue<N>,
                     rem: &mut BitQueue<u8>) -> Result<(), io::Error>
    where N: Numeric {

    debug_assert!(bits <= 8);

    if bits > 0 {
        let length = {
            let buf = reader.fill_buf()?;
            if buf.len() > 0 {
                rem.set(buf[0], 8);
                acc.push(bits, N::from_u8(rem.pop(bits)));
                1
            } else {0}
        };
        if length > 0 {
            Ok(reader.consume(length))
        } else {
            Err(io::Error::new(
                io::ErrorKind::UnexpectedEof, "EOF in stream"))
        }
    } else {
        Ok(())
    }
}

fn skip_aligned(reader: &mut io::BufRead,
                mut bytes: u32) -> Result<(), io::Error> {
    use std::cmp::min;

    while bytes > 0 {
        let processed = {
            let buf = reader.fill_buf()?;
            let to_process = min(bytes as usize, buf.len());
            to_process
        };
        if processed > 0 {
            reader.consume(processed);
            bytes -= processed as u32;
        } else {
            return Err(io::Error::new(
                io::ErrorKind::UnexpectedEof, "EOF in stream"));
        }
    }
    Ok(())
}

fn skip_unaligned(reader: &mut io::BufRead,
                  bits: u32,
                  rem: &mut BitQueue<u8>) -> Result<(), io::Error> {
    debug_assert!(bits <= 8);

    if bits > 0 {
        let length = {
            let buf = reader.fill_buf()?;
            if buf.len() > 0 {
                rem.set(buf[0], 8);
                rem.pop(bits);
                1
            } else {0}
        };
        if length > 0 {
            Ok(reader.consume(length))
        } else {
            Err(io::Error::new(
                io::ErrorKind::UnexpectedEof, "EOF in stream"))
        }
    } else {
        Ok(())
    }
}
