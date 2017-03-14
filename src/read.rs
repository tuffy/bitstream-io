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
//!     let mut file_header: [u8; 4] = [0, 0, 0, 0];
//!     reader.read_bytes(&mut file_header).unwrap();
//!     assert_eq!(&file_header, b"fLaC");
//!
//!     let last_block: bool = reader.read_bit().unwrap();
//!     let block_type: u8 = reader.read(7).unwrap();
//!     let block_size: u32 = reader.read(24).unwrap();
//!     assert_eq!(last_block, false);
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

use super::{Numeric, SignedNumeric, Endianness, BitQueue};
use huffman::ReadHuffmanTree;

pub struct BitReader<'a, E: Endianness> {
    reader: &'a mut io::Read,
    bitqueue: BitQueue<E,u8>
}

impl<'a, E: Endianness> BitReader<'a, E> {
    pub fn new(reader: &mut io::Read) -> BitReader<E> {
        BitReader{reader: reader, bitqueue: BitQueue::new()}
    }

    /// Reads a single bit from the stream.
    /// `true` indicates 1, `false` indicates 0
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
            self.bitqueue.set(read_byte(self.reader)?, 8);
        }
        Ok(self.bitqueue.pop(1) == 1)
    }

    /// Reads an unsigned value from the stream with
    /// the given number of bits.  This method assumes
    /// that the programmer is using an output type
    /// sufficiently large to hold those bits.
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
    pub fn read<U>(&mut self, mut bits: u32) -> Result<U, io::Error>
        where U: Numeric {

        use std::cmp::min;
        let mut acc = BitQueue::new();

        /*transfer un-processed bits from queue to accumulator*/
        let queue_len = self.bitqueue.len();
        if queue_len > 0 {
            let to_transfer = min(queue_len, bits);
            acc.push(to_transfer,
                     U::from_u8(self.bitqueue.pop(to_transfer)));
            bits -= to_transfer;
        }

        read_aligned(&mut self.reader, bits / 8, &mut acc)
        .and_then(|()| read_unaligned(&mut self.reader,
                                      bits % 8,
                                      &mut acc,
                                      &mut self.bitqueue))
        .map(|()| acc.value())
    }

    /// Reads a twos-complement signed value from the stream with
    /// the given number of bits.  This method assumes
    /// that the programmer is using an output type
    /// sufficiently large to hold those bits.
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
    /// use bitstream_io::{LittleEndian, BitReader};
    /// let data = [0b10110111];
    /// let mut cursor = Cursor::new(&data);
    /// let mut reader = BitReader::<LittleEndian>::new(&mut cursor);
    /// assert_eq!(reader.read_signed::<i8>(4).unwrap(), 7);
    /// assert_eq!(reader.read_signed::<i8>(4).unwrap(), -5);
    /// ```
    pub fn read_signed<S>(&mut self, bits: u32) -> Result<S, io::Error>
        where S: SignedNumeric {

        /*FIXME - there should be a better way to do this*/

        if E::leading_sign() {
            let is_negative = self.read_bit()?;
            let unsigned = self.read::<S>(bits - 1)?;
            Ok(if is_negative {unsigned.as_negative(bits)} else {unsigned})
        } else {
            let unsigned = self.read::<S>(bits - 1)?;
            let is_negative = self.read_bit()?;
            Ok(if is_negative {unsigned.as_negative(bits)} else {unsigned})
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

        let queue_len = self.bitqueue.len();
        if queue_len > 0 {
            let to_drop = min(queue_len, bits);
            self.bitqueue.drop(to_drop);
            bits -= to_drop;
        }

        skip_aligned(&mut self.reader, bits / 8)
        .and_then(|()| skip_unaligned(&mut self.reader,
                                      bits % 8,
                                      &mut self.bitqueue))
    }

    /// Completely fills the given buffer with whole bytes.
    /// If the stream is already byte-aligned, it will typically map
    /// to a faster `read_exact` call.  Otherwise it will read
    /// bytes individually in 8-bit increments.
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
            self.reader.read_exact(buf)
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
        /*FIXME - optimize this*/
        let mut acc = 0;
        while self.read_bit()? == true {
            acc += 1;
        }
        Ok(acc)
    }

    /// Counts the number of 0 bits in the stream until the next
    /// 1 bit and returns the amount read.
    /// Because this field is variably-sized and may be large,
    /// its output is always a `u32` type.
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
        /*FIXME - optimize this*/
        let mut acc = 0;
        while self.read_bit()? == false {
            acc += 1;
        }
        Ok(acc)
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
    /// # Example
    /// ```
    /// use std::io::{Read, Cursor};
    /// use bitstream_io::{BigEndian, BitReader};
    /// use bitstream_io::huffman::ReadHuffmanTree;
    /// let tree = ReadHuffmanTree::new(
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
    pub fn read_huffman<T>(&mut self, mut tree: &ReadHuffmanTree<T>) ->
        Result<T,io::Error> where T: Clone {
        loop {
            match tree {
                &ReadHuffmanTree::Leaf(ref v) => {return Ok(v.clone());}
                &ReadHuffmanTree::Tree(ref zero, ref one) => {
                    tree = match self.read_bit() {
                        Ok(false) => {zero}
                        Ok(true) => {one}
                        Err(err) => {return Err(err);}
                    };
                }
            }
        }
    }
}

#[inline]
fn read_byte(reader: &mut io::Read) -> Result<u8,io::Error> {
	let mut buf = [0; 1];
    reader.read_exact(&mut buf).map(|()| buf[0])
}

fn read_aligned<E,N>(reader: &mut io::Read,
                     mut bytes: u32,
                     acc: &mut BitQueue<E,N>) -> Result<(), io::Error>
    where E: Endianness, N: Numeric {
    use std::cmp::min;

    // for native types, it's difficult to imagine a situation
    // in which this would require more than a single pass
    let mut buf = [0; 8];
    while bytes > 0 {
        let to_read = min(8, bytes);
        reader.read_exact(&mut buf[0..to_read as usize])?;
        for b in buf.iter().take(to_read as usize) {
            acc.push(8, N::from_u8(*b));
        }
        bytes -= to_read;
    }
    Ok(())
}

fn skip_aligned(reader: &mut io::Read,
                mut bytes: u32) -> Result<(), io::Error> {
    use std::cmp::min;

    // for native types, it's difficult to imagine a situation
    // in which this would require more than a single pass
    let mut buf = [0; 8];
    while bytes > 0 {
        let to_read = min(8, bytes);
        reader.read_exact(&mut buf[0..to_read as usize])?;
        bytes -= to_read;
    }
    Ok(())
}


#[inline]
fn read_unaligned<E,N>(reader: &mut io::Read,
                       bits: u32,
                       acc: &mut BitQueue<E,N>,
                       rem: &mut BitQueue<E,u8>) -> Result<(), io::Error>
    where E: Endianness, N: Numeric {

    debug_assert!(bits <= 8);

    if bits > 0 {
        rem.set(read_byte(reader)?, 8);
        acc.push(bits, N::from_u8(rem.pop(bits)));
    }
    Ok(())
}

#[inline]
fn skip_unaligned<E>(reader: &mut io::Read,
                    bits: u32,
                    rem: &mut BitQueue<E,u8>) -> Result<(), io::Error>
    where E: Endianness {
    debug_assert!(bits <= 8);

    if bits > 0 {
        rem.set(read_byte(reader)?, 8);
        rem.pop(bits);
    }
    Ok(())
}

// #[inline]
// fn read_aligned_unary(reader: &mut io::Read,
//                       continue_val: u8,
//                       rem: &mut BitQueue<u8>) -> Result<u32,io::Error> {
//     let mut acc = 0;
//     let mut byte = read_byte(reader)?;
//     while byte == continue_val {
//         acc += 8;
//         byte = read_byte(reader)?;
//     }
//     rem.set(byte, 8);
//     Ok(acc)
// }
