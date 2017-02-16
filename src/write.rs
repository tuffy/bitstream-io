use std::io;

use super::{Numeric, SignedNumeric, BitQueue, BitQueueBE, BitQueueLE};

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
    /// If the stream is already byte-aligned, it will
    /// map to a faster write_all call.  Otherwise it will
    /// write bytes individually in 8-bit increments.
    fn write_bytes(&mut self, buf: &[u8]) -> Result<(), io::Error>;

    /// Writes an unsigned unary value with a stop bit of 0.
    fn write_unary0(&mut self, mut value: u32) -> Result<(), io::Error> {
        while value > 8 {
            self.write(8, 0xFFu8)?;
            value -= 8;
        }
        if value > 0 {
            self.write(value, (1 << value) - 1)?;
        }
        self.write(1, 0u8)
    }

    /// Writes an unsigned unary value with a stop bit of 1.
    fn write_unary1(&mut self, mut value: u32) -> Result<(), io::Error> {
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

    /*FIXME - add support for writing Huffman codes*/
}

pub struct BitWriterBE<'a> {
    writer: &'a mut io::Write,
    bitqueue: BitQueueBE<u8>
}

impl<'a> BitWriterBE<'a> {
    pub fn new(writer: &mut io::Write) -> BitWriterBE {
        BitWriterBE{writer: writer, bitqueue: BitQueueBE::new()}
    }
}

impl<'a> BitWrite for BitWriterBE<'a> {
    fn write<U>(&mut self, bits: u32, value: U) -> Result<(), io::Error>
        where U: Numeric {
        let mut acc = BitQueueBE::from_value(value, bits);
        write_unaligned(&mut self.writer, &mut acc, &mut self.bitqueue)
        .and_then(|()| write_aligned(&mut self.writer, &mut acc))
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

pub struct BitWriterLE<'a> {
    writer: &'a mut io::Write,
    bitqueue: BitQueueLE<u8>
}

impl<'a> BitWriterLE<'a> {
    pub fn new(writer: &mut io::Write) -> BitWriterLE {
        BitWriterLE{writer: writer, bitqueue: BitQueueLE::new()}
    }
}

impl<'a> BitWrite for BitWriterLE<'a> {
    fn write<U>(&mut self, bits: u32, value: U) -> Result<(), io::Error>
        where U: Numeric {
        let mut acc = BitQueueLE::from_value(value, bits);
        write_unaligned(&mut self.writer, &mut acc, &mut self.bitqueue)
        .and_then(|()| write_aligned(&mut self.writer, &mut acc))
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
                    acc: &mut BitQueue<N>) -> Result<(), io::Error>
    where N: Numeric {
    let bytes_to_write = (acc.len() / 8) as usize;
    if bytes_to_write > 0 {
        let mut byte_buf: Vec<u8> = Vec::with_capacity(bytes_to_write);
        unsafe {
            /*no sense in initializing the buffer with 0s
              only to overwrite each byte from the accumulator
              in the very next step, so this should be okay*/
            byte_buf.set_len(bytes_to_write);
            // safe version
            // byte_buf.resize(bytes_to_write, 0);
        }
        for byte in byte_buf.iter_mut() {
            *byte = acc.pop(8).to_u8();
        }
        writer.write_all(&byte_buf)
    } else {
        Ok(())
    }
}
