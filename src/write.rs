use std::io;

use super::{Numeric, SignedNumeric};

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
    fn byte_align(&mut self) -> Result<(), io::Error>;

    /*FIXME - add support for writing Huffman codes*/
}

pub struct BitWriterBE<'a> {
    writer: &'a mut io::Write,
    buffer: [u8; 1],
    bits: usize
}

impl<'a> BitWriterBE<'a> {
    pub fn new(writer: &mut io::Write) -> BitWriterBE {
        BitWriterBE{writer: writer, buffer: [0], bits: 0}
    }

    fn write_bit(&mut self, bit: bool) -> Result<(), io::Error> {
        if bit {
            self.buffer[0] |= 1 << (7 - self.bits);
        }
        self.bits += 1;
        if self.bits == 8 {
            self.writer.write_all(&self.buffer)?;
            self.buffer[0] = 0;
            self.bits = 0;
        }
        Ok(())
    }
}

impl<'a> BitWrite for BitWriterBE<'a> {
    fn write<U>(&mut self, mut bits: u32, value: U) -> Result<(), io::Error>
        where U: Numeric {
        /*FIXME - optimize this*/
        while bits > 0 {
            let mask = U::one() << (bits - 1);
            self.write_bit((value & mask).to_bit())?;
            bits -= 1;
        }
        Ok(())
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

    fn byte_aligned(&self) -> bool {
        self.bits == 0
    }

    fn byte_align(&mut self) -> Result<(), io::Error> {
        /*FIXME - optimize this*/
        while !self.byte_aligned() {
            self.write(1, 0u8)?;
        }
        Ok(())
    }
}

pub struct BitWriterLE<'a> {
    writer: &'a mut io::Write,
    buffer: [u8; 1],
    bits: usize
}

impl<'a> BitWriterLE<'a> {
    pub fn new(writer: &mut io::Write) -> BitWriterLE {
        BitWriterLE{writer: writer, buffer: [0], bits: 0}
    }

    fn write_bit(&mut self, bit: bool) -> Result<(), io::Error> {
        if bit {
            self.buffer[0] |= 1 << self.bits;
        }
        self.bits += 1;
        if self.bits == 8 {
            self.writer.write_all(&self.buffer)?;
            self.buffer[0] = 0;
            self.bits = 0;
        }
        Ok(())
    }
}

impl<'a> BitWrite for BitWriterLE<'a> {
    fn write<U>(&mut self, mut bits: u32, mut value: U) -> Result<(), io::Error>
        where U: Numeric {
        /*FIXME - optimize this*/
        while bits > 0 {
            self.write_bit((value & U::one()).to_bit())?;
            value >>= 1;
            bits -= 1;
        }
        Ok(())
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

    fn byte_aligned(&self) -> bool {
        self.bits == 0
    }

    fn byte_align(&mut self) -> Result<(), io::Error> {
        /*FIXME - optimize this*/
        while !self.byte_aligned() {
            self.write(1, 0u8)?;
        }
        Ok(())
    }
}
