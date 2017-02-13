use std::io;
use std::ops::{BitOrAssign, Shl, ShlAssign};
use std::collections::VecDeque;


pub trait BitRead {
    /// Reads an unsigned value from the stream with
    /// the given number of bits.  This method assumes
    /// that the programmer is using an output value
    /// sufficiently large to hold those bits.
    fn read<U>(&mut self, bits: u32) -> Result<U, io::Error>
        where U: Sized + FromBit + Default + ShlAssign<U> + BitOrAssign<U> +
        Shl<u32,Output=U>;

    /// Reads a twos-complement signed value from the stream with
    /// the given number of bits.  This method assumes
    /// that the programmer is using an output value
    /// sufficiently large to hold those bits.
    fn read_signed(&mut self, bits: u32) -> Result<i32, io::Error>;

    /// Skips the given number of bits in the stream.
    /// Since this method does not need an accumulator,
    /// it may be slightly faster than reading to an empty variable.
    fn skip(&mut self, bits: u32) -> Result<(), io::Error>;

    /// Completely fills the given buffer with whole bytes.
    /// If the stream is already byte-aligned, it will map
    /// to a faster read_exact call.  Otherwise it will read
    /// bytes individually in 8-bit increments.
    fn read_bytes(&mut self, buf: &mut [u8]) -> Result<(), io::Error>;

    /// Reads an unsigned unary value with a stop bit of 0.
    fn read_unary0(&mut self) -> Result<u32, io::Error>;

    /// Reads an unsigned unary value with a stop bit of 1.
    fn read_unary1(&mut self) -> Result<u32, io::Error>;

    /// Returns true if the stream is aligned at a whole byte.
    fn byte_aligned(&self) -> bool;

    /// Throws away all unread bit values until the next whole byte.
    fn byte_align(&mut self);
}

pub struct BitReaderBE<'a> {
    reader: &'a mut io::Read,
    buffer: VecDeque<bool>
}

impl<'a> BitReaderBE<'a> {
    pub fn new(reader: &mut io::Read) -> BitReaderBE {
        BitReaderBE{reader: reader, buffer: VecDeque::with_capacity(8)}
    }

    fn next_bit(&mut self) -> Result<bool, io::Error> {
        if self.buffer.len() == 0 {
            let mut buf = [0; 1];
            self.reader.read_exact(&mut buf)?;
            self.buffer.push_back(((buf[0] >> 7) & 1) != 0);
            self.buffer.push_back(((buf[0] >> 6) & 1) != 0);
            self.buffer.push_back(((buf[0] >> 5) & 1) != 0);
            self.buffer.push_back(((buf[0] >> 4) & 1) != 0);
            self.buffer.push_back(((buf[0] >> 3) & 1) != 0);
            self.buffer.push_back(((buf[0] >> 2) & 1) != 0);
            self.buffer.push_back(((buf[0] >> 1) & 1) != 0);
            self.buffer.push_back(((buf[0] >> 0) & 1) != 0);
        }
        Ok(self.buffer.pop_front().unwrap())
    }
}

impl<'a> BitRead for BitReaderBE<'a> {
    fn read<U>(&mut self, mut bits: u32) -> Result<U, io::Error>
        where U: Sized + FromBit + Default + ShlAssign<U> + BitOrAssign<U> +
        Shl<u32,Output=U> {
        /*FIXME - optimize this*/
        let mut acc = U::default();
        while bits > 0 {
            acc <<= U::one();
            acc |= U::from_bit(self.next_bit()?);
            bits -= 1;
        }
        Ok(acc)
    }

    fn read_signed(&mut self, bits: u32) -> Result<i32, io::Error> {
        /*FIXME - make this generic*/
        /*FIXME - optimize this*/
        self.read::<u32>(bits).map(|u| if (u & (1 << (bits - 1))) == 0 {
            u as i32
        } else {
            -((1 << bits) - (u as i32))
        })
    }

    fn skip(&mut self, bits: u32) -> Result<(), io::Error> {
        /*FIXME - optimize this*/
        self.read::<u32>(bits).map(|_| ())
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

    fn read_unary0(&mut self) -> Result<u32, io::Error> {
        /*FIXME - optimize this*/
        let mut acc = 0;
        while self.read::<u32>(1)? != 0 {
            acc += 1;
        }
        Ok(acc)
    }

    fn read_unary1(&mut self) -> Result<u32, io::Error> {
        /*FIXME - optimize this*/
        let mut acc = 0;
        while self.read::<u32>(1)? != 1 {
            acc += 1;
        }
        Ok(acc)
    }

    fn byte_aligned(&self) -> bool {
        self.buffer.is_empty()
    }

    fn byte_align(&mut self) {
        self.buffer.clear()
    }
}

pub struct BitReaderLE<'a> {
    reader: &'a mut io::Read,
    buffer: VecDeque<bool>
}

impl<'a> BitReaderLE<'a> {
    pub fn new(reader: &mut io::Read) -> BitReaderLE {
        BitReaderLE{reader: reader, buffer: VecDeque::with_capacity(8)}
    }

    fn next_bit(&mut self) -> Result<bool, io::Error> {
        if self.buffer.len() == 0 {
            let mut buf = [0; 1];
            self.reader.read_exact(&mut buf)?;
            self.buffer.push_back(((buf[0] >> 0) & 1) != 0);
            self.buffer.push_back(((buf[0] >> 1) & 1) != 0);
            self.buffer.push_back(((buf[0] >> 2) & 1) != 0);
            self.buffer.push_back(((buf[0] >> 3) & 1) != 0);
            self.buffer.push_back(((buf[0] >> 4) & 1) != 0);
            self.buffer.push_back(((buf[0] >> 5) & 1) != 0);
            self.buffer.push_back(((buf[0] >> 6) & 1) != 0);
            self.buffer.push_back(((buf[0] >> 7) & 1) != 0);
        }
        Ok(self.buffer.pop_front().unwrap())
    }
}

impl<'a> BitRead for BitReaderLE<'a> {
    fn read<U>(&mut self, bits: u32) -> Result<U, io::Error>
        where U: Sized + FromBit + Default + ShlAssign<U> + BitOrAssign<U> +
        Shl<u32,Output=U> {
        /*FIXME - optimize this*/
        let mut acc = U::default();
        for i in 0..bits {
            acc |= U::from_bit(self.next_bit()?) << i;
        }
        Ok(acc)
    }

    fn read_signed(&mut self, bits: u32) -> Result<i32, io::Error> {
        /*FIXME - make this generic*/
        /*FIXME - optimize this*/
        self.read::<u32>(bits).map(|u| if (u & (1 << (bits - 1))) == 0 {
            u as i32
        } else {
            -((1 << bits) - (u as i32))
        })
    }

    fn skip(&mut self, bits: u32) -> Result<(), io::Error> {
        /*FIXME - optimize this*/
        self.read::<u32>(bits).map(|_| ())
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

    fn read_unary0(&mut self) -> Result<u32, io::Error> {
        /*FIXME - optimize this*/
        let mut acc = 0;
        while self.read::<u32>(1)? != 0 {
            acc += 1;
        }
        Ok(acc)
    }

    fn read_unary1(&mut self) -> Result<u32, io::Error> {
        /*FIXME - optimize this*/
        let mut acc = 0;
        while self.read::<u32>(1)? != 1 {
            acc += 1;
        }
        Ok(acc)
    }

    fn byte_aligned(&self) -> bool {
        self.buffer.is_empty()
    }

    fn byte_align(&mut self) {
        self.buffer.clear()
    }
}

pub trait FromBit: Sized {
    fn one() -> Self;
    fn from_bit(bit: bool) -> Self;
}

impl FromBit for u8 {
    #[inline]
    fn one() -> Self {1}
    #[inline]
    fn from_bit(bit: bool) -> Self {if bit {1} else {0}}
}

impl FromBit for u16 {
    #[inline]
    fn one() -> Self {1}
    #[inline]
    fn from_bit(bit: bool) -> Self {if bit {1} else {0}}
}

impl FromBit for u32 {
    #[inline]
    fn one() -> Self {1}
    #[inline]
    fn from_bit(bit: bool) -> Self {if bit {1} else {0}}
}

impl FromBit for u64 {
    #[inline]
    fn one() -> Self {1}
    #[inline]
    fn from_bit(bit: bool) -> Self {if bit {1} else {0}}
}
