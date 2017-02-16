use std::io;

use super::{Numeric, SignedNumeric, BitQueueBE, BitQueueLE, BitQueue};

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
    fn skip(&mut self, bits: u32) -> Result<(), io::Error>;

    /// Completely fills the given buffer with whole bytes.
    /// If the stream is already byte-aligned, it will map
    /// to a faster read_exact call.  Otherwise it will read
    /// bytes individually in 8-bit increments.
    fn read_bytes(&mut self, buf: &mut [u8]) -> Result<(), io::Error>;

    /// Reads an unsigned unary value with a stop bit of 0.
    fn read_unary0(&mut self) -> Result<u32, io::Error> {
        /*FIXME - optimize this*/
        let mut acc = 0;
        while self.read::<u32>(1)? != 0 {
            acc += 1;
        }
        Ok(acc)
    }

    /// Reads an unsigned unary value with a stop bit of 1.
    fn read_unary1(&mut self) -> Result<u32, io::Error> {
        /*FIXME - optimize this*/
        let mut acc = 0;
        while self.read::<u32>(1)? != 1 {
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

pub struct BitReaderBE<'a> {
    reader: &'a mut io::BufRead,
    bitqueue: BitQueueBE<u8>
}

impl<'a> BitReaderBE<'a> {
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

    fn read_signed<S>(&mut self, bits: u32) -> Result<S, io::Error>
        where S: SignedNumeric {
        debug_assert!(bits >= 1);
        let sign = self.read::<S>(1)?;
        let unsigned = self.read::<S>(bits - 1)?;
        Ok(if sign.is_zero() {unsigned} else{unsigned.as_negative(bits)})
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

    #[inline]
    fn byte_aligned(&self) -> bool {
        self.bitqueue.is_empty()
    }

    #[inline]
    fn byte_align(&mut self) {
        self.bitqueue.clear()
    }
}

pub struct BitReaderLE<'a> {
    reader: &'a mut io::BufRead,
    bitqueue: BitQueueLE<u8>
}

impl<'a> BitReaderLE<'a> {
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

    fn read_signed<S>(&mut self, bits: u32) -> Result<S, io::Error>
        where S: SignedNumeric {
        debug_assert!(bits >= 1);
        let unsigned = self.read::<S>(bits - 1)?;
        let sign = self.read::<S>(1)?;
        Ok(if sign.is_zero() {unsigned} else {unsigned.as_negative(bits)})
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
