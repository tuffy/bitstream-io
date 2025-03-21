// Copyright 2017 Brian Langenberger
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

extern crate bitstream_io;

use bitstream_io::{BigEndian, BitRead, BitReader, BitWrite, BitWriter, LittleEndian};
#[cfg(not(feature = "std"))]
use core2::io::Cursor;

#[cfg(feature = "std")]
use std::io::Cursor;

macro_rules! define_roundtrip {
    ($func_name:ident, $endianness:ident) => {
        #[test]
        fn $func_name() {
            /*unsigned values*/
            for bits in 1..17 {
                let max = 1 << bits;
                let mut output: Vec<u8> = Vec::with_capacity(max);
                {
                    let mut writer = BitWriter::endian(&mut output, $endianness);
                    for value in 0..max {
                        writer.write_var(bits, value as u32).unwrap();
                    }
                    writer.byte_align().unwrap();
                }
                {
                    let mut c = Cursor::new(&output);
                    let mut reader = BitReader::endian(&mut c, $endianness);
                    for value in 0..max {
                        assert_eq!(reader.read_var::<u32>(bits).unwrap(), value as u32);
                    }
                }
            }

            /*signed values*/
            for bits in 2..17 {
                let min = -1i32 << (bits - 1);
                let max = 1i32 << (bits - 1);
                let mut output: Vec<u8> = Vec::with_capacity(max as usize);
                {
                    let mut writer = BitWriter::endian(&mut output, $endianness);
                    for value in min..max {
                        writer.write_signed_var(bits, value as i32).unwrap();
                    }
                    writer.byte_align().unwrap();
                }
                {
                    let mut c = Cursor::new(&output);
                    let mut reader = BitReader::endian(&mut c, $endianness);
                    for value in min..max {
                        assert_eq!(reader.read_signed_var::<i32>(bits).unwrap(), value as i32);
                    }
                }
            }
        }
    };
}

define_roundtrip!(test_roundtrip_be, BigEndian);
define_roundtrip!(test_roundtrip_le, LittleEndian);

macro_rules! define_unary_roundtrip {
    ($func_name:ident, $endianness:ident) => {
        #[test]
        fn $func_name() {
            let mut output: Vec<u8> = Vec::new();
            {
                let mut writer = BitWriter::endian(&mut output, $endianness);
                for value in 0..1024 {
                    writer.write_unary::<0>(value).unwrap();
                }
                writer.byte_align().unwrap();
            }
            {
                let mut c = Cursor::new(&output);
                let mut reader = BitReader::endian(&mut c, $endianness);
                for value in 0..1024 {
                    assert_eq!(reader.read_unary::<0>().unwrap(), value);
                }
            }

            let mut output: Vec<u8> = Vec::new();
            {
                let mut writer = BitWriter::endian(&mut output, $endianness);
                for value in 0..1024 {
                    writer.write_unary::<1>(value).unwrap();
                }
                writer.byte_align().unwrap();
            }
            {
                let mut c = Cursor::new(&output);
                let mut reader = BitReader::endian(&mut c, $endianness);
                for value in 0..1024 {
                    assert_eq!(reader.read_unary::<1>().unwrap(), value);
                }
            }
        }
    };
}

define_unary_roundtrip!(test_unary_roundtrip_be, BigEndian);
define_unary_roundtrip!(test_unary_roundtrip_le, LittleEndian);

macro_rules! define_float_roundtrip {
    ($func_name:ident, $endianness:ident, $t:ty) => {
        #[test]
        fn $func_name() {
            let mut output: Vec<u8> = Vec::new();
            {
                let mut writer = BitWriter::endian(&mut output, $endianness);
                // these values should all be exact in floating-point
                for value in 0..1024 {
                    writer.write_from(value as $t).unwrap();
                }
                writer.byte_align().unwrap();
            }
            {
                let mut c = Cursor::new(&output);
                let mut reader = BitReader::endian(&mut c, $endianness);
                for value in 0..1024 {
                    assert_eq!(reader.read_to::<$t>().unwrap(), value as $t);
                }
            }
        }
    };
}

define_float_roundtrip!(test_f32_roundtrip_be, BigEndian, f32);
define_float_roundtrip!(test_f64_roundtrip_be, BigEndian, f64);
define_float_roundtrip!(test_f32_roundtrip_le, LittleEndian, f32);
define_float_roundtrip!(test_f64_roundtrip_le, LittleEndian, f64);

#[test]
fn test_auto_signedness() {
    use bitstream_io::{
        BigEndian, BitRead, BitReader, BitWrite, BitWriter, Endianness, Integer, LittleEndian,
        SignedNumeric, UnsignedNumeric,
    };

    macro_rules! define_roundtrip {
        ($n:ident, $i:ident, $w:ident, $r:ident) => {
            fn $n<I: Integer + $i + core::ops::AddAssign, E: Endianness>(
                mut start: I,
                end: I,
                bits: u32,
            ) {
                let mut w: BitWriter<_, E> = BitWriter::new(Cursor::new(Vec::new()));
                w.write_bit(true).unwrap();
                let mut i = start;
                while i < end {
                    w.$w(bits, i).unwrap();
                    i += I::ONE;
                }
                w.$w(bits, end).unwrap();

                w.byte_align().unwrap();

                let mut r: BitReader<_, E> =
                    BitReader::new(Cursor::new(w.into_writer().into_inner()));
                assert_eq!(r.read_bit().unwrap(), true);
                while start < end {
                    assert_eq!(r.$r::<I>(bits).unwrap(), start);
                    start += I::ONE;
                }
                assert_eq!(r.$r::<I>(bits).unwrap(), end);
            }
        };
    }

    define_roundtrip!(
        test_writer_unsigned,
        UnsignedNumeric,
        write_var,
        read_unsigned_var
    );
    test_writer_unsigned::<_, BigEndian>(u8::MIN, u8::MAX, 8);
    test_writer_unsigned::<_, LittleEndian>(u8::MIN, u8::MAX, 8);

    define_roundtrip!(
        test_writer_signed,
        SignedNumeric,
        write_var,
        read_signed_var
    );
    test_writer_signed::<_, BigEndian>(i8::MIN, i8::MAX, 8);
    test_writer_signed::<_, LittleEndian>(i8::MIN, i8::MAX, 8);

    define_roundtrip!(
        test_reader_unsigned,
        UnsignedNumeric,
        write_unsigned_var,
        read_var
    );
    test_reader_unsigned::<_, BigEndian>(u8::MIN, u8::MAX, 8);
    test_reader_unsigned::<_, LittleEndian>(u8::MIN, u8::MAX, 8);

    define_roundtrip!(
        test_reader_signed,
        SignedNumeric,
        write_signed_var,
        read_var
    );
    test_reader_signed::<_, BigEndian>(i8::MIN, i8::MAX, 8);
    test_reader_signed::<_, LittleEndian>(i8::MIN, i8::MAX, 8);
}
