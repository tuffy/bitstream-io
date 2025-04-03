// Copyright 2017 Brian Langenberger
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

extern crate bitstream_io;

use bitstream_io::{
    BigEndian, BitRead, BitReader, BitWrite, BitWriter, Endianness, LittleEndian, Primitive,
};

fn roundtrip<E: Endianness>() {
    /*unsigned values*/
    for bits in 1..17 {
        let max = 1 << bits;
        let mut output: Vec<u8> = Vec::with_capacity(max);
        {
            let mut writer = BitWriter::<_, E>::new(&mut output);
            for value in 0..max {
                writer.write_var(bits, value as u32).unwrap();
            }
            writer.byte_align().unwrap();
        }
        {
            let mut reader = BitReader::<_, E>::new(output.as_slice());
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
            let mut writer = BitWriter::<_, E>::new(&mut output);
            for value in min..max {
                writer.write_signed_var(bits, value as i32).unwrap();
            }
            writer.byte_align().unwrap();
        }
        {
            let mut reader = BitReader::<_, E>::new(output.as_slice());
            for value in min..max {
                assert_eq!(reader.read_signed_var::<i32>(bits).unwrap(), value as i32);
            }
        }
    }
}

#[test]
fn test_rountrip_be() {
    roundtrip::<BigEndian>();
}

#[test]
fn test_roundtrip_le() {
    roundtrip::<LittleEndian>();
}

fn unary<E: Endianness>() {
    let mut output: Vec<u8> = Vec::new();
    {
        let mut writer = BitWriter::<_, E>::new(&mut output);
        for value in 0..1024 {
            writer.write_unary::<0>(value).unwrap();
        }
        writer.byte_align().unwrap();
    }
    {
        let mut c = output.as_slice();
        let mut reader = BitReader::<_, E>::new(&mut c);
        for value in 0..1024 {
            assert_eq!(reader.read_unary::<0>().unwrap(), value);
        }
    }

    let mut output: Vec<u8> = Vec::new();
    {
        let mut writer = BitWriter::<_, E>::new(&mut output);
        for value in 0..1024 {
            writer.write_unary::<1>(value).unwrap();
        }
        writer.byte_align().unwrap();
    }
    {
        let mut c = output.as_slice();
        let mut reader = BitReader::<_, E>::new(&mut c);
        for value in 0..1024 {
            assert_eq!(reader.read_unary::<1>().unwrap(), value);
        }
    }
}

#[test]
fn test_unary_roundtrip_be() {
    unary::<BigEndian>()
}

#[test]
fn test_unary_roundtrip_le() {
    unary::<LittleEndian>()
}

fn float<E, P>()
where
    E: Endianness,
    P: Primitive + From<u16> + core::fmt::Debug + core::cmp::PartialEq,
{
    let mut output: Vec<u8> = Vec::new();
    {
        let mut writer = BitWriter::<_, E>::new(&mut output);
        // these values should all be exact in floating-point
        for value in 0..1024 {
            writer.write_from(P::from(value)).unwrap();
        }
        writer.byte_align().unwrap();
    }
    {
        let mut c = output.as_slice();
        let mut reader = BitReader::<_, E>::new(&mut c);
        for value in 0..1024 {
            assert_eq!(reader.read_to::<P>().unwrap(), P::from(value));
        }
    }
}

#[test]
fn test_f32_roundtrip_be() {
    float::<BigEndian, f32>()
}

#[test]
fn test_f64_roundtrip_be() {
    float::<BigEndian, f64>()
}

#[test]
fn test_f32_roundtrip_le() {
    float::<LittleEndian, f32>()
}

#[test]
fn test_f64_roundtrip_le() {
    float::<LittleEndian, f64>()
}

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
                let mut w: BitWriter<_, E> = BitWriter::new(Vec::new());
                w.write_bit(true).unwrap();
                let mut i = start;
                while i < end {
                    w.$w(bits, i).unwrap();
                    i += I::ONE;
                }
                w.$w(bits, end).unwrap();

                w.byte_align().unwrap();

                let v = w.into_writer();
                let mut r: BitReader<_, E> = BitReader::new(v.as_slice());
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

#[test]
fn test_bit_count() {
    use bitstream_io::{BigEndian, BitRead, BitReader, BitWrite, BitWriter};

    let data: &[u8] = &[0b1111_0000];

    // read a count from a 4-bit field
    let count = BitReader::endian(data, BigEndian)
        .read_count::<0b1111>()
        .unwrap();
    assert_eq!(u32::from(count), 0b1111);

    // increment it by 1
    let count = count.try_map::<16, _>(|i| i.checked_add(1)).unwrap();
    assert_eq!(u32::from(count), 0b1111 + 1);

    // decrement it by 1
    let count = count.try_map::<0b1111, _>(|i| i.checked_sub(1)).unwrap();
    assert_eq!(u32::from(count), 0b1111);

    // write the count back to disk
    let mut w = BitWriter::endian(vec![], BigEndian);
    w.write_count::<0b1111>(count).unwrap();
    w.byte_align().unwrap();
    assert_eq!(w.into_writer(), data);
}
