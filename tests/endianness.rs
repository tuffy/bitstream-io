// Copyright 2017 Brian Langenberger
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

extern crate bitstream_io;

#[test]
fn test_big_endian() {
    use bitstream_io::{BigEndian, Endianness};

    let mut q: u32 = 0;
    let mut bits: u32 = 0;

    BigEndian::push_bits(&mut q, &mut bits, 2, 0b10);
    assert_eq!(q, BigEndian::align(0b10, 2));
    assert_eq!(BigEndian::unalign(q, 2), 0b10);
    BigEndian::push_bits(&mut q, &mut bits, 3, 0b110);
    assert_eq!(q, BigEndian::align(0b10_110, 2 + 3));
    assert_eq!(BigEndian::unalign(q, 2 + 3), 0b10_110);
    BigEndian::push_bits(&mut q, &mut bits, 5, 0b00111);
    assert_eq!(q, BigEndian::align(0b10_110_00111, 2 + 3 + 5));
    assert_eq!(BigEndian::unalign(q, 2 + 3 + 5), 0b10_110_00111);
    BigEndian::push_bits(&mut q, &mut bits, 3, 0b101);
    assert_eq!(q, BigEndian::align(0b10_110_00111_101, 2 + 3 + 5 + 3));
    assert_eq!(BigEndian::unalign(q, 2 + 3 + 5 + 3), 0b10_110_00111_101);
    BigEndian::push_bits(&mut q, &mut bits, 19, 0b101_0011_1011_1100_0001);
    assert_eq!(bits, 32);
    assert_eq!(q, 0b10_110_00111_101_101_0011_1011_1100_0001);

    assert_eq!(BigEndian::pop_bits(&mut q, &mut bits, 2), 0b10);
    assert_eq!(
        q,
        BigEndian::align(0b110_00111_101_101_0011_1011_1100_0001, 3 + 5 + 3 + 19)
    );
    assert_eq!(
        BigEndian::unalign(q, 3 + 5 + 3 + 19),
        0b110_00111_101_101_0011_1011_1100_0001
    );
    assert_eq!(BigEndian::pop_bits(&mut q, &mut bits, 3), 0b110);
    assert_eq!(
        q,
        BigEndian::align(0b00111_101_101_0011_1011_1100_0001, 5 + 3 + 19)
    );
    assert_eq!(
        BigEndian::unalign(q, 5 + 3 + 19),
        0b00111_101_101_0011_1011_1100_0001
    );
    assert_eq!(BigEndian::pop_bits(&mut q, &mut bits, 5), 0b00111);
    assert_eq!(q, BigEndian::align(0b101_101_0011_1011_1100_0001, 3 + 19));
    assert_eq!(BigEndian::unalign(q, 3 + 19), 0b101_101_0011_1011_1100_0001);
    assert_eq!(BigEndian::pop_bits(&mut q, &mut bits, 3), 0b101);
    assert_eq!(q, BigEndian::align(0b101_0011_1011_1100_0001, 19));
    assert_eq!(BigEndian::unalign(q, 19), 0b101_0011_1011_1100_0001);
    assert_eq!(
        BigEndian::pop_bits(&mut q, &mut bits, 19),
        0b101_0011_1011_1100_0001
    );
    assert_eq!(bits, 0);
    assert_eq!(q, 0);

    BigEndian::push_bits(&mut q, &mut bits, 2, 0b10);
    assert_eq!(BigEndian::pop_bits(&mut q, &mut bits, 2), 0b10);
    BigEndian::push_bits(&mut q, &mut bits, 3, 0b110);
    assert_eq!(BigEndian::pop_bits(&mut q, &mut bits, 3), 0b110);
    BigEndian::push_bits(&mut q, &mut bits, 5, 0b00111);
    assert_eq!(BigEndian::pop_bits(&mut q, &mut bits, 5), 0b00111);
    BigEndian::push_bits(&mut q, &mut bits, 3, 0b101);
    assert_eq!(BigEndian::pop_bits(&mut q, &mut bits, 3), 0b101);
    BigEndian::push_bits(&mut q, &mut bits, 19, 0b101_0011_1011_1100_0001);
    assert_eq!(
        BigEndian::pop_bits(&mut q, &mut bits, 19),
        0b101_0011_1011_1100_0001
    );
}

#[test]
fn test_little_endian() {
    use bitstream_io::{Endianness, LittleEndian};

    let mut q: u32 = 0;
    let mut bits: u32 = 0;

    LittleEndian::push_bits(&mut q, &mut bits, 2, 0b01);
    assert_eq!(q, LittleEndian::align(0b01, 2));
    assert_eq!(LittleEndian::unalign(q, 2), 0b01);
    LittleEndian::push_bits(&mut q, &mut bits, 3, 0b011);
    assert_eq!(q, LittleEndian::align(0b011_01, 2 + 3));
    assert_eq!(LittleEndian::unalign(q, 2 + 3), 0b011_01);
    LittleEndian::push_bits(&mut q, &mut bits, 5, 0b11100);
    assert_eq!(q, LittleEndian::align(0b11100_011_01, 2 + 3 + 5));
    assert_eq!(LittleEndian::unalign(q, 2 + 3 + 5), 0b11100_011_01);
    LittleEndian::push_bits(&mut q, &mut bits, 3, 0b101);
    assert_eq!(q, LittleEndian::align(0b101_11100_011_01, 2 + 3 + 5 + 3));
    assert_eq!(LittleEndian::unalign(q, 2 + 3 + 5 + 3), 0b101_11100_011_01);
    LittleEndian::push_bits(&mut q, &mut bits, 19, 0b100_0001_1110_1110_0101);
    assert_eq!(bits, 32);
    assert_eq!(q, 0b100_0001_1110_1110_0101_101_11100_011_01);

    assert_eq!(LittleEndian::pop_bits(&mut q, &mut bits, 2), 0b01);
    assert_eq!(
        q,
        LittleEndian::align(0b100_0001_1110_1110_0101_101_11100_011, 3 + 5 + 3 + 19)
    );
    assert_eq!(
        LittleEndian::unalign(q, 3 + 5 + 3 + 19),
        0b100_0001_1110_1110_0101_101_11100_011
    );
    assert_eq!(LittleEndian::pop_bits(&mut q, &mut bits, 3), 0b011);
    assert_eq!(
        q,
        LittleEndian::align(0b100_0001_1110_1110_0101_101_11100, 5 + 3 + 19)
    );
    assert_eq!(
        LittleEndian::unalign(q, 5 + 3 + 19),
        0b100_0001_1110_1110_0101_101_11100
    );
    assert_eq!(LittleEndian::pop_bits(&mut q, &mut bits, 5), 0b11100);
    assert_eq!(
        q,
        LittleEndian::align(0b100_0001_1110_1110_0101_101, 3 + 19)
    );
    assert_eq!(
        LittleEndian::unalign(q, 3 + 19),
        0b100_0001_1110_1110_0101_101
    );
    assert_eq!(LittleEndian::pop_bits(&mut q, &mut bits, 3), 0b101);
    assert_eq!(q, LittleEndian::align(0b100_0001_1110_1110_0101, 19));
    assert_eq!(LittleEndian::unalign(q, 19), 0b100_0001_1110_1110_0101);
    assert_eq!(
        LittleEndian::pop_bits(&mut q, &mut bits, 19),
        0b100_0001_1110_1110_0101
    );
    assert_eq!(bits, 0);
    assert_eq!(q, 0);

    LittleEndian::push_bits(&mut q, &mut bits, 2, 0b01);
    assert_eq!(LittleEndian::pop_bits(&mut q, &mut bits, 2), 0b01);
    LittleEndian::push_bits(&mut q, &mut bits, 3, 0b011);
    assert_eq!(LittleEndian::pop_bits(&mut q, &mut bits, 3), 0b011);
    LittleEndian::push_bits(&mut q, &mut bits, 5, 0b11100);
    assert_eq!(LittleEndian::pop_bits(&mut q, &mut bits, 5), 0b11100);
    LittleEndian::push_bits(&mut q, &mut bits, 3, 0b101);
    assert_eq!(LittleEndian::pop_bits(&mut q, &mut bits, 3), 0b101);
    LittleEndian::push_bits(&mut q, &mut bits, 19, 0b100_0001_1110_1110_0101);
    assert_eq!(
        LittleEndian::pop_bits(&mut q, &mut bits, 19),
        0b100_0001_1110_1110_0101
    );
}
