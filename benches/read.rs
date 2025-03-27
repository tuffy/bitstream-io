// Copyright 2017 Brian Langenberger
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use bitstream_io::{BigEndian, BitRead, BitReader, Endianness, LittleEndian};

fn main() {
    divan::main();
}

fn bytes() -> impl std::io::Read {
    use std::io::Read;

    std::io::repeat(0b10100100).take(112972074)
}

#[divan::bench]
fn be_bits() {
    bits::<BigEndian>();
}

#[divan::bench]
fn le_bits() {
    bits::<LittleEndian>();
}

#[divan::bench]
fn be_partials() {
    partials::<BigEndian>();
}

#[divan::bench]
fn le_partials() {
    partials::<LittleEndian>();
}

#[divan::bench]
fn be_wholes() {
    wholes::<BigEndian>();
}

#[divan::bench]
fn le_wholes() {
    wholes::<LittleEndian>();
}

#[divan::bench]
fn be_to() {
    to::<BigEndian>();
}

#[divan::bench]
fn le_to() {
    to::<LittleEndian>();
}

#[divan::bench]
fn be_unary() {
    unaries::<BigEndian>();
}

#[divan::bench]
fn le_unary() {
    unaries::<LittleEndian>();
}

#[divan::bench]
fn be_off_by_1() {
    off_by_1::<BigEndian>();
}

#[divan::bench]
fn le_off_by_1() {
    off_by_1::<LittleEndian>();
}

fn bits<E: Endianness>() {
    let mut bits: u32 = 0;
    let mut reader = BitReader::<_, E>::new(bytes());

    while let Ok(bit) = reader.read_bit() {
        bits += u32::from(bit);
    }

    let _ = bits;
}

fn partials<E: Endianness>() {
    let mut values: u32 = 0;
    let mut reader = BitReader::<_, E>::new(bytes());

    while let Ok(value) = reader.read::<7, u32>() {
        values += value;
    }

    let _ = values;
}

fn wholes<E: Endianness>() {
    let mut values: u32 = 0;
    let mut reader = BitReader::<_, E>::new(bytes());

    while let Ok(value) = reader.read::<32, u32>() {
        values += value;
    }

    let _ = values;
}

fn to<E: Endianness>() {
    let mut values: u32 = 0;
    let mut reader = BitReader::<_, E>::new(bytes());

    while let Ok(value) = reader.read_to::<u32>() {
        values += value;
    }

    let _ = values;
}

fn unaries<E: Endianness>() {
    let mut values: u32 = 0;
    let mut reader = BitReader::<_, E>::new(bytes());

    while let Ok(value) = reader.read_unary::<1>() {
        values += value;
    }

    let _ = values;
}

fn off_by_1<E: Endianness>() {
    let mut values: u32 = 0;
    let mut reader = BitReader::<_, E>::new(bytes());

    let _ = reader.read_bit();

    while let Ok(value) = reader.read::<32, u32>() {
        values += value;
    }

    let _ = values;
}
