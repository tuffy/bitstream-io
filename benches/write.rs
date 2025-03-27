// Copyright 2017 Brian Langenberger
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use bitstream_io::{BigEndian, BitWrite, BitWriter, Endianness, LittleEndian};

const TOTAL_BYTES: usize = 112972072;

#[derive(Default)]
struct ByteCounter {
    bytes: usize,
}

impl std::io::Write for ByteCounter {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.bytes += buf.len();
        Ok(buf.len())
    }

    #[inline]
    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

fn main() {
    divan::main();
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
fn be_off_by_1() {
    off_by_1::<BigEndian>();
}

#[divan::bench]
fn le_off_by_1() {
    off_by_1::<LittleEndian>();
}

#[divan::bench]
fn be_unary() {
    unaries::<BigEndian>();
}

#[divan::bench]
fn le_unary() {
    unaries::<LittleEndian>();
}

fn bits<E: Endianness>() {
    let mut writer = BitWriter::<_, E>::new(ByteCounter::default());
    let bits = [true, false, true, false, false, true, false, false];
    bits.iter()
        .cycle()
        .copied()
        .take(TOTAL_BYTES * 8)
        .try_for_each(|b| writer.write_bit(b))
        .unwrap();
    // try to do something to keep the optimizer
    // from just elminating the whole thing
    assert!(writer.into_writer().bytes == TOTAL_BYTES);
}

fn partials<E: Endianness>() {
    let mut writer = BitWriter::<_, E>::new(ByteCounter::default());
    std::iter::repeat(0b01001100)
        .take((TOTAL_BYTES * 8) / 7)
        .try_for_each(|b| writer.write::<7, u32>(b))
        .unwrap();
    assert!(writer.into_writer().bytes > 0);
}

fn wholes<E: Endianness>() {
    let mut writer = BitWriter::<_, E>::new(ByteCounter::default());
    std::iter::repeat(0b01001100_11011011_00000000_11111111)
        .take(TOTAL_BYTES / 4)
        .try_for_each(|b| writer.write::<32, u32>(b))
        .unwrap();
    assert!(writer.into_writer().bytes == TOTAL_BYTES);
}

fn off_by_1<E: Endianness>() {
    let mut writer = BitWriter::<_, E>::new(ByteCounter::default());

    writer.write_bit(true).unwrap();
    std::iter::repeat(0b01001100_11011011_00000000_11111111)
        .take(TOTAL_BYTES / 4)
        .try_for_each(|b| writer.write::<32, u32>(b))
        .unwrap();
    writer.byte_align().unwrap();
    assert!(writer.into_writer().bytes == TOTAL_BYTES + 1);
}

fn unaries<E: Endianness>() {
    let mut writer = BitWriter::<_, E>::new(ByteCounter::default());
    let values = [0, 9, 4, 5, 3, 7, 2];
    values
        .iter()
        .cycle()
        .copied()
        .take(TOTAL_BYTES * 2)
        .try_for_each(|v| writer.write_unary::<1>(v))
        .unwrap();
    assert!(writer.into_writer().bytes > 0);
}
