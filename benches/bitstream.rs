use bitstream_io::{BigEndian, BitRead, BitReader, LittleEndian, Endianness};

fn main() {
    divan::main();
}

fn bytes() -> impl std::io::Read {
    use std::io::Read;

    std::io::repeat(0b10100100).take(112972074)
}

#[divan::bench]
fn read_be_bits() {
    read_bits::<BigEndian>();
}

#[divan::bench]
fn read_le_bits() {
    read_bits::<LittleEndian>();
}

#[divan::bench]
fn read_be_partials() {
    read_partials::<BigEndian>();
}

#[divan::bench]
fn read_le_partials() {
    read_partials::<LittleEndian>();
}

#[divan::bench]
fn read_be_wholes() {
    read_wholes::<BigEndian>();
}

#[divan::bench]
fn read_le_wholes() {
    read_wholes::<LittleEndian>();
}

#[divan::bench]
fn read_be_to() {
    read_to::<BigEndian>();
}

#[divan::bench]
fn read_le_to() {
    read_to::<LittleEndian>();
}

#[divan::bench]
fn read_be_unary() {
    read_unaries::<BigEndian>();
}

#[divan::bench]
fn read_le_unary() {
    read_unaries::<LittleEndian>();
}

fn read_bits<E: Endianness>() {
    let mut bits: u32 = 0;
    let mut reader = BitReader::<_, E>::new(bytes());

    while let Ok(bit) = reader.read_bit() {
        bits += u32::from(bit);
    }

    let _ = bits;
}

fn read_partials<E: Endianness>() {
    let mut values: u32 = 0;
    let mut reader = BitReader::<_, E>::new(bytes());

    while let Ok(value) = reader.read::<7, u32>() {
        values += value;
    }

    let _ = values;
}

fn read_wholes<E: Endianness>() {
    let mut values: u32 = 0;
    let mut reader = BitReader::<_, E>::new(bytes());

    while let Ok(value) = reader.read::<32, u32>() {
        values += value;
    }

    let _ = values;
}

fn read_to<E: Endianness>() {
    let mut values: u32 = 0;
    let mut reader = BitReader::<_, E>::new(bytes());

    while let Ok(value) = reader.read_to::<u32>() {
        values += value;
    }

    let _ = values;
}

fn read_unaries<E: Endianness>() {
    let mut values: u32 = 0;
    let mut reader = BitReader::<_, E>::new(bytes());

    while let Ok(value) = reader.read_unary::<1>() {
        values += value;
    }

    let _ = values;
}
