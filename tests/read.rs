// Copyright 2017 Brian Langenberger
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

extern crate bitstream_io;

#[cfg(not(feature = "std"))]
use core2::io::{self};

#[cfg(feature = "std")]
use std::io::{self};

#[test]
fn test_queue_pop_be() {
    use bitstream_io::{BitSourceRefill, BE};

    let mut q: BitSourceRefill<BE, u8> = BitSourceRefill::default();
    assert_eq!(q.pop_bit(|| Ok::<_, ()>(0b10110001)), Ok(true));
    assert_eq!(q.pop_bit(|| panic!()), Ok::<bool, ()>(false));
    assert_eq!(q.pop_bit(|| panic!()), Ok::<bool, ()>(true));
    assert_eq!(q.pop_bit(|| panic!()), Ok::<bool, ()>(true));
    assert_eq!(q.pop_bit(|| panic!()), Ok::<bool, ()>(false));
    assert_eq!(q.pop_bit(|| panic!()), Ok::<bool, ()>(false));
    assert_eq!(q.pop_bit(|| panic!()), Ok::<bool, ()>(false));
    assert_eq!(q.pop_bit(|| panic!()), Ok::<bool, ()>(true));
    assert_eq!(q.pop_bit(|| Err(())), Err(()));
}

#[test]
fn test_queue_unary_be() {
    use bitstream_io::{BitSourceRefill, BE};

    assert_eq!(
        BitSourceRefill::<BE, u8>::default().pop_unary::<0, _, _>(|| Ok::<_, ()>(0b00000000)),
        Ok(0),
    );
    assert_eq!(
        BitSourceRefill::<BE, u8>::default().pop_unary::<0, _, _>(|| Ok::<_, ()>(0b10000000)),
        Ok(1),
    );
    assert_eq!(
        BitSourceRefill::<BE, u8>::default().pop_unary::<0, _, _>(|| Ok::<_, ()>(0b11000000)),
        Ok(2),
    );
    assert_eq!(
        BitSourceRefill::<BE, u8>::default().pop_unary::<0, _, _>(|| Ok::<_, ()>(0b11100000)),
        Ok(3),
    );
    assert_eq!(
        BitSourceRefill::<BE, u8>::default().pop_unary::<0, _, _>(|| Ok::<_, ()>(0b11110000)),
        Ok(4),
    );
    assert_eq!(
        BitSourceRefill::<BE, u8>::default().pop_unary::<0, _, _>(|| Ok::<_, ()>(0b11111000)),
        Ok(5),
    );
    assert_eq!(
        BitSourceRefill::<BE, u8>::default().pop_unary::<0, _, _>(|| Ok::<_, ()>(0b11111100)),
        Ok(6),
    );
    assert_eq!(
        BitSourceRefill::<BE, u8>::default().pop_unary::<0, _, _>(|| Ok::<_, ()>(0b11111110)),
        Ok(7),
    );

    assert_eq!(
        BitSourceRefill::<BE, u8>::default().pop_unary::<1, _, _>(|| Ok::<_, ()>(0b11111111)),
        Ok(0),
    );
    assert_eq!(
        BitSourceRefill::<BE, u8>::default().pop_unary::<1, _, _>(|| Ok::<_, ()>(0b01111111)),
        Ok(1),
    );
    assert_eq!(
        BitSourceRefill::<BE, u8>::default().pop_unary::<1, _, _>(|| Ok::<_, ()>(0b00111111)),
        Ok(2),
    );
    assert_eq!(
        BitSourceRefill::<BE, u8>::default().pop_unary::<1, _, _>(|| Ok::<_, ()>(0b00011111)),
        Ok(3),
    );
    assert_eq!(
        BitSourceRefill::<BE, u8>::default().pop_unary::<1, _, _>(|| Ok::<_, ()>(0b00001111)),
        Ok(4),
    );
    assert_eq!(
        BitSourceRefill::<BE, u8>::default().pop_unary::<1, _, _>(|| Ok::<_, ()>(0b00000111)),
        Ok(5),
    );
    assert_eq!(
        BitSourceRefill::<BE, u8>::default().pop_unary::<1, _, _>(|| Ok::<_, ()>(0b00000011)),
        Ok(6),
    );
    assert_eq!(
        BitSourceRefill::<BE, u8>::default().pop_unary::<1, _, _>(|| Ok::<_, ()>(0b00000001)),
        Ok(7),
    );

    // unary value that spans bytes
    let mut r = BitSourceRefill::<BE, u8>::default();
    assert_eq!(r.pop_bit(|| Ok::<_, ()>(0b11111111)), Ok(true));
    assert_eq!(
        r.pop_unary::<0, _, _>(|| Ok::<_, ()>(0b11111101)),
        Ok(7 + 6)
    );
    assert_eq!(r.pop_bit(|| panic!()), Ok::<_, ()>(true));

    let mut r = BitSourceRefill::<BE, u8>::default();
    assert_eq!(r.pop_bit(|| Ok::<_, ()>(0b00000000)), Ok(false));
    assert_eq!(
        r.pop_unary::<1, _, _>(|| Ok::<_, ()>(0b00000010)),
        Ok(7 + 6)
    );
    assert_eq!(r.pop_bit(|| panic!()), Ok::<_, ()>(false));

    let mut bytes = vec![0b11111111, 0b11111111, 0b11111101];
    let mut r = BitSourceRefill::<BE, u8>::default();
    assert_eq!(r.pop_bit(|| Ok::<u8, ()>(bytes.remove(0))), Ok(true));
    assert_eq!(
        r.pop_unary::<0, _, _>(|| Ok::<u8, ()>(bytes.remove(0))),
        Ok(7 + 8 + 6)
    );
    assert_eq!(r.pop_bit(|| Ok::<u8, ()>(bytes.remove(0))), Ok(true));

    let mut bytes = vec![0b00000000, 0b00000000, 0b00000010];
    let mut r = BitSourceRefill::<BE, u8>::default();
    assert_eq!(r.pop_bit(|| Ok::<u8, ()>(bytes.remove(0))), Ok(false));
    assert_eq!(
        r.pop_unary::<1, _, _>(|| Ok::<u8, ()>(bytes.remove(0))),
        Ok(7 + 8 + 6)
    );
    assert_eq!(r.pop_bit(|| Ok::<u8, ()>(bytes.remove(0))), Ok(false));
}

#[test]
fn test_queue_pop_le() {
    use bitstream_io::{BitSourceRefill, LE};

    let mut q: BitSourceRefill<LE, u8> = BitSourceRefill::default();

    assert_eq!(q.pop_bit(|| Ok::<_, ()>(0b10110001)), Ok(true));
    assert_eq!(q.pop_bit(|| panic!()), Ok::<bool, ()>(false));
    assert_eq!(q.pop_bit(|| panic!()), Ok::<bool, ()>(false));
    assert_eq!(q.pop_bit(|| panic!()), Ok::<bool, ()>(false));
    assert_eq!(q.pop_bit(|| panic!()), Ok::<bool, ()>(true));
    assert_eq!(q.pop_bit(|| panic!()), Ok::<bool, ()>(true));
    assert_eq!(q.pop_bit(|| panic!()), Ok::<bool, ()>(false));
    assert_eq!(q.pop_bit(|| panic!()), Ok::<bool, ()>(true));
    assert_eq!(q.pop_bit(|| Err(())), Err(()));
}

#[test]
fn test_queue_unary_le() {
    use bitstream_io::{BitSourceRefill, LE};

    assert_eq!(
        BitSourceRefill::<LE, u8>::default().pop_unary::<0, _, _>(|| Ok::<_, ()>(0b00000000)),
        Ok(0),
    );
    assert_eq!(
        BitSourceRefill::<LE, u8>::default().pop_unary::<0, _, _>(|| Ok::<_, ()>(0b00000001)),
        Ok(1),
    );
    assert_eq!(
        BitSourceRefill::<LE, u8>::default().pop_unary::<0, _, _>(|| Ok::<_, ()>(0b00000011)),
        Ok(2),
    );
    assert_eq!(
        BitSourceRefill::<LE, u8>::default().pop_unary::<0, _, _>(|| Ok::<_, ()>(0b00000111)),
        Ok(3),
    );
    assert_eq!(
        BitSourceRefill::<LE, u8>::default().pop_unary::<0, _, _>(|| Ok::<_, ()>(0b00001111)),
        Ok(4),
    );
    assert_eq!(
        BitSourceRefill::<LE, u8>::default().pop_unary::<0, _, _>(|| Ok::<_, ()>(0b00011111)),
        Ok(5),
    );
    assert_eq!(
        BitSourceRefill::<LE, u8>::default().pop_unary::<0, _, _>(|| Ok::<_, ()>(0b00111111)),
        Ok(6),
    );
    assert_eq!(
        BitSourceRefill::<LE, u8>::default().pop_unary::<0, _, _>(|| Ok::<_, ()>(0b01111111)),
        Ok(7),
    );

    assert_eq!(
        BitSourceRefill::<LE, u8>::default().pop_unary::<1, _, _>(|| Ok::<_, ()>(0b11111111)),
        Ok(0),
    );
    assert_eq!(
        BitSourceRefill::<LE, u8>::default().pop_unary::<1, _, _>(|| Ok::<_, ()>(0b11111110)),
        Ok(1),
    );
    assert_eq!(
        BitSourceRefill::<LE, u8>::default().pop_unary::<1, _, _>(|| Ok::<_, ()>(0b11111100)),
        Ok(2),
    );
    assert_eq!(
        BitSourceRefill::<LE, u8>::default().pop_unary::<1, _, _>(|| Ok::<_, ()>(0b11111000)),
        Ok(3),
    );
    assert_eq!(
        BitSourceRefill::<LE, u8>::default().pop_unary::<1, _, _>(|| Ok::<_, ()>(0b11110000)),
        Ok(4),
    );
    assert_eq!(
        BitSourceRefill::<LE, u8>::default().pop_unary::<1, _, _>(|| Ok::<_, ()>(0b11100000)),
        Ok(5),
    );
    assert_eq!(
        BitSourceRefill::<LE, u8>::default().pop_unary::<1, _, _>(|| Ok::<_, ()>(0b11000000)),
        Ok(6),
    );
    assert_eq!(
        BitSourceRefill::<LE, u8>::default().pop_unary::<1, _, _>(|| Ok::<_, ()>(0b10000000)),
        Ok(7),
    );

    // unary value that spans bytes
    let mut r = BitSourceRefill::<LE, u8>::default();
    assert_eq!(r.pop_bit(|| Ok::<_, ()>(0b11111111)), Ok(true));
    assert_eq!(
        r.pop_unary::<0, _, _>(|| Ok::<_, ()>(0b10111111)),
        Ok(7 + 6)
    );
    assert_eq!(r.pop_bit(|| panic!()), Ok::<_, ()>(true));

    let mut r = BitSourceRefill::<LE, u8>::default();
    assert_eq!(r.pop_bit(|| Ok::<_, ()>(0b00000000)), Ok(false));
    assert_eq!(
        r.pop_unary::<1, _, _>(|| Ok::<_, ()>(0b01000000)),
        Ok(7 + 6)
    );
    assert_eq!(r.pop_bit(|| panic!()), Ok::<_, ()>(false));

    let mut bytes = vec![0b11111111, 0b11111111, 0b10111111];
    let mut r = BitSourceRefill::<LE, u8>::default();
    assert_eq!(r.pop_bit(|| Ok::<u8, ()>(bytes.remove(0))), Ok(true));
    assert_eq!(
        r.pop_unary::<0, _, _>(|| Ok::<u8, ()>(bytes.remove(0))),
        Ok(7 + 8 + 6)
    );
    assert_eq!(r.pop_bit(|| Ok::<u8, ()>(bytes.remove(0))), Ok(true));

    let mut bytes = vec![0b00000000, 0b00000000, 0b01000000];
    let mut r = BitSourceRefill::<LE, u8>::default();
    assert_eq!(r.pop_bit(|| Ok::<u8, ()>(bytes.remove(0))), Ok(false));
    assert_eq!(
        r.pop_unary::<1, _, _>(|| Ok::<u8, ()>(bytes.remove(0))),
        Ok(7 + 8 + 6)
    );
    assert_eq!(r.pop_bit(|| Ok::<u8, ()>(bytes.remove(0))), Ok(false));
}

#[test]
fn test_reader_be() {
    use bitstream_io::{BigEndian, BitRead, BitReader};

    let actual_data: [u8; 4] = [0xB1, 0xED, 0x3B, 0xC1];

    /*reading individual bits*/
    let mut r = BitReader::endian(actual_data.as_slice(), BigEndian);
    assert_eq!(r.read_bit().unwrap(), true);
    assert_eq!(r.read_bit().unwrap(), false);
    assert_eq!(r.read_bit().unwrap(), true);
    assert_eq!(r.read_bit().unwrap(), true);
    assert_eq!(r.read_bit().unwrap(), false);
    assert_eq!(r.read_bit().unwrap(), false);
    assert_eq!(r.read_bit().unwrap(), false);
    assert_eq!(r.read_bit().unwrap(), true);
    assert_eq!(r.read_bit().unwrap(), true);
    assert_eq!(r.read_bit().unwrap(), true);
    assert_eq!(r.read_bit().unwrap(), true);
    assert_eq!(r.read_bit().unwrap(), false);
    assert_eq!(r.read_bit().unwrap(), true);
    assert_eq!(r.read_bit().unwrap(), true);
    assert_eq!(r.read_bit().unwrap(), false);
    assert_eq!(r.read_bit().unwrap(), true);

    /*reading unsigned values*/
    let mut r = BitReader::endian(actual_data.as_slice(), BigEndian);
    assert!(r.byte_aligned());
    assert_eq!(r.read_var::<u32>(2).unwrap(), 2);
    assert!(!r.byte_aligned());
    assert_eq!(r.read_var::<u32>(3).unwrap(), 6);
    assert!(!r.byte_aligned());
    assert_eq!(r.read_var::<u32>(5).unwrap(), 7);
    assert!(!r.byte_aligned());
    assert_eq!(r.read_var::<u32>(3).unwrap(), 5);
    assert!(!r.byte_aligned());
    assert_eq!(r.read_var::<u32>(19).unwrap(), 0x53BC1);
    assert!(r.byte_aligned());
    assert!(r.read_var::<u32>(1).is_err());

    /*reading const unsigned values*/
    let mut r = BitReader::endian(actual_data.as_slice(), BigEndian);
    assert!(r.byte_aligned());
    assert_eq!(r.read::<2, u32>().unwrap(), 2);
    assert!(!r.byte_aligned());
    assert_eq!(r.read::<3, u32>().unwrap(), 6);
    assert!(!r.byte_aligned());
    assert_eq!(r.read::<5, u32>().unwrap(), 7);
    assert!(!r.byte_aligned());
    assert_eq!(r.read::<3, u32>().unwrap(), 5);
    assert!(!r.byte_aligned());
    assert_eq!(r.read::<19, u32>().unwrap(), 0x53BC1);
    assert!(r.byte_aligned());
    assert!(r.read::<1, u32>().is_err());

    /*skipping bits*/
    let mut r = BitReader::endian(actual_data.as_slice(), BigEndian);
    assert_eq!(r.read_var::<u32>(2).unwrap(), 2);
    assert!(r.skip(3).is_ok());
    assert_eq!(r.read_var::<u32>(5).unwrap(), 7);
    assert!(r.skip(3).is_ok());
    assert_eq!(r.read_var::<u32>(19).unwrap(), 0x53BC1);

    /*reading signed values*/
    let mut r = BitReader::endian(actual_data.as_slice(), BigEndian);
    assert_eq!(r.read_signed_var::<i32>(2).unwrap(), -2);
    assert_eq!(r.read_signed_var::<i32>(3).unwrap(), -2);
    assert_eq!(r.read_signed_var::<i32>(5).unwrap(), 7);
    assert_eq!(r.read_signed_var::<i32>(3).unwrap(), -3);
    assert_eq!(r.read_signed_var::<i32>(19).unwrap(), -181311);

    /*reading const signed values*/
    let mut r = BitReader::endian(actual_data.as_slice(), BigEndian);
    assert_eq!(r.read_signed::<2, i32>().unwrap(), -2);
    assert_eq!(r.read_signed::<3, i32>().unwrap(), -2);
    assert_eq!(r.read_signed::<5, i32>().unwrap(), 7);
    assert_eq!(r.read_signed::<3, i32>().unwrap(), -3);
    assert_eq!(r.read_signed::<19, i32>().unwrap(), -181311);

    /*reading unary 0 values*/
    let mut r = BitReader::endian(actual_data.as_slice(), BigEndian);
    assert_eq!(r.read_unary::<0>().unwrap(), 1);
    assert_eq!(r.read_unary::<0>().unwrap(), 2);
    assert_eq!(r.read_unary::<0>().unwrap(), 0);
    assert_eq!(r.read_unary::<0>().unwrap(), 0);
    assert_eq!(r.read_unary::<0>().unwrap(), 4);

    /*reading unary 1 values*/
    let mut r = BitReader::endian(actual_data.as_slice(), BigEndian);
    assert_eq!(r.read_unary::<1>().unwrap(), 0);
    assert_eq!(r.read_unary::<1>().unwrap(), 1);
    assert_eq!(r.read_unary::<1>().unwrap(), 0);
    assert_eq!(r.read_unary::<1>().unwrap(), 3);
    assert_eq!(r.read_unary::<1>().unwrap(), 0);

    /*byte aligning*/
    let mut r = BitReader::endian(actual_data.as_slice(), BigEndian);
    assert_eq!(r.read_var::<u32>(3).unwrap(), 5);
    r.byte_align();
    assert_eq!(r.read_var::<u32>(3).unwrap(), 7);
    r.byte_align();
    r.byte_align();
    assert_eq!(r.read_var::<u32>(8).unwrap(), 59);
    r.byte_align();
    assert_eq!(r.read_var::<u32>(4).unwrap(), 12);

    /*reading bytes, aligned*/
    let mut r = BitReader::endian(actual_data.as_slice(), BigEndian);
    let mut sub_data = [0; 2];
    assert!(r.read_bytes(&mut sub_data).is_ok());
    assert_eq!(&sub_data, b"\xB1\xED");

    /*reading bytes, un-aligned*/
    let mut r = BitReader::endian(actual_data.as_slice(), BigEndian);
    let mut sub_data = [0; 2];
    assert_eq!(r.read_var::<u32>(4).unwrap(), 11);
    assert!(r.read_bytes(&mut sub_data).is_ok());
    assert_eq!(&sub_data, b"\x1E\xD3");
}

#[test]
fn test_edge_cases_be() {
    use bitstream_io::{BigEndian, BitRead, BitReader};

    let data: Vec<u8> = vec![
        0, 0, 0, 0, 255, 255, 255, 255, 128, 0, 0, 0, 127, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0,
        255, 255, 255, 255, 255, 255, 255, 255, 128, 0, 0, 0, 0, 0, 0, 0, 127, 255, 255, 255, 255,
        255, 255, 255,
    ];

    /*0 bit reads*/
    let mut r = BitReader::endian([255; 1].as_slice(), BigEndian);
    assert_eq!(r.read_var::<u8>(0).unwrap(), 0);
    assert_eq!(r.read_var::<u16>(0).unwrap(), 0);
    assert_eq!(r.read_var::<u32>(0).unwrap(), 0);
    assert_eq!(r.read_var::<u64>(0).unwrap(), 0);
    assert_eq!(r.read_var::<u8>(8).unwrap(), 255);

    let mut r = BitReader::endian([255; 1].as_slice(), BigEndian);
    assert_eq!(r.read::<0, u8>().unwrap(), 0);
    assert_eq!(r.read::<0, u16>().unwrap(), 0);
    assert_eq!(r.read::<0, u32>().unwrap(), 0);
    assert_eq!(r.read::<0, u64>().unwrap(), 0);
    assert_eq!(r.read::<8, u8>().unwrap(), 255);

    let mut r = BitReader::endian([255; 1].as_slice(), BigEndian);
    assert!(r.read_signed_var::<i8>(0).is_err());
    assert!(r.read_signed_var::<i16>(0).is_err());
    assert!(r.read_signed_var::<i32>(0).is_err());
    assert!(r.read_signed_var::<i64>(0).is_err());

    /*unsigned 32 and 64-bit values*/
    let mut r = BitReader::endian(data.as_slice(), BigEndian);
    assert_eq!(r.read_var::<u32>(32).unwrap(), 0);
    assert_eq!(r.read_var::<u32>(32).unwrap(), 4294967295);
    assert_eq!(r.read_var::<u32>(32).unwrap(), 2147483648);
    assert_eq!(r.read_var::<u32>(32).unwrap(), 2147483647);
    assert_eq!(r.read_var::<u64>(64).unwrap(), 0);
    assert_eq!(r.read_var::<u64>(64).unwrap(), 0xFFFFFFFFFFFFFFFF);
    assert_eq!(r.read_var::<u64>(64).unwrap(), 9223372036854775808);
    assert_eq!(r.read_var::<u64>(64).unwrap(), 9223372036854775807);

    let mut r = BitReader::endian(data.as_slice(), BigEndian);
    assert_eq!(r.read::<32, u32>().unwrap(), 0);
    assert_eq!(r.read::<32, u32>().unwrap(), 4294967295);
    assert_eq!(r.read::<32, u32>().unwrap(), 2147483648);
    assert_eq!(r.read::<32, u32>().unwrap(), 2147483647);
    assert_eq!(r.read::<64, u64>().unwrap(), 0);
    assert_eq!(r.read::<64, u64>().unwrap(), 0xFFFFFFFFFFFFFFFF);
    assert_eq!(r.read::<64, u64>().unwrap(), 9223372036854775808);
    assert_eq!(r.read::<64, u64>().unwrap(), 9223372036854775807);

    /*signed 32 and 64-bit values*/
    let mut r = BitReader::endian(data.as_slice(), BigEndian);
    assert_eq!(r.read_signed_var::<i32>(32).unwrap(), 0);
    assert_eq!(r.read_signed_var::<i32>(32).unwrap(), -1);
    assert_eq!(r.read_signed_var::<i32>(32).unwrap(), -2147483648);
    assert_eq!(r.read_signed_var::<i32>(32).unwrap(), 2147483647);
    assert_eq!(r.read_signed_var::<i64>(64).unwrap(), 0);
    assert_eq!(r.read_signed_var::<i64>(64).unwrap(), -1);
    assert_eq!(r.read_signed_var::<i64>(64).unwrap(), -9223372036854775808);
    assert_eq!(r.read_signed_var::<i64>(64).unwrap(), 9223372036854775807);

    let mut r = BitReader::endian(data.as_slice(), BigEndian);
    assert_eq!(r.read_signed::<32, i32>().unwrap(), 0);
    assert_eq!(r.read_signed::<32, i32>().unwrap(), -1);
    assert_eq!(r.read_signed::<32, i32>().unwrap(), -2147483648);
    assert_eq!(r.read_signed::<32, i32>().unwrap(), 2147483647);
    assert_eq!(r.read_signed::<64, i64>().unwrap(), 0);
    assert_eq!(r.read_signed::<64, i64>().unwrap(), -1);
    assert_eq!(r.read_signed::<64, i64>().unwrap(), -9223372036854775808);
    assert_eq!(r.read_signed::<64, i64>().unwrap(), 9223372036854775807);
}

#[test]
fn test_reader_huffman_be() {
    use bitstream_io::define_huffman_tree;
    use bitstream_io::{BigEndian, BitRead, BitReader};

    define_huffman_tree!(SomeTree : i32 = [[[4, 3], 2], [1, 0]]);

    let actual_data: [u8; 4] = [0xB1, 0xED, 0x3B, 0xC1];
    let mut r = BitReader::endian(actual_data.as_slice(), BigEndian);

    assert_eq!(r.read_huffman::<SomeTree>().unwrap(), 1);
    assert_eq!(r.read_huffman::<SomeTree>().unwrap(), 0);
    assert_eq!(r.read_huffman::<SomeTree>().unwrap(), 4);
    assert_eq!(r.read_huffman::<SomeTree>().unwrap(), 0);
    assert_eq!(r.read_huffman::<SomeTree>().unwrap(), 0);
    assert_eq!(r.read_huffman::<SomeTree>().unwrap(), 2);
    assert_eq!(r.read_huffman::<SomeTree>().unwrap(), 1);
    assert_eq!(r.read_huffman::<SomeTree>().unwrap(), 1);
    assert_eq!(r.read_huffman::<SomeTree>().unwrap(), 2);
    assert_eq!(r.read_huffman::<SomeTree>().unwrap(), 0);
    assert_eq!(r.read_huffman::<SomeTree>().unwrap(), 2);
    assert_eq!(r.read_huffman::<SomeTree>().unwrap(), 0);
    assert_eq!(r.read_huffman::<SomeTree>().unwrap(), 1);
    assert_eq!(r.read_huffman::<SomeTree>().unwrap(), 4);
    assert_eq!(r.read_huffman::<SomeTree>().unwrap(), 2);
}

#[test]
fn test_reader_le() {
    use bitstream_io::{BitRead, BitReader, LittleEndian};

    let actual_data: [u8; 4] = [0xB1, 0xED, 0x3B, 0xC1];

    /*reading individual bits*/
    let mut r = BitReader::endian(actual_data.as_slice(), LittleEndian);
    assert_eq!(r.read_bit().unwrap(), true);
    assert_eq!(r.read_bit().unwrap(), false);
    assert_eq!(r.read_bit().unwrap(), false);
    assert_eq!(r.read_bit().unwrap(), false);
    assert_eq!(r.read_bit().unwrap(), true);
    assert_eq!(r.read_bit().unwrap(), true);
    assert_eq!(r.read_bit().unwrap(), false);
    assert_eq!(r.read_bit().unwrap(), true);
    assert_eq!(r.read_bit().unwrap(), true);
    assert_eq!(r.read_bit().unwrap(), false);
    assert_eq!(r.read_bit().unwrap(), true);
    assert_eq!(r.read_bit().unwrap(), true);
    assert_eq!(r.read_bit().unwrap(), false);
    assert_eq!(r.read_bit().unwrap(), true);
    assert_eq!(r.read_bit().unwrap(), true);
    assert_eq!(r.read_bit().unwrap(), true);

    /*reading unsigned values*/
    let mut r = BitReader::endian(actual_data.as_slice(), LittleEndian);
    assert!(r.byte_aligned());
    assert_eq!(r.read_var::<u32>(2).unwrap(), 1);
    assert!(!r.byte_aligned());
    assert_eq!(r.read_var::<u32>(3).unwrap(), 4);
    assert!(!r.byte_aligned());
    assert_eq!(r.read_var::<u32>(5).unwrap(), 13);
    assert!(!r.byte_aligned());
    assert_eq!(r.read_var::<u32>(3).unwrap(), 3);
    assert!(!r.byte_aligned());
    assert_eq!(r.read_var::<u32>(19).unwrap(), 0x609DF);
    assert!(r.byte_aligned());
    assert!(r.read_var::<u32>(1).is_err());

    /*reading const unsigned values*/
    let mut r = BitReader::endian(actual_data.as_slice(), LittleEndian);
    assert!(r.byte_aligned());
    assert_eq!(r.read::<2, u32>().unwrap(), 1);
    assert!(!r.byte_aligned());
    assert_eq!(r.read::<3, u32>().unwrap(), 4);
    assert!(!r.byte_aligned());
    assert_eq!(r.read::<5, u32>().unwrap(), 13);
    assert!(!r.byte_aligned());
    assert_eq!(r.read::<3, u32>().unwrap(), 3);
    assert!(!r.byte_aligned());
    assert_eq!(r.read::<19, u32>().unwrap(), 0x609DF);
    assert!(r.byte_aligned());
    assert!(r.read::<1, u32>().is_err());

    /*skipping bits*/
    let mut r = BitReader::endian(actual_data.as_slice(), LittleEndian);
    assert_eq!(r.read_var::<u32>(2).unwrap(), 1);
    assert!(r.skip(3).is_ok());
    assert_eq!(r.read_var::<u32>(5).unwrap(), 13);
    assert!(r.skip(3).is_ok());
    assert_eq!(r.read_var::<u32>(19).unwrap(), 0x609DF);

    /*reading signed values*/
    let mut r = BitReader::endian(actual_data.as_slice(), LittleEndian);
    assert_eq!(r.read_signed_var::<i32>(2).unwrap(), 1);
    assert_eq!(r.read_signed_var::<i32>(3).unwrap(), -4);
    assert_eq!(r.read_signed_var::<i32>(5).unwrap(), 13);
    assert_eq!(r.read_signed_var::<i32>(3).unwrap(), 3);
    assert_eq!(r.read_signed_var::<i32>(19).unwrap(), -128545);

    /*reading const signed values*/
    let mut r = BitReader::endian(actual_data.as_slice(), LittleEndian);
    assert_eq!(r.read_signed::<2, i32>().unwrap(), 1);
    assert_eq!(r.read_signed::<3, i32>().unwrap(), -4);
    assert_eq!(r.read_signed::<5, i32>().unwrap(), 13);
    assert_eq!(r.read_signed::<3, i32>().unwrap(), 3);
    assert_eq!(r.read_signed::<19, i32>().unwrap(), -128545);

    /*reading unary 0 values*/
    let mut r = BitReader::endian(actual_data.as_slice(), LittleEndian);
    assert_eq!(r.read_unary::<0>().unwrap(), 1);
    assert_eq!(r.read_unary::<0>().unwrap(), 0);
    assert_eq!(r.read_unary::<0>().unwrap(), 0);
    assert_eq!(r.read_unary::<0>().unwrap(), 2);
    assert_eq!(r.read_unary::<0>().unwrap(), 2);

    /*reading unary 1 values*/
    let mut r = BitReader::endian(actual_data.as_slice(), LittleEndian);
    assert_eq!(r.read_unary::<1>().unwrap(), 0);
    assert_eq!(r.read_unary::<1>().unwrap(), 3);
    assert_eq!(r.read_unary::<1>().unwrap(), 0);
    assert_eq!(r.read_unary::<1>().unwrap(), 1);
    assert_eq!(r.read_unary::<1>().unwrap(), 0);

    /*byte aligning*/
    let mut r = BitReader::endian(actual_data.as_slice(), LittleEndian);
    assert_eq!(r.read_var::<u32>(3).unwrap(), 1);
    r.byte_align();
    assert_eq!(r.read_var::<u32>(3).unwrap(), 5);
    r.byte_align();
    r.byte_align();
    assert_eq!(r.read_var::<u32>(8).unwrap(), 59);
    r.byte_align();
    assert_eq!(r.read_var::<u32>(4).unwrap(), 1);

    /*reading bytes, aligned*/
    let mut r = BitReader::endian(actual_data.as_slice(), LittleEndian);
    let mut sub_data = [0; 2];
    assert!(r.read_bytes(&mut sub_data).is_ok());
    assert_eq!(&sub_data, b"\xB1\xED");

    /*reading bytes, un-aligned*/
    let mut r = BitReader::endian(actual_data.as_slice(), LittleEndian);
    let mut sub_data = [0; 2];
    assert_eq!(r.read_var::<u32>(4).unwrap(), 1);
    assert!(r.read_bytes(&mut sub_data).is_ok());
    assert_eq!(&sub_data, b"\xDB\xBE");
}

#[test]
fn test_edge_cases_le() {
    use bitstream_io::{BitRead, BitReader, LittleEndian};

    let data: Vec<u8> = vec![
        0, 0, 0, 0, 255, 255, 255, 255, 0, 0, 0, 128, 255, 255, 255, 127, 0, 0, 0, 0, 0, 0, 0, 0,
        255, 255, 255, 255, 255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 128, 255, 255, 255, 255, 255,
        255, 255, 127,
    ];

    /*0 bit reads*/
    let mut r = BitReader::endian([255; 1].as_slice(), LittleEndian);
    assert_eq!(r.read_var::<u8>(0).unwrap(), 0);
    assert_eq!(r.read_var::<u16>(0).unwrap(), 0);
    assert_eq!(r.read_var::<u32>(0).unwrap(), 0);
    assert_eq!(r.read_var::<u64>(0).unwrap(), 0);
    assert_eq!(r.read_var::<u8>(8).unwrap(), 255);

    let mut r = BitReader::endian([255; 1].as_slice(), LittleEndian);
    assert_eq!(r.read::<0, u8>().unwrap(), 0);
    assert_eq!(r.read::<0, u16>().unwrap(), 0);
    assert_eq!(r.read::<0, u32>().unwrap(), 0);
    assert_eq!(r.read::<0, u64>().unwrap(), 0);
    assert_eq!(r.read::<8, u8>().unwrap(), 255);

    let mut r = BitReader::endian([255; 1].as_slice(), LittleEndian);
    assert!(r.read_signed_var::<i8>(0).is_err());
    assert!(r.read_signed_var::<i16>(0).is_err());
    assert!(r.read_signed_var::<i32>(0).is_err());
    assert!(r.read_signed_var::<i64>(0).is_err());

    /*unsigned 32 and 64-bit values*/
    let mut r = BitReader::endian(data.as_slice(), LittleEndian);
    assert_eq!(r.read_var::<u32>(32).unwrap(), 0);
    assert_eq!(r.read_var::<u32>(32).unwrap(), 4294967295);
    assert_eq!(r.read_var::<u32>(32).unwrap(), 2147483648);
    assert_eq!(r.read_var::<u32>(32).unwrap(), 2147483647);
    assert_eq!(r.read_var::<u64>(64).unwrap(), 0);
    assert_eq!(r.read_var::<u64>(64).unwrap(), 0xFFFFFFFFFFFFFFFF);
    assert_eq!(r.read_var::<u64>(64).unwrap(), 9223372036854775808);
    assert_eq!(r.read_var::<u64>(64).unwrap(), 9223372036854775807);

    let mut r = BitReader::endian(data.as_slice(), LittleEndian);
    assert_eq!(r.read::<32, u32>().unwrap(), 0);
    assert_eq!(r.read::<32, u32>().unwrap(), 4294967295);
    assert_eq!(r.read::<32, u32>().unwrap(), 2147483648);
    assert_eq!(r.read::<32, u32>().unwrap(), 2147483647);
    assert_eq!(r.read::<64, u64>().unwrap(), 0);
    assert_eq!(r.read::<64, u64>().unwrap(), 0xFFFFFFFFFFFFFFFF);
    assert_eq!(r.read::<64, u64>().unwrap(), 9223372036854775808);
    assert_eq!(r.read::<64, u64>().unwrap(), 9223372036854775807);

    let mut r = BitReader::endian(data.as_slice(), LittleEndian);
    assert_eq!(r.read_signed_var::<i32>(32).unwrap(), 0);
    assert_eq!(r.read_signed_var::<i32>(32).unwrap(), -1);
    assert_eq!(r.read_signed_var::<i32>(32).unwrap(), -2147483648);
    assert_eq!(r.read_signed_var::<i32>(32).unwrap(), 2147483647);
    assert_eq!(r.read_signed_var::<i64>(64).unwrap(), 0);
    assert_eq!(r.read_signed_var::<i64>(64).unwrap(), -1);
    assert_eq!(r.read_signed_var::<i64>(64).unwrap(), -9223372036854775808);
    assert_eq!(r.read_signed_var::<i64>(64).unwrap(), 9223372036854775807);

    let mut r = BitReader::endian(data.as_slice(), LittleEndian);
    assert_eq!(r.read_signed::<32, i32>().unwrap(), 0);
    assert_eq!(r.read_signed::<32, i32>().unwrap(), -1);
    assert_eq!(r.read_signed::<32, i32>().unwrap(), -2147483648);
    assert_eq!(r.read_signed::<32, i32>().unwrap(), 2147483647);
    assert_eq!(r.read_signed::<64, i64>().unwrap(), 0);
    assert_eq!(r.read_signed::<64, i64>().unwrap(), -1);
    assert_eq!(r.read_signed::<64, i64>().unwrap(), -9223372036854775808);
    assert_eq!(r.read_signed::<64, i64>().unwrap(), 9223372036854775807);
}

#[test]
fn test_reader_huffman_le() {
    use bitstream_io::define_huffman_tree;
    use bitstream_io::{BitRead, BitReader, LittleEndian};

    define_huffman_tree!(SomeTree : i32 = [[[4, 3], 2], [1, 0]]);

    let actual_data: [u8; 4] = [0xB1, 0xED, 0x3B, 0xC1];
    let mut r = BitReader::endian(actual_data.as_slice(), LittleEndian);

    assert_eq!(r.read_huffman::<SomeTree>().unwrap(), 1);
    assert_eq!(r.read_huffman::<SomeTree>().unwrap(), 3);
    assert_eq!(r.read_huffman::<SomeTree>().unwrap(), 1);
    assert_eq!(r.read_huffman::<SomeTree>().unwrap(), 0);
    assert_eq!(r.read_huffman::<SomeTree>().unwrap(), 2);
    assert_eq!(r.read_huffman::<SomeTree>().unwrap(), 1);
    assert_eq!(r.read_huffman::<SomeTree>().unwrap(), 0);
    assert_eq!(r.read_huffman::<SomeTree>().unwrap(), 0);
    assert_eq!(r.read_huffman::<SomeTree>().unwrap(), 1);
    assert_eq!(r.read_huffman::<SomeTree>().unwrap(), 0);
    assert_eq!(r.read_huffman::<SomeTree>().unwrap(), 1);
    assert_eq!(r.read_huffman::<SomeTree>().unwrap(), 2);
    assert_eq!(r.read_huffman::<SomeTree>().unwrap(), 4);
    assert_eq!(r.read_huffman::<SomeTree>().unwrap(), 3);
}

#[test]
fn test_reader_io_errors_be() {
    use bitstream_io::{BigEndian, BitRead, BitReader};
    use io::ErrorKind;

    let actual_data: [u8; 1] = [0xB1];

    /*individual bits*/
    let mut r = BitReader::endian(actual_data.as_slice(), BigEndian);
    assert!(r.read_bit().is_ok());
    assert!(r.read_bit().is_ok());
    assert!(r.read_bit().is_ok());
    assert!(r.read_bit().is_ok());
    assert!(r.read_bit().is_ok());
    assert!(r.read_bit().is_ok());
    assert!(r.read_bit().is_ok());
    assert!(r.read_bit().is_ok());
    assert_eq!(r.read_bit().unwrap_err().kind(), ErrorKind::UnexpectedEof);

    /*skipping bits*/
    let mut r = BitReader::endian(actual_data.as_slice(), BigEndian);
    assert!(r.read_var::<u32>(7).is_ok());
    assert_eq!(r.skip(5).unwrap_err().kind(), ErrorKind::UnexpectedEof);

    /*signed values*/
    let mut r = BitReader::endian(actual_data.as_slice(), BigEndian);
    assert!(r.read_signed_var::<i32>(2).is_ok());
    assert!(r.read_signed_var::<i32>(3).is_ok());
    assert_eq!(
        r.read_signed_var::<i32>(5).unwrap_err().kind(),
        ErrorKind::UnexpectedEof
    );

    let mut r = BitReader::endian(actual_data.as_slice(), BigEndian);
    assert!(r.read_signed::<2, i32>().is_ok());
    assert!(r.read_signed::<3, i32>().is_ok());
    assert_eq!(
        r.read_signed::<5, i32>().unwrap_err().kind(),
        ErrorKind::UnexpectedEof
    );

    /*unary 0 values*/
    let mut r = BitReader::endian(actual_data.as_slice(), BigEndian);
    assert!(r.read_unary::<0>().is_ok());
    assert!(r.read_unary::<0>().is_ok());
    assert!(r.read_unary::<0>().is_ok());
    assert!(r.read_unary::<0>().is_ok());
    assert_eq!(
        r.read_unary::<0>().unwrap_err().kind(),
        ErrorKind::UnexpectedEof
    );

    /*unary 1 values*/
    let mut r = BitReader::endian(actual_data.as_slice(), BigEndian);
    assert!(r.read_unary::<1>().is_ok());
    assert!(r.read_unary::<1>().is_ok());
    assert!(r.read_unary::<1>().is_ok());
    assert!(r.read_unary::<1>().is_ok());
    assert_eq!(
        r.read_unary::<1>().unwrap_err().kind(),
        ErrorKind::UnexpectedEof
    );

    /*reading bytes, aligned*/
    let mut r = BitReader::endian(actual_data.as_slice(), BigEndian);
    let mut sub_data = [0; 2];
    assert_eq!(
        r.read_bytes(&mut sub_data).unwrap_err().kind(),
        ErrorKind::UnexpectedEof
    );

    /*reading bytes, un-aligned*/
    let mut r = BitReader::endian(actual_data.as_slice(), BigEndian);
    let mut sub_data = [0; 2];
    assert!(r.read_var::<u32>(4).is_ok());
    assert_eq!(
        r.read_bytes(&mut sub_data).unwrap_err().kind(),
        ErrorKind::UnexpectedEof
    );
}

#[test]
fn test_reader_io_errors_le() {
    use bitstream_io::{BitRead, BitReader, LittleEndian};
    use io::ErrorKind;

    let actual_data: [u8; 1] = [0xB1];

    /*individual bits*/
    let mut r = BitReader::endian(actual_data.as_slice(), LittleEndian);
    assert!(r.read_bit().is_ok());
    assert!(r.read_bit().is_ok());
    assert!(r.read_bit().is_ok());
    assert!(r.read_bit().is_ok());
    assert!(r.read_bit().is_ok());
    assert!(r.read_bit().is_ok());
    assert!(r.read_bit().is_ok());
    assert!(r.read_bit().is_ok());
    assert_eq!(r.read_bit().unwrap_err().kind(), ErrorKind::UnexpectedEof);

    /*skipping bits*/
    let mut r = BitReader::endian(actual_data.as_slice(), LittleEndian);
    assert!(r.read_var::<u32>(7).is_ok());
    assert_eq!(r.skip(5).unwrap_err().kind(), ErrorKind::UnexpectedEof);

    /*signed values*/
    let mut r = BitReader::endian(actual_data.as_slice(), LittleEndian);
    assert!(r.read_signed_var::<i32>(2).is_ok());
    assert!(r.read_signed_var::<i32>(3).is_ok());
    assert_eq!(
        r.read_signed_var::<i32>(5).unwrap_err().kind(),
        ErrorKind::UnexpectedEof
    );

    let mut r = BitReader::endian(actual_data.as_slice(), LittleEndian);
    assert!(r.read_signed::<2, i32>().is_ok());
    assert!(r.read_signed::<3, i32>().is_ok());
    assert_eq!(
        r.read_signed::<5, i32>().unwrap_err().kind(),
        ErrorKind::UnexpectedEof
    );

    /*unary 0 values*/
    let mut r = BitReader::endian(actual_data.as_slice(), LittleEndian);
    assert!(r.read_unary::<0>().is_ok());
    assert!(r.read_unary::<0>().is_ok());
    assert!(r.read_unary::<0>().is_ok());
    assert!(r.read_unary::<0>().is_ok());
    assert_eq!(
        r.read_unary::<0>().unwrap_err().kind(),
        ErrorKind::UnexpectedEof
    );

    /*unary 1 values*/
    let mut r = BitReader::endian(actual_data.as_slice(), LittleEndian);
    assert!(r.read_unary::<1>().is_ok());
    assert!(r.read_unary::<1>().is_ok());
    assert!(r.read_unary::<1>().is_ok());
    assert!(r.read_unary::<1>().is_ok());
    assert_eq!(
        r.read_unary::<1>().unwrap_err().kind(),
        ErrorKind::UnexpectedEof
    );

    /*reading bytes, aligned*/
    let mut r = BitReader::endian(actual_data.as_slice(), LittleEndian);
    let mut sub_data = [0; 2];
    assert_eq!(
        r.read_bytes(&mut sub_data).unwrap_err().kind(),
        ErrorKind::UnexpectedEof
    );

    /*reading bytes, un-aligned*/
    let mut r = BitReader::endian(actual_data.as_slice(), LittleEndian);
    let mut sub_data = [0; 2];
    assert!(r.read_var::<u32>(4).is_ok());
    assert_eq!(
        r.read_bytes(&mut sub_data).unwrap_err().kind(),
        ErrorKind::UnexpectedEof
    );
}

#[test]
fn test_reader_bits_errors() {
    use bitstream_io::{BigEndian, BitRead, BitReader, LittleEndian};
    use io::ErrorKind;
    let actual_data = [0u8; 10];

    let mut r = BitReader::endian(actual_data.as_slice(), BigEndian);

    assert_eq!(
        r.read_var::<u8>(9).unwrap_err().kind(),
        ErrorKind::InvalidInput
    );
    assert_eq!(
        r.read_var::<u16>(17).unwrap_err().kind(),
        ErrorKind::InvalidInput
    );
    assert_eq!(
        r.read_var::<u32>(33).unwrap_err().kind(),
        ErrorKind::InvalidInput
    );
    assert_eq!(
        r.read_var::<u64>(65).unwrap_err().kind(),
        ErrorKind::InvalidInput
    );

    assert_eq!(
        r.read_signed_var::<i8>(9).unwrap_err().kind(),
        ErrorKind::InvalidInput
    );
    assert_eq!(
        r.read_signed_var::<i16>(17).unwrap_err().kind(),
        ErrorKind::InvalidInput
    );
    assert_eq!(
        r.read_signed_var::<i32>(33).unwrap_err().kind(),
        ErrorKind::InvalidInput
    );
    assert_eq!(
        r.read_signed_var::<i64>(65).unwrap_err().kind(),
        ErrorKind::InvalidInput
    );

    let mut r = BitReader::endian(actual_data.as_slice(), LittleEndian);

    assert_eq!(
        r.read_var::<u8>(9).unwrap_err().kind(),
        ErrorKind::InvalidInput
    );
    assert_eq!(
        r.read_var::<u16>(17).unwrap_err().kind(),
        ErrorKind::InvalidInput
    );
    assert_eq!(
        r.read_var::<u32>(33).unwrap_err().kind(),
        ErrorKind::InvalidInput
    );
    assert_eq!(
        r.read_var::<u64>(65).unwrap_err().kind(),
        ErrorKind::InvalidInput
    );

    assert_eq!(
        r.read_signed_var::<i8>(9).unwrap_err().kind(),
        ErrorKind::InvalidInput
    );
    assert_eq!(
        r.read_signed_var::<i16>(17).unwrap_err().kind(),
        ErrorKind::InvalidInput
    );
    assert_eq!(
        r.read_signed_var::<i32>(33).unwrap_err().kind(),
        ErrorKind::InvalidInput
    );
    assert_eq!(
        r.read_signed_var::<i64>(65).unwrap_err().kind(),
        ErrorKind::InvalidInput
    );
}

#[test]
fn test_clone() {
    use bitstream_io::{BigEndian, BitRead, BitReader};

    // Reading unsigned examples, cloning while unaligned.
    let actual_data: [u8; 4] = [0xB1, 0xED, 0x3B, 0xC1];
    let mut r = BitReader::endian(actual_data.as_slice(), BigEndian);
    assert!(r.byte_aligned());
    assert_eq!(r.read_var::<u32>(4).unwrap(), 0xB);
    let mut r2 = r.clone();
    assert!(!r.byte_aligned());
    assert_eq!(r.read_var::<u32>(4).unwrap(), 0x1);
    assert_eq!(r.read_var::<u32>(8).unwrap(), 0xED);
    assert!(!r2.byte_aligned());
    assert_eq!(r2.read_var::<u32>(4).unwrap(), 0x1);
    assert_eq!(r2.read_var::<u32>(8).unwrap(), 0xED);

    // Can still instantiate a BitReader when the backing std::io::Read is
    // !Clone.
    struct NotCloneRead<'a>(&'a [u8]);
    impl<'a> io::Read for NotCloneRead<'a> {
        fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
            self.0.read(buf)
        }
    }
    let _r = BitReader::endian(NotCloneRead(&actual_data[..]), BigEndian);
}

#[test]
fn test_read_bytes() {
    use bitstream_io::{BigEndian, BitRead, BitReader, LittleEndian};

    let actual_data: [u8; 4] = [0xB1, 0xED, 0x3B, 0xC1];
    let mut r = BitReader::endian(actual_data.as_slice(), BigEndian);
    let read_data: [u8; 4] = r.read_to().unwrap();
    assert_eq!(actual_data, read_data);

    let actual_data: [u8; 4] = [0xB1, 0xED, 0x3B, 0xC1];
    let mut r = BitReader::endian(actual_data.as_slice(), LittleEndian);
    let read_data: [u8; 4] = r.read_to().unwrap();
    assert_eq!(actual_data, read_data);
}

#[test]
fn test_large_reads() {
    use bitstream_io::{BigEndian, BitRead, BitReader, ByteRead, ByteReader, LittleEndian};

    for size in [0, 1, 4096, 4097, 10000] {
        let input = (0..255).cycle().take(size).collect::<Vec<u8>>();
        assert_eq!(input.len(), size);

        let mut r = BitReader::endian(input.as_slice(), BigEndian);
        let output = r.read_to_vec(size).unwrap();
        assert_eq!(input, output);

        let mut r = BitReader::endian(input.as_slice(), LittleEndian);
        let output = r.read_to_vec(size).unwrap();
        assert_eq!(input, output);

        let mut r = ByteReader::endian(input.as_slice(), BigEndian);
        let output = r.read_to_vec(size).unwrap();
        assert_eq!(input, output);

        let mut r = ByteReader::endian(input.as_slice(), LittleEndian);
        let output = r.read_to_vec(size).unwrap();
        assert_eq!(input, output);
    }

    let input: [u8; 5] = [0, 0, 0, 0, 0];

    let mut r = BitReader::endian(input.as_slice(), BigEndian);
    assert!(r.read_to_vec(usize::MAX).is_err());

    let mut r = BitReader::endian(input.as_slice(), LittleEndian);
    assert!(r.read_to_vec(usize::MAX).is_err());

    let mut r = ByteReader::endian(input.as_slice(), BigEndian);
    assert!(r.read_to_vec(usize::MAX).is_err());

    let mut r = ByteReader::endian(input.as_slice(), LittleEndian);
    assert!(r.read_to_vec(usize::MAX).is_err());
}

#[test]
fn test_bitcount_read() {
    use bitstream_io::{BigEndian, BitCount, BitRead, BitReader};

    // 1 bit count - reading 1 bit
    let bytes = &[0b1_1_000000];
    let mut reader = BitReader::endian(bytes.as_slice(), BigEndian);
    let count = reader.read_count::<0b1>().unwrap();
    assert_eq!(count, BitCount::new::<1>());
    assert_eq!(reader.read_counted::<1, u8>(count).unwrap(), 0b1);

    // 2 bits count - reading 3 bits
    let bytes = &[0b11_111_000];
    let mut reader = BitReader::endian(bytes.as_slice(), BigEndian);
    let count = reader.read_count::<0b11>().unwrap();
    assert_eq!(count, BitCount::new::<0b11>());
    assert_eq!(reader.read_counted::<0b11, u8>(count).unwrap(), 0b111);

    // 3 bits count - reading 7 bits
    let bytes = &[0b111_11111, 0b11_000000];
    let mut reader = BitReader::endian(bytes.as_slice(), BigEndian);
    let count = reader.read_count::<0b111>().unwrap();
    assert_eq!(count, BitCount::new::<0b111>());
    assert_eq!(reader.read_counted::<0b111, u8>(count).unwrap(), 0b11111_11);

    // 4 bits count - reading 15 bits
    let bytes = &[0b1111_1111, 0b11111111, 0b111_00000];
    let mut reader = BitReader::endian(bytes.as_slice(), BigEndian);
    let count = reader.read_count::<0b1111>().unwrap();
    assert_eq!(count, BitCount::new::<0b1111>());
    assert_eq!(
        reader.read_counted::<0b1111, u16>(count).unwrap(),
        0b1111_11111111_111
    );

    // 5 bits count - reading 31 bits
    let bytes = &[0b11111_111, 0b11111111, 0b11111111, 0b11111111, 0b1111_0000];
    let mut reader = BitReader::endian(bytes.as_slice(), BigEndian);
    let count = reader.read_count::<0b11111>().unwrap();
    assert_eq!(count, BitCount::new::<0b11111>());
    assert_eq!(
        reader.read_counted::<0b11111, u32>(count).unwrap(),
        0b111_11111111_11111111_11111111_1111,
    );

    // 6 bits count - reading 63 bits
    let bytes = &[
        0b111111_11,
        0b11111111,
        0b11111111,
        0b11111111,
        0b11111111,
        0b11111111,
        0b11111111,
        0b11111111,
        0b11111_000,
    ];
    let mut reader = BitReader::endian(bytes.as_slice(), BigEndian);
    let count = reader.read_count::<0b111111>().unwrap();
    assert_eq!(count, BitCount::new::<0b111111>());
    assert_eq!(
        reader.read_counted::<0b111111, u64>(count).unwrap(),
        0b11_11111111_11111111_11111111_11111111_11111111_11111111_11111111_11111,
    );

    // 7 bits count - reading 127 bits
    let bytes = &[
        0b1111111_1,
        0b11111111,
        0b11111111,
        0b11111111,
        0b11111111,
        0b11111111,
        0b11111111,
        0b11111111,
        0b11111111,
        0b11111111,
        0b11111111,
        0b11111111,
        0b11111111,
        0b11111111,
        0b11111111,
        0b11111111,
        0b111111_00,
    ];
    let mut reader = BitReader::endian(bytes.as_slice(), BigEndian);
    let count = reader.read_count::<0b1111111>().unwrap();
    assert_eq!(count, BitCount::new::<0b1111111>());
    assert_eq!(
        reader.read_counted::<0b1111111, u128>(count).unwrap(),
        0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
    );

    // We have to stop here because no primitive type gets any larger.
    // So while BitCount technically extends out to 32 bits,
    // it's not practical to get anywhere near that.
}
