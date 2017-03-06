// Copyright 2017 Brian Langenberger
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

extern crate bitstream_io;
use std::io::Cursor;

#[test]
fn test_read_queue_be() {
    use bitstream_io::{BitQueueBE, BitQueue};
    let mut q: BitQueueBE<u32> = BitQueueBE::new();
    assert!(q.is_empty());
    assert_eq!(q.len(), 0);
    q.push(8, 0xB1);
    assert_eq!(q.len(), 8);
    assert_eq!(q.pop(2), 2);
    assert_eq!(q.len(), 6);
    assert_eq!(q.pop(3), 6);
    assert_eq!(q.len(), 3);
    q.push(8, 0xED);
    assert_eq!(q.len(), 11);
    assert_eq!(q.pop(5), 7);
    assert_eq!(q.len(), 6);
    assert_eq!(q.pop(3), 5);
    q.push(8, 0x3B);
    q.push(8, 0xC1);
    assert_eq!(q.pop(19), 342977);
    assert!(q.is_empty());
    assert_eq!(q.value(), 0);
}

#[test]
fn test_read_queue_le() {
    use bitstream_io::{BitQueueLE, BitQueue};
    let mut q: BitQueueLE<u32> = BitQueueLE::new();
    assert!(q.is_empty());
    assert_eq!(q.len(), 0);
    q.push(8, 0xB1);
    assert_eq!(q.len(), 8);
    assert_eq!(q.pop(2), 1);
    assert_eq!(q.len(), 6);
    assert_eq!(q.pop(3), 4);
    assert_eq!(q.len(), 3);
    q.push(8, 0xED);
    assert_eq!(q.len(), 11);
    assert_eq!(q.pop(5), 13);
    assert_eq!(q.len(), 6);
    assert_eq!(q.pop(3), 3);
    q.push(8, 0x3B);
    q.push(8, 0xC1);
    assert_eq!(q.pop(19), 395743);
    assert!(q.is_empty());
    assert_eq!(q.value(), 0);
}

#[test]
fn test_reader_be() {
    use bitstream_io::BitReaderBE;
    use bitstream_io::BitRead;

    let actual_data: [u8;4] = [0xB1, 0xED, 0x3B, 0xC1];

    {
        /*reading individual bits*/
        let mut c = Cursor::new(&actual_data);
        let mut r = BitReaderBE::new(&mut c);
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
    }
    {
        /*reading unsigned values*/
        let mut c = Cursor::new(&actual_data);
        let mut r = BitReaderBE::new(&mut c);
        assert!(r.byte_aligned());
        assert_eq!(r.read::<u32>(2).unwrap(), 2);
        assert!(!r.byte_aligned());
        assert_eq!(r.read::<u32>(3).unwrap(), 6);
        assert!(!r.byte_aligned());
        assert_eq!(r.read::<u32>(5).unwrap(), 7);
        assert!(!r.byte_aligned());
        assert_eq!(r.read::<u32>(3).unwrap(), 5);
        assert!(!r.byte_aligned());
        assert_eq!(r.read::<u32>(19).unwrap(), 0x53BC1);
        assert!(r.byte_aligned());
        assert!(r.read::<u32>(1).is_err());
    }
    {
        /*skipping bits*/
        let mut c = Cursor::new(&actual_data);
        let mut r = BitReaderBE::new(&mut c);
        assert_eq!(r.read::<u32>(2).unwrap(), 2);
        assert!(r.skip(3).is_ok());
        assert_eq!(r.read::<u32>(5).unwrap(), 7);
        assert!(r.skip(3).is_ok());
        assert_eq!(r.read::<u32>(19).unwrap(), 0x53BC1);
    }
    {
        /*reading signed values*/
        let mut c = Cursor::new(&actual_data);
        let mut r = BitReaderBE::new(&mut c);
        assert_eq!(r.read_signed::<i32>(2).unwrap(), -2);
        assert_eq!(r.read_signed::<i32>(3).unwrap(), -2);
        assert_eq!(r.read_signed::<i32>(5).unwrap(), 7);
        assert_eq!(r.read_signed::<i32>(3).unwrap(), -3);
        assert_eq!(r.read_signed::<i32>(19).unwrap(), -181311);
    }
    {
        /*reading unary 0 values*/
        let mut c = Cursor::new(&actual_data);
        let mut r = BitReaderBE::new(&mut c);
        assert_eq!(r.read_unary0().unwrap(), 1);
        assert_eq!(r.read_unary0().unwrap(), 2);
        assert_eq!(r.read_unary0().unwrap(), 0);
        assert_eq!(r.read_unary0().unwrap(), 0);
        assert_eq!(r.read_unary0().unwrap(), 4);
    }
    {
        /*reading unary 1 values*/
        let mut c = Cursor::new(&actual_data);
        let mut r = BitReaderBE::new(&mut c);
        assert_eq!(r.read_unary1().unwrap(), 0);
        assert_eq!(r.read_unary1().unwrap(), 1);
        assert_eq!(r.read_unary1().unwrap(), 0);
        assert_eq!(r.read_unary1().unwrap(), 3);
        assert_eq!(r.read_unary1().unwrap(), 0);
    }
    {
        /*byte aligning*/
        let mut c = Cursor::new(&actual_data);
        let mut r = BitReaderBE::new(&mut c);
        assert_eq!(r.read::<u32>(3).unwrap(), 5);
        r.byte_align();
        assert_eq!(r.read::<u32>(3).unwrap(), 7);
        r.byte_align();
        r.byte_align();
        assert_eq!(r.read::<u32>(8).unwrap(), 59);
        r.byte_align();
        assert_eq!(r.read::<u32>(4).unwrap(), 12);
    }
    {
        /*reading bytes, aligned*/
        let mut c = Cursor::new(&actual_data);
        let mut r = BitReaderBE::new(&mut c);
        let mut sub_data = [0; 2];
        assert!(r.read_bytes(&mut sub_data).is_ok());
        assert_eq!(&sub_data, b"\xB1\xED");
    }
    {
        /*reading bytes, un-aligned*/
        let mut c = Cursor::new(&actual_data);
        let mut r = BitReaderBE::new(&mut c);
        let mut sub_data = [0; 2];
        assert_eq!(r.read::<u32>(4).unwrap(), 11);
        assert!(r.read_bytes(&mut sub_data).is_ok());
        assert_eq!(&sub_data, b"\x1E\xD3");
    }
}

#[test]
fn test_edge_cases_be() {
    use bitstream_io::BitReaderBE;
    use bitstream_io::BitRead;

    let data: Vec<u8> = vec![0, 0, 0, 0, 255, 255, 255, 255,
                             128, 0, 0, 0, 127, 255, 255, 255,
                             0, 0, 0, 0, 0, 0, 0, 0,
                             255, 255, 255, 255, 255, 255, 255, 255,
                             128, 0, 0, 0, 0, 0, 0, 0,
                             127, 255, 255, 255, 255, 255, 255, 255];

    {
        /*unsigned 32 and 64-bit values*/
        let mut c = Cursor::new(&data);
        let mut r = BitReaderBE::new(&mut c);
        assert_eq!(r.read::<u32>(32).unwrap(), 0);
        assert_eq!(r.read::<u32>(32).unwrap(), 4294967295);
        assert_eq!(r.read::<u32>(32).unwrap(), 2147483648);
        assert_eq!(r.read::<u32>(32).unwrap(), 2147483647);
        assert_eq!(r.read::<u64>(64).unwrap(), 0);
        assert_eq!(r.read::<u64>(64).unwrap(), 0xFFFFFFFFFFFFFFFF);
        assert_eq!(r.read::<u64>(64).unwrap(), 9223372036854775808);
        assert_eq!(r.read::<u64>(64).unwrap(), 9223372036854775807);
    }

    {
        /*signed 32 and 64-bit values*/
        let mut c = Cursor::new(&data);
        let mut r = BitReaderBE::new(&mut c);
        assert_eq!(r.read::<i32>(32).unwrap(), 0);
        assert_eq!(r.read::<i32>(32).unwrap(), -1);
        assert_eq!(r.read::<i32>(32).unwrap(), -2147483648);
        assert_eq!(r.read::<i32>(32).unwrap(), 2147483647);
        assert_eq!(r.read::<i64>(64).unwrap(), 0);
        assert_eq!(r.read::<i64>(64).unwrap(), -1);
        assert_eq!(r.read::<i64>(64).unwrap(), -9223372036854775808);
        assert_eq!(r.read::<i64>(64).unwrap(), 9223372036854775807);
    }
}

#[test]
fn test_reader_huffman_be() {
    use bitstream_io::BitReaderBE;
    use bitstream_io::BitRead;
    use bitstream_io::huffman::ReadHuffmanTree;

    let tree = ReadHuffmanTree::new(
        vec![(0, vec![1, 1]),
             (1, vec![1, 0]),
             (2, vec![0, 1]),
             (3, vec![0, 0, 1]),
             (4, vec![0, 0, 0])]).unwrap();

    let actual_data: [u8;4] = [0xB1, 0xED, 0x3B, 0xC1];
    let mut c = Cursor::new(&actual_data);
    let mut r = BitReaderBE::new(&mut c);

    assert_eq!(r.read_huffman(&tree).unwrap(), 1);
    assert_eq!(r.read_huffman(&tree).unwrap(), 0);
    assert_eq!(r.read_huffman(&tree).unwrap(), 4);
    assert_eq!(r.read_huffman(&tree).unwrap(), 0);
    assert_eq!(r.read_huffman(&tree).unwrap(), 0);
    assert_eq!(r.read_huffman(&tree).unwrap(), 2);
    assert_eq!(r.read_huffman(&tree).unwrap(), 1);
    assert_eq!(r.read_huffman(&tree).unwrap(), 1);
    assert_eq!(r.read_huffman(&tree).unwrap(), 2);
    assert_eq!(r.read_huffman(&tree).unwrap(), 0);
    assert_eq!(r.read_huffman(&tree).unwrap(), 2);
    assert_eq!(r.read_huffman(&tree).unwrap(), 0);
    assert_eq!(r.read_huffman(&tree).unwrap(), 1);
    assert_eq!(r.read_huffman(&tree).unwrap(), 4);
    assert_eq!(r.read_huffman(&tree).unwrap(), 2);
}

#[test]
fn test_reader_le() {
    use bitstream_io::BitReaderLE;
    use bitstream_io::BitRead;

    let actual_data: [u8;4] = [0xB1, 0xED, 0x3B, 0xC1];

    {
        /*reading individual bits*/
        let mut c = Cursor::new(&actual_data);
        let mut r = BitReaderLE::new(&mut c);
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
    }
    {
        /*reading unsigned values*/
        let mut c = Cursor::new(&actual_data);
        let mut r = BitReaderLE::new(&mut c);
        assert!(r.byte_aligned());
        assert_eq!(r.read::<u32>(2).unwrap(), 1);
        assert!(!r.byte_aligned());
        assert_eq!(r.read::<u32>(3).unwrap(), 4);
        assert!(!r.byte_aligned());
        assert_eq!(r.read::<u32>(5).unwrap(), 13);
        assert!(!r.byte_aligned());
        assert_eq!(r.read::<u32>(3).unwrap(), 3);
        assert!(!r.byte_aligned());
        assert_eq!(r.read::<u32>(19).unwrap(), 0x609DF);
        assert!(r.byte_aligned());
        assert!(r.read::<u32>(1).is_err());
    }
    {
        /*skipping bits*/
        let mut c = Cursor::new(&actual_data);
        let mut r = BitReaderLE::new(&mut c);
        assert_eq!(r.read::<u32>(2).unwrap(), 1);
        assert!(r.skip(3).is_ok());
        assert_eq!(r.read::<u32>(5).unwrap(), 13);
        assert!(r.skip(3).is_ok());
        assert_eq!(r.read::<u32>(19).unwrap(), 0x609DF);
    }
    {
        /*reading signed values*/
        let mut c = Cursor::new(&actual_data);
        let mut r = BitReaderLE::new(&mut c);
        assert_eq!(r.read_signed::<i32>(2).unwrap(), 1);
        assert_eq!(r.read_signed::<i32>(3).unwrap(), -4);
        assert_eq!(r.read_signed::<i32>(5).unwrap(), 13);
        assert_eq!(r.read_signed::<i32>(3).unwrap(), 3);
        assert_eq!(r.read_signed::<i32>(19).unwrap(), -128545);
    }
    {
        /*reading unary 0 values*/
        let mut c = Cursor::new(&actual_data);
        let mut r = BitReaderLE::new(&mut c);
        assert_eq!(r.read_unary0().unwrap(), 1);
        assert_eq!(r.read_unary0().unwrap(), 0);
        assert_eq!(r.read_unary0().unwrap(), 0);
        assert_eq!(r.read_unary0().unwrap(), 2);
        assert_eq!(r.read_unary0().unwrap(), 2);
    }
    {
        /*reading unary 1 values*/
        let mut c = Cursor::new(&actual_data);
        let mut r = BitReaderLE::new(&mut c);
        assert_eq!(r.read_unary1().unwrap(), 0);
        assert_eq!(r.read_unary1().unwrap(), 3);
        assert_eq!(r.read_unary1().unwrap(), 0);
        assert_eq!(r.read_unary1().unwrap(), 1);
        assert_eq!(r.read_unary1().unwrap(), 0);
    }
    {
        /*byte aligning*/
        let mut c = Cursor::new(&actual_data);
        let mut r = BitReaderLE::new(&mut c);
        assert_eq!(r.read::<u32>(3).unwrap(), 1);
        r.byte_align();
        assert_eq!(r.read::<u32>(3).unwrap(), 5);
        r.byte_align();
        r.byte_align();
        assert_eq!(r.read::<u32>(8).unwrap(), 59);
        r.byte_align();
        assert_eq!(r.read::<u32>(4).unwrap(), 1);
    }
    {
        /*reading bytes, aligned*/
        let mut c = Cursor::new(&actual_data);
        let mut r = BitReaderLE::new(&mut c);
        let mut sub_data = [0; 2];
        assert!(r.read_bytes(&mut sub_data).is_ok());
        assert_eq!(&sub_data, b"\xB1\xED");
    }
    {
        /*reading bytes, un-aligned*/
        let mut c = Cursor::new(&actual_data);
        let mut r = BitReaderLE::new(&mut c);
        let mut sub_data = [0; 2];
        assert_eq!(r.read::<u32>(4).unwrap(), 1);
        assert!(r.read_bytes(&mut sub_data).is_ok());
        assert_eq!(&sub_data, b"\xDB\xBE");
    }
}

#[test]
fn test_edge_cases_le() {
    use bitstream_io::BitReaderLE;
    use bitstream_io::BitRead;

    let data: Vec<u8> = vec![0, 0, 0, 0, 255, 255, 255, 255,
                             0, 0, 0, 128, 255, 255, 255, 127,
                             0, 0, 0, 0, 0, 0, 0, 0,
                             255, 255, 255, 255, 255, 255, 255, 255,
                             0, 0, 0, 0, 0, 0, 0, 128,
                             255, 255, 255, 255, 255, 255, 255, 127];
    {
        /*unsigned 32 and 64-bit values*/
        let mut c = Cursor::new(&data);
        let mut r = BitReaderLE::new(&mut c);
        assert_eq!(r.read::<u32>(32).unwrap(), 0);
        assert_eq!(r.read::<u32>(32).unwrap(), 4294967295);
        assert_eq!(r.read::<u32>(32).unwrap(), 2147483648);
        assert_eq!(r.read::<u32>(32).unwrap(), 2147483647);
        assert_eq!(r.read::<u64>(64).unwrap(), 0);
        assert_eq!(r.read::<u64>(64).unwrap(), 0xFFFFFFFFFFFFFFFF);
        assert_eq!(r.read::<u64>(64).unwrap(), 9223372036854775808);
        assert_eq!(r.read::<u64>(64).unwrap(), 9223372036854775807);
    }

    {
        let mut c = Cursor::new(&data);
        let mut r = BitReaderLE::new(&mut c);
        assert_eq!(r.read_signed::<i32>(32).unwrap(), 0);
        assert_eq!(r.read_signed::<i32>(32).unwrap(), -1);
        assert_eq!(r.read_signed::<i32>(32).unwrap(), -2147483648);
        assert_eq!(r.read_signed::<i32>(32).unwrap(), 2147483647);
        assert_eq!(r.read_signed::<i64>(64).unwrap(), 0);
        assert_eq!(r.read_signed::<i64>(64).unwrap(), -1);
        assert_eq!(r.read_signed::<i64>(64).unwrap(), -9223372036854775808);
        assert_eq!(r.read_signed::<i64>(64).unwrap(), 9223372036854775807);
    }
}

#[test]
fn test_reader_huffman_le() {
    use bitstream_io::BitReaderLE;
    use bitstream_io::BitRead;
    use bitstream_io::huffman::ReadHuffmanTree;

    let tree = ReadHuffmanTree::new(
        vec![(0, vec![1, 1]),
             (1, vec![1, 0]),
             (2, vec![0, 1]),
             (3, vec![0, 0, 1]),
             (4, vec![0, 0, 0])]).unwrap();

    let actual_data: [u8;4] = [0xB1, 0xED, 0x3B, 0xC1];
    let mut c = Cursor::new(&actual_data);
    let mut r = BitReaderLE::new(&mut c);

    assert_eq!(r.read_huffman(&tree).unwrap(), 1);
    assert_eq!(r.read_huffman(&tree).unwrap(), 3);
    assert_eq!(r.read_huffman(&tree).unwrap(), 1);
    assert_eq!(r.read_huffman(&tree).unwrap(), 0);
    assert_eq!(r.read_huffman(&tree).unwrap(), 2);
    assert_eq!(r.read_huffman(&tree).unwrap(), 1);
    assert_eq!(r.read_huffman(&tree).unwrap(), 0);
    assert_eq!(r.read_huffman(&tree).unwrap(), 0);
    assert_eq!(r.read_huffman(&tree).unwrap(), 1);
    assert_eq!(r.read_huffman(&tree).unwrap(), 0);
    assert_eq!(r.read_huffman(&tree).unwrap(), 1);
    assert_eq!(r.read_huffman(&tree).unwrap(), 2);
    assert_eq!(r.read_huffman(&tree).unwrap(), 4);
    assert_eq!(r.read_huffman(&tree).unwrap(), 3);
}
