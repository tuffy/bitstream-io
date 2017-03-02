// Copyright 2017 Brian Langenberger
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

extern crate bitstream_io;

#[test]
fn test_write_queue_be() {
    use bitstream_io::{BitQueueBE, BitQueue, Numeric};
    let mut q: BitQueueBE<u8> = BitQueueBE::new();
    let mut v = BitQueueBE::from_value(2u8, 2);
    q.push(2, v.pop(2).to_u8());
    let mut v = BitQueueBE::from_value(6u8, 3);
    q.push(3, v.pop(3).to_u8());
    let mut v = BitQueueBE::from_value(7u8, 5);
    q.push(3, v.pop(3).to_u8());
    assert_eq!(q.len(), 8);
    assert_eq!(q.pop(8), 0xB1);
    q.push(2, v.pop(2).to_u8());
    let mut v = BitQueueBE::from_value(5u8, 3);
    q.push(3, v.pop(3).to_u8());
    let mut v = BitQueueBE::from_value(342977u32, 19);
    q.push(3, v.pop(3).to_u8());
    assert_eq!(q.len(), 8);
    assert_eq!(q.pop(8), 0xED);
    q.push(8, v.pop(8).to_u8());
    assert_eq!(q.len(), 8);
    assert_eq!(q.pop(8), 0x3B);
    q.push(8, v.pop(8).to_u8());
    assert_eq!(q.len(), 8);
    assert_eq!(q.pop(8), 0xC1);
    assert!(v.is_empty());
    assert!(q.is_empty());
}

#[test]
fn test_write_queue_le() {
    use bitstream_io::{BitQueueLE, BitQueue, Numeric};
    let mut q: BitQueueLE<u8> = BitQueueLE::new();
    let mut v = BitQueueLE::from_value(1u8, 2);
    q.push(2, v.pop(2).to_u8());
    let mut v = BitQueueLE::from_value(4u8, 3);
    q.push(3, v.pop(3).to_u8());
    let mut v = BitQueueLE::from_value(13u8, 5);
    q.push(3, v.pop(3).to_u8());
    assert_eq!(q.len(), 8);
    assert_eq!(q.pop(8), 0xB1);
    q.push(2, v.pop(2).to_u8());
    let mut v = BitQueueLE::from_value(3u8, 3);
    q.push(3, v.pop(3).to_u8());
    let mut v = BitQueueLE::from_value(395743u32, 19);
    q.push(3, v.pop(3).to_u8());
    assert_eq!(q.len(), 8);
    assert_eq!(q.pop(8), 0xED);
    q.push(8, v.pop(8).to_u8());
    assert_eq!(q.len(), 8);
    assert_eq!(q.pop(8), 0x3B);
    q.push(8, v.pop(8).to_u8());
    assert_eq!(q.len(), 8);
    assert_eq!(q.pop(8), 0xC1);
    assert!(v.is_empty());
    assert!(q.is_empty());
}

#[test]
fn test_writer_be() {
    use bitstream_io::BitWriterBE;
    use bitstream_io::BitWrite;

    let final_data: [u8;4] = [0xB1, 0xED, 0x3B, 0xC1];

    /*writing unsigned values*/
    let mut output = Vec::with_capacity(4);
    {
        let mut w = BitWriterBE::new(&mut output);
        assert!(w.byte_aligned());
        w.write(2, 2u32).unwrap();
        assert!(!w.byte_aligned());
        w.write(3, 6u32).unwrap();
        assert!(!w.byte_aligned());
        w.write(5, 7u32).unwrap();
        assert!(!w.byte_aligned());
        w.write(3, 5u32).unwrap();
        assert!(!w.byte_aligned());
        w.write(19, 0x53BC1u32).unwrap();
        assert!(w.byte_aligned());
    }
    assert_eq!(output.as_slice(), &final_data);

    /*writing signed values*/
    let mut output = Vec::with_capacity(4);
    {
        let mut w = BitWriterBE::new(&mut output);
        w.write_signed(2, -2).unwrap();
        w.write_signed(3, -2).unwrap();
        w.write_signed(5, 7).unwrap();
        w.write_signed(3, -3).unwrap();
        w.write_signed(19, -181311).unwrap();
    }
    assert_eq!(output.as_slice(), &final_data);

    /*writing unary 0 values*/
    let mut output = Vec::with_capacity(4);
    {
        let mut w = BitWriterBE::new(&mut output);
        w.write_unary0(1).unwrap();
        w.write_unary0(2).unwrap();
        w.write_unary0(0).unwrap();
        w.write_unary0(0).unwrap();
        w.write_unary0(4).unwrap();
        w.write_unary0(2).unwrap();
        w.write_unary0(1).unwrap();
        w.write_unary0(0).unwrap();
        w.write_unary0(3).unwrap();
        w.write_unary0(4).unwrap();
        w.write_unary0(0).unwrap();
        w.write_unary0(0).unwrap();
        w.write_unary0(0).unwrap();
        w.write_unary0(0).unwrap();
        w.write(1, 1u32).unwrap();
    }
    assert_eq!(output.as_slice(), &final_data);

    /*writing unary 1 values*/
    let mut output = Vec::with_capacity(4);
    {
        let mut w = BitWriterBE::new(&mut output);
        w.write_unary1(0).unwrap();
        w.write_unary1(1).unwrap();
        w.write_unary1(0).unwrap();
        w.write_unary1(3).unwrap();
        w.write_unary1(0).unwrap();
        w.write_unary1(0).unwrap();
        w.write_unary1(0).unwrap();
        w.write_unary1(1).unwrap();
        w.write_unary1(0).unwrap();
        w.write_unary1(1).unwrap();
        w.write_unary1(2).unwrap();
        w.write_unary1(0).unwrap();
        w.write_unary1(0).unwrap();
        w.write_unary1(1).unwrap();
        w.write_unary1(0).unwrap();
        w.write_unary1(0).unwrap();
        w.write_unary1(0).unwrap();
        w.write_unary1(5).unwrap();
    }
    assert_eq!(output.as_slice(), &final_data);

    /*byte aligning*/
    let mut output = Vec::with_capacity(4);
    let aligned_data = [0xA0, 0xE0, 0x3B, 0xC0];
    {
        let mut w = BitWriterBE::new(&mut output);
        w.write(3, 5u32).unwrap();
        w.byte_align().unwrap();
        w.write(3, 7u32).unwrap();
        w.byte_align().unwrap();
        w.byte_align().unwrap();
        w.write(8, 59u32).unwrap();
        w.byte_align().unwrap();
        w.write(4, 12u32).unwrap();
        w.byte_align().unwrap();
    }
    assert_eq!(output.as_slice(), &aligned_data);

    /*writing bytes, aligned*/
    let mut output = Vec::with_capacity(2);
    let final_data = [0xB1, 0xED];
    {
        let mut w = BitWriterBE::new(&mut output);
        w.write_bytes(b"\xB1\xED").unwrap();
    }
    assert_eq!(output.as_slice(), &final_data);

    /*writing bytes, un-aligned*/
    let mut output = Vec::with_capacity(3);
    let final_data = [0xBB, 0x1E, 0xD0];
    {
        let mut w = BitWriterBE::new(&mut output);
        w.write(4, 11u32).unwrap();
        w.write_bytes(b"\xB1\xED").unwrap();
        w.byte_align().unwrap();
    }
    assert_eq!(output.as_slice(), &final_data);
}

#[test]
fn test_writer_edge_cases_be() {
    use bitstream_io::BitWriterBE;
    use bitstream_io::BitWrite;

    let final_data: Vec<u8> = vec![0, 0, 0, 0, 255, 255, 255, 255,
                                   128, 0, 0, 0, 127, 255, 255, 255,
                                   0, 0, 0, 0, 0, 0, 0, 0,
                                   255, 255, 255, 255, 255, 255, 255, 255,
                                   128, 0, 0, 0, 0, 0, 0, 0,
                                   127, 255, 255, 255, 255, 255, 255, 255];

    let mut output = Vec::with_capacity(48);
    {
        /*unsigned 32 and 64-bit values*/
        let mut w = BitWriterBE::new(&mut output);
        w.write(32, 0u32).unwrap();
        w.write(32, 4294967295u32).unwrap();
        w.write(32, 2147483648u32).unwrap();
        w.write(32, 2147483647u32).unwrap();
        w.write(64, 0u64).unwrap();
        w.write(64, 0xFFFFFFFFFFFFFFFFu64).unwrap();
        w.write(64, 9223372036854775808u64).unwrap();
        w.write(64, 9223372036854775807u64).unwrap();
    }
    assert_eq!(output, final_data);

    /*signed 32 and 64-bit values*/
    let mut output = Vec::with_capacity(48);
    {
        let mut w = BitWriterBE::new(&mut output);
        w.write(32, 0i64).unwrap();
        w.write(32, -1i64).unwrap();
        w.write(32, -2147483648i64).unwrap();
        w.write(32, 2147483647i64).unwrap();
        w.write(64, 0i64).unwrap();
        w.write(64, -1i64).unwrap();
        w.write(64, -9223372036854775808i64).unwrap();
        w.write(64, 9223372036854775807i64).unwrap();
    }
    assert_eq!(output, final_data);
}

#[test]
fn test_writer_huffman_be() {
    use bitstream_io::BitWriterBE;
    use bitstream_io::BitWrite;
    use bitstream_io::huffman::WriteHuffmanTreeBE;

    let final_data: [u8;4] = [0xB1, 0xED, 0x3B, 0xC1];
    let table = WriteHuffmanTreeBE::compile(
        &[(vec![1, 1], 0),
          (vec![1, 0], 1),
          (vec![0, 1], 2),
          (vec![0, 0, 1], 3),
          (vec![0, 0, 0], 4)]).unwrap();
    let mut output = Vec::with_capacity(4);
    {
        let mut w = BitWriterBE::new(&mut output);
        w.write_huffman(&table, 1).unwrap();
        w.write_huffman(&table, 0).unwrap();
        w.write_huffman(&table, 4).unwrap();
        w.write_huffman(&table, 0).unwrap();
        w.write_huffman(&table, 0).unwrap();
        w.write_huffman(&table, 2).unwrap();
        w.write_huffman(&table, 1).unwrap();
        w.write_huffman(&table, 1).unwrap();
        w.write_huffman(&table, 2).unwrap();
        w.write_huffman(&table, 0).unwrap();
        w.write_huffman(&table, 2).unwrap();
        w.write_huffman(&table, 0).unwrap();
        w.write_huffman(&table, 1).unwrap();
        w.write_huffman(&table, 4).unwrap();
        w.write_huffman(&table, 2).unwrap();
        w.byte_align().unwrap();
    }
    assert_eq!(output.as_slice(), &final_data);
}

#[test]
fn test_writer_le() {
    use bitstream_io::BitWriterLE;
    use bitstream_io::BitWrite;

    let final_data: [u8;4] = [0xB1, 0xED, 0x3B, 0xC1];

    /*writing unsigned values*/
    let mut output = Vec::with_capacity(4);
    {
        let mut w = BitWriterLE::new(&mut output);
        assert!(w.byte_aligned());
        w.write(2, 1u32).unwrap();
        assert!(!w.byte_aligned());
        w.write(3, 4u32).unwrap();
        assert!(!w.byte_aligned());
        w.write(5, 13u32).unwrap();
        assert!(!w.byte_aligned());
        w.write(3, 3u32).unwrap();
        assert!(!w.byte_aligned());
        w.write(19, 0x609DFu32).unwrap();
        assert!(w.byte_aligned());
    }
    assert_eq!(output.as_slice(), &final_data);

    /*writing signed values*/
    let mut output = Vec::with_capacity(4);
    {
        let mut w = BitWriterLE::new(&mut output);
        w.write_signed(2, 1).unwrap();
        w.write_signed(3, -4).unwrap();
        w.write_signed(5, 13).unwrap();
        w.write_signed(3, 3).unwrap();
        w.write_signed(19, -128545).unwrap();
    }
    assert_eq!(output.as_slice(), &final_data);

    /*writing unary 0 values*/
    let mut output = Vec::with_capacity(4);
    {
        let mut w = BitWriterLE::new(&mut output);
        w.write_unary0(1).unwrap();
        w.write_unary0(0).unwrap();
        w.write_unary0(0).unwrap();
        w.write_unary0(2).unwrap();
        w.write_unary0(2).unwrap();
        w.write_unary0(2).unwrap();
        w.write_unary0(5).unwrap();
        w.write_unary0(3).unwrap();
        w.write_unary0(0).unwrap();
        w.write_unary0(1).unwrap();
        w.write_unary0(0).unwrap();
        w.write_unary0(0).unwrap();
        w.write_unary0(0).unwrap();
        w.write_unary0(0).unwrap();
        w.write(2, 3u32).unwrap();
    }
    assert_eq!(output.as_slice(), &final_data);

    /*writing unary 1 values*/
    let mut output = Vec::with_capacity(4);
    {
        let mut w = BitWriterLE::new(&mut output);
        w.write_unary1(0).unwrap();
        w.write_unary1(3).unwrap();
        w.write_unary1(0).unwrap();
        w.write_unary1(1).unwrap();
        w.write_unary1(0).unwrap();
        w.write_unary1(1).unwrap();
        w.write_unary1(0).unwrap();
        w.write_unary1(1).unwrap();
        w.write_unary1(0).unwrap();
        w.write_unary1(0).unwrap();
        w.write_unary1(0).unwrap();
        w.write_unary1(0).unwrap();
        w.write_unary1(1).unwrap();
        w.write_unary1(0).unwrap();
        w.write_unary1(0).unwrap();
        w.write_unary1(2).unwrap();
        w.write_unary1(5).unwrap();
        w.write_unary1(0).unwrap();
    }
    assert_eq!(output.as_slice(), &final_data);

    /*byte aligning*/
    let mut output = Vec::with_capacity(4);
    let aligned_data = [0x05, 0x07, 0x3B, 0x0C];
    {
        let mut w = BitWriterLE::new(&mut output);
        w.write(3, 5u32).unwrap();
        w.byte_align().unwrap();
        w.write(3, 7u32).unwrap();
        w.byte_align().unwrap();
        w.byte_align().unwrap();
        w.write(8, 59u32).unwrap();
        w.byte_align().unwrap();
        w.write(4, 12u32).unwrap();
        w.byte_align().unwrap();
    }
    assert_eq!(output.as_slice(), &aligned_data);

    /*writing bytes, aligned*/
    let mut output = Vec::with_capacity(2);
    let final_data = [0xB1, 0xED];
    {
        let mut w = BitWriterLE::new(&mut output);
        w.write_bytes(b"\xB1\xED").unwrap();
    }
    assert_eq!(output.as_slice(), &final_data);

    /*writing bytes, un-aligned*/
    let mut output = Vec::with_capacity(3);
    let final_data = [0x1B, 0xDB, 0x0E];
    {
        let mut w = BitWriterLE::new(&mut output);
        w.write(4, 11u32).unwrap();
        w.write_bytes(b"\xB1\xED").unwrap();
        w.byte_align().unwrap();
    }
    assert_eq!(output.as_slice(), &final_data);
}

#[test]
fn test_writer_edge_cases_le() {
    use bitstream_io::BitWriterLE;
    use bitstream_io::BitWrite;

    let final_data: Vec<u8> = vec![0, 0, 0, 0, 255, 255, 255, 255,
                                   0, 0, 0, 128, 255, 255, 255, 127,
                                   0, 0, 0, 0, 0, 0, 0, 0,
                                   255, 255, 255, 255, 255, 255, 255, 255,
                                   0, 0, 0, 0, 0, 0, 0, 128,
                                   255, 255, 255, 255, 255, 255, 255, 127];

    let mut output = Vec::with_capacity(48);
    {
        /*unsigned 32 and 64-bit values*/
        let mut w = BitWriterLE::new(&mut output);
        w.write(32, 0u32).unwrap();
        w.write(32, 4294967295u32).unwrap();
        w.write(32, 2147483648u32).unwrap();
        w.write(32, 2147483647u32).unwrap();
        w.write(64, 0u64).unwrap();
        w.write(64, 0xFFFFFFFFFFFFFFFFu64).unwrap();
        w.write(64, 9223372036854775808u64).unwrap();
        w.write(64, 9223372036854775807u64).unwrap();
    }
    assert_eq!(output, final_data);

    /*signed 32 and 64-bit values*/
    let mut output = Vec::with_capacity(48);
    {
        let mut w = BitWriterLE::new(&mut output);
        w.write(32, 0i64).unwrap();
        w.write(32, -1i64).unwrap();
        w.write(32, -2147483648i64).unwrap();
        w.write(32, 2147483647i64).unwrap();
        w.write(64, 0i64).unwrap();
        w.write(64, -1i64).unwrap();
        w.write(64, -9223372036854775808i64).unwrap();
        w.write(64, 9223372036854775807i64).unwrap();
    }
    assert_eq!(output, final_data);
}

#[test]
fn test_writer_huffman_le() {
    use bitstream_io::BitWriterLE;
    use bitstream_io::BitWrite;
    use bitstream_io::huffman::WriteHuffmanTreeLE;

    let final_data: [u8;4] = [0xB1, 0xED, 0x3B, 0xC1];
    let table = WriteHuffmanTreeLE::compile(
        &[(vec![1, 1], 0),
          (vec![1, 0], 1),
          (vec![0, 1], 2),
          (vec![0, 0, 1], 3),
          (vec![0, 0, 0], 4)]).unwrap();
    let mut output = Vec::with_capacity(4);
    {
        let mut w = BitWriterLE::new(&mut output);
        w.write_huffman(&table, 1).unwrap();
        w.write_huffman(&table, 3).unwrap();
        w.write_huffman(&table, 1).unwrap();
        w.write_huffman(&table, 0).unwrap();
        w.write_huffman(&table, 2).unwrap();
        w.write_huffman(&table, 1).unwrap();
        w.write_huffman(&table, 0).unwrap();
        w.write_huffman(&table, 0).unwrap();
        w.write_huffman(&table, 1).unwrap();
        w.write_huffman(&table, 0).unwrap();
        w.write_huffman(&table, 1).unwrap();
        w.write_huffman(&table, 2).unwrap();
        w.write_huffman(&table, 4).unwrap();
        w.write_huffman(&table, 3).unwrap();
        w.write(1, 1).unwrap();
    }
    assert_eq!(output.as_slice(), &final_data);
}
