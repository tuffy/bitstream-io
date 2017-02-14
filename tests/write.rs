extern crate bitstream_io;

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
        w.write(2, 2).unwrap();
        assert!(!w.byte_aligned());
        w.write(3, 6).unwrap();
        assert!(!w.byte_aligned());
        w.write(5, 7).unwrap();
        assert!(!w.byte_aligned());
        w.write(3, 5).unwrap();
        assert!(!w.byte_aligned());
        w.write(19, 0x53BC1).unwrap();
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
        w.write(1, 1).unwrap();
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
        w.write(3, 5).unwrap();
        w.byte_align().unwrap();
        w.write(3, 7).unwrap();
        w.byte_align().unwrap();
        w.byte_align().unwrap();
        w.write(8, 59).unwrap();
        w.byte_align().unwrap();
        w.write(4, 12).unwrap();
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
        w.write(4, 11).unwrap();
        w.write_bytes(b"\xB1\xED").unwrap();
        w.byte_align().unwrap();
    }
    assert_eq!(output.as_slice(), &final_data);
}

/*FIXME - edge cases - BE*/

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
        w.write(2, 1).unwrap();
        assert!(!w.byte_aligned());
        w.write(3, 4).unwrap();
        assert!(!w.byte_aligned());
        w.write(5, 13).unwrap();
        assert!(!w.byte_aligned());
        w.write(3, 3).unwrap();
        assert!(!w.byte_aligned());
        w.write(19, 0x609DF).unwrap();
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
        w.write(2, 3).unwrap();
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
        w.write(3, 5).unwrap();
        w.byte_align().unwrap();
        w.write(3, 7).unwrap();
        w.byte_align().unwrap();
        w.byte_align().unwrap();
        w.write(8, 59).unwrap();
        w.byte_align().unwrap();
        w.write(4, 12).unwrap();
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
        w.write(4, 11).unwrap();
        w.write_bytes(b"\xB1\xED").unwrap();
        w.byte_align().unwrap();
    }
    assert_eq!(output.as_slice(), &final_data);
}

/*FIXME - edge cases - LE*/
