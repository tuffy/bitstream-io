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
    /*FIXME*/

    /*writing bytes, aligned*/
    /*FIXME*/

    /*writing bytes, un-aligned*/
    /*FIXME*/
}

/*FIXME - edge cases - BE*/

/*FIXME - writing LE*/

/*FIXME - edge cases - LE*/
