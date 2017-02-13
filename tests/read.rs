extern crate bitstream_io;
use std::io::Cursor;

#[test]
fn test_reader_be() {
    use bitstream_io::BitReaderBE;
    use bitstream_io::BitRead;

    let actual_data: [u8;4] = [0xB1, 0xED, 0x3B, 0xC1];

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
        assert_eq!(r.read_signed(2).unwrap(), -2);
        assert_eq!(r.read_signed(3).unwrap(), -2);
        assert_eq!(r.read_signed(5).unwrap(), 7);
        assert_eq!(r.read_signed(3).unwrap(), -3);
        assert_eq!(r.read_signed(19).unwrap(), -181311);
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
fn test_reader_le() {
    use bitstream_io::BitReaderLE;
    use bitstream_io::BitRead;

    let actual_data: [u8;4] = [0xB1, 0xED, 0x3B, 0xC1];

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
        assert_eq!(r.read_signed(2).unwrap(), 1);
        assert_eq!(r.read_signed(3).unwrap(), -4);
        assert_eq!(r.read_signed(5).unwrap(), 13);
        assert_eq!(r.read_signed(3).unwrap(), 3);
        assert_eq!(r.read_signed(19).unwrap(), -128545);
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
