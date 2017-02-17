// Copyright 2017 Brian Langenberger
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

extern crate bitstream_io;
use bitstream_io::{BitReaderBE, BitReaderLE, BitRead};
use bitstream_io::{BitWriterBE, BitWriterLE, BitWrite};
use std::io::Cursor;

macro_rules! define_roundtrip {
    ($func_name:ident, $reader_type:ident, $writer_type:ident) => {
       #[test]
        fn $func_name() {
            /*unsigned values*/
            for bits in 1..17 {
                let max = 1 << bits;
                let mut output: Vec<u8> = Vec::with_capacity(max);
                {
                    let mut writer = $writer_type::new(&mut output);
                    for value in 0..max {
                        writer.write(bits, value as u32).unwrap();
                    }
                    writer.byte_align().unwrap();
                }
                {
                    let mut c = Cursor::new(&output);
                    let mut reader = $reader_type::new(&mut c);
                    for value in 0..max {
                        assert_eq!(reader.read::<u32>(bits).unwrap(),
                                   value as u32);
                    }
                }
            }

            /*signed values*/
            for bits in 2..17 {
                let min = -1i32 << (bits - 1);
                let max = 1i32 << (bits - 1);
                let mut output: Vec<u8> = Vec::with_capacity(max as usize);
                {
                    let mut writer = $writer_type::new(&mut output);
                    for value in min..max {
                        writer.write_signed(bits, value as i32).unwrap();
                    }
                    writer.byte_align().unwrap();
                }
                {
                    let mut c = Cursor::new(&output);
                    let mut reader = $reader_type::new(&mut c);
                    for value in min..max {
                        assert_eq!(reader.read_signed::<i32>(bits).unwrap(),
                                   value as i32);
                    }
                }
            }

        }
    }
}

define_roundtrip!(test_roundtrip_be, BitReaderBE, BitWriterBE);
define_roundtrip!(test_roundtrip_le, BitReaderLE, BitWriterLE);
