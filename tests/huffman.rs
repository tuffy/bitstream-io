extern crate alloc;
extern crate bitstream_io;

use bitstream_io::huffman::{compile_write_tree, HuffmanTreeError};
#[cfg(not(feature = "std"))]
use core2::io;

#[cfg(feature = "std")]
use std::io;

#[test]
fn test_huffman_errors() {
    assert!(
        if let Err(err) = compile_write_tree::<u32>(vec![(0, vec![1, 1, 2])]) {
            err == HuffmanTreeError::InvalidBit
        } else {
            false
        }
    );
}

#[test]
fn test_huffman_values() {
    use bitstream_io::{define_huffman_tree, BigEndian, BitRead, BitReader};
    use io::Cursor;

    let data = [0b10110001, 0b11101101];

    define_huffman_tree!(Tree1 : i32 , [0, [1, [2, 5]]]);
    define_huffman_tree!(Tree2 : &'static str, ["foo", ["bar", ["baz", "kelp"]]]);

    let mut r = BitReader::endian(Cursor::new(&data), BigEndian);
    assert_eq!(r.read_huffman::<Tree1>().unwrap(), 1);
    assert_eq!(r.read_huffman::<Tree1>().unwrap(), 2);
    assert_eq!(r.read_huffman::<Tree1>().unwrap(), 0);
    assert_eq!(r.read_huffman::<Tree1>().unwrap(), 0);
    assert_eq!(r.read_huffman::<Tree1>().unwrap(), 5);

    let mut r = BitReader::endian(Cursor::new(&data), BigEndian);
    assert_eq!(r.read_huffman::<Tree2>().unwrap(), "bar");
    assert_eq!(r.read_huffman::<Tree2>().unwrap(), "baz");
    assert_eq!(r.read_huffman::<Tree2>().unwrap(), "foo");
    assert_eq!(r.read_huffman::<Tree2>().unwrap(), "foo");
    assert_eq!(r.read_huffman::<Tree2>().unwrap(), "kelp");
}
