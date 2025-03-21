extern crate alloc;
extern crate bitstream_io;

use bitstream_io::compile_read_tree;
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
    use bitstream_io::{BigEndian, BitRead, BitReader};
    use io::Cursor;

    let data = [0b10110001, 0b11101101];

    let tree = compile_read_tree!([0, [1, [2, 5]]]);

    let mut r = BitReader::endian(Cursor::new(&data), BigEndian);
    assert_eq!(r.read_huffman(&tree).unwrap().clone(), 1);
    assert_eq!(r.read_huffman(&tree).unwrap().clone(), 2);
    assert_eq!(r.read_huffman(&tree).unwrap().clone(), 0);
    assert_eq!(r.read_huffman(&tree).unwrap().clone(), 0);
    assert_eq!(r.read_huffman(&tree).unwrap().clone(), 5);

    let tree = compile_read_tree!(["foo", ["bar", ["baz", "kelp"]]]);

    let mut r = BitReader::endian(Cursor::new(&data), BigEndian);
    assert_eq!(r.read_huffman(&tree).unwrap(), &"bar");
    assert_eq!(r.read_huffman(&tree).unwrap(), &"baz");
    assert_eq!(r.read_huffman(&tree).unwrap(), &"foo");
    assert_eq!(r.read_huffman(&tree).unwrap(), &"foo");
    assert_eq!(r.read_huffman(&tree).unwrap(), &"kelp");
}
