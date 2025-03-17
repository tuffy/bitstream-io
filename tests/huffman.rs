extern crate alloc;
extern crate bitstream_io;

use bitstream_io::huffman::{compile_read_tree, compile_write_tree, HuffmanTreeError};
#[cfg(not(feature = "std"))]
use core2::io;

#[cfg(feature = "std")]
use std::io;

#[test]
fn test_huffman_errors() {
    let empty: Vec<(i32, Vec<u8>)> = Vec::new();
    assert!(if let Err(err) = compile_read_tree::<i32>(empty) {
        err == HuffmanTreeError::MissingLeaf
    } else {
        false
    });

    assert!(
        if let Err(err) = compile_read_tree::<u32>(vec![(0u32, vec![0, 1, 2])]) {
            err == HuffmanTreeError::InvalidBit
        } else {
            false
        }
    );

    assert!(
        if let Err(err) = compile_read_tree::<u32>(vec![(0u32, vec![1]), (1u32, vec![0, 1])]) {
            err == HuffmanTreeError::MissingLeaf
        } else {
            false
        }
    );

    assert!(if let Err(err) = compile_read_tree::<u32>(vec![
        (0u32, vec![1]),
        (1u32, vec![0, 1]),
        (2u32, vec![0, 0]),
        (3u32, vec![0, 0]),
    ]) {
        err == HuffmanTreeError::DuplicateLeaf
    } else {
        false
    });

    assert!(if let Err(err) = compile_read_tree::<u32>(vec![
        (0u32, vec![1]),
        (1u32, vec![0]),
        (2u32, vec![0, 0]),
        (3u32, vec![0, 1]),
    ]) {
        err == HuffmanTreeError::OrphanedLeaf
    } else {
        false
    });

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
    use bitstream_io::huffman::compile_read_tree;
    use bitstream_io::{BigEndian, BitRead, BitReader};
    use io::Cursor;

    let data = [0b10110001, 0b11101101];

    // we can lookup values that aren't just integers also
    let tree = compile_read_tree(vec![
        (Some(0), vec![0]),
        (Some(1), vec![1, 0]),
        (Some(2), vec![1, 1, 0]),
        (None, vec![1, 1, 1]),
    ])
    .unwrap();
    let mut r = BitReader::endian(Cursor::new(&data), BigEndian);
    assert_eq!(r.read_huffman(&tree).unwrap().clone(), Some(1));
    assert_eq!(r.read_huffman(&tree).unwrap().clone(), Some(2));
    assert_eq!(r.read_huffman(&tree).unwrap().clone(), Some(0));
    assert_eq!(r.read_huffman(&tree).unwrap().clone(), Some(0));
    assert_eq!(r.read_huffman(&tree).unwrap().clone(), None);

    let tree = compile_read_tree(vec![
        ("foo", vec![0]),
        ("bar", vec![1, 0]),
        ("baz", vec![1, 1, 0]),
        ("kelp", vec![1, 1, 1]),
    ])
    .unwrap();

    let mut r = BitReader::endian(Cursor::new(&data), BigEndian);
    assert_eq!(r.read_huffman(&tree).unwrap(), &"bar");
    assert_eq!(r.read_huffman(&tree).unwrap(), &"baz");
    assert_eq!(r.read_huffman(&tree).unwrap(), &"foo");
    assert_eq!(r.read_huffman(&tree).unwrap(), &"foo");
    assert_eq!(r.read_huffman(&tree).unwrap(), &"kelp");
}

#[test]
fn test_lengthy_huffman_values() {
    use bitstream_io::huffman::{compile_read_tree, compile_write_tree};
    use bitstream_io::{BitRead, BitReader, BitWrite, BitWriter, BE, LE};
    use io::Cursor;

    let max_bits = 70;
    let mut spec = Vec::new();
    for bits in 0..max_bits {
        let mut entry = Vec::new();
        for _ in 0..bits {
            entry.push(0);
        }
        entry.push(1);
        spec.push((Some(bits), entry));
    }
    let mut entry = Vec::new();
    for _ in 0..max_bits {
        entry.push(0);
    }
    spec.push((None, entry));

    let read_tree_be = compile_read_tree::<Option<i32>>(spec.clone()).unwrap();
    let write_tree_be = compile_write_tree::<Option<i32>>(spec.clone()).unwrap();
    let read_tree_le = compile_read_tree::<Option<i32>>(spec.clone()).unwrap();
    let write_tree_le = compile_write_tree::<Option<i32>>(spec).unwrap();

    let mut data_be = Vec::new();
    let mut data_le = Vec::new();
    {
        let mut writer_be = BitWriter::<_, BE>::new(&mut data_be);
        let mut writer_le = BitWriter::<_, LE>::new(&mut data_le);
        for _ in 0..20 {
            for bits in 0..max_bits {
                writer_be.write_huffman(&write_tree_be, Some(bits)).unwrap();
                writer_le.write_huffman(&write_tree_le, Some(bits)).unwrap();
            }
        }
        writer_be.byte_align().unwrap();
        writer_le.byte_align().unwrap();
    }
    {
        let mut cursor_be = Cursor::new(&data_be);
        let mut cursor_le = Cursor::new(&data_le);
        let mut reader_be = BitReader::<_, BE>::new(&mut cursor_be);
        let mut reader_le = BitReader::<_, LE>::new(&mut cursor_le);
        for _ in 0..20 {
            for bits in 0..max_bits {
                assert_eq!(
                    reader_be.read_huffman(&read_tree_be).unwrap().clone(),
                    Some(bits)
                );
                assert_eq!(
                    reader_le.read_huffman(&read_tree_le).unwrap().clone(),
                    Some(bits)
                );
            }
        }
    }
}
