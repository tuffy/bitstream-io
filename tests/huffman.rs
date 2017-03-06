extern crate bitstream_io;
use bitstream_io::huffman::{ReadHuffmanTree,
                            WriteHuffmanTree,
                            HuffmanTreeError};

#[test]
fn test_huffman_errors() {
    let empty: Vec<(i32, Vec<u8>)> = Vec::new();
    assert!(
        if let Err(err) = ReadHuffmanTree::new(empty) {
            err == HuffmanTreeError::MissingLeaf
        } else {false}
    );

    assert!(
        if let Err(err) = ReadHuffmanTree::new(vec![(0u32, vec![0,1,2])]) {
            err == HuffmanTreeError::InvalidBit
        } else {false}
    );

    assert!(
        if let Err(err) = ReadHuffmanTree::new(
                vec![(0u32, vec![1]), (1u32, vec![0, 1])]) {
            err == HuffmanTreeError::MissingLeaf
        } else {false}
    );

    assert!(
        if let Err(err) = ReadHuffmanTree::new(
                vec![(0u32, vec![1]),
                     (1u32, vec![0, 1]),
                     (2u32, vec![0, 0]),
                     (3u32, vec![0, 0])]) {
            err == HuffmanTreeError::DuplicateLeaf
        } else {false}
    );

    assert!(
        if let Err(err) = ReadHuffmanTree::new(
                vec![(0u32, vec![1]),
                     (1u32, vec![0]),
                     (2u32, vec![0, 0]),
                     (3u32, vec![0, 1])]) {
            err == HuffmanTreeError::OrphanedLeaf
        } else {false}
    );

    assert!(
        if let Err(err) = WriteHuffmanTree::new(vec![(0u32, vec![1,1,2])]) {
            err == HuffmanTreeError::InvalidBit
        } else {false}
    );
}

#[test]
fn test_huffman_values() {
    use std::io::Cursor;
    use std::ops::Deref;
    use std::rc::Rc;
    use bitstream_io::{BitReaderBE, BitRead};
    use bitstream_io::huffman::ReadHuffmanTree;

    let data = [0xB1, 0xED];
    {
        // we can lookup values that aren't just integers also
        let tree = ReadHuffmanTree::new(
            vec![(Some(0), vec![0]),
                 (Some(1), vec![1, 0]),
                 (Some(2), vec![1, 1, 0]),
                 (None, vec![1, 1, 1])]).unwrap();
        let mut c = Cursor::new(&data);
        let mut r = BitReaderBE::new(&mut c);
        assert_eq!(r.read_huffman(&tree).unwrap(), Some(1));
        assert_eq!(r.read_huffman(&tree).unwrap(), Some(2));
        assert_eq!(r.read_huffman(&tree).unwrap(), Some(0));
        assert_eq!(r.read_huffman(&tree).unwrap(), Some(0));
        assert_eq!(r.read_huffman(&tree).unwrap(), None);
    }
    {
        // we can even lookup potentially large values,
        // preferably using Rc to avoid making copies of each one
        let tree = ReadHuffmanTree::new(
            vec![(Rc::new("foo".to_owned()), vec![0]),
                 (Rc::new("bar".to_owned()), vec![1, 0]),
                 (Rc::new("baz".to_owned()), vec![1, 1, 0]),
                 (Rc::new("kelp".to_owned()), vec![1, 1, 1])]).unwrap();
        let mut c = Cursor::new(&data);
        let mut r = BitReaderBE::new(&mut c);
        assert_eq!(r.read_huffman(&tree).unwrap().deref(), "bar");
        assert_eq!(r.read_huffman(&tree).unwrap().deref(), "baz");
        assert_eq!(r.read_huffman(&tree).unwrap().deref(), "foo");
        assert_eq!(r.read_huffman(&tree).unwrap().deref(), "foo");
        assert_eq!(r.read_huffman(&tree).unwrap().deref(), "kelp");
    }
}
