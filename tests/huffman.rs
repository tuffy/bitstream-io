extern crate bitstream_io;
use bitstream_io::huffman::{ReadHuffmanTree,
                            WriteHuffmanTree,
                            HuffmanTreeError};

#[test]
fn test_huffman_errors() {
    let empty: [(Vec<u8>, i32);0] = [];
    assert!(
        if let Err(err) = ReadHuffmanTree::new(&empty) {
            err == HuffmanTreeError::MissingLeaf
        } else {false}
    );

    assert!(
        if let Err(err) = ReadHuffmanTree::new(&[(vec![0,1,2], 0u32)]) {
            err == HuffmanTreeError::InvalidBit
        } else {false}
    );

    assert!(
        if let Err(err) = ReadHuffmanTree::new(
                &[(vec![1], 0u32), (vec![0, 1], 1u32)]) {
            err == HuffmanTreeError::MissingLeaf
        } else {false}
    );

    assert!(
        if let Err(err) = ReadHuffmanTree::new(
                &[(vec![1], 0u32),
                  (vec![0, 1], 1u32),
                  (vec![0, 0], 2u32),
                  (vec![0, 0], 3u32)]) {
            err == HuffmanTreeError::DuplicateLeaf
        } else {false}
    );

    assert!(
        if let Err(err) = ReadHuffmanTree::new(
                &[(vec![1], 0u32),
                  (vec![0], 1u32),
                  (vec![0, 0], 2u32),
                  (vec![0, 1], 3u32)]) {
            err == HuffmanTreeError::OrphanedLeaf
        } else {false}
    );

    assert!(
        if let Err(err) = WriteHuffmanTree::new(&[(vec![1,1,2], 0u32)]) {
            err == HuffmanTreeError::InvalidBit
        } else {false}
    );
}
