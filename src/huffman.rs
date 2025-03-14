// Copyright 2017 Brian Langenberger
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Traits and implementations for reading or writing Huffman codes
//! from or to a stream.

#![warn(missing_docs)]

use alloc::{boxed::Box, collections::BTreeMap, vec::Vec};
use core::{error::Error, fmt};

/// Given a vector of symbol/code pairs, compiles a Huffman tree
/// for reading.
///
/// Code must be 0 or 1 bits and are always read from the stream
/// from least-significant in the list to most signficant
/// (which makes them easier to read for humans).
///
/// All possible codes must be assigned some symbol,
/// and it is acceptable for the same symbol to occur multiple times.
///
/// ## Examples
/// ```
/// use bitstream_io::huffman::compile_read_tree;
/// use bitstream_io::BigEndian;
/// assert!(compile_read_tree::<i32>(
///     vec![(1, vec![0]),
///          (2, vec![1, 0]),
///          (3, vec![1, 1])]).is_ok());
/// ```
///
/// ```
/// use std::io::{Read, Cursor};
/// use bitstream_io::{BigEndian, BitReader, BitRead};
/// use bitstream_io::huffman::compile_read_tree;
/// let tree = compile_read_tree(
///     vec![('a', vec![0]),
///          ('b', vec![1, 0]),
///          ('c', vec![1, 1, 0]),
///          ('d', vec![1, 1, 1])]).unwrap();
/// let data = [0b10110111];
/// let mut cursor = Cursor::new(&data);
/// let mut reader = BitReader::endian(&mut cursor, BigEndian);
/// assert_eq!(reader.read_huffman(&tree).unwrap().clone(), 'b');
/// assert_eq!(reader.read_huffman(&tree).unwrap().clone(), 'c');
/// assert_eq!(reader.read_huffman(&tree).unwrap().clone(), 'd');
/// ```
// pub fn compile_read_tree<E, T>(
//     values: Vec<(T, Vec<u8>)>,
// ) -> Result<Box<[ReadHuffmanTree<E, T>]>, HuffmanTreeError>
// where
//     E: Endianness,
//     T: Clone,
// {
pub fn compile_read_tree<T>(
    values: Vec<(T, Vec<u8>)>,
) -> Result<FinalHuffmanTree<T>, HuffmanTreeError> {
    FinalHuffmanTree::new(values)
}

///usr A complete Huffman tree with no empty nodes
pub enum FinalHuffmanTree<T> {
    /// A Huffman tree leaf node
    Leaf(T),
    /// A Huffman tree non-leaf node
    Tree(Box<FinalHuffmanTree<T>>, Box<FinalHuffmanTree<T>>),
}

impl<T> FinalHuffmanTree<T> {
    fn new(values: Vec<(T, Vec<u8>)>) -> Result<FinalHuffmanTree<T>, HuffmanTreeError> {
        let mut tree = WipHuffmanTree::new_empty();

        for (symbol, code) in values {
            tree.add(code.as_slice(), symbol)?;
        }

        tree.into_read_tree()
    }

    /// Reads a value from the compiled Huffman tree
    ///
    /// # Errors
    ///
    /// Passes along any I/O error from the underlying stream.
    pub fn read<R: crate::BitRead + ?Sized>(&self, reader: &mut R) -> crate::io::Result<&T> {
        let mut tree = self;

        loop {
            match tree {
                Self::Leaf(t) => break Ok(t),
                Self::Tree(bit_0, bit_1) => {
                    tree = match reader.read_bit()? {
                        false => bit_0,
                        true => bit_1,
                    };
                }
            }
        }
    }
}

// Work-in-progress trees may have empty nodes during construction
// but those are not allowed in a finalized tree.
// If the user wants some codes to be None or an error symbol of some sort,
// those will need to be specified explicitly.
enum WipHuffmanTree<T> {
    Empty,
    Leaf(T),
    Tree(Box<WipHuffmanTree<T>>, Box<WipHuffmanTree<T>>),
}

impl<T> WipHuffmanTree<T> {
    fn new_empty() -> WipHuffmanTree<T> {
        WipHuffmanTree::Empty
    }

    fn new_leaf(value: T) -> WipHuffmanTree<T> {
        WipHuffmanTree::Leaf(value)
    }

    fn new_tree() -> WipHuffmanTree<T> {
        WipHuffmanTree::Tree(Box::new(Self::new_empty()), Box::new(Self::new_empty()))
    }

    fn into_read_tree(self) -> Result<FinalHuffmanTree<T>, HuffmanTreeError> {
        match self {
            WipHuffmanTree::Empty => Err(HuffmanTreeError::MissingLeaf),
            WipHuffmanTree::Leaf(v) => Ok(FinalHuffmanTree::Leaf(v)),
            WipHuffmanTree::Tree(zero, one) => {
                let zero = zero.into_read_tree()?;
                let one = one.into_read_tree()?;
                Ok(FinalHuffmanTree::Tree(Box::new(zero), Box::new(one)))
            }
        }
    }

    fn add(&mut self, code: &[u8], symbol: T) -> Result<(), HuffmanTreeError> {
        match self {
            WipHuffmanTree::Empty => {
                if code.is_empty() {
                    *self = WipHuffmanTree::new_leaf(symbol);
                    Ok(())
                } else {
                    *self = WipHuffmanTree::new_tree();
                    self.add(code, symbol)
                }
            }
            WipHuffmanTree::Leaf(_) => Err(if code.is_empty() {
                HuffmanTreeError::DuplicateLeaf
            } else {
                HuffmanTreeError::OrphanedLeaf
            }),
            WipHuffmanTree::Tree(ref mut zero, ref mut one) => {
                if code.is_empty() {
                    Err(HuffmanTreeError::DuplicateLeaf)
                } else {
                    match code[0] {
                        0 => zero.add(&code[1..], symbol),
                        1 => one.add(&code[1..], symbol),
                        _ => Err(HuffmanTreeError::InvalidBit),
                    }
                }
            }
        }
    }
}

/// An error type during Huffman tree compilation.
#[derive(PartialEq, Eq, Copy, Clone, Debug)]
pub enum HuffmanTreeError {
    /// One of the bits in a Huffman code is not 0 or 1
    InvalidBit,
    /// A Huffman code in the specification has no defined symbol
    MissingLeaf,
    /// The same Huffman code specifies multiple symbols
    DuplicateLeaf,
    /// A Huffman code is the prefix of some longer code
    OrphanedLeaf,
}

impl fmt::Display for HuffmanTreeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            HuffmanTreeError::InvalidBit => write!(f, "invalid bit in code"),
            HuffmanTreeError::MissingLeaf => write!(f, "missing leaf node in specification"),
            HuffmanTreeError::DuplicateLeaf => write!(f, "duplicate leaf node in specification"),
            HuffmanTreeError::OrphanedLeaf => write!(f, "orphaned leaf node in specification"),
        }
    }
}

impl Error for HuffmanTreeError {}

/// Given a vector of symbol/code pairs, compiles a Huffman tree
/// for writing.
///
/// Code must be 0 or 1 bits and are always written to the stream
/// from least-significant in the list to most signficant
/// (which makes them easier to read for humans).
///
/// If the same symbol occurs multiple times, the first code is used.
/// Unlike in read trees, not all possible codes need to be
/// assigned a symbol.
///
/// ## Examples
/// ```
/// use bitstream_io::huffman::compile_write_tree;
/// assert!(compile_write_tree::<i32>(
///     vec![(1, vec![0]),
///          (2, vec![1, 0]),
///          (3, vec![1, 1])]).is_ok());
/// ```
///
/// ```
/// use std::io::Write;
/// use bitstream_io::{BigEndian, BitWriter, BitWrite};
/// use bitstream_io::huffman::compile_write_tree;
/// let tree = compile_write_tree(
///     vec![('a', vec![0]),
///          ('b', vec![1, 0]),
///          ('c', vec![1, 1, 0]),
///          ('d', vec![1, 1, 1])]).unwrap();
/// let mut data = Vec::new();
/// {
///     let mut writer = BitWriter::endian(&mut data, BigEndian);
///     writer.write_huffman(&tree, 'b').unwrap();
///     writer.write_huffman(&tree, 'c').unwrap();
///     writer.write_huffman(&tree, 'd').unwrap();
/// }
/// assert_eq!(data, [0b10110111]);
/// ```
pub fn compile_write_tree<T>(
    values: Vec<(T, Vec<u8>)>,
) -> Result<WriteHuffmanTree<T>, HuffmanTreeError>
where
    T: Ord,
{
    values
        .into_iter()
        .map(|(symbol, bits)| {
            bits.into_iter()
                .map(|bit| match bit {
                    0 => Ok(false),
                    1 => Ok(true),
                    _ => Err(HuffmanTreeError::InvalidBit),
                })
                .collect::<Result<Vec<_>, _>>()
                .map(|bits| (symbol, bits.into_boxed_slice()))
        })
        .collect::<Result<BTreeMap<_, _>, _>>()
        .map(|map| WriteHuffmanTree { map })
}

/// A compiled Huffman tree for use with the `write_huffman` method.
/// Returned by `compiled_write_tree`.
pub struct WriteHuffmanTree<T: Ord> {
    map: BTreeMap<T, Box<[bool]>>,
}

impl<T: Ord> WriteHuffmanTree<T> {
    /// Returns true if symbol is in tree.
    #[inline]
    pub fn has_symbol(&self, symbol: &T) -> bool {
        self.map.contains_key(symbol)
    }

    /// Given symbol, returns iterator of bits for writing code.
    ///
    /// # Panics
    /// Panics if symbol is not found.
    pub fn get(&self, symbol: &T) -> impl Iterator<Item = bool> + use<'_, T> {
        self.map[symbol].iter().copied()
    }
}
