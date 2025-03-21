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

/// A trait for walking Huffman trees one bit at a time.
pub trait FromBits {
    /// Our final output type
    type Output;

    /// Returns either ourself (if we're a leaf node)
    /// or recursively calls the next item in the tree.
    fn from_bits<F, E>(&self, next: F) -> Result<&Self::Output, E>
    where
        F: FnMut() -> Result<bool, E>;
}

/// A Huffman tree leaf node containing a final value
#[derive(Debug)]
pub struct HuffmanReadTreeLeaf<T>(T);

impl<T> HuffmanReadTreeLeaf<T> {
    /// Constructs a node from its final value
    pub const fn new(value: T) -> Self {
        Self(value)
    }
}

impl<T> FromBits for HuffmanReadTreeLeaf<T> {
    type Output = T;

    #[inline(always)]
    fn from_bits<F, E>(&self, _: F) -> Result<&Self::Output, E>
    where
        F: FnMut() -> Result<bool, E>,
    {
        Ok(&self.0)
    }
}

/// A Huffman tree non-leaf node containing two sub-trees
#[derive(Debug)]
pub struct HuffmanReadTree<X, Y> {
    bit_0: X,
    bit_1: Y,
}

impl<X, Y> HuffmanReadTree<X, Y> {
    /// Constructs a tree from the 0 bit sub-tree, and 1 bit sub-tree
    pub const fn new(bit_0: X, bit_1: Y) -> Self {
        Self { bit_0, bit_1 }
    }
}

impl<X: FromBits, Y: FromBits<Output = X::Output>> FromBits for HuffmanReadTree<X, Y> {
    type Output = X::Output;

    #[inline(always)]
    fn from_bits<F, E>(&self, mut next: F) -> Result<&Self::Output, E>
    where
        F: FnMut() -> Result<bool, E>,
    {
        match next()? {
            false => self.bit_0.from_bits(next),
            true => self.bit_1.from_bits(next),
        }
    }
}

/// Builds a new Huffman tree for reading
#[macro_export]
macro_rules! compile_read_tree {
    ([$left:tt, $right:tt]) => {
        $crate::huffman::HuffmanReadTree::new(compile_read_tree!($left), compile_read_tree!($right))
    };
    ($final:tt) => {
        $crate::huffman::HuffmanReadTreeLeaf::new($final)
    };
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
