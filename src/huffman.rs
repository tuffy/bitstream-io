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

/// A trait for building a final value from individual bits
pub trait FromBits {
    /// Our final output type
    type Output;

    /// Given a fallable bit generator, return our output type
    ///
    /// # Errors
    ///
    /// Passes along any error from the bit generator
    fn from_bits<F, E>(next: F) -> Result<Self::Output, E>
    where
        F: FnMut() -> Result<bool, E>;
}

/// Defines a new Huffman tree for reading
///
/// Its syntax is: `define_huffman_tree!(name : type , nodes)`
/// where `name` is some identifier to identify the tree in the
/// macro's current scope, `type` is the tree's output
/// type (which should implement `Copy`), and `nodes` is either a
/// final leaf value or a `[bit_0, bit_1]` pair where `bit_0` is
/// the tree visited on a `0` bit, and `bit_1` is the tree visited
/// on a `1` bit.
///
/// # Example
///
/// ```
/// use bitstream_io::{define_huffman_tree, huffman::FromBits};
/// define_huffman_tree!(TreeName : &'static str , ["bit 0", ["bit 1->0", "bit 1->1"]]);
/// let mut bits = [true, false].iter().copied();
/// assert_eq!(TreeName::from_bits(|| bits.next().ok_or(())).unwrap(), "bit 1->0");
/// ```
#[macro_export]
macro_rules! define_huffman_tree {
    ($name:ident : $type:ty , $nodes:tt) => {
        #[derive(Copy, Clone, Debug)]
        struct $name;

        impl $crate::huffman::FromBits for $name {
            type Output = $type;

            fn from_bits<F, E>(mut next: F) -> Result<Self::Output, E>
            where
                F: FnMut() -> Result<bool, E>,
            {
                $crate::compile_tree_nodes!(next, $nodes)
            }
        }
    };
}

/// A helper macro for compiling individual Huffman tree nodes
#[macro_export]
macro_rules! compile_tree_nodes {
    ($next:ident , [$bit_0:tt, $bit_1:tt]) => {
        if $next()? {
            $crate::compile_tree_nodes!($next, $bit_1)
        } else {
            $crate::compile_tree_nodes!($next, $bit_0)
        }
    };
    ($next:ident , $final:tt) => {
        Ok($final)
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
