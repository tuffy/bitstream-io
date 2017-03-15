// Copyright 2017 Brian Langenberger
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Traits and implementations for reading or writing Huffman codes
//! from or to a stream.

use std::fmt;
use std::marker::PhantomData;
use std::collections::BTreeMap;
use super::Endianness;
use super::BitQueue;

pub type ReadHuffmanTree<E,T> = Vec<ReadHuffmanTreePart<E,T>>;

pub enum ReadHuffmanTreePart<E: Endianness, T: Clone> {
    Continue(Vec<ReadHuffmanTreePart<E,T>>),
    Done(T,u8,u32,PhantomData<E>)
}

pub fn compile_read_tree<E,T>(values: Vec<(T,Vec<u8>)>) ->
    Result<ReadHuffmanTree<E,T>,HuffmanTreeError>
    where E: Endianness, T: Clone {

    let tree = FinalHuffmanTree::new(values)?;

    let mut result = Vec::with_capacity(256);
    result.push(compile(BitQueue::from_value(0, 0), &tree));
    result.push(compile(BitQueue::from_value(0, 0), &tree));
    for bits in 1..8 {
        for value in 0..(1 << bits) {
            result.push(compile(BitQueue::from_value(value, bits), &tree));
        }
    }
    assert_eq!(result.len(), 256);
    Ok(result)
}

enum FinalHuffmanTree<T: Clone> {
    Leaf(T),
    Tree(Box<FinalHuffmanTree<T>>, Box<FinalHuffmanTree<T>>)
}

impl<T: Clone> FinalHuffmanTree<T> {
    fn new(values: Vec<(T, Vec<u8>)>) ->
        Result<FinalHuffmanTree<T>,HuffmanTreeError> {
        let mut tree = WipHuffmanTree::new_empty();

        for (symbol, code) in values.into_iter() {
            tree.add(code.as_slice(), symbol)?;
        }

        tree.into_read_tree()
    }
}

// Work-in-progress trees may have empty nodes during construction
// but those are not allowed in a finalized tree.
// If the user wants some codes to be None or an error symbol of some sort,
// those will need to be specified explicitly.
enum WipHuffmanTree<T: Clone> {
    Empty,
    Leaf(T),
    Tree(Box<WipHuffmanTree<T>>, Box<WipHuffmanTree<T>>)
}

impl<T: Clone> WipHuffmanTree<T> {
    fn new_empty() -> WipHuffmanTree<T> {
        WipHuffmanTree::Empty
    }

    fn new_leaf(value: T) -> WipHuffmanTree<T> {
        WipHuffmanTree::Leaf(value)
    }

    fn new_tree() -> WipHuffmanTree<T> {
        WipHuffmanTree::Tree(Box::new(Self::new_empty()),
                             Box::new(Self::new_empty()))
    }

    fn into_read_tree(self) -> Result<FinalHuffmanTree<T>,HuffmanTreeError> {
        match self {
            WipHuffmanTree::Empty => {
                Err(HuffmanTreeError::MissingLeaf)
            }
            WipHuffmanTree::Leaf(v) => {
                Ok(FinalHuffmanTree::Leaf(v))
            }
            WipHuffmanTree::Tree(zero, one) => {
                let zero = zero.into_read_tree()?;
                let one = one.into_read_tree()?;
                Ok(FinalHuffmanTree::Tree(Box::new(zero), Box::new(one)))
            }
        }
    }

    fn add(&mut self, code: &[u8], symbol: T) -> Result<(),HuffmanTreeError> {
        match self {
            &mut WipHuffmanTree::Empty => {
                if code.len() == 0 {
                    *self = WipHuffmanTree::new_leaf(symbol);
                    Ok(())
                } else {
                    *self = WipHuffmanTree::new_tree();
                    self.add(code, symbol)
                }
            }
            &mut WipHuffmanTree::Leaf(_) => {
                Err(if code.len() == 0 {
                    HuffmanTreeError::DuplicateLeaf
                } else {
                    HuffmanTreeError::OrphanedLeaf
                })
            }
            &mut WipHuffmanTree::Tree(ref mut zero, ref mut one) => {
                if code.len() == 0 {
                    Err(HuffmanTreeError::DuplicateLeaf)
                } else {
                    match code[0] {
                        0 => {zero.add(&code[1..], symbol)}
                        1 => {one.add(&code[1..], symbol)}
                        _ => {Err(HuffmanTreeError::InvalidBit)}
                    }
                }
            }
        }
    }
}

#[derive(PartialEq, Copy, Clone, Debug)]
pub enum HuffmanTreeError {
    InvalidBit,
    MissingLeaf,
    DuplicateLeaf,
    OrphanedLeaf
}

impl fmt::Display for HuffmanTreeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            HuffmanTreeError::InvalidBit => {
                write!(f, "invalid bit in code")
            }
            HuffmanTreeError::MissingLeaf => {
                write!(f, "missing leaf node in specification")
            }
            HuffmanTreeError::DuplicateLeaf => {
                write!(f, "duplicate leaf node in specification")
            }
            HuffmanTreeError::OrphanedLeaf => {
                write!(f, "orphaned leaf node in specification")
            }
        }
    }
}

pub struct WriteHuffmanTree<E: Endianness, T: Ord> {
    map: BTreeMap<T,(u32,u64)>,
    phantom: PhantomData<E>
}

impl<E: Endianness, T: Ord + Clone> WriteHuffmanTree<E,T> {
    /// Given a vector of symbol/code pairs, compiles a Huffman tree
    /// for writing.
    /// Code must be 0 or 1 bits and are always written to the stream
    /// from least-significant in the list to most signficant
    /// (which makes them easier to read for humans).
    ///
    /// If the same symbol occurs multiple times, the first code is used.
    /// Unlike in read trees, not all possible codes need to be
    /// assigned a symbol.
    ///
    /// ## Example
    /// ```
    /// use bitstream_io::huffman::WriteHuffmanTree;
    /// use bitstream_io::BigEndian;
    /// assert!(WriteHuffmanTree::<BigEndian,i32>::new(
    ///     vec![(1, vec![0]),
    ///          (2, vec![1, 0]),
    ///          (3, vec![1, 1])]).is_ok());
    /// ```
    pub fn new(values: Vec<(T, Vec<u8>)>) ->
        Result<WriteHuffmanTree<E,T>,HuffmanTreeError> {
        use super::BitQueue;

        // This current implementation is limited to Huffman codes
        // that generate up to 64 bits.  It may need to be updated
        // if I can find anything larger.

        let mut map = BTreeMap::new();

        for (symbol, code) in values.into_iter() {
            let mut encoded = BitQueue::<E,u64>::new();
            let code_len = code.len() as u32;
            for bit in code {
                if (bit != 0) && (bit != 1) {
                    return Err(HuffmanTreeError::InvalidBit);
                }
                encoded.push(1, bit as u64);
            }
            map.entry(symbol.clone()).or_insert((code_len, encoded.value()));
        }

        Ok(WriteHuffmanTree{map: map, phantom: PhantomData})
    }

    /// Returns true if symbol is in tree.
    pub fn has_symbol(&self, symbol: T) -> bool {
        self.map.contains_key(&symbol)
    }

    /// Given symbol, returns (bits, value) pair for writing code.
    /// Panics if symbol is not found.
    pub fn get(&self, symbol: T) -> (u32, u64) {
        self.map[&symbol]
    }
}

fn compile<E,T>(mut queue: BitQueue<E,u8>, tree: &FinalHuffmanTree<T>) ->
    ReadHuffmanTreePart<E,T> where E: Endianness, T: Clone {
    match tree {
        &FinalHuffmanTree::Leaf(ref value) => {
            let len = queue.len();
            ReadHuffmanTreePart::Done(
                value.clone(), queue.value(), len, PhantomData)
        }
        &FinalHuffmanTree::Tree(ref bit0, ref bit1) => {
            if queue.is_empty() {
                let mut next_byte = Vec::with_capacity(256);
                for byte in 0..256u16 {
                    next_byte.push(
                        compile(BitQueue::from_value(byte as u8, 8), tree));
                }
                ReadHuffmanTreePart::Continue(next_byte)
            } else {
                if queue.pop(1) == 0 {
                    compile(queue, bit0)
                } else {
                    compile(queue, bit1)
                }
            }
        }
    }
}
