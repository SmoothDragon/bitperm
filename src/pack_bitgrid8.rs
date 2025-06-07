// -----------------------------------------------------------------
// Methods for packing 2D geometric pieces into an 8x8 grid
// -----------------------------------------------------------------
//
// Partial solution state has the following:
// frame: BitGrit8 => This marks the original puzzle frame. Black. (May be first piece?)
// fill: BitGrit8 => Current packing state. Starts equal to frame.
// piece: { PieceBitGrid8 -> count: u32 } => Copy of each piece.
// location: { PieceBitGrid8 -> Vec<BitGrid8> }
//      => valid locations where a piece can still fit.
//  cover: { loc: u32 -> Vec<BitGrid8> } 
//      => valid piece placements that cover bit at (1 << loc)
// -----------------------------------------------------------------

use std::fmt;
use std::collections::HashMap;

use derive_more::*;
use thiserror::*;
use arrayvec::*;

use crate::bitgrid8::*;
use crate::piece_bitgrid8::*;


#[derive(Debug, Clone, PartialEq)]
pub struct PackBitGrid8{
    fill: BitGrid8,  // Current packing state. Starts equal to frame.
    piece: HashMap<PieceBitGrid8, u32>,  // Number of copies of each piece.
    location: HashMap<PieceBitGrid8, Vec<BitGrid8>>,  // valid locations where a piece can still fit.
    border: HashMap<u32, Vec<BitGrid8>>,  // valid piece placements that cover border bit at (1 << loc)
}



// #[derive(Error, Debug, Clone, PartialEq)]
// #[error("{0} is not origin shifted.")]
// pub struct PieceGrid8Error(u64, String);

#[cfg(test)]
mod test {
    use super::*;
    
    /*
    #[test]
    /// The pentominoes are supposed to tile an 8x8 square minus the 2x2 square in the middle.
    fn test_pentomino_annulus{
        let start = PackBitGrid8 {
            fill: BitGrit8(0x8181000000),
            piece: pentomino_map().into_iter().map(|(_, piece)| (piece, 1)).collect::<HashMap<PieceBitGrid8, u32>>,
            location: 
    */

}
