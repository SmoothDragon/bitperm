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

// use derive_more::*;
// use thiserror::*;
// use arrayvec::*;

use crate::bitgrid8::*;
use crate::piece_bitgrid8::*;


#[derive(Debug, Clone, PartialEq)]
pub struct PackBitGrid8{
    placed: Vec<BitGrid8>,  // List of placed pieces. The first piece should be the frame (black).
    fill: BitGrid8,  // Current packing state. Union of all the placed pieces.
    piece: HashMap<PieceBitGrid8, u32>,  // Number of available copies of each piece.
    location: HashMap<PieceBitGrid8, Vec<BitGrid8>>,  // valid locations where a piece can still fit.
    border: HashMap<BitGrid8, Vec<BitGrid8>>,  // valid piece placements that cover border bit at (1 << loc)
}

impl PackBitGrid8 {
    /// TODO: Pass in an iterator of &T instead of a vector
    pub fn new(frame: BitGrid8, pieces: Vec<PieceBitGrid8>) -> Self 
    // where
        // T: Iterator<Item = PieceBitGrid8>,
    {
        let piece_count = Self::piece_counter(&pieces);

        let piece_location = Self::piece_location(frame, &pieces);

        Self {
            placed: vec![frame],
            fill: frame,
            piece: piece_count,
            border: Self::domino_covers(frame, &piece_location),
            location: piece_location,
        }
    }

    pub fn piece_location(frame: BitGrid8, pieces: &Vec<PieceBitGrid8>) -> HashMap<PieceBitGrid8, Vec<BitGrid8>> {
        let mut piece_location = HashMap::<PieceBitGrid8, Vec<BitGrid8>>::new();
        for &piece in pieces {
            piece_location.insert(piece, Self::piece_placement(frame, piece));
        }
        piece_location
    }


    pub fn piece_counter(pieces: &Vec<PieceBitGrid8>) -> HashMap<PieceBitGrid8, u32> {
        // This mimics Counter returning a HashMap with the number of times an item is seen.
        let mut piece_count = HashMap::<PieceBitGrid8, u32>::new();
        for piece in pieces {
            piece_count.entry(*piece).and_modify(|counter| *counter += 1).or_insert(1);
        }
        piece_count
    }

    pub fn piece_placement(frame: BitGrid8, piece: PieceBitGrid8) -> Vec<BitGrid8> {
        let mut good = Vec::<BitGrid8>::new();
        for putative in piece.rotate_flip_all() {
            let grid = putative.grid;
            let (m, n) = putative.xy;
            for ii in 0..=(8-m) {
                for jj in 0..=(8-n) {
                    if let Some(shifted) = grid.checked_shift_xy(ii as i32, jj as i32) {
                        if shifted.0 & frame.0 == 0 { 
                            // println!("{}", shifted | frame);
                            good.push(shifted) 
                        }
                    }
                }
            }
        }
        good
    }

    pub fn domino_covers(
        filled: BitGrid8, 
        piece_location: &HashMap<PieceBitGrid8, Vec<BitGrid8>>
        ) -> HashMap<BitGrid8, Vec<BitGrid8>> 
    {
        let mut domino_location = HashMap::<BitGrid8, Vec<BitGrid8>>::new();
        for ii in 0..7 {
            for jj in 0..8 {
                let pos_x = ii+8*jj;
                let block_x = 0x3 << pos_x;
                if block_x & filled.0 != 0 { continue };
                let mut cover_x = Vec::<BitGrid8>::new();
                for piece_grid in piece_location.values() {
                    for &grid in piece_grid {
                        if grid.0 & block_x == block_x {
                            cover_x.push(grid);
                        }
                    }
                }
                domino_location.insert(BitGrid8(block_x), cover_x);
            }
        }
        for ii in 0..7 {
            for jj in 0..8 {
                let pos_y = 8*ii+jj;
                let block_y = 0x101 << pos_y;
                if block_y & filled.0 != 0 { continue };
                let mut cover_y = Vec::<BitGrid8>::new();
                for piece_grid in piece_location.values() {
                    for &grid in piece_grid {
                        if grid.0 & block_y == block_y {
                            cover_y.push(grid);
                        }
                    }
                }
                domino_location.insert(BitGrid8(block_y), cover_y);
            }
        }
        domino_location
    }

}

impl fmt::Display for PackBitGrid8 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", 
            (0..8).rev().map(|y|
                (0..8)
                    .map(|x| format!("{}", if (self.fill.0 >> (x + 8*y)) & 0x1 == 1 { "\u{2B1B}" } else { "⬜" }))
                    .collect::<String>()
                    +"\n")
            .collect::<String>()
        )
    } 
} 


#[cfg(test)]
mod test {
    use super::*;
    
    #[test]
    fn test_pack_bitgrid8_new() {
        assert_eq!(PackBitGrid8::new(BitGrid8(0x1818000000), PieceBitGrid8::pentomino_map().into_values().collect::<Vec<_>>()).piece,
            HashMap::from([(PieceBitGrid8::new(0x03010101), 1), (PieceBitGrid8::new(0x00070101), 1), (PieceBitGrid8::new(0x00000f04), 1), (PieceBitGrid8::new(0x00060301), 1), (PieceBitGrid8::new(0x101010101), 1), (PieceBitGrid8::new(0x00000705), 1), (PieceBitGrid8::new(0x00020207), 1), (PieceBitGrid8::new(0x00010303), 1), (PieceBitGrid8::new(0x00020306), 1), (PieceBitGrid8::new(0x00060203), 1), (PieceBitGrid8::new(0x00020702), 1), (PieceBitGrid8::new(0x00000e03), 1)]))
    }

    #[test]
    fn test_pack_bitgrid8_display() {
        // assert_eq!(Some(PieceBitGrid8::pentomino_map().values().collect::<Vec<_>>()), None);
        // println!("{}", PackBitGrid8::new(0x1818000000, PieceBitGrid8::pentomino_map().values()));
        assert_eq!(format!("{}", PackBitGrid8::new(BitGrid8(0x1818000000), PieceBitGrid8::pentomino_map().into_values().collect::<Vec<_>>())),
        "⬜⬜⬜⬜⬜⬜⬜⬜\n⬜⬜⬜⬜⬜⬜⬜⬜\n⬜⬜⬜⬜⬜⬜⬜⬜\n⬜⬜⬜⬛⬛⬜⬜⬜\n⬜⬜⬜⬛⬛⬜⬜⬜\n⬜⬜⬜⬜⬜⬜⬜⬜\n⬜⬜⬜⬜⬜⬜⬜⬜\n⬜⬜⬜⬜⬜⬜⬜⬜\n");
    }

    #[test]
    fn test_pack_bitgrid8_piece_placement() {
        // Placements avoid central 4x4 square
        assert_eq!(PackBitGrid8::piece_placement(BitGrid8(0x3c3c3c3c0000), PieceBitGrid8::pentomino_map()[&'F']).len(), 32);
        assert_eq!(PackBitGrid8::piece_placement(BitGrid8(0x3c3c3c3c0000), PieceBitGrid8::pentomino_map()[&'L']).len(), 96);
        assert_eq!(PackBitGrid8::piece_placement(BitGrid8(0x3c3c3c3c0000), PieceBitGrid8::pentomino_map()[&'I']).len(), 32);
        assert_eq!(PackBitGrid8::piece_placement(BitGrid8(0x3c3c3c3c0000), PieceBitGrid8::pentomino_map()[&'P']).len(), 104);
        assert_eq!(PackBitGrid8::piece_placement(BitGrid8(0x3c3c3c3c0000), PieceBitGrid8::pentomino_map()[&'N']).len(), 88);
        assert_eq!(PackBitGrid8::piece_placement(BitGrid8(0x3c3c3c3c0000), PieceBitGrid8::pentomino_map()[&'T']).len(), 16);
        assert_eq!(PackBitGrid8::piece_placement(BitGrid8(0x3c3c3c3c0000), PieceBitGrid8::pentomino_map()[&'U']).len(), 48);
        assert_eq!(PackBitGrid8::piece_placement(BitGrid8(0x3c3c3c3c0000), PieceBitGrid8::pentomino_map()[&'V']).len(), 16);
        assert_eq!(PackBitGrid8::piece_placement(BitGrid8(0x3c3c3c3c0000), PieceBitGrid8::pentomino_map()[&'W']).len(), 16);
        assert_eq!(PackBitGrid8::piece_placement(BitGrid8(0x3c3c3c3c0000), PieceBitGrid8::pentomino_map()[&'X']).len(), 4);
        assert_eq!(PackBitGrid8::piece_placement(BitGrid8(0x3c3c3c3c0000), PieceBitGrid8::pentomino_map()[&'Y']).len(), 88);
        assert_eq!(PackBitGrid8::piece_placement(BitGrid8(0x3c3c3c3c0000), PieceBitGrid8::pentomino_map()[&'Z']).len(), 16);
    }

    #[test]
    fn test_pack_bitgrid8_domino_covers() {
        // Placements avoid central 4x4 square
        let frame = BitGrid8(0x3c3c3c3c0000);
        let piece_location = PackBitGrid8::piece_location(frame, &PieceBitGrid8::pentomino_map().into_values().collect::<Vec<_>>());
        let domino = PackBitGrid8::domino_covers(frame, &piece_location);
        // for grid in &domino[&BitGrid8(0x1800)] {
            // println!("{:}", grid);
        // }
        // Horizontal 2x1 domino
        assert_eq!(domino[&BitGrid8(0x3)].len(), 20);
        assert_eq!(domino[&BitGrid8(0x6)].len(), 30);
        assert_eq!(domino[&BitGrid8(0xc)].len(), 31);
        assert_eq!(domino[&BitGrid8(0x18)].len(), 30);
        assert_eq!(domino[&BitGrid8(0x30)].len(), 31);
        assert_eq!(domino[&BitGrid8(0x60)].len(), 30);
        assert_eq!(domino[&BitGrid8(0xc0)].len(), 20);
        assert_eq!(domino[&BitGrid8(0x300)].len(), 38);
        assert_eq!(domino[&BitGrid8(0x600)].len(), 50);
        assert_eq!(domino[&BitGrid8(0xc00)].len(), 37);
        assert_eq!(domino[&BitGrid8(0x1800)].len(), 32);
        assert_eq!(domino[&BitGrid8(0x3000)].len(), 37);
        assert_eq!(domino[&BitGrid8(0x6000)].len(), 50);
        assert_eq!(domino[&BitGrid8(0xc000)].len(), 38);

        // Vertical 1x2 domino
        assert_eq!(domino[&BitGrid8(0x101)].len(), 20);
        assert_eq!(domino[&BitGrid8(0x10100)].len(), 30);
        assert_eq!(domino[&BitGrid8(0x202)].len(), 38);
    }

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
