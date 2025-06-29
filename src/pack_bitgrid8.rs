// -----------------------------------------------------------------
// Methods for packing 2D geometric pieces into an 8x8 grid
// -----------------------------------------------------------------
//
// Partial solution state has the following:
// frame: BitGrit8 => This marks the original puzzle frame. Black. (May be first piece?)
// fill: BitGrit8 => Current packing state. Starts equal to frame.
// piece_counts: { OriginBitGrid8 -> count: usize } => Copies to be used of each piece.
// putative_pieces: { OriginBitGrid8 -> Vec<BitGrid8> }
//      => valid locations where a piece can still fit.
//  cover: { loc: usize -> Vec<BitGrid8> } 
//      => valid piece placements that cover bit at (1 << loc)
// -----------------------------------------------------------------

use std::fmt;
// use std::collections::HashMap;
use std::{ops::SubAssign, collections::{HashMap, hash_map::Entry::*}};

// use std::iter::once;
// use derive_more::*;
// use thiserror::*;
// use arrayvec::*;

use crate::bitgrid8::*;
use crate::piece_bitgrid8::*;


#[derive(Debug, Clone, PartialEq)]
pub struct PackingGrid8{
    fill: BitGrid8,
    pieces: Vec<BitGrid8>,
}

impl PackingGrid8 {
    pub fn new() -> Self {
        Self{ fill: BitGrid8(0), pieces: vec![] }
    }

    pub fn from_vec(pieces: Vec<BitGrid8>) -> Option<Self> {
        let mut fill = BitGrid8(0);

        for piece in &pieces {
            if fill.has_overlap(*piece) { return None };
            fill |= *piece;
        }
        Some(Self{ fill: fill, pieces: pieces })
    }

    pub fn add(&self, piece: BitGrid8) -> Option<Self> {
        if self.fill.has_overlap(piece) { return None };

        let new_pieces: Vec<BitGrid8> = self.pieces
            .iter()
            .map(|x| *x)
            .chain(std::iter::once(piece))
            .collect();
        Some(Self{ fill: self.fill | piece, pieces: new_pieces })
    }
}

const COLORED_BLOCKS: [&str; 15] = [ 
    "\u{2B1C}",  // white square
    "\u{2B1B}",  // black square
    "\u{1F7E5}",  // red square
    "\u{1F7E6}",  // blue square
    "\u{1F7E7}",  // black square
    "\u{1F7E8}",  // black square
    "\u{1F7E9}",  // black square
    "\u{1F7EA}",  // black square
    "\u{1F7EB}",  // black square
    // "\u{25EF}",  // white circle
    "\u{26AB}",  // black circle
    "\u{1F7E0}",  // orange circle
    "\u{1F7E1}",  // yellow circle
    "\u{1F7E2}",  // green circle
    "\u{1F7E3}",  // purple circle
    "\u{1F7E4}",  // brown circle
    ];

impl fmt::Display for PackingGrid8 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut array: [&str; 64] = [&COLORED_BLOCKS[0]; 64];
        let mut count: usize = 1;
        for grid in &self.pieces {
            // TODO: this can be sped up by a better iterator
            for ii in 0..64 {
                if (grid.0 >> ii) & 1 == 1 {
                    array[ii] = &COLORED_BLOCKS[count];
                }
            }
            count += 1;
        }
        write!(f, "{}", 
            (0..8).rev().map(|y|
                (0..8)
                    .map(|x| format!("{}", &array[x + 8*y]))
                    .collect::<String>()
                    +"\n")
            .collect::<String>()
        )
    } 
} 

// TODO:
// new() is creation of initial solution state
// + add entropy calculation
// + remove domino cover
// + add square cover
// add_piece() should create a new solution state
// - Update the piece location lists
// - Update the grid square cover lists
// - If any of the above lists have length zero -> return None
// 

#[derive(Debug, Clone, PartialEq)]
pub struct PackBitGrid8{
    packing: PackingGrid8, // List of placed pieces. The first piece should be the frame (black).
    piece_counts: HashMap<D4CanonicalGrid8, usize>,  // Number of available copies of each piece.
    putative_pieces: HashMap<D4CanonicalGrid8, Vec<BitGrid8>>,  // valid locations where a piece can still fit.
    putative_corners: BitGrid8,
    entropy: f64,
    // domino_covers: HashMap<BitGrid8, Vec<BitGrid8>>,  // valid piece placements that cover a given domino
}

impl PackBitGrid8 {
    pub fn new(frame: BitGrid8, piece_counts: HashMap<D4CanonicalGrid8, usize>) -> Self 
    {
        let putative_pieces = Self::putative_pieces(frame, piece_counts.keys());
        let entropy = putative_pieces.iter().map(|(piece, locations)| 
            (piece_counts[piece] as f64) * (locations.len() as f64).log2()).sum();

        Self {
            packing: PackingGrid8::from_vec(vec![frame]).expect("Adding a single piece shouldn't conflict."),
            piece_counts: piece_counts,
            putative_pieces: putative_pieces,
            putative_corners: frame.find_corners(),
            entropy: entropy,
        }
    }

    pub fn add_piece(&self, grid: BitGrid8) -> Option<Self> {
        if let Some(packing) = self.packing.add(grid) {
            let mut piece_counts = self.piece_counts.clone();
            let piece = D4CanonicalGrid8::from(grid);

            // Reduce piece count by one, removing the piece if none left.
            match piece_counts.entry(piece) {
                Vacant(_) => { return None },  // Can't remove a piece we don't have
                Occupied(x) if *x.get() <= 1 => { x.remove(); },  // Remove final piece from dict
                Occupied(mut x) => { x.get_mut().sub_assign(1); },
            }

            // Remove putative locations that conflict with new piece
            // let putative_pieces = Self::putative_pieces(packing.fill, &pieces);
            
            Some(Self {
                packing: packing,
                piece_counts: piece_counts,
                ..self.clone()
                // putative_pieces: putative_pieces,
            })
        } else {
            return None
        }
    }

    // pub fn putative_pieces(frame: BitGrid8, pieces: &Vec<OriginBitGrid8>) -> HashMap<OriginBitGrid8, Vec<BitGrid8>> {
        // let mut putative_pieces = HashMap::<OriginBitGrid8, Vec<BitGrid8>>::new();
        // for &piece in pieces {
            // putative_pieces.insert(piece.canonical(), Self::piece_placement(frame, piece));
        // }
        // putative_pieces
    // }

    pub fn putative_pieces<'a, I>(frame: BitGrid8, pieces: I) -> HashMap<D4CanonicalGrid8, Vec<BitGrid8>> 
        where
            I: IntoIterator<Item = &'a D4CanonicalGrid8>,
    {
        let mut putative_pieces = HashMap::<D4CanonicalGrid8, Vec<BitGrid8>>::new();
        for &piece in pieces.into_iter() {
            putative_pieces.insert(piece, Self::piece_placement(frame, piece));
        }
        putative_pieces
    }

    pub fn piece_counter(pieces: &Vec<D4CanonicalGrid8>) -> HashMap<D4CanonicalGrid8, usize> {
        // This mimics Counter returning a HashMap with the number of times an item is seen.
        let mut piece_counts = HashMap::<D4CanonicalGrid8, usize>::new();
        for piece in pieces {
            piece_counts.entry(*piece).and_modify(|counter| *counter += 1).or_insert(1);
        }
        piece_counts
    }

    pub fn piece_placement(frame: BitGrid8, piece: D4CanonicalGrid8) -> Vec<BitGrid8> {
        let mut good = Vec::<BitGrid8>::new();
        for putative in piece.symmetry_d4() {
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

    /*
    pub fn next_piece(&self) -> OriginBitGrid8 {
        let mut best_count = 1000000;
        let mut best_piece = OriginBitGrid8::new(0);
        for (piece, piece_list) in &self.putative_pieces {
            let count = piece_list.len();
            if count < best_count {
                best_piece = *piece;
                best_count = count;
            }
        }
        best_piece
    }

    pub fn next_domino(&self) -> BitGrid8 {
        let mut best_count = 1000000;
        let mut best_domino = BitGrid8(0);
        for (domino, domino_list) in &self.domino_covers {
            let count = domino_list.len();
            if count < best_count {
                best_domino = *domino;
                best_count = count;
            }
        }
        best_domino
    }
    */

    // pub fn next_corner(&self) -> BitGrid8 {
        // let mut best_count = 1000000;
        // let mut best_corner = BitGrid8(0);
        // for (domino, domino_list) in &self.domino_covers {
            // let count = domino_list.len();
            // if count < best_count {
                // best_domino = *domino;
                // best_count = count;
            // }
        // }
        // best_domino
    // }

    /// Return all the pieces that cover a corner.
    /// This assumes that all piece locations do not intersect with the filled area.
    pub fn corner_covers(
        filled: BitGrid8, 
        putative_pieces: &HashMap<D4CanonicalGrid8, Vec<BitGrid8>>
        ) -> Vec<BitGrid8>
    {
        let mut corner_pieces = Vec::<BitGrid8>::new();
        let corners = filled.find_corners();

        for piece_grid in putative_pieces.values() {
            for &grid in piece_grid {
                if grid.has_overlap(corners) {
                    corner_pieces.push(grid);
                }
            }
        }
        corner_pieces
    }


    /* 
    pub fn next_corner(
        filled: BitGrid8, 
        corner_pieces: &Vec<BitGrid8>
        ) -> BitGrid8
    {
        let corners = filled.find_corners();

        for piece_grid in putative_pieces.values() {
            for &grid in piece_grid {
                if grid.has_overlap(corners) {
                    corner_pieces.push(grid);
                }
            }
        }
        corner_pieces
    }
    */

    // For each non-fill domino, return a list of the available pieces that can cover it.
    pub fn domino_covers(
        filled: BitGrid8, 
        putative_pieces: &HashMap<D4CanonicalGrid8, Vec<BitGrid8>>
        ) -> HashMap<BitGrid8, Vec<BitGrid8>> 
    {
        let mut domino_location = HashMap::<BitGrid8, Vec<BitGrid8>>::new();
        for ii in 0..7 {
            for jj in 0..8 {
                let pos_x = ii+8*jj;
                let block_x = 0x3 << pos_x;
                if block_x & filled.0 != 0 { continue };
                let mut cover_x = Vec::<BitGrid8>::new();
                for piece_grid in putative_pieces.values() {
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
                for piece_grid in putative_pieces.values() {
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
                    .map(|x| format!("{}", if (self.packing.fill.0 >> (x + 8*y)) & 0x1 == 1 { "\u{2B1B}" } else { "⬜" }))
                    .collect::<String>()
                    +"\n")
            .collect::<String>()
        )
    } 
} 


#[cfg(test)]
mod test {
    use super::*;
    
    // #[test]
    // fn test_pack_bitgrid8_new() {
        // assert_eq!(PackBitGrid8::new(BitGrid8(0x1818000000), OriginBitGrid8::pentomino_map().into_values().map(|x| (x, 1_usize)).collect::<HashMap<OriginBitGrid8, usize>>()).piece_counts,
            // HashMap::from([(OriginBitGrid8::new(0x03010101), 1), (OriginBitGrid8::new(0x00070101), 1), (OriginBitGrid8::new(0x00000f04), 1), (OriginBitGrid8::new(0x00060301), 1), (OriginBitGrid8::new(0x101010101), 1), (OriginBitGrid8::new(0x00000705), 1), (OriginBitGrid8::new(0x00020207), 1), (OriginBitGrid8::new(0x00010303), 1), (OriginBitGrid8::new(0x00020306), 1), (OriginBitGrid8::new(0x00060203), 1), (OriginBitGrid8::new(0x00020702), 1), (OriginBitGrid8::new(0x00000e03), 1)]))
    // }

    /*
    #[test]
    fn test_pack_bitgrid8_display() {
        // assert_eq!(Some(OriginBitGrid8::pentomino_map().values().collect::<Vec<_>>()), None);
        // println!("{}", PackBitGrid8::new(0x1818000000, OriginBitGrid8::pentomino_map().values()));
        assert_eq!(format!("{}", PackBitGrid8::new(BitGrid8(0x1818000000), OriginBitGrid8::pentomino_map().into_values().map(|x| (x, 1_usize)).collect::<HashMap<OriginBitGrid8, usize>>())),
        // assert_eq!(format!("{}", PackBitGrid8::new(BitGrid8(0x1818000000), OriginBitGrid8::pentomino_map().into_values().collect::<Vec<_>>())),
        "⬜⬜⬜⬜⬜⬜⬜⬜\n⬜⬜⬜⬜⬜⬜⬜⬜\n⬜⬜⬜⬜⬜⬜⬜⬜\n⬜⬜⬜⬛⬛⬜⬜⬜\n⬜⬜⬜⬛⬛⬜⬜⬜\n⬜⬜⬜⬜⬜⬜⬜⬜\n⬜⬜⬜⬜⬜⬜⬜⬜\n⬜⬜⬜⬜⬜⬜⬜⬜\n");
    }
    */

    #[test]
    fn test_packing_grid8_display() {
        assert_eq!(format!("{}", PackingGrid8::new()),
        "⬜⬜⬜⬜⬜⬜⬜⬜\n⬜⬜⬜⬜⬜⬜⬜⬜\n⬜⬜⬜⬜⬜⬜⬜⬜\n⬜⬜⬜⬜⬜⬜⬜⬜\n⬜⬜⬜⬜⬜⬜⬜⬜\n⬜⬜⬜⬜⬜⬜⬜⬜\n⬜⬜⬜⬜⬜⬜⬜⬜\n⬜⬜⬜⬜⬜⬜⬜⬜\n");
        assert_eq!(format!("{}", PackingGrid8::from_vec(vec![BitGrid8(0x1818000000)]).unwrap()),
        "⬜⬜⬜⬜⬜⬜⬜⬜\n⬜⬜⬜⬜⬜⬜⬜⬜\n⬜⬜⬜⬜⬜⬜⬜⬜\n⬜⬜⬜⬛⬛⬜⬜⬜\n⬜⬜⬜⬛⬛⬜⬜⬜\n⬜⬜⬜⬜⬜⬜⬜⬜\n⬜⬜⬜⬜⬜⬜⬜⬜\n⬜⬜⬜⬜⬜⬜⬜⬜\n");
        assert_eq!(format!("{}", PackingGrid8::from_vec(vec![BitGrid8(0x1818000000), BitGrid8(0x20306)]).unwrap()),
        "⬜⬜⬜⬜⬜⬜⬜⬜\n⬜⬜⬜⬜⬜⬜⬜⬜\n⬜⬜⬜⬜⬜⬜⬜⬜\n⬜⬜⬜⬛⬛⬜⬜⬜\n⬜⬜⬜⬛⬛⬜⬜⬜\n⬜🟥⬜⬜⬜⬜⬜⬜\n🟥🟥⬜⬜⬜⬜⬜⬜\n⬜🟥🟥⬜⬜⬜⬜⬜\n");
        assert_eq!(format!("{}", PackingGrid8::from_vec(vec![BitGrid8(0x1818000000), BitGrid8(0x20306), BitGrid8(0x203060)]).unwrap()),
        "⬜⬜⬜⬜⬜⬜⬜⬜\n⬜⬜⬜⬜⬜⬜⬜⬜\n⬜⬜⬜⬜⬜⬜⬜⬜\n⬜⬜⬜⬛⬛⬜⬜⬜\n⬜⬜⬜⬛⬛⬜⬜⬜\n⬜🟥⬜⬜⬜🟦⬜⬜\n🟥🟥⬜⬜🟦🟦⬜⬜\n⬜🟥🟥⬜⬜🟦🟦⬜\n");
    }

    #[test]
    fn test_packing_grid8_add() {
        assert_eq!(PackingGrid8::new().add(BitGrid8(0x1818000000)),
            PackingGrid8::from_vec(vec![BitGrid8(0x1818000000)]));
        assert_eq!(PackingGrid8::from_vec(vec![BitGrid8(0x1818000000), BitGrid8(0x20306)]).unwrap().add(BitGrid8(0x203060)),
            PackingGrid8::from_vec(vec![BitGrid8(0x1818000000), BitGrid8(0x20306), BitGrid8(0x203060)]));
    }

    #[test]
    fn test_pack_bitgrid8_piece_placement() {
        let pentomino = OriginBitGrid8::pentomino_map();
        // Placements avoid central 4x4 square
        assert_eq!(PackBitGrid8::piece_placement(BitGrid8(0x3c3c3c3c0000), D4CanonicalGrid8::new(pentomino[&'F'])).len(), 32);
        assert_eq!(PackBitGrid8::piece_placement(BitGrid8(0x3c3c3c3c0000), D4CanonicalGrid8::new(pentomino[&'L'])).len(), 96);
        assert_eq!(PackBitGrid8::piece_placement(BitGrid8(0x3c3c3c3c0000), D4CanonicalGrid8::new(pentomino[&'I'])).len(), 32);
        assert_eq!(PackBitGrid8::piece_placement(BitGrid8(0x3c3c3c3c0000), D4CanonicalGrid8::new(pentomino[&'P'])).len(), 104);
        assert_eq!(PackBitGrid8::piece_placement(BitGrid8(0x3c3c3c3c0000), D4CanonicalGrid8::new(pentomino[&'N'])).len(), 88);
        assert_eq!(PackBitGrid8::piece_placement(BitGrid8(0x3c3c3c3c0000), D4CanonicalGrid8::new(pentomino[&'T'])).len(), 16);
        assert_eq!(PackBitGrid8::piece_placement(BitGrid8(0x3c3c3c3c0000), D4CanonicalGrid8::new(pentomino[&'U'])).len(), 48);
        assert_eq!(PackBitGrid8::piece_placement(BitGrid8(0x3c3c3c3c0000), D4CanonicalGrid8::new(pentomino[&'V'])).len(), 16);
        assert_eq!(PackBitGrid8::piece_placement(BitGrid8(0x3c3c3c3c0000), D4CanonicalGrid8::new(pentomino[&'W'])).len(), 16);
        assert_eq!(PackBitGrid8::piece_placement(BitGrid8(0x3c3c3c3c0000), D4CanonicalGrid8::new(pentomino[&'X'])).len(), 4);
        assert_eq!(PackBitGrid8::piece_placement(BitGrid8(0x3c3c3c3c0000), D4CanonicalGrid8::new(pentomino[&'Y'])).len(), 88);
        assert_eq!(PackBitGrid8::piece_placement(BitGrid8(0x3c3c3c3c0000), D4CanonicalGrid8::new(pentomino[&'Z'])).len(), 16);
    }

    #[test]
    fn test_pack_bitgrid8_domino_covers() {
        // Placements avoid central 4x4 square
        let frame = BitGrid8(0x3c3c3c3c0000);
        let putative_pieces = PackBitGrid8::putative_pieces(frame, &OriginBitGrid8::pentomino_map().values()
            .map(|x| D4CanonicalGrid8::new(*x)).collect::<Vec<_>>());
        let domino = PackBitGrid8::domino_covers(frame, &putative_pieces);
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

    /* TODO: return to this
    #[test]
    fn test_pack_bitgrid8_next_piece() {
        // Placements avoid central 4x4 square
        let center4x4 = BitGrid8(0x3c3c3c3c0000);
        let center2x2 = BitGrid8(0x1818000000);
        let start = PackBitGrid8::new(center2x2, OriginBitGrid8::pentomino_map().into_values().collect::<Vec<_>>());
        let next_piece = start.next_piece();
        assert_eq!(next_piece, OriginBitGrid8::new(0x20702));
        assert_eq!(start.putative_pieces[&next_piece].len(), 24);
        let start = PackBitGrid8::new(center4x4, OriginBitGrid8::pentomino_map().into_values().collect::<Vec<_>>());
        let next_piece = start.next_piece();
        assert_eq!(next_piece, OriginBitGrid8::new(0x20702));
        assert_eq!(start.putative_pieces[&next_piece].len(), 4);
    }
    */

    // #[test]
    // fn test_pack_bitgrid8_add_piece() {
        // let center2x2 = BitGrid8(0x1818000000);
        // let state0 = PackBitGrid8::new(center2x2, OriginBitGrid8::pentomino_map().into_values().collect::<Vec<_>>());
        // assert_eq!(state0.piece_counts.len(), 12);
        // let next_piece = state0.next_piece();
        // let piece_to_add = state0.putative_pieces[&next_piece][0];
        // let state1 = state0.add_piece(piece_to_add).unwrap();
        // assert_eq!(state1.piece_counts.len(), 11);
        // dbg!(&state1.piece_counts);
        // println!("{:}", state1.fill);
        // dbg!(COLORED_BLOCKS);
        // assert_eq!(state1.putative_pieces[&next_piece].len(), 24);
    // }

    /*
    #[test]
    /// The pentominoes are supposed to tile an 8x8 square minus the 2x2 square in the middle.
    fn test_pentomino_annulus{
        let start = PackBitGrid8 {
            fill: BitGrit8(0x8181000000),
            piece: pentomino_map().into_iter().map(|(_, piece)| (piece, 1)).collect::<HashMap<OriginBitGrid8, usize>>,
            putative_pieces: 
    */

}
