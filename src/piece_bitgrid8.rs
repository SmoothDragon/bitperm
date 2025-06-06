// -----------------------------------------------------------------
// 2D geometric pieces shifted to the origin an 8x8 grid
// Bounding box information is included for other useful functions
// -----------------------------------------------------------------

// -----------------------------------------------------------------
// 8x8 square space represented by the 64 bits in a u64
// -----------------------------------------------------------------
// Position at (x,y) = x + 8*y
// The low bit corresponds to the upper left most position.
// The high bit corresponds to the lower right most position.
// 00 01 02 03 04 05 06 07
// 10 11 12 13 14 15 16 17
// 20 21 22 23 24 25 26 27
// 30 31 32 33 34 35 36 37
// 40 41 42 43 44 45 46 47
// 50 51 52 53 54 55 56 57
// 60 61 62 63 64 65 66 67
// 70 71 72 73 74 75 76 77
//
// Rotations will happen from the center of the square.

use std::fmt;
use std::collections::HashMap;

use derive_more::*;
use thiserror::*;
use arrayvec::*;

// use crate::bitlib::swap_mask_shift_u64;
use crate::bitgrid8::*;


#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PieceBitGrid8{
    grid: BitGrid8,  // This acts like a u64
    xy: (u32, u32),  // xy dimensions of bounding box
}

#[derive(Error, Debug, Clone, PartialEq)]
#[error("{0} is not origin shifted.")]
pub struct PieceGrid8Error(u64, String);

impl PieceBitGrid8 {
    pub fn new(raw_u64: u64) -> Self {
        let grid = BitGrid8(raw_u64).shift_to_origin();
        Self{ grid: grid, xy: grid.bounding_box() }
    }

    /// Find the (x,y) bounding box of a piece shifted to origin
    fn bounding_box(grid: BitGrid8) -> (u32, u32) {
        let mut shape:u64 = grid.0;
        // Collect ones on x and y axes
        shape |= ((shape >> 1) & 0x7f7f7f7f7f7f7f7f) | shape >> 8;
        shape |= ((shape >> 2) & 0x3f3f3f3f3f3f3f3f) | shape >> 16;
        shape |= ((shape >> 4) & 0x0f0f0f0f0f0f0f0f) | shape >> 32;
        let len_x = (shape & 0xff).count_ones();
        let len_y = (shape & 0x0101010101010101).count_ones();
        (len_x as u32, len_y as u32)
    }

    pub fn rotate_cc(self) -> Self {
        Self{ grid: self.grid.rotate_cc() >> ((8 - self.xy.0) << 3).into(),
            xy: (self.xy.1, self.xy.0),
            ..self
        }
    }

    // Flip along x-axis. For 2D this is the same as mirror.
    pub fn flip_x(self) -> Self { 
        Self{ grid: self.grid.flip_x() >> ((8 - self.xy.1) << 3).into(),
            ..self
        }
    }
    
    /// Generate all xy-shifts of piece that cover "target" and avoid "board".
    /// "target=x+8*y" represents the bit the 1 << target 
    pub fn targeted_fit(self, board: BitGrid8, target: u32) -> Option<Vec<BitGrid8>> {
        if target >= 64 { return None };
        let (m,n) = self.xy;
        let x = target & 0x7;
        let y = target.unbounded_shr(3);
        let x_min: u32 = if m > x { 0 } else { x - m + 1 };
        let x_max: u32 = u32::min(9-m, x+1);
        let y_min: u32 = if n > y { 0 } else { y - n + 1 };
        let y_max: u32 = u32::min(9-n, y+1);
        println!("{} {} {} {}", x_min, x_max, y_min, y_max);
        let mut result = Vec::<BitGrid8>::new();

        for jj in y_min..y_max {
            for ii in x_min..x_max {
                let grid = self.grid.shift_xy(ii as i32, jj as i32);
                // result.push(grid);
                if grid.0.unbounded_shr(target) & 1 == 1 
                    && grid & board == BitGrid8(0) 
                    { 
                        result.push(grid);
                        println!("{:}", &grid);
                    }
            }
        }
        if result.len() == 0 { None } else { Some(result) }
    }

    /*
    /// Pentominoes indexed by wikipedia naming convention.
    /// Diagonal presentations are rotated 45 degrees clockwise.
    pub fn pentomino_map() -> HashMap::<char, PieceBitGrid8> {
        HashMap::<char, PieceBitGrid8>::from([
            ('F', PieceBitGrid8::new(0x20306)),
            ('I', PieceBitGrid8::new(0x101010101)),
            ('L', PieceBitGrid8::new(0x3010101)),
            ('N', PieceBitGrid8::new(0xe03)),
            ('P', PieceBitGrid8::new(0x10303)),
            ('T', PieceBitGrid8::new(0x20207)),
            ('U', PieceBitGrid8::new(0x705)),
            ('V', PieceBitGrid8::new(0x70101)),
            ('W', PieceBitGrid8::new(0x60301)),
            ('X', PieceBitGrid8::new(0x20702)),
            ('Y', PieceBitGrid8::new(0xf04)),
            ('Z', PieceBitGrid8::new(0x60203)),
        ])
    }

    /// Produce all rotations of a BitGrid object translated towards origin.
    /// Prefer a gray code path through all rotations
    pub fn rotate_all(self) -> ArrayVec::<PieceBitGrid8, 4> {
        let mut vec = ArrayVec::<PieceBitGrid8, 4>::new();
        let mut grid = self.grid;
        vec.push(PieceBitGrid8::new(*grid));
        for _ in 0..3 { grid = grid.rotate(); vec.push(PieceBitGrid8::new(*grid)); }
        vec.sort_unstable();
        let symmetries = vec.partition_dedup().0.len();  // Move duplicates to the end.
        vec.truncate(symmetries);
        vec
    }
    */

    /*
    /// Produce all rotations and reflections of a BitGrid object translated towards origin.
    /// Prefer a gray code path through all rotations
    pub fn origin_dihedral_all(self) -> ArrayVec::<BitGrid8, 8> {
        let mut vec = ArrayVec::<BitGrid8, 8>::new();
        let mut x = self.shift_to_origin();
        vec.push(x);
        for _ in 0..3 { x = x.rotate_cc().shift_to_origin(); vec.push(x); }
        x = x.flip_x().shift_to_origin(); 
        vec.push(x);
        for _ in 0..3 { x = x.rotate_cc().shift_to_origin(); vec.push(x); }
        vec.sort_unstable();
        let symmetries = vec.partition_dedup().0.len();  // Move duplicates to the end.
        vec.truncate(symmetries);
        vec
    }
    */
}

impl fmt::Debug for PieceBitGrid8 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "PieceBitGrid8({:#010x})", self.grid.0)
    } 
} 

// impl fmt::Display for PieceBitGrid8 {
    // fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // let (m, n) = self.xy;
        // write!(f, "{}",     
            // (0..m*n)
            // .map(|l| (l%m, l / m) )
            // .map(|(x,y)| format!("{}{}", if (self.grid.0 >> (x+8*y)) & 0x1 == 1 { "#" } else { "." },
                // if x+1 == m { "\n" } else { "" }))
            // .collect::<String>()
            // )
    // } 
// } 

impl fmt::Display for PieceBitGrid8 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (m, n) = self.xy;
        write!(f, "{}", 
            (0..n).rev().map(|y|
                (0..m)
                    .map(|x| format!("{}", if (self.0 >> (x + 8*y)) & 0x1 == 1 { "🟥" } else { "⬜" }))
                    .collect::<String>()
                    +"\n")
            .collect::<String>()
        )
    } 
} 

impl std::convert::From<BitGrid8> for PieceBitGrid8 {
    fn from(grid: BitGrid8) -> PieceBitGrid8 {
        Self::new(grid.0)
    }
}


// impl std::convert::TryFrom<BitGrid8> for PieceBitGrid8 {
    // type Error = PieceGrid8Error;

    // fn try_from(grid: BitGrid8) -> Result<PieceBitGrid8, Self::Error> {
        // Self::new(*grid)
    // }
// }

impl core::ops::Deref for PieceBitGrid8 {
    type Target = BitGrid8;

    fn deref(&self) -> &Self::Target {
        &self.grid
    }
}



#[cfg(test)]
mod test {
    use super::*;
    
    #[test]
    fn test_size_of_piece_grid8() {
        use std::mem;
        assert_eq!(mem::size_of::<PieceBitGrid8>(), 16);  // Could be 10
        assert_eq!(mem::size_of::<Option<PieceBitGrid8>>(), 24); // Could be 10
    }

    #[test]
    fn test_new() {
        assert_eq!(PieceBitGrid8::new(0x8040201008040201).grid, BitGrid8(0x8040201008040201));
        assert_eq!(PieceBitGrid8::new(0x8040201008040201).xy, (8, 8));
    }

    #[test]
    fn test_from_bitgrid8() {
        assert_eq!(PieceBitGrid8::from(BitGrid8(0x8040201008040201)).grid, BitGrid8(0x8040201008040201));
        assert_eq!(PieceBitGrid8::from(BitGrid8(0x8040201008040201)).xy, (8,8));

        let pentomino = BitGrid8::pentomino_map();
        assert_eq!(PieceBitGrid8::from(pentomino[&'U']).xy, (3,2));
        assert_eq!(PieceBitGrid8::from(pentomino[&'U']).grid, pentomino[&'U']);
    }

    #[test]
    fn test_targeted_fit() {
        let board = BitGrid8(0);
        let square = PieceBitGrid8::new(0x303);
        assert_eq!(square.targeted_fit(board, 0), Some(vec![BitGrid8(0x00000303)]));
        assert_eq!(square.targeted_fit(board, 1), Some(vec![BitGrid8(0x00000303), BitGrid8(0x00000606)]));
        assert_eq!(square.targeted_fit(board, 2), Some(vec![BitGrid8(0x00000606), BitGrid8(0x00000c0c)]));
        assert_eq!(square.targeted_fit(board, 3), Some(vec![BitGrid8(0x00000c0c), BitGrid8(0x00001818)]));
        assert_eq!(square.targeted_fit(board, 10), Some(vec![BitGrid8(0x00000606), BitGrid8(0x00000c0c), BitGrid8(0x00060600), BitGrid8(0x000c0c00)]));

        let tee = PieceBitGrid8::new(0x702);
        assert_eq!(tee.targeted_fit(board, 0), None);
        assert_eq!(tee.targeted_fit(board, 1), Some(vec![BitGrid8(0x00000702)]));
        assert_eq!(tee.targeted_fit(board, 2), Some(vec![BitGrid8(0x00000e04)]));
        assert_eq!(tee.targeted_fit(board, 10), Some(vec![BitGrid8(0x00000702), BitGrid8(0x00000e04), BitGrid8(0x00001c08), BitGrid8(0x000e0400)]));

        let pentomino = BitGrid8::pentomino_map();
        let pent_f = PieceBitGrid8::from(pentomino[&'F']);
        println!("{:}", pent_f);
        assert_eq!(pent_f.targeted_fit(board, 21).unwrap().len(), 5);
        let board = FULL ^ (pent_f.grid << 20);
        // println!("{:}", board);
        // println!("{:}", BitGrid8(1<<21));
        assert_eq!(pent_f.targeted_fit(board, 21), Some(vec![BitGrid8(0x2030600000)]));
        assert_eq!(pent_f.targeted_fit(board, 21), Some(vec![pent_f.grid << 20]));
    }

    #[test]
    fn test_piece_bitgrid8_display() {
        let pentomino = BitGrid8::pentomino_map();
        assert_eq!(format!("{}", PieceBitGrid8::new(0x8040201008040201)), 
            "⬜⬜⬜⬜⬜⬜⬜🟥\n⬜⬜⬜⬜⬜⬜🟥⬜\n⬜⬜⬜⬜⬜🟥⬜⬜\n⬜⬜⬜⬜🟥⬜⬜⬜\n⬜⬜⬜🟥⬜⬜⬜⬜\n⬜⬜🟥⬜⬜⬜⬜⬜\n⬜🟥⬜⬜⬜⬜⬜⬜\n🟥⬜⬜⬜⬜⬜⬜⬜\n");
        assert_eq!(format!("{}", PieceBitGrid8::from(pentomino[&'U'])),
            "🟥🟥🟥\n🟥⬜🟥\n");
        assert_eq!(format!("{}", PieceBitGrid8::from(pentomino[&'F'])),
            "⬜🟥⬜\n🟥🟥⬜\n⬜🟥🟥\n");
        assert_eq!(format!("{}", PieceBitGrid8::new(0x8040201008040201)), 
            "⬜⬜⬜⬜⬜⬜⬜🟥\n⬜⬜⬜⬜⬜⬜🟥⬜\n⬜⬜⬜⬜⬜🟥⬜⬜\n⬜⬜⬜⬜🟥⬜⬜⬜\n⬜⬜⬜🟥⬜⬜⬜⬜\n⬜⬜🟥⬜⬜⬜⬜⬜\n⬜🟥⬜⬜⬜⬜⬜⬜\n🟥⬜⬜⬜⬜⬜⬜⬜\n");
        assert_eq!(format!("{}", PieceBitGrid8::new(0x1)), 
            "🟥\n");
    }

    #[test]
    fn test_new_pentomino() {
        let pentomino = BitGrid8::pentomino_map();
        assert_eq!(PieceBitGrid8::from(pentomino[&'F']).grid, BitGrid8(0x20306));
        assert_eq!(PieceBitGrid8::from((pentomino[&'F'] << 20)).grid, BitGrid8(0x20306));
        assert_eq!(PieceBitGrid8::from(pentomino[&'F']).xy, (3, 3));
        assert_eq!(PieceBitGrid8::from(pentomino[&'I']).xy, (1, 5));
        assert_eq!(PieceBitGrid8::from(pentomino[&'L']).xy, (2, 4));
        assert_eq!(PieceBitGrid8::from(pentomino[&'U']).xy, (3, 2));
    }

    #[test]
    fn test_rotate_cc() {
        let pentomino = BitGrid8::pentomino_map();
        assert_eq!(PieceBitGrid8::from(pentomino[&'U']).rotate_cc(),
            PieceBitGrid8::new(0x30203));
        assert_eq!(PieceBitGrid8::from(pentomino[&'X']).rotate_cc(),
            PieceBitGrid8::from(pentomino[&'X']));
    }

    #[test]
    fn test_flip_x() {
        let pentomino = BitGrid8::pentomino_map();
        assert_eq!(PieceBitGrid8::from(pentomino[&'U']).flip_x(),
            PieceBitGrid8::new(0x507));
        assert_eq!(PieceBitGrid8::from(pentomino[&'X']).flip_x(),
            PieceBitGrid8::from(pentomino[&'X']));
    }

    /*
    #[test]
    fn test_shift_to_origin() {
        assert_eq!(FULL.shift_to_origin(), FULL);
        assert_eq!(UPPER_RIGHT.shift_to_origin(), UPPER_LEFT);
        assert_eq!(ANTIDIAG.shift_to_origin(), ANTIDIAG);
        assert_eq!(CENTER_XY.shift_to_origin(), CENTER_XY);
    }

    #[test]
    fn test_origin_bounding_box() {
        assert_eq!(FULL.origin_bounding_box(), (8,8));
        assert_eq!(UPPER_LEFT.origin_bounding_box(), (4,4));
        assert_eq!(ANTIDIAG.origin_bounding_box(), (8,8));
        assert_eq!(HIGHFIVE.origin_bounding_box(), (8,5));
        assert_eq!(SMALL_FIVE.origin_bounding_box(), (4,5));
    }

    #[test]
    fn test_origin_bounding_box_pentomino() {
        let pentomino = BitGrid8::pentomino_map();
        assert_eq!((&pentomino[&'F']).origin_bounding_box(), (3,3));
        assert_eq!((&pentomino[&'I']).origin_bounding_box(), (1,5));
        assert_eq!((&pentomino[&'L']).origin_bounding_box(), (2,4));
        assert_eq!((&pentomino[&'P']).origin_bounding_box(), (2,3));
        assert_eq!((&pentomino[&'W']).origin_bounding_box(), (3,3));
    }

    #[test]
    fn test_origin_bounded_shift() {
        assert_eq!(FULL.origin_bounded_shifts().len(), 1);
        assert_eq!(UPPER_LEFT.origin_bounded_shifts().len(), 25);
        assert_eq!(ANTIDIAG.origin_bounded_shifts().len(), 1);
        assert_eq!(HIGHFIVE.origin_bounded_shifts().len(), 4);
        assert_eq!(SMALL_FIVE.origin_bounded_shifts().len(), 20);
    }

    #[test]
    fn test_rotate_cc() {
        assert_eq!(HIGHFIVE.rotate_cc(), BitGrid8(0x171515151515151d));
        assert_eq!(SMALL_FIVE.rotate_cc(), BitGrid8(0x1715151d00000000));
        assert_eq!(ANTIDIAG, IDENTITY.rotate_cc());
        assert_eq!(FULL.rotate_cc(), FULL);
        assert_eq!(UPPER_LEFT.rotate_cc(), LOWER_LEFT);
        // println!("{}\n{}", HIGHFIVE, HIGHFIVE.rotate());
        // println!("{}\n{}", SMALL_FIVE, SMALL_FIVE.rotate_cc());
        // println!("{}\n{}", CHECKER2, CHECKER2.rotate_cc());
        // assert_eq!(ANTIDIAG, IDENTITY.rotate());
    }

    #[test]
    fn test_flipx() {
        // assert_eq!(SMALL_FIVE.rotate_cc(), BitGrid8(0x1715151d00000000));
        assert_eq!(ANTIDIAG, IDENTITY.flip_x());
        assert_eq!(FULL.flip_x(), FULL);
        assert_eq!(UPPER_LEFT.flip_x(), LOWER_LEFT);
        assert_eq!(HIGHFIVE.flip_x(), BitGrid8(0xff01_ff80_ff00_0000));
    }

    #[test]
    fn test_rotate_all_vec() {
        assert_eq!(BitGrid8::rotate_all_vec(CENTER_XY).as_slice(), &[CENTER_XY]);
        assert_eq!(BitGrid8::rotate_all_vec(UPPER_LEFT).as_slice(), &[UPPER_LEFT, UPPER_RIGHT, LOWER_LEFT, LOWER_RIGHT]);
        assert_eq!(BitGrid8::rotate_all_vec(IDENTITY).len(), 2);
        assert_eq!(BitGrid8::rotate_all_vec(CHECKER2).len(), 4);
    }

    #[test]
    fn test_origin_rotate_all() {
        assert_eq!(BitGrid8::origin_rotate_all(CENTER_XY).as_slice(), &[CENTER_XY]);
        assert_eq!(BitGrid8::origin_rotate_all(UPPER_LEFT).len(), 1);
        assert_eq!(BitGrid8::origin_rotate_all(HIGHFIVE).len(), 2);
        assert_eq!(BitGrid8::origin_rotate_all(CHECKER2).len(), 2);
        assert_eq!(BitGrid8::origin_rotate_all(BitGrid8(0x103)).len(), 4);
    }

    #[test]
    fn test_origin_dihedral_all() {
        assert_eq!(BitGrid8::origin_dihedral_all(CENTER_XY).as_slice(), &[CENTER_XY]);
        assert_eq!(BitGrid8::origin_dihedral_all(UPPER_LEFT).len(), 1);
        assert_eq!(BitGrid8::origin_dihedral_all(HIGHFIVE).len(), 4);
        assert_eq!(BitGrid8::origin_dihedral_all(CHECKER2).len(), 2);
        assert_eq!(BitGrid8::origin_dihedral_all(BitGrid8(0x103)).len(), 4);
    }

    #[test]
    fn test_origin_dihedral_all_pentomino() {
        let pentomino = BitGrid8::pentomino_map();
        assert_eq!((&pentomino[&'F']).origin_dihedral_all().len(), 8);
        assert_eq!((&pentomino[&'N']).origin_dihedral_all().len(), 8);
        assert_eq!((&pentomino[&'P']).origin_dihedral_all().len(), 8);
        assert_eq!((&pentomino[&'Y']).origin_dihedral_all().len(), 8);
        assert_eq!((&pentomino[&'V']).origin_dihedral_all().len(), 4);
        assert_eq!((&pentomino[&'W']).origin_dihedral_all().len(), 4);
    }

    /// Shift a piece in the 8-grid towards the origin so that it touches the x and y axes
    pub fn shift_to_origin(grid: BitGrid8) -> Self {
        let mut shape = grid;
        // y-shift the zero rows away
        shape = shape >> ((shape.trailing_zeros() / 8) * 8);
        // x-shift the zero rows away
        let mut x_shift = shape >> 32;
        x_shift |= x_shift >> 32;
        x_shift |= x_shift >> 16;
        x_shift |= x_shift >> 8;
        shape = shape >> x_shift.trailing_zeros();
        Self{ grid: shape, xy: Self::bounding_box(shape) }
    }

*/
}
