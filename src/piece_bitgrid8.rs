// -----------------------------------------------------------------
// 2D geometric pieces shifted to the origin an 8x8 grid
// Bounding box information is included for other useful functions
// -----------------------------------------------------------------

// -----------------------------------------------------------------
// 8x8 square space represented by the 64 bits in a u64
// -----------------------------------------------------------------
// Position at (x,y) = x + 8*y
// The low bit corresponds to the lower left most position.
// The high bit corresponds to the upper right most position.
// 70 71 72 73 74 75 76 77
// 60 61 62 63 64 65 66 67
// 50 51 52 53 54 55 56 57
// 40 41 42 43 44 45 46 47
// 30 31 32 33 34 35 36 37
// 20 21 22 23 24 25 26 27
// 10 11 12 13 14 15 16 17
// 00 01 02 03 04 05 06 07
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

    pub fn rotate(self) -> Self {
        Self{ grid: self.grid.rotate() >> (((8 - self.xy.0) << 3) as i32),
            xy: (self.xy.1, self.xy.0),
            ..self
        }
    }

    pub fn rotate_cc(self) -> Self {
        Self{ grid: self.grid.rotate_cc() >> ((8 - self.xy.1) as i32),
            xy: (self.xy.1, self.xy.0),
            ..self
        }
    }

    // Flip along x-axis. For 2D this is the same as mirror.
    pub fn flip_x(self) -> Self { 
        Self{ grid: self.grid.flip_x() >> (((8 - self.xy.1) << 3) as i32),
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
                        // println!("{:}", &grid);
                    }
            }
        }
        if result.len() == 0 { None } else { Some(result) }
    }

    /// Pentominoes indexed by wikipedia naming convention.
    /// FLIPN TUVWXYZ (Flippin' T to Z)
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


    /// Produce all rotations of a PieceBitGrid8.
    pub fn rotate_all(self) -> ArrayVec::<PieceBitGrid8, 4> {
        let mut vec = ArrayVec::<PieceBitGrid8, 4>::new();
        let mut grid = self;
        vec.push(grid);
        for _ in 0..3 { grid = grid.rotate_cc(); vec.push(grid) };
        vec.sort_unstable();
        let symmetries = vec.partition_dedup().0.len();  // Move duplicates to the end.
        vec.truncate(symmetries);
        vec
    }

    /// Produce all rotations and flips of a PieceBitGrid8.
    /// This is the same as the dihedral group acting on the piece.
    pub fn rotate_flip_all(self) -> ArrayVec::<PieceBitGrid8, 8> {
        let mut vec = ArrayVec::<PieceBitGrid8, 8>::new();
        let mut grid = self;
        vec.push(grid);
        for _ in 0..3 { grid = grid.rotate_cc(); vec.push(grid) };
        grid = grid.flip_x();
        vec.push(grid);
        for _ in 0..3 { grid = grid.rotate_cc(); vec.push(grid) };
        vec.sort_unstable();
        let symmetries = vec.partition_dedup().0.len();  // Move duplicates to the end.
        vec.truncate(symmetries);
        // for grid in &vec { println!("{:}", grid) };
        vec
    }
}

impl fmt::Debug for PieceBitGrid8 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "PieceBitGrid8({:#010x})", self.grid.0)
    } 
} 

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

impl core::ops::Deref for PieceBitGrid8 {
    type Target = BitGrid8;

    fn deref(&self) -> &Self::Target {
        &self.grid
    }
}

// pub REP_01:u64 = 0x0101010101010101u64;
// REP_7F:u64 = 0x7f7f7f7f7f7f7f7fu64;
// pub const ALL: u64 = 0xffff_ffff_ffff_ffff;
// pub static CENTER_XY: PieceBitGrid8 = PieceBitGrid8::new(0x1818_18ff_ff18_1818);
// pub FULL: PieceBitGrid8 = PieceBitGrid8::new(0xffff_ffff_ffff_ffff_u64);
// pub const ORDER: PieceBitGrid8 = PieceBitGrid8::new(0xfedc_ba98_7654_3210_u64);
// pub UPPER_LEFT: PieceBitGrid8 = PieceBitGrid8::new(0x0f0f_0f0f_u64);
// pub UPPER_RIGHT: PieceBitGrid8 = PieceBitGrid8::new(0xf0f0_f0f0_u64);
// pub LOWER_LEFT: PieceBitGrid8 = PieceBitGrid8::new(0x0f0f_0f0f_0000_0000_u64);
// pub LOWER_RIGHT: PieceBitGrid8 = PieceBitGrid8::new(0xf0f0_f0f0_0000_0000_u64);

// pub HIGHFIVE: PieceBitGrid8 = PieceBitGrid8::new(0xff80ff01ff);
// pub SMALL_FIVE: PieceBitGrid8 = PieceBitGrid8::new(0x00f080f010f);
// pub CHECKER2: PieceBitGrid8 = PieceBitGrid8::new(0x0c0c_0303);
// pub IDENTITY:PieceBitGrid8 = PieceBitGrid8::new(0x8040201008040201);
// pub ANTIDIAG:PieceBitGrid8 = PieceBitGrid8::new(0x0102040810204080);
// pub BORDER:PieceBitGrid8 = PieceBitGrid8::new(0xff81_8181_8181_81ff);



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
        assert_eq!(PieceBitGrid8::from(pentomino[&'F'] << 20).grid, BitGrid8(0x20306));
        assert_eq!(PieceBitGrid8::from(pentomino[&'F']).xy, (3, 3));
        assert_eq!(PieceBitGrid8::from(pentomino[&'L']).xy, (2, 4));
        assert_eq!(PieceBitGrid8::from(pentomino[&'I']).xy, (1, 5));
        assert_eq!(PieceBitGrid8::from(pentomino[&'P']).xy, (2, 3));
        assert_eq!(PieceBitGrid8::from(pentomino[&'N']).xy, (4, 2));
        assert_eq!(PieceBitGrid8::from(pentomino[&'T']).xy, (3, 3));
        assert_eq!(PieceBitGrid8::from(pentomino[&'U']).xy, (3, 2));
        assert_eq!(PieceBitGrid8::from(pentomino[&'V']).xy, (3, 3));
        assert_eq!(PieceBitGrid8::from(pentomino[&'W']).xy, (3, 3));
        assert_eq!(PieceBitGrid8::from(pentomino[&'X']).xy, (3, 3));
        assert_eq!(PieceBitGrid8::from(pentomino[&'Y']).xy, (4, 2));
        assert_eq!(PieceBitGrid8::from(pentomino[&'Z']).xy, (3, 3));
    }

    #[test]
    fn test_rotate_cc() {
        let pentomino = BitGrid8::pentomino_map();
        assert_eq!(PieceBitGrid8::from(pentomino[&'U']).rotate(),
            PieceBitGrid8::new(0x30203));
        assert_eq!(PieceBitGrid8::from(pentomino[&'X']).rotate_cc(),
            PieceBitGrid8::from(pentomino[&'X']));
        // assert_eq!(HIGHFIVE.rotate_cc(), BitGrid8(0x171515151515151d));
        // assert_eq!(SMALL_FIVE.rotate_cc(), BitGrid8(0x1715151d00000000));
        // assert_eq!(ANTIDIAG, IDENTITY.rotate_cc());
        // assert_eq!(FULL.rotate_cc(), FULL);
        // assert_eq!(UPPER_LEFT.rotate_cc(), LOWER_LEFT);
        // println!("{}\n{}", HIGHFIVE, HIGHFIVE.rotate());
        // println!("{}\n{}", SMALL_FIVE, SMALL_FIVE.rotate_cc());
        // println!("{}\n{}", CHECKER2, CHECKER2.rotate_cc());
        // assert_eq!(ANTIDIAG, IDENTITY.rotate());
    }

    #[test]
    fn test_flip_x() {
        let pentomino = BitGrid8::pentomino_map();
        assert_eq!(PieceBitGrid8::from(pentomino[&'U']).flip_x(),
            PieceBitGrid8::new(0x507));
        assert_eq!(PieceBitGrid8::from(pentomino[&'X']).flip_x(),
            PieceBitGrid8::from(pentomino[&'X']));
        assert_eq!(PieceBitGrid8::from(IDENTITY).flip_x(), PieceBitGrid8::from(ANTIDIAG));
        assert_eq!(PieceBitGrid8::from(FULL).flip_x(), PieceBitGrid8::from(FULL));
        assert_eq!(PieceBitGrid8::from(UPPER_LEFT).flip_x(), PieceBitGrid8::from(UPPER_LEFT));
        // println!("{:}", PieceBitGrid8::from(HIGHFIVE));
        // println!("{:}", PieceBitGrid8::new(0xff01_ff80_ff00_0000));
        assert_eq!(PieceBitGrid8::from(HIGHFIVE).flip_x(), PieceBitGrid8::new(0xff01_ff80_ff));
        assert_eq!(PieceBitGrid8::from(SMALL_FIVE).flip_x(), PieceBitGrid8::new(0xf010f080f));
    }

    #[test]
    fn test_rotate_all() {
        assert_eq!(PieceBitGrid8::from(CENTER_XY).rotate_all().as_slice(), &[PieceBitGrid8::from(CENTER_XY)]);
        assert_eq!(PieceBitGrid8::from(IDENTITY).rotate_all().len(), 2);
        assert_eq!(PieceBitGrid8::from(HIGHFIVE).rotate_all().len(), 2);
        assert_eq!(PieceBitGrid8::from(CHECKER2).rotate_all().len(), 2);
    }

    #[test]
    fn test_rotate_all_pentomino() {
        assert_eq!(PieceBitGrid8::from(BitGrid8::pentomino_map()[&'F']).rotate_all().as_slice(), 
                   &[PieceBitGrid8::new(0x00020306), PieceBitGrid8::new(0x00020701), PieceBitGrid8::new(0x00030602), PieceBitGrid8::new(0x00040702)]);
        assert_eq!(PieceBitGrid8::from(BitGrid8::pentomino_map()[&'F']).rotate_all().len(), 4);
        assert_eq!(PieceBitGrid8::from(BitGrid8::pentomino_map()[&'L']).rotate_all().len(), 4);
        assert_eq!(PieceBitGrid8::from(BitGrid8::pentomino_map()[&'I']).rotate_all().len(), 2);
        assert_eq!(PieceBitGrid8::from(BitGrid8::pentomino_map()[&'I']).rotate_all().len(), 2);
        assert_eq!(PieceBitGrid8::from(BitGrid8::pentomino_map()[&'P']).rotate_all().len(), 4);
        assert_eq!(PieceBitGrid8::from(BitGrid8::pentomino_map()[&'N']).rotate_all().len(), 4);
        assert_eq!(PieceBitGrid8::from(BitGrid8::pentomino_map()[&'T']).rotate_all().len(), 4);
        assert_eq!(PieceBitGrid8::from(BitGrid8::pentomino_map()[&'U']).rotate_all().len(), 4);
        assert_eq!(PieceBitGrid8::from(BitGrid8::pentomino_map()[&'V']).rotate_all().len(), 4);
        assert_eq!(PieceBitGrid8::from(BitGrid8::pentomino_map()[&'W']).rotate_all().len(), 4);
        assert_eq!(PieceBitGrid8::from(BitGrid8::pentomino_map()[&'X']).rotate_all().len(), 1);
        assert_eq!(PieceBitGrid8::from(BitGrid8::pentomino_map()[&'Y']).rotate_all().len(), 4);
        assert_eq!(PieceBitGrid8::from(BitGrid8::pentomino_map()[&'Z']).rotate_all().len(), 2);
    }

    #[test]
    fn test_rotate_flip_all() {
        assert_eq!(PieceBitGrid8::from(CENTER_XY).rotate_flip_all().as_slice(), &[PieceBitGrid8::from(CENTER_XY)]);
        assert_eq!(PieceBitGrid8::from(IDENTITY).rotate_flip_all().len(), 2);
        assert_eq!(PieceBitGrid8::from(HIGHFIVE).rotate_flip_all().len(), 4);
        assert_eq!(PieceBitGrid8::from(CHECKER2).rotate_flip_all().len(), 2);
    }

    #[test]
    fn test_rotate_flip_all_pentomino() {
        assert_eq!(PieceBitGrid8::from(BitGrid8::pentomino_map()[&'F']).rotate_flip_all().as_slice(), 
            &[PieceBitGrid8::new(0x00010702), PieceBitGrid8::new(0x00020306), PieceBitGrid8::new(0x00020603), PieceBitGrid8::new(0x00020701), PieceBitGrid8::new(0x00020704), PieceBitGrid8::new(0x00030602), PieceBitGrid8::new(0x00040702), PieceBitGrid8::new(0x00060302)]);
        assert_eq!(PieceBitGrid8::from(BitGrid8::pentomino_map()[&'F']).rotate_flip_all().len(), 8);
        assert_eq!(PieceBitGrid8::from(BitGrid8::pentomino_map()[&'L']).rotate_flip_all().len(), 8);
        assert_eq!(PieceBitGrid8::from(BitGrid8::pentomino_map()[&'I']).rotate_flip_all().len(), 2);
        assert_eq!(PieceBitGrid8::from(BitGrid8::pentomino_map()[&'P']).rotate_flip_all().len(), 8);
        assert_eq!(PieceBitGrid8::from(BitGrid8::pentomino_map()[&'N']).rotate_flip_all().len(), 8);
        assert_eq!(PieceBitGrid8::from(BitGrid8::pentomino_map()[&'T']).rotate_flip_all().len(), 4);
        assert_eq!(PieceBitGrid8::from(BitGrid8::pentomino_map()[&'U']).rotate_flip_all().len(), 4);
        assert_eq!(PieceBitGrid8::from(BitGrid8::pentomino_map()[&'V']).rotate_flip_all().len(), 4);
        assert_eq!(PieceBitGrid8::from(BitGrid8::pentomino_map()[&'W']).rotate_flip_all().len(), 4);
        assert_eq!(PieceBitGrid8::from(BitGrid8::pentomino_map()[&'X']).rotate_flip_all().len(), 1);
        assert_eq!(PieceBitGrid8::from(BitGrid8::pentomino_map()[&'Y']).rotate_flip_all().len(), 8);
        assert_eq!(PieceBitGrid8::from(BitGrid8::pentomino_map()[&'Z']).rotate_flip_all().len(), 4);
    }
}
