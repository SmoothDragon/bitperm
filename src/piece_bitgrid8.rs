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

use crate::bitgrid8::*;

/// OriginBitGrid8 is always touching the x and y axes.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct OriginBitGrid8{
    pub(crate) grid: BitGrid8,  // This acts like a u64
    pub(crate) xy: (u32, u32),  // xy dimensions of bounding box
}

/// OriginBitGrid8 is always touching the x and y axes.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct C4CanonicalGrid8(OriginBitGrid8);

impl C4CanonicalGrid8 {
    pub fn new(grid: OriginBitGrid8) -> Self {
        Self(grid.symmetry_c4().into_iter().min().expect("Somehow piece list is empty"))
    }
}

impl std::convert::From<BitGrid8> for C4CanonicalGrid8 {
    fn from(grid: BitGrid8) -> Self {
        Self::new(OriginBitGrid8::from(grid))
    }
}

impl core::ops::Deref for C4CanonicalGrid8 {
    type Target = OriginBitGrid8;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// D4CanonicalGrid8 is the smallest u64 that contains the given grid.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct D4CanonicalGrid8(OriginBitGrid8);

impl D4CanonicalGrid8 {
    pub fn new(grid: OriginBitGrid8) -> Self {
        Self(grid.symmetry_d4().into_iter().min().expect("Somehow piece list is empty"))
    }
}

impl From<BitGrid8> for D4CanonicalGrid8 {
    fn from(grid: BitGrid8) -> Self {
        Self::new(OriginBitGrid8::from(grid))
    }
}

impl core::ops::Deref for D4CanonicalGrid8 {
    type Target = OriginBitGrid8;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Error, Debug, Clone, PartialEq)]
#[error("{0} is not origin shifted.")]
pub struct PieceGrid8Error(u64, String);

impl OriginBitGrid8 {
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
    /// "target=x+8*y" represents the bit at location 1 << target 
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
    pub fn pentomino_map() -> HashMap::<char, OriginBitGrid8> {
        HashMap::<char, OriginBitGrid8>::from([
            ('F', OriginBitGrid8::new(0x20306)),
            ('I', OriginBitGrid8::new(0x101010101)),
            ('L', OriginBitGrid8::new(0x3010101)),
            ('N', OriginBitGrid8::new(0xe03)),
            ('P', OriginBitGrid8::new(0x10303)),
            ('T', OriginBitGrid8::new(0x20207)),
            ('U', OriginBitGrid8::new(0x705)),
            ('V', OriginBitGrid8::new(0x70101)),
            ('W', OriginBitGrid8::new(0x60301)),
            ('X', OriginBitGrid8::new(0x20702)),
            ('Y', OriginBitGrid8::new(0xf04)),
            ('Z', OriginBitGrid8::new(0x60203)),
        ])
    }


    /// Produce all rotations of a OriginBitGrid8.
    pub fn symmetry_c4(self) -> ArrayVec::<OriginBitGrid8, 4> {
        let mut vec = ArrayVec::<OriginBitGrid8, 4>::new();
        let mut grid = self;
        vec.push(grid);
        for _ in 0..3 { grid = grid.rotate_cc(); vec.push(grid) };
        vec.sort_unstable();
        let symmetries = vec.partition_dedup().0.len();  // Move duplicates to the end.
        vec.truncate(symmetries);
        vec
    }

    /// Produce all rotations and flips of a OriginBitGrid8.
    /// This is the same as the dihedral group acting on the piece.
    pub fn symmetry_d4(self) -> ArrayVec::<OriginBitGrid8, 8> {
        let mut vec = ArrayVec::<OriginBitGrid8, 8>::new();
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

impl fmt::Debug for OriginBitGrid8 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "OriginBitGrid8({:#010x})", self.grid.0)
    } 
} 

impl fmt::Display for OriginBitGrid8 {
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

impl From<BitGrid8> for OriginBitGrid8 {
    fn from(grid: BitGrid8) -> OriginBitGrid8 {
        Self::new(grid.0)
    }
}

impl From<u64> for OriginBitGrid8 {
    fn from(raw_grid: u64) -> OriginBitGrid8 {
        Self::new(raw_grid)
    }
}

impl core::ops::Deref for OriginBitGrid8 {
    type Target = BitGrid8;

    fn deref(&self) -> &Self::Target {
        &self.grid
    }
}

// pub REP_01:u64 = 0x0101010101010101u64;
// REP_7F:u64 = 0x7f7f7f7f7f7f7f7fu64;
// pub const ALL: u64 = 0xffff_ffff_ffff_ffff;
// pub static CENTER_XY: OriginBitGrid8 = OriginBitGrid8::new(0x1818_18ff_ff18_1818);
// pub FULL: OriginBitGrid8 = OriginBitGrid8::new(0xffff_ffff_ffff_ffff_u64);
// pub const ORDER: OriginBitGrid8 = OriginBitGrid8::new(0xfedc_ba98_7654_3210_u64);
// pub UPPER_LEFT: OriginBitGrid8 = OriginBitGrid8::new(0x0f0f_0f0f_u64);
// pub UPPER_RIGHT: OriginBitGrid8 = OriginBitGrid8::new(0xf0f0_f0f0_u64);
// pub LOWER_LEFT: OriginBitGrid8 = OriginBitGrid8::new(0x0f0f_0f0f_0000_0000_u64);
// pub LOWER_RIGHT: OriginBitGrid8 = OriginBitGrid8::new(0xf0f0_f0f0_0000_0000_u64);

// pub HIGHFIVE: OriginBitGrid8 = OriginBitGrid8::new(0xff80ff01ff);
// pub SMALL_FIVE: OriginBitGrid8 = OriginBitGrid8::new(0x00f080f010f);
// pub CHECKER2: OriginBitGrid8 = OriginBitGrid8::new(0x0c0c_0303);
// pub IDENTITY:OriginBitGrid8 = OriginBitGrid8::new(0x8040201008040201);
// pub ANTIDIAG:OriginBitGrid8 = OriginBitGrid8::new(0x0102040810204080);
// pub BORDER:OriginBitGrid8 = OriginBitGrid8::new(0xff81_8181_8181_81ff);



#[cfg(test)]
mod test {
    use super::*;
    use crate::bitlib::*;
    
    #[test]
    fn test_size_of_piece_grid8() {
        use std::mem;
        assert_eq!(mem::size_of::<OriginBitGrid8>(), 16);  // Could be 10
        assert_eq!(mem::size_of::<Option<OriginBitGrid8>>(), 24); // Could be 10
    }

    #[test]
    fn test_new() {
        assert_eq!(OriginBitGrid8::new(0x8040201008040201).grid, BitGrid8(0x8040201008040201));
        assert_eq!(OriginBitGrid8::new(0x8040201008040201).xy, (8, 8));
    }

    #[test]
    fn test_from_bitgrid8() {
        assert_eq!(OriginBitGrid8::from(BitGrid8(0x8040201008040201)).grid, BitGrid8(0x8040201008040201));
        assert_eq!(OriginBitGrid8::from(BitGrid8(0x8040201008040201)).xy, (8,8));

        let pentomino = BitGrid8::pentomino_map();
        assert_eq!(OriginBitGrid8::from(pentomino[&'U']).xy, (3,2));
        assert_eq!(OriginBitGrid8::from(pentomino[&'U']).grid, pentomino[&'U']);
    }

    #[test]
    fn test_targeted_fit() {
        let board = BitGrid8(0);
        let square = OriginBitGrid8::new(0x303);
        assert_eq!(square.targeted_fit(board, 0), Some(vec![BitGrid8(0x00000303)]));
        assert_eq!(square.targeted_fit(board, 1), Some(vec![BitGrid8(0x00000303), BitGrid8(0x00000606)]));
        assert_eq!(square.targeted_fit(board, 2), Some(vec![BitGrid8(0x00000606), BitGrid8(0x00000c0c)]));
        assert_eq!(square.targeted_fit(board, 3), Some(vec![BitGrid8(0x00000c0c), BitGrid8(0x00001818)]));
        assert_eq!(square.targeted_fit(board, 10), Some(vec![BitGrid8(0x00000606), BitGrid8(0x00000c0c), BitGrid8(0x00060600), BitGrid8(0x000c0c00)]));

        let tee = OriginBitGrid8::new(0x702);
        assert_eq!(tee.targeted_fit(board, 0), None);
        assert_eq!(tee.targeted_fit(board, 1), Some(vec![BitGrid8(0x00000702)]));
        assert_eq!(tee.targeted_fit(board, 2), Some(vec![BitGrid8(0x00000e04)]));
        assert_eq!(tee.targeted_fit(board, 10), Some(vec![BitGrid8(0x00000702), BitGrid8(0x00000e04), BitGrid8(0x00001c08), BitGrid8(0x000e0400)]));

        let pentomino = BitGrid8::pentomino_map();
        let pent_f = OriginBitGrid8::from(pentomino[&'F']);
        println!("{:}", pent_f);
        assert_eq!(pent_f.targeted_fit(board, 21).unwrap().len(), 5);
        let board = (pent_f.grid << 20) ^ FULL;
        // println!("{:}", board);
        // println!("{:}", BitGrid8(1<<21));
        assert_eq!(pent_f.targeted_fit(board, 21), Some(vec![BitGrid8(0x2030600000)]));
        assert_eq!(pent_f.targeted_fit(board, 21), Some(vec![pent_f.grid << 20]));
    }

    #[test]
    fn test_piece_bitgrid8_display() {
        let pentomino = BitGrid8::pentomino_map();
        assert_eq!(format!("{}", OriginBitGrid8::new(0x8040201008040201)), 
            "⬜⬜⬜⬜⬜⬜⬜🟥\n⬜⬜⬜⬜⬜⬜🟥⬜\n⬜⬜⬜⬜⬜🟥⬜⬜\n⬜⬜⬜⬜🟥⬜⬜⬜\n⬜⬜⬜🟥⬜⬜⬜⬜\n⬜⬜🟥⬜⬜⬜⬜⬜\n⬜🟥⬜⬜⬜⬜⬜⬜\n🟥⬜⬜⬜⬜⬜⬜⬜\n");
        assert_eq!(format!("{}", OriginBitGrid8::from(pentomino[&'U'])),
            "🟥⬜🟥\n🟥🟥🟥\n");
        assert_eq!(format!("{}", OriginBitGrid8::from(pentomino[&'F'])),
            "⬜🟥⬜\n🟥🟥⬜\n⬜🟥🟥\n");
        assert_eq!(format!("{}", OriginBitGrid8::new(0x8040201008040201)), 
            "⬜⬜⬜⬜⬜⬜⬜🟥\n⬜⬜⬜⬜⬜⬜🟥⬜\n⬜⬜⬜⬜⬜🟥⬜⬜\n⬜⬜⬜⬜🟥⬜⬜⬜\n⬜⬜⬜🟥⬜⬜⬜⬜\n⬜⬜🟥⬜⬜⬜⬜⬜\n⬜🟥⬜⬜⬜⬜⬜⬜\n🟥⬜⬜⬜⬜⬜⬜⬜\n");
        assert_eq!(format!("{}", OriginBitGrid8::new(0x1)), 
            "🟥\n");
    }

    #[test]
    fn test_new_pentomino() {
        let pentomino = BitGrid8::pentomino_map();
        assert_eq!(OriginBitGrid8::from(pentomino[&'F']).grid, BitGrid8(0x20306));
        assert_eq!(OriginBitGrid8::from(pentomino[&'F'] << 20).grid, BitGrid8(0x20306));
        assert_eq!(OriginBitGrid8::from(pentomino[&'F']).xy, (3, 3));
        assert_eq!(OriginBitGrid8::from(pentomino[&'L']).xy, (2, 4));
        assert_eq!(OriginBitGrid8::from(pentomino[&'I']).xy, (1, 5));
        assert_eq!(OriginBitGrid8::from(pentomino[&'P']).xy, (2, 3));
        assert_eq!(OriginBitGrid8::from(pentomino[&'N']).xy, (4, 2));
        assert_eq!(OriginBitGrid8::from(pentomino[&'T']).xy, (3, 3));
        assert_eq!(OriginBitGrid8::from(pentomino[&'U']).xy, (3, 2));
        assert_eq!(OriginBitGrid8::from(pentomino[&'V']).xy, (3, 3));
        assert_eq!(OriginBitGrid8::from(pentomino[&'W']).xy, (3, 3));
        assert_eq!(OriginBitGrid8::from(pentomino[&'X']).xy, (3, 3));
        assert_eq!(OriginBitGrid8::from(pentomino[&'Y']).xy, (4, 2));
        assert_eq!(OriginBitGrid8::from(pentomino[&'Z']).xy, (3, 3));
    }

    /*
    #[test]
    fn test_canonical() {
        let pentomino = BitGrid8::pentomino_map();
        assert_eq!(PieceBitGrid8::new(0x30203).canonical(),
            PieceBitGrid8::from(pentomino[&'U']));
        assert_eq!(PieceBitGrid8::from(pentomino[&'X']).canonical(),
            PieceBitGrid8::from(pentomino[&'X']));
        println!("{}", PieceBitGrid8::from(pentomino[&'F']).canonical());
        assert_eq!(PieceBitGrid8::from(pentomino[&'F']).canonical(),
            PieceBitGrid8::new(0x10702));
    }
    */

    #[test]
    fn test_rotate_cc() {
        let pentomino = BitGrid8::pentomino_map();
        assert_eq!(OriginBitGrid8::from(pentomino[&'U']).rotate(),
            OriginBitGrid8::new(0x30103));
        assert_eq!(OriginBitGrid8::from(pentomino[&'X']).rotate_cc(),
            OriginBitGrid8::from(pentomino[&'X']));
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
        assert_eq!(OriginBitGrid8::from(pentomino[&'U']).flip_x(),
            OriginBitGrid8::new(0x705));
        assert_eq!(OriginBitGrid8::from(pentomino[&'X']).flip_x(),
            OriginBitGrid8::from(pentomino[&'X']));
        assert_eq!(OriginBitGrid8::from(IDENTITY).flip_x(), OriginBitGrid8::from(ANTIDIAG));
        assert_eq!(OriginBitGrid8::from(FULL).flip_x(), OriginBitGrid8::from(FULL));
        assert_eq!(OriginBitGrid8::from(UPPER_LEFT).flip_x(), OriginBitGrid8::from(UPPER_LEFT));
        // println!("{:}", OriginBitGrid8::from(HIGHFIVE));
        // println!("{:}", OriginBitGrid8::new(0xff01_ff80_ff00_0000));
        assert_eq!(OriginBitGrid8::from(HIGHFIVE).flip_x(), OriginBitGrid8::new(0xff01_ff80_ff));
        assert_eq!(OriginBitGrid8::from(SMALL_FIVE).flip_x(), OriginBitGrid8::new(0xf010f080f));
    }

    #[test]
    fn test_symmetry_c4() {
        assert_eq!(OriginBitGrid8::from(CENTER_XY).symmetry_c4().as_slice(), &[OriginBitGrid8::from(CENTER_XY)]);
        assert_eq!(OriginBitGrid8::from(IDENTITY).symmetry_c4().len(), 2);
        assert_eq!(OriginBitGrid8::from(HIGHFIVE).symmetry_c4().len(), 2);
        assert_eq!(OriginBitGrid8::from(CHECKER2).symmetry_c4().len(), 2);
    }

    #[test]
    fn test_symmetry_c4_pentomino() {
        assert_eq!(OriginBitGrid8::from(BitGrid8::pentomino_map()[&'F']).symmetry_c4().as_slice(), 
                   &[OriginBitGrid8::new(0x00020306), OriginBitGrid8::new(0x00020701), OriginBitGrid8::new(0x00030602), OriginBitGrid8::new(0x00040702)]);
        assert_eq!(OriginBitGrid8::from(BitGrid8::pentomino_map()[&'F']).symmetry_c4().len(), 4);
        assert_eq!(OriginBitGrid8::from(BitGrid8::pentomino_map()[&'L']).symmetry_c4().len(), 4);
        assert_eq!(OriginBitGrid8::from(BitGrid8::pentomino_map()[&'I']).symmetry_c4().len(), 2);
        assert_eq!(OriginBitGrid8::from(BitGrid8::pentomino_map()[&'I']).symmetry_c4().len(), 2);
        assert_eq!(OriginBitGrid8::from(BitGrid8::pentomino_map()[&'P']).symmetry_c4().len(), 4);
        assert_eq!(OriginBitGrid8::from(BitGrid8::pentomino_map()[&'N']).symmetry_c4().len(), 4);
        assert_eq!(OriginBitGrid8::from(BitGrid8::pentomino_map()[&'T']).symmetry_c4().len(), 4);
        assert_eq!(OriginBitGrid8::from(BitGrid8::pentomino_map()[&'U']).symmetry_c4().len(), 4);
        assert_eq!(OriginBitGrid8::from(BitGrid8::pentomino_map()[&'V']).symmetry_c4().len(), 4);
        assert_eq!(OriginBitGrid8::from(BitGrid8::pentomino_map()[&'W']).symmetry_c4().len(), 4);
        assert_eq!(OriginBitGrid8::from(BitGrid8::pentomino_map()[&'X']).symmetry_c4().len(), 1);
        assert_eq!(OriginBitGrid8::from(BitGrid8::pentomino_map()[&'Y']).symmetry_c4().len(), 4);
        assert_eq!(OriginBitGrid8::from(BitGrid8::pentomino_map()[&'Z']).symmetry_c4().len(), 2);
    }

    #[test]
    fn test_symmetry_d4() {
        assert_eq!(OriginBitGrid8::from(CENTER_XY).symmetry_d4().as_slice(), &[OriginBitGrid8::from(CENTER_XY)]);
        assert_eq!(OriginBitGrid8::from(IDENTITY).symmetry_d4().len(), 2);
        assert_eq!(OriginBitGrid8::from(HIGHFIVE).symmetry_d4().len(), 4);
        assert_eq!(OriginBitGrid8::from(CHECKER2).symmetry_d4().len(), 2);
    }

    #[test]
    fn test_symmetry_d4_pentomino() {
        assert_eq!(OriginBitGrid8::from(BitGrid8::pentomino_map()[&'F']).symmetry_d4().as_slice(), 
            &[OriginBitGrid8::new(0x00010702), OriginBitGrid8::new(0x00020306), OriginBitGrid8::new(0x00020603), OriginBitGrid8::new(0x00020701), OriginBitGrid8::new(0x00020704), OriginBitGrid8::new(0x00030602), OriginBitGrid8::new(0x00040702), OriginBitGrid8::new(0x00060302)]);
        assert_eq!(OriginBitGrid8::from(BitGrid8::pentomino_map()[&'F']).symmetry_d4().len(), 8);
        assert_eq!(OriginBitGrid8::from(BitGrid8::pentomino_map()[&'L']).symmetry_d4().len(), 8);
        assert_eq!(OriginBitGrid8::from(BitGrid8::pentomino_map()[&'I']).symmetry_d4().len(), 2);
        assert_eq!(OriginBitGrid8::from(BitGrid8::pentomino_map()[&'P']).symmetry_d4().len(), 8);
        assert_eq!(OriginBitGrid8::from(BitGrid8::pentomino_map()[&'N']).symmetry_d4().len(), 8);
        assert_eq!(OriginBitGrid8::from(BitGrid8::pentomino_map()[&'T']).symmetry_d4().len(), 4);
        assert_eq!(OriginBitGrid8::from(BitGrid8::pentomino_map()[&'U']).symmetry_d4().len(), 4);
        assert_eq!(OriginBitGrid8::from(BitGrid8::pentomino_map()[&'V']).symmetry_d4().len(), 4);
        assert_eq!(OriginBitGrid8::from(BitGrid8::pentomino_map()[&'W']).symmetry_d4().len(), 4);
        assert_eq!(OriginBitGrid8::from(BitGrid8::pentomino_map()[&'X']).symmetry_d4().len(), 1);
        assert_eq!(OriginBitGrid8::from(BitGrid8::pentomino_map()[&'Y']).symmetry_d4().len(), 8);
        assert_eq!(OriginBitGrid8::from(BitGrid8::pentomino_map()[&'Z']).symmetry_d4().len(), 4);
    }
}
