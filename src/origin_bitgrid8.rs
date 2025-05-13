use std::fmt;
// use std::collections::HashMap;


use derive_more::*;
// use arrayvec::*;

// use crate::bitlib::swap_mask_shift_u64;
use crate::bitgrid8::*;

// -----------------------------------------------------------------
// 2D geometric pieces and operations on an 8x8 grid
//
// "origin" pieces are shifted as close to origin as possible.
// -----------------------------------------------------------------

// -----------------------------------------------------------------
// 8x8 square space represented by the 64 bits in a u64
// -----------------------------------------------------------------
// Position at (x,y) = x + 8*y
// The low bit corresponds to the upper left most position.
// The high bit corresponds to the lower right most position.
// Rotations will happen from the center of the square.



#[derive(Copy, Clone, Eq, PartialEq, Hash, PartialOrd, Ord,)]
pub struct OriginBitGrid8(BitGrid8);  // This is a u64 under the hood

impl fmt::Debug for OriginBitGrid8 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "OriginBitGrid8({:#010x})", *self.0)
    } 
} 

impl fmt::Display for OriginBitGrid8 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", 
            (0..64)
            .map(|x| format!("{}{}", if (*self.0 >> x) & 0x1 == 1 { "#" } else { "." },
                if x%8 ==7 { "\n" } else { "" }))
            .collect::<String>()
            )
    } 
} 

impl OriginBitGrid8 {
    pub fn parse(grid: BitGrid8) -> Result<OriginBitGrid8, String> {
        if *grid & 0xff == 0 { return Err("First row is all zeros.".to_string()); }
        if *grid & 0x0101010101010101 == 0 { return Err("First column is all zeros.".to_string()); }
        Ok(Self(grid))
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
        Self(shape)
    }

    /*
    /// Pentominoes indexed by wikipedia naming convention.
    /// Diagonal presentations are rotated 45 degrees clockwise.
    pub fn pentomino_map() -> HashMap::<char, OriginBitGrid8> {
        HashMap::<char, OriginBitGrid8>::from([
            ('F', OriginBitGrid8(0x20306)),
            ('I', OriginBitGrid8(0x101010101)),
            ('L', OriginBitGrid8(0x3010101)),
            ('N', OriginBitGrid8(0xe03)),
            ('P', OriginBitGrid8(0x10303)),
            ('T', OriginBitGrid8(0x20207)),
            ('U', OriginBitGrid8(0x705)),
            ('V', OriginBitGrid8(0x70101)),
            ('W', OriginBitGrid8(0x60301)),
            ('X', OriginBitGrid8(0x20702)),
            ('Y', OriginBitGrid8(0xf04)),
            ('Z', OriginBitGrid8(0x60203)),
        ])
    }

    /// Produce all rotations of a BitGrid object translated towards origin.
    /// Prefer a gray code path through all rotations
    pub fn origin_rotate_all(self) -> ArrayVec::<BitGrid8, 4> {
        let mut vec = ArrayVec::<BitGrid8, 4>::new();
        let mut x = self.shift_to_origin();
        vec.push(x);
        for _ in 0..3 { x = x.rotate_cc().shift_to_origin(); vec.push(x); }
        vec.sort_unstable();
        let symmetries = vec.partition_dedup().0.len();  // Move duplicates to the end.
        vec.truncate(symmetries);
        vec
    }

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


impl std::convert::TryFrom<BitGrid8> for OriginBitGrid8 {
    type Error = String;

    fn try_from(grid: BitGrid8) -> Result<OriginBitGrid8, Self::Error> {
        if *grid & 0xff == 0 { return Err("First row is all zeros.".to_string()); }
        if *grid & 0x0101010101010101 == 0 { return Err("First column is all zeros.".to_string()); }
        Ok(Self(grid))
    }
}

impl core::ops::Deref for OriginBitGrid8 {
    type Target = BitGrid8;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}



#[cfg(test)]
mod test {
    use super::*;
    

    // #[test]
    // fn test_rank() {
        // assert_eq!(IDENTITY.rank(), 8);
        // assert_eq!(BitGrid8(0xfedcba9876543210u64).rank(), 4);
    // }

    #[test]
    fn test_origin_bitgrid8_display() {
        assert_eq!(format!("{}", OriginBitGrid8::try_from(BitGrid8(0x8040201008040201)).unwrap()), 
            "#.......\n.#......\n..#.....\n...#....\n....#...\n.....#..\n......#.\n.......#\n");
        // assert_eq!(format!("{}", OriginBitGrid8(0x1)), 
            // "#.......\n........\n........\n........\n........\n........\n........\n........\n");
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

*/
}
