use std::fmt;
// use std::collections::HashMap;


use derive_more::*;
use thiserror::*;
// use arrayvec::*;

// use crate::bitlib::swap_mask_shift_u64;
use crate::bitgrid8::*;

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
// Rotations will happen from the center of the square.


#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PieceBitGrid8{
    bitgrid: BitGrid8,  // This acts like a u64
    xy: (u8, u8),  // xy dimensions of bounding box
}

#[derive(Error, Debug, Clone, PartialEq)]
#[error("{0} is not origin shifted.")]
pub struct PieceGrid8Error(u64, String);

impl PieceBitGrid8 {
    pub fn new(raw_u64: u64) -> Result<Self, PieceGrid8Error> {
        if raw_u64 == 0 { return Ok(Self{ bitgrid: BitGrid8(raw_u64), xy: (0, 0) }) }
        if raw_u64 & 0xff == 0 { return Err(PieceGrid8Error(raw_u64, "First row is all zeros.".to_string())); }
        if raw_u64 & 0x0101010101010101 == 0 { return Err(PieceGrid8Error(raw_u64, "First column is all zeros.".to_string())); }
        let grid = BitGrid8(raw_u64);
        Ok(Self{ bitgrid: grid, xy: Self::bounding_box(grid) })
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
        Self{ bitgrid: shape, xy: Self::bounding_box(shape) }
    }

    /// Find the (x,y) bounding box of a piece shifted to origin
    fn bounding_box(grid: BitGrid8) -> (u8, u8) {
        let mut shape = grid;
        // Collect ones on x and y axes
        shape |= ((shape >> 1) & 0x7f7f7f7f7f7f7f7f) | shape >> 8;
        shape |= ((shape >> 2) & 0x3f3f3f3f3f3f3f3f) | shape >> 16;
        shape |= ((shape >> 4) & 0x0f0f0f0f0f0f0f0f) | shape >> 32;
        let len_x = (shape & 0xff).count_ones();
        let len_y = (shape & 0x0101010101010101).count_ones();
        (len_x as u8, len_y as u8)
    }

    /*
    /// Pentominoes indexed by wikipedia naming convention.
    /// Diagonal presentations are rotated 45 degrees clockwise.
    pub fn pentomino_map() -> HashMap::<char, PieceBitGrid8> {
        HashMap::<char, PieceBitGrid8>::from([
            ('F', PieceBitGrid8(0x20306)),
            ('I', PieceBitGrid8(0x101010101)),
            ('L', PieceBitGrid8(0x3010101)),
            ('N', PieceBitGrid8(0xe03)),
            ('P', PieceBitGrid8(0x10303)),
            ('T', PieceBitGrid8(0x20207)),
            ('U', PieceBitGrid8(0x705)),
            ('V', PieceBitGrid8(0x70101)),
            ('W', PieceBitGrid8(0x60301)),
            ('X', PieceBitGrid8(0x20702)),
            ('Y', PieceBitGrid8(0xf04)),
            ('Z', PieceBitGrid8(0x60203)),
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

impl fmt::Debug for PieceBitGrid8 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "PieceBitGrid8({:#010x})", *self.bitgrid)
    } 
} 

impl fmt::Display for PieceBitGrid8 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", 
            (0..64)
            .map(|x| format!("{}{}", if (*self.bitgrid >> x) & 0x1 == 1 { "#" } else { "." },
                if x%8 ==7 { "\n" } else { "" }))
            .collect::<String>()
            )
    } 
} 


impl std::convert::TryFrom<BitGrid8> for PieceBitGrid8 {
    type Error = PieceGrid8Error;

    fn try_from(grid: BitGrid8) -> Result<PieceBitGrid8, Self::Error> {
        Self::new(*grid)
    }
}

impl core::ops::Deref for PieceBitGrid8 {
    type Target = BitGrid8;

    fn deref(&self) -> &Self::Target {
        &self.bitgrid
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
    fn test_piece_bitgrid8_display() {
        assert_eq!(format!("{}", PieceBitGrid8::try_from(BitGrid8(0x8040201008040201)).unwrap()), 
            "#.......\n.#......\n..#.....\n...#....\n....#...\n.....#..\n......#.\n.......#\n");
        // assert_eq!(format!("{}", PieceBitGrid8(0x1)), 
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
