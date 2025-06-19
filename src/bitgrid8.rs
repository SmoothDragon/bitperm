use std::fmt;
use std::collections::HashMap;


use derive_more::*;
use arrayvec::*;

use crate::bitlib::swap_mask_shift_u64;

// -----------------------------------------------------------------
// 2D geometric operations on an 8x8 grid
// -----------------------------------------------------------------

// -----------------------------------------------------------------
// 8x8 square space represented by the 64 bits in a u64
// -----------------------------------------------------------------
// Position at (x,y) = x + 8*y
// The low bit corresponds to the lower left most position.
// The high bit corresponds to the upper right most position.
// Rotations will happen from the center of the square.
//
// The operators >> and << implement unbounded_shr() and unbounded_shl(),
// so they may be used safely.


// TODO: It seems like we would shift the border box over the designated square in all possible
// ways. For each of these ways, test that the piece in the box overlaps, that the shift is valid,
// that it doesn't overlap with the filled portion.

#[derive(Copy, Clone, Eq, PartialEq, Hash, PartialOrd, Ord,
    BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign,
    )]
pub struct BitGrid8(pub u64);

/// Let BitGrid8 use >> operator safely with i32 like Julia
impl core::ops::Shr<i32> for BitGrid8 {
    type Output = Self;

    fn shr(self, shift: i32) -> Self {
        let positive = shift >= 0;
        let shift: u32 = shift.unsigned_abs();
        if positive {
            Self(self.0.unbounded_shr(shift))
        } else {
            Self(self.0.unbounded_shl(shift))
        }
    }
}

/// Let BitGrid8 use << operator safely with i32 like Julia
impl core::ops::Shl<i32> for BitGrid8 {
    type Output = Self;

    fn shl(self, shift: i32) -> Self {
        let positive = shift >= 0;
        let shift: u32 = shift.unsigned_abs();
        if positive {
            Self(self.0.unbounded_shl(shift))
        } else {
            Self(self.0.unbounded_shr(shift))
        }
    }
}

impl core::ops::Not for BitGrid8 {
    type Output = Self;

    fn not(self) -> Self {
        Self(!self.0)
    }
}

/// Define BitAnd with u64 for BitGrid8
impl core::ops::BitAnd<u64> for BitGrid8 {
    type Output = Self;

    fn bitand(self, rhs: u64) -> Self {
        Self(self.0 & rhs)
    }
}

/// Define BitOr with u64 for BitGrid8
impl core::ops::BitOr<u64> for BitGrid8 {
    type Output = Self;

    fn bitor(self, rhs: u64) -> Self {
        Self(self.0 | rhs)
    }
}

/// Define BitXor with u64 for BitGrid8
impl core::ops::BitXor<u64> for BitGrid8 {
    type Output = Self;

    fn bitxor(self, rhs: u64) -> Self {
        Self(self.0 ^ rhs)
    }
}

impl fmt::Debug for BitGrid8 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "BitGrid8({:#010x})", self.0)
    } 
} 

impl fmt::Display for BitGrid8 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", 
            (0..8).rev().map(|y|
                (0..8)
                    .map(|x| format!("{}", if (self.0 >> (x + 8*y)) & 0x1 == 1 { "🟥" } else { "⬜" }))
                    .collect::<String>()
                    +"\n")
            .collect::<String>()
        )
    } 
} 

pub const ALL: u64 = 0xffff_ffff_ffff_ffff;
pub const CENTER_XY: BitGrid8 = BitGrid8(0x1818_18ff_ff18_1818);
pub const FULL: BitGrid8 = BitGrid8(0xffff_ffff_ffff_ffff_u64);
pub const ORDER: BitGrid8 = BitGrid8(0xfedc_ba98_7654_3210_u64);
pub const LOWER_LEFT: BitGrid8 = BitGrid8(0x0f0f_0f0f_u64);
pub const LOWER_RIGHT: BitGrid8 = BitGrid8(0xf0f0_f0f0_u64);
pub const UPPER_LEFT: BitGrid8 = BitGrid8(0x0f0f_0f0f_0000_0000_u64);
pub const UPPER_RIGHT: BitGrid8 = BitGrid8(0xf0f0_f0f0_0000_0000_u64);

pub const HIGHFIVE: BitGrid8 = BitGrid8(0xff80ff01ff);
pub const SMALL_FIVE: BitGrid8 = BitGrid8(0x00f080f010f);
pub const CHECKER2: BitGrid8 = BitGrid8(0x0c0c_0303);
pub const SLASH:BitGrid8 = BitGrid8(0x8040201008040201);
pub const BACKSLASH:BitGrid8 = BitGrid8(0x0102040810204080);
pub const BORDER:BitGrid8 = BitGrid8(0xff81_8181_8181_81ff);
pub const IDENTITY:BitGrid8 = BitGrid8(0x8040201008040201);
pub const ANTIDIAG:BitGrid8 = BitGrid8(0x0102040810204080);

// Beware using automatic deref
// impl core::ops::Deref for BitGrid8 {
    // type Target = u64;

    // fn deref(&self) -> &Self::Target {
        // &self.0
    // }
// }

impl Iterator for BitGrid8 {
    type Item = Self;

    fn next(&mut self) -> Option<Self::Item> {
        let grid:u64 = self.0;
        if grid != 0 {
            let bit:u64 = grid.isolate_least_significant_one();
            *self = Self(grid ^ bit);
            Some(Self(bit))
        } else {
            None
        }
    }
}


impl BitGrid8 {
    /// Pentominoes indexed by wikipedia naming convention.
    /// Diagonal presentations are rotated 45 degrees clockwise.
    pub fn pentomino_map() -> HashMap::<char, BitGrid8> {
        HashMap::<char, BitGrid8>::from([
            ('F', BitGrid8(0x20306)),
            ('I', BitGrid8(0x101010101)),
            ('L', BitGrid8(0x3010101)),
            ('N', BitGrid8(0xe03)),
            ('P', BitGrid8(0x10303)),
            ('T', BitGrid8(0x20207)),
            ('U', BitGrid8(0x705)),
            ('V', BitGrid8(0x70101)),
            ('W', BitGrid8(0x60301)),
            ('X', BitGrid8(0x20702)),
            ('Y', BitGrid8(0xf04)),
            ('Z', BitGrid8(0x60203)),
        ])
    }

    /// Find corners in the upper right (north east)
    pub fn find_corners_ne(self) -> BitGrid8 {
        (self.shift_x(-1) | 0x8080_8080_8080_8080) & (self.shift_y(-1) | 0xff00_0000_0000_0000) & !self
    }

    /// Find corners in the lower left (south west)
    pub fn find_corners_sw(self) -> BitGrid8 {
        (self.shift_x(1) | 0x0101_0101_0101_0101) & (self.shift_y(1) | 0xff) & !self
    }

    /// Find corners in the lower right (south east)
    pub fn find_corners_se(self) -> BitGrid8 {
        (self.shift_x(-1) | 0x8080_8080_8080_8080) & (self.shift_y(1) | 0xff) & !self
    }

    /// Find corners in the upper left (north west)
    pub fn find_corners_nw(self) -> BitGrid8 {
        (self.shift_x(1) | 0x0101_0101_0101_0101) & (self.shift_y(-1) | 0xff00_0000_0000_0000) & !self
    }

    /// Produce all rotations of a BitGrid object translated towards origin.
    /// Prefer a gray code path through all rotations
    /// TODO: This should just rotate and not shift to origin like piece_bitgtid8
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

    /// Return the NSEW border of a BitGrid8. This includes the border of the 8x8 square.
    pub fn border(self) -> Self {
        (self | self.shift_x(1) | self.shift_x(-1) | self.shift_y(1) | self.shift_y(-1) | BORDER) ^ self
    }

    /// Do two BitGrid8 objects overlap?
    pub fn has_overlap(self, other: Self) -> bool {
        self.0 & other.0 != 0
    }

    /// Does the BitGrid8 contain nothing?
    #[inline(always)]
    pub fn is_empty(self) -> bool {
        self.0 == 0
    }

    /// Return the king move border of a BitGrid8. This includes the border of the 8x8 square.
    pub fn border8(self) -> Self {
        let mut grid = self | self.shift_x(1) | self.shift_x(-1);
        grid |= grid.shift_y(1) | grid.shift_y(-1) | BORDER;
        grid ^ self
    }

    // pub fn border_domino_iter(self) -> impl Iterator<Item = Self> {
        // self.border8().into_iter().flat_map(|pixel| {
            // if (pixel.shift_x(1) & self).0 == 0{ vec![pixel | pixel.shift_x(1)].into_iter() };
            // if (pixel.shift_y(1) & self).0 == 0 { vec![pixel | pixel.shift_y(1)].into_iter() };
        // })
    // }

    /// This method ignores the corner connections in a down right direction, but messes up with
    /// down left.
    /// Perhaps we count the connections both ways and correct by both diagonals.
    /// This algorithm uses a fast local computation to compute the number of connected components
    /// minus the number of holes in a shape.
    /// The original algorithm assumes that no filled squares can be only corner adjacent.
    /// This algorithm gives the correct count allows for adjacent corners (not considered connected).
    /// TODO: This could be sped up by doing all three antimask counts simulataneously.
    pub fn count_components(self) -> u32 {
        self.count_2x2_antimask(0x55ff_55ff_55ff_55ff_u64)
        + self.count_2x2_antimask(0x55aa_55aa_55aa_55aa_u64)  // Only needed if corners touch
        - self.count_2x2_antimask(0x0055_0055_0055_0055_u64)
    }

    /// Count how many complete 2x2 blocks there are in the 4x4 subgrid of such blocks
    #[inline]
    pub fn count_2x2_blocks(self) -> u32 {
        let mut grid: u64 = self.0;
        grid &= grid.unbounded_shr(8);
        grid &= grid.unbounded_shr(1) & 0x0055_0055_0055_0055u64;
        grid.count_ones()
    }

    /// Count the total number of a specific 2x2 block fill.
    /// The mask provided should be the complement of this fill so that when it is XORed in it
    /// creates a filled 2x2 block.
    /// In particular, a 0x0 mask will return the number of 2x2 full blocks.
    /// ##  =>  0x0055_0055_0055_0055_u64
    /// .#
    /// .#  =>  0x55ff_55ff_55ff_55ff_u64
    /// ..
    /// .#  =>  0x55aa_55aa_55aa_55aa_u64
    /// #.
    #[inline]
    pub fn count_2x2_antimask(self, antimask: u64) -> u32 {
        const RIGHT: u64 = 0xfefe_fefe_fefe_fefe_u64;
        BitGrid8((self.0.unbounded_shl(9) & RIGHT) ^ antimask).count_2x2_blocks()
            + BitGrid8((self.0.unbounded_shl(1) & RIGHT) ^ antimask).count_2x2_blocks()
            + BitGrid8(self.0.unbounded_shl(8) ^ antimask).count_2x2_blocks()
            + (self ^ BitGrid8(antimask)).count_2x2_blocks()
    }


    /// TODO: These can be sped up by doing them simultaneously
    /// Count upper right 2x2 blocks
    /// .#
    /// ..
    #[inline]
    pub fn count_upper_right_2x2_blocks(self) -> u32 {
        println!("{:}", BitGrid8((self.0.unbounded_shl(9) & 0xfefe_fefe_fefe_fe00_u64) ^ 0x55ff_55ff_55ff_55ff_u64));
        BitGrid8((self.0.unbounded_shl(9) & 0xfefe_fefe_fefe_fe00_u64) ^ 0x55ff_55ff_55ff_55ff_u64).count_2x2_blocks()
            + BitGrid8((self.0.unbounded_shl(1) & 0xfefe_fefe_fefe_fefe_u64) ^ 0x55ff_55ff_55ff_55ff_u64).count_2x2_blocks()
            + BitGrid8(self.0.unbounded_shl(8) ^ 0x55ff_55ff_55ff_55ff_u64).count_2x2_blocks()
            + (self ^ BitGrid8(0x55ff_55ff_55ff_55ff_u64)).count_2x2_blocks()
    }

    /// Count lower left 2x2 blocks
    /// ##
    /// .#
    #[inline]
    pub fn count_lower_left_2x2_blocks(self) -> u32 {
        const ANTIMASK: u64 = 0x0055_0055_0055_0055_u64;
        BitGrid8((self.0.unbounded_shl(9) & 0xfefe_fefe_fefe_fe00_u64) ^ ANTIMASK).count_2x2_blocks()
            + BitGrid8((self.0.unbounded_shl(1) & 0xfefe_fefe_fefe_fefe_u64) ^ ANTIMASK).count_2x2_blocks()
            + BitGrid8(self.0.unbounded_shl(8) ^ ANTIMASK).count_2x2_blocks()
            + (self ^ BitGrid8(ANTIMASK)).count_2x2_blocks()
    }


    /// Count antidiagonal 2x2 blocks
    /// .#
    /// #.
    #[inline]
    pub fn count_antidiagonal_2x2_blocks(self) -> u32 {
        const ANTIMASK: u64 = 0x55aa_55aa_55aa_55aa_u64;
        BitGrid8((self.0.unbounded_shl(9) & 0xfefe_fefe_fefe_fe00_u64) ^ ANTIMASK).count_2x2_blocks()
            + BitGrid8((self.0.unbounded_shl(1) & 0xfefe_fefe_fefe_fefe_u64) ^ ANTIMASK).count_2x2_blocks()
            + BitGrid8(self.0.unbounded_shl(8) ^ ANTIMASK).count_2x2_blocks()
            + (self ^ BitGrid8(ANTIMASK)).count_2x2_blocks()
    }


    /// Produce all rotations and reflections of a BitGrid object translated towards origin.
    /// Prefer a gray code path through all rotations
    /// TODO: This should just rotate and not shift to oorigin like piece_bitgtid8
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

    /// Produce all rotations of a BitGrid
    /// Prefer a gray code path through all rotations
    pub fn rotate_all_vec(self) -> ArrayVec::<BitGrid8, 4> {
        let mut vec = ArrayVec::<BitGrid8, 4>::new();
        let mut x = self;
        vec.push(x);
        for _ in 0..3 { x = x.rotate_cc(); vec.push(x); }
        vec.sort_unstable();
        let symmetries = vec.partition_dedup().0.len();  // Move duplicates to the end.
        vec.truncate(symmetries);
        vec
    }

    /// 2x2x2 Example: 01 23 | 45 67 => 20 31 | 64 75 
    /// The z-rotation is the easiest to understand since the rotation happens in the xy-plane and
    /// is copied in the other dimension.
    /// 23 32 31
    /// 01 10 20
    pub fn rotate_cc(self) -> Self { 
        let mut square = self.0;
        // Swap diagonal 4x4 squares
        swap_mask_shift_u64(&mut square, 0x0f0f_0f0f_u64, 36);
        // Swap 4x4 squares top <-> bottom
        swap_mask_shift_u64(&mut square, 0xffff_ffff_u64, 32);
        // Swap diagonal 2x2 squares
        swap_mask_shift_u64(&mut square, 0x0000_3333_0000_3333_u64, 18);
        // Swap 2x2 squares top <-> bottom
        swap_mask_shift_u64(&mut square, 0xffff_0000_ffff_u64, 16);
        // Within 2x2 squares swap diagonal entries
        swap_mask_shift_u64(&mut square, 0x0055_0055_0055_0055_u64, 9);
        // Within 2x2 squares swap top <-> bottom rows
        swap_mask_shift_u64(&mut square, 0x00ff_00ff_00ff_00ff_u64, 8);
        BitGrid8(square)
    }

    /// 2x2x2 Example: 01 23 | 45 67 => 20 31 | 64 75 
    /// The z-rotation is the easiest to understand since the rotation happens in the xy-plane and
    /// is copied in the other dimension.
    /// 23 32 31
    /// 01 10 20
    pub fn rotate(self) -> Self { 
        let mut square = self.0;
        // Swap 4x4 squares top <-> bottom
        swap_mask_shift_u64(&mut square, 0xffff_ffff_u64, 32);
        // Swap diagonal 4x4 squares
        swap_mask_shift_u64(&mut square, 0x0f0f_0f0f_u64, 36);
        // Swap 2x2 squares top <-> bottom
        swap_mask_shift_u64(&mut square, 0xffff_0000_ffff_u64, 16);
        // Swap diagonal 2x2 squares
        // GOOD TO HERE?
        swap_mask_shift_u64(&mut square, 0x0000_3333_0000_3333_u64, 18);
        // Within 2x2 squares swap top <-> bottom rows
        swap_mask_shift_u64(&mut square, 0x00ff_00ff_00ff_00ff_u64, 8);
        // Within 2x2 squares swap diagonal entries
        swap_mask_shift_u64(&mut square, 0x0055_0055_0055_0055_u64, 9);
        BitGrid8(square)
    }

    // Flip along x-axis. For 2D this is the same as mirror.
    pub fn flip_x(self) -> Self { 
        let mut square = self.0;
        // Swap halves top <-> bottom
        swap_mask_shift_u64(&mut square, 0xffff_ffff_u64, 32);
        // Swap quartiles top <-> bottom
        swap_mask_shift_u64(&mut square, 0xffff_0000_ffff_u64, 16);
        // Swap eight top <-> bottom rows
        swap_mask_shift_u64(&mut square, 0x00ff_00ff_00ff_00ff_u64, 8);
        BitGrid8(square)
    }

    /// Shift a piece in the 8-grid towards the origin so that it touches the x and y axes
    pub fn shift_to_origin(self) -> Self {
        let mut shape = self.0;
        let y_shift = (shape.trailing_zeros() / 8) * 8;
        shape = shape.unbounded_shr(y_shift);
        let mut x_shift = shape | shape.unbounded_shr(32);
        x_shift |= x_shift.unbounded_shr(32);
        x_shift |= x_shift.unbounded_shr(16);
        x_shift |= x_shift.unbounded_shr(8);
        shape = shape.unbounded_shr(x_shift.trailing_zeros());
        Self(shape)
    }

    /// Find the (x,y) bounding box of a BitGrid8.
    /// The box includes the origin and all nonzero squares.
    pub fn bounding_box(self) -> (u32, u32) {
        let mut shape = self.0;
        // Collect ones on x and y axes
        shape |= ((shape >> 1) & 0x7f7f7f7f7f7f7f7f) | shape >> 8;
        shape |= ((shape >> 2) & 0x3f3f3f3f3f3f3f3f) | shape >> 16;
        shape |= ((shape >> 4) & 0x0f0f0f0f0f0f0f0f) | shape >> 32;
        let len_x = (shape & 0xff).count_ones();
        let len_y = (shape & 0x0101010101010101).count_ones();
        (len_x as u32, len_y as u32)
    }

    /// Shifts off the side are lost.
    pub fn shift_x(self, shift: i32) -> Self { 
        if shift > 7 || shift < -7 { return Self(0) };
        if shift == 0 { return self };
        let sign = shift > 0;
        let shift: u32 = shift.unsigned_abs();
        let mask: u64 = ((1_u64 << (8_u32-shift)) - 1_u64) * 0x0101_0101_0101_0101_u64;
        if sign {
            BitGrid8((mask & self.0).unbounded_shl(shift))
        } else {
            BitGrid8(mask & self.0.unbounded_shr(shift))
        }
    }

    /// Verifies that the x_shift does not cross the boundary edges
    pub fn checked_shift_x(self, shift: i32) -> Option<Self> { 
        let shifted = self.shift_x(shift);
        if self.0.count_ones() == shifted.0.count_ones() {
            Some(shifted)
        } else {
            None
        }
    }

    /// Shifts off the side are lost.
    pub fn shift_y(self, shift: i32) -> Self { 
        if shift > 7 || shift < -7 { return Self(0) };
        if shift == 0 { return self };
        let sign = shift > 0;
        let shift: u32 = shift.unsigned_abs().unbounded_shl(3);  // Shift by multiples of 8
        // let mask: u64 = ((1_u64 << (8_u32-shift)) - 1_u64) * 0x0101_0101_0101_0101_u64;
        let mask: u64 = 0xffff_ffff_ffff_ffff_u64.unbounded_shr(shift);
        if sign {
            BitGrid8((mask & self.0).unbounded_shl(shift))
        } else {
            BitGrid8(mask & self.0.unbounded_shr(shift))
        }
    }

    /// Verifies that the x_shift does not cross the boundary edges
    pub fn checked_shift_y(self, shift: i32) -> Option<Self> { 
        let shifted = self.shift_y(shift);
        if self.0.count_ones() == shifted.0.count_ones() {
            Some(shifted)
        } else {
            None
        }
    }

    /// Shifts off the side are lost.
    /// The low three bits of shift are the x-shift, and the high three the y-shift.
    /// Low six bits of shift = y2 y2 y0 x2 x1 x0
    /// Only 
    pub fn shift_xy(self, x_shift: i32, y_shift: i32) -> Self { 
        self.shift_x(x_shift).shift_y(y_shift)
    }

    /// Verifies that the x_shift does not cross the boundary edges
    pub fn checked_shift_xy(self, x_shift: i32, y_shift: i32) -> Option<Self> { 
        let shifted = self.shift_xy(x_shift, y_shift);
        if self.0.count_ones() == shifted.0.count_ones() {
            Some(shifted)
        } else {
            None
        }
    }
}


#[cfg(test)]
mod test {
    use super::*;
    
    #[test]
    fn test_bitgrid8_display() {
        assert_eq!(format!("{}", BACKSLASH),
"🟥⬜⬜⬜⬜⬜⬜⬜\n⬜🟥⬜⬜⬜⬜⬜⬜\n⬜⬜🟥⬜⬜⬜⬜⬜\n⬜⬜⬜🟥⬜⬜⬜⬜\n⬜⬜⬜⬜🟥⬜⬜⬜\n⬜⬜⬜⬜⬜🟥⬜⬜\n⬜⬜⬜⬜⬜⬜🟥⬜\n⬜⬜⬜⬜⬜⬜⬜🟥\n");
        assert_eq!(format!("{}", BitGrid8(0x1)), 
            "⬜⬜⬜⬜⬜⬜⬜⬜\n⬜⬜⬜⬜⬜⬜⬜⬜\n⬜⬜⬜⬜⬜⬜⬜⬜\n⬜⬜⬜⬜⬜⬜⬜⬜\n⬜⬜⬜⬜⬜⬜⬜⬜\n⬜⬜⬜⬜⬜⬜⬜⬜\n⬜⬜⬜⬜⬜⬜⬜⬜\n🟥⬜⬜⬜⬜⬜⬜⬜\n");
    }

    #[test]
    fn test_shift_to_origin() {
        assert_eq!(FULL.shift_to_origin(), FULL);
        assert_eq!(UPPER_RIGHT.shift_to_origin(), LOWER_LEFT);
        assert_eq!(BACKSLASH.shift_to_origin(), BACKSLASH);
        assert_eq!(CENTER_XY.shift_to_origin(), CENTER_XY);
        assert_eq!(BitGrid8(0xf00f00).shift_to_origin(), BitGrid8(0xf00f));

        let pentomino = BitGrid8::pentomino_map();
        assert_eq!((*(&pentomino[&'F']) << 24).shift_to_origin(), pentomino[&'F']);
    }

    #[test]
    fn test_find_corner_sw() {
        assert_eq!(FULL.find_corners_sw(), BitGrid8(0));
        println!("{}", UPPER_RIGHT.find_corners_sw());
        assert_eq!(UPPER_RIGHT.find_corners_sw(), BitGrid8(0x1));
        assert_eq!(BACKSLASH.find_corners_sw(), BitGrid8(0x204081020408001));
        assert_eq!(CENTER_XY.find_corners_sw(), BitGrid8(0x210000000021));

        let pentomino = BitGrid8::pentomino_map();
        println!("{:}", pentomino[&'F'].find_corners_sw());
        println!("{:}", pentomino[&'F']);
        assert_eq!((pentomino[&'F']).find_corners_sw(), BitGrid8(0x00010409));
    }

    #[test]
    fn test_find_corner_nw() {
        assert_eq!(FULL.find_corners_nw(), BitGrid8(0));
        println!("{}", UPPER_RIGHT);
        println!("{}", UPPER_RIGHT.find_corners_nw());
        assert_eq!(UPPER_RIGHT.find_corners_nw(), BitGrid8(0x0100_0000_0000_0000));
        assert_eq!(BACKSLASH.find_corners_nw(), BitGrid8(0x201000000000000));
        println!("{}", CENTER_XY.find_corners_nw());
        assert_eq!(CENTER_XY.find_corners_nw(), BitGrid8(0x210000000021_0000));

        let pentomino = BitGrid8::pentomino_map();
        println!("{:}", pentomino[&'F'].find_corners_nw());
        println!("{:}", pentomino[&'F']);
        assert_eq!((pentomino[&'F']).find_corners_nw(), BitGrid8(0x100000000000001));
    }

    #[test]
    fn test_find_corner_se() {
        assert_eq!(FULL.find_corners_se(), BitGrid8(0));
        println!("{}", UPPER_RIGHT.find_corners_se());
        assert_eq!(UPPER_RIGHT.find_corners_se(), BitGrid8(0x80));
        assert_eq!(BACKSLASH.find_corners_se(), BitGrid8(0x08040));
        assert_eq!(CENTER_XY.find_corners_se(), BitGrid8(0x840000000084));

        let pentomino = BitGrid8::pentomino_map();
        println!("{:}", pentomino[&'F'].find_corners_se());
        println!("{:}", pentomino[&'F']);
        assert_eq!((pentomino[&'F']).find_corners_se(), BitGrid8(0x00010081));
    }

    #[test]
    fn test_find_corner_ne() {
        assert_eq!(FULL.find_corners_ne(), BitGrid8(0));
        assert_eq!(UPPER_RIGHT.find_corners_ne(), BitGrid8(0x800000080000000));
        assert_eq!(BACKSLASH.find_corners_ne(), BitGrid8(0x8001020408102040));
        println!("{}", CENTER_XY.find_corners_ne());
        assert_eq!(CENTER_XY.find_corners_ne(), BitGrid8(0x8400000000840000));

        let pentomino = BitGrid8::pentomino_map();
        println!("{:}", pentomino[&'F'].find_corners_ne());
        println!("{:}", pentomino[&'F']);
        assert_eq!((pentomino[&'F']).find_corners_ne(), BitGrid8(0x8000000000000001));
    }

    #[test]
    fn test_border() {
        assert_eq!(FULL.border(), BitGrid8(0));
        assert_eq!(UPPER_RIGHT.border(), BitGrid8(0xf090909f18181ff));
        assert_eq!(BACKSLASH.border(), BitGrid8(0xfe858b95a9d1a17f));
        assert_eq!(CENTER_XY.border(), BitGrid8(0xe7a5e70000e7a5e7));
        assert_eq!(BitGrid8(0x1818000000).border(), BitGrid8(0xff8199a5a59981ff));

        let pentomino = BitGrid8::pentomino_map();
        println!("{:}", pentomino[&'F'].border());
        assert_eq!((pentomino[&'F']).border(), BitGrid8(0xff818181838584f9));
    }

    #[test]
    fn test_border_connected() {
        assert_eq!(FULL.border8(), BitGrid8(0));
        assert_eq!(UPPER_RIGHT.border8(), BitGrid8(0xf090909f98181ff));
        assert_eq!(BACKSLASH.border8(), BitGrid8(0xfe8d9bb7edd9b17f));
        assert_eq!(CENTER_XY.border8(), BitGrid8(0xe7a5e70000e7a5e7));
        assert_eq!(BitGrid8(0x1818000000).border8(), BitGrid8(0xff81bda5a5bd81ff));

        let pentomino = BitGrid8::pentomino_map();
        println!("{:}", pentomino[&'F'].border8());
        assert_eq!((pentomino[&'F']).border8(), BitGrid8(0xff81818187858cf9));
    }

    #[test]
    fn test_count_2x2_blocks() {
        assert_eq!(FULL.count_2x2_blocks(), 16);
        assert_eq!(UPPER_RIGHT.count_2x2_blocks(), 4);
        assert_eq!(BACKSLASH.count_2x2_blocks(), 0);
        assert_eq!(CENTER_XY.count_2x2_blocks(), 0);
    }

    #[test]
    fn test_count_upper_right_2x2_blocks_all() {
        assert_eq!(FULL.count_upper_right_2x2_blocks(), 1);
        assert_eq!(CENTER_XY.count_upper_right_2x2_blocks(), 2);
        assert_eq!(HIGHFIVE.count_upper_right_2x2_blocks(), 2);
        assert_eq!(BACKSLASH.count_upper_right_2x2_blocks(), 8);
    }

    #[test]
    fn test_count_lower_left_2x2_blocks_all() {
        assert_eq!(FULL.count_lower_left_2x2_blocks(), 0);
        assert_eq!(CENTER_XY.count_lower_left_2x2_blocks(), 1);
        assert_eq!(HIGHFIVE.count_lower_left_2x2_blocks(), 1);
        assert_eq!(BACKSLASH.count_lower_left_2x2_blocks(), 0);
    }

    #[test]
    fn test_count_components() {
        assert_eq!(FULL.count_components(), 1);
        assert_eq!(CENTER_XY.count_components(), 1);
        assert_eq!(HIGHFIVE.count_components(), 1);
        assert_eq!(BACKSLASH.count_components(), 8);
        assert_eq!(SLASH.count_components(), 8);
    }

    #[test]
    fn test_shift_x() {
        assert_eq!(FULL.shift_x(1), BitGrid8(0xfefe_fefe_fefe_fefe_u64));
        assert_eq!(FULL.shift_x(4), BitGrid8(0xf0f0_f0f0_f0f0_f0f0_u64));
        assert_eq!(FULL.shift_x(-1), BitGrid8(0x7f7f_7f7f_7f7f_7f7f_u64));
        assert_eq!(FULL.shift_x(-4), BitGrid8(0x0f0f_0f0f_0f0f_0f0f_u64));
        assert_eq!(FULL.shift_x(-8), BitGrid8(0));
        assert_eq!(FULL.shift_x(8), BitGrid8(0));

        let pentomino = BitGrid8::pentomino_map();
        assert_eq!((*(&pentomino[&'F'])).shift_x(1), BitGrid8(0x4060c));
        assert_eq!((*(&pentomino[&'F'])).shift_x(-1), BitGrid8(0x10103));
    }

    #[test]
    fn test_checked_shift_x() {
        assert_eq!(FULL.checked_shift_x(1), None);
        assert_eq!(FULL.checked_shift_x(-1), None);

        let pentomino = BitGrid8::pentomino_map();
        assert_eq!((*(&pentomino[&'F'])).checked_shift_x(1), Some(BitGrid8(0x4060c)));
        assert_eq!((*(&pentomino[&'F'])).checked_shift_x(-1), None);
    }

    #[test]
    fn test_shift_y() {
        assert_eq!(FULL.shift_y(1), BitGrid8(0xffff_ffff_ffff_ff00_u64));
        assert_eq!(FULL.shift_y(-1), BitGrid8(0x00ff_ffff_ffff_ffff_u64));
        assert_eq!(FULL.shift_y(4), BitGrid8(0xffff_ffff_0000_0000_u64));
        assert_eq!(FULL.shift_y(-4), BitGrid8(0x0000_0000_ffff_ffff_u64));
        assert_eq!(FULL.shift_y(8), BitGrid8(0));
        assert_eq!(FULL.shift_y(-8), BitGrid8(0));
        assert_eq!(BitGrid8(0xf00f).shift_y(-1), BitGrid8(0xf0));
        assert_eq!(BitGrid8(0xf00f00).shift_y(-1), BitGrid8(0xf00f));

        let pentomino = BitGrid8::pentomino_map();
        assert_eq!((*(&pentomino[&'F'])).shift_y(1), BitGrid8(0x2030600));
        assert_eq!((*(&pentomino[&'F'])).shift_y(-1), BitGrid8(0x203));
    }

    #[test]
    fn test_checked_shift_y() {
        assert_eq!(FULL.checked_shift_y(1), None);
        assert_eq!(FULL.checked_shift_y(-1), None);
        assert_eq!(BitGrid8(0xf00f).checked_shift_y(-1), None);
        assert_eq!(BitGrid8(0xf00f00).checked_shift_y(-1), Some(BitGrid8(0xf00f)));

        let pentomino = BitGrid8::pentomino_map();
        assert_eq!((*(&pentomino[&'F'])).checked_shift_y(1), Some(BitGrid8(0x2030600)));
        assert_eq!((*(&pentomino[&'F'])).checked_shift_y(-1), None);
    }

    #[test]
    fn test_shift_xy() {
        assert_eq!(FULL.shift_xy(1,1), BitGrid8(0xfefe_fefe_fefe_fe00_u64));
        assert_eq!(FULL.shift_xy(1,-1), BitGrid8(0x00fe_fefe_fefe_fefe_u64));
        assert_eq!(FULL.shift_xy(-8,1), BitGrid8(0));
        assert_eq!(FULL.shift_xy(1,8), BitGrid8(0));

        let pentomino = BitGrid8::pentomino_map();
        assert_eq!((*(&pentomino[&'F'])).shift_xy(1,1), BitGrid8(0x4060c00));
        assert_eq!((*(&pentomino[&'F'])).shift_xy(1,-1), BitGrid8(0x406));
        assert_eq!((*(&pentomino[&'F'])).shift_xy(-1,1), BitGrid8(0x1010300));
        assert_eq!((*(&pentomino[&'F'])).shift_xy(-1,-1), BitGrid8(0x101));
    }

    #[test]
    fn test_checked_shift_xy() {
        assert_eq!(FULL.checked_shift_xy(1,1), None);
        assert_eq!(FULL.checked_shift_xy(-1,-1), None);

        let pentomino = BitGrid8::pentomino_map();
        assert_eq!((*(&pentomino[&'F'])).checked_shift_xy(1,1), Some(BitGrid8(0x4060c00)));
        assert_eq!((*(&pentomino[&'F'])).checked_shift_xy(1,-1), None);
        assert_eq!((*(&pentomino[&'F'])).checked_shift_xy(-1,1), None);
        assert_eq!((*(&pentomino[&'F'])).checked_shift_xy(-1,-1), None);
    }

    #[test]
    fn test_bitgrid8_iterator() {
        let pentomino = BitGrid8::pentomino_map();
        let pent_i_points = pentomino[&'I'].into_iter();
        assert_eq!(pent_i_points.collect::<Vec<_>>(), [BitGrid8(0x00000001), BitGrid8(0x00000100), BitGrid8(0x00010000), BitGrid8(0x01000000), BitGrid8(0x100000000)]);
        // Do it again to make sure iterator isn't consumed
        assert_eq!(pent_i_points.collect::<Vec<_>>(), [BitGrid8(0x00000001), BitGrid8(0x00000100), BitGrid8(0x00010000), BitGrid8(0x01000000), BitGrid8(0x100000000)]);

        let pent_i_points_rotate = pentomino[&'I'].rotate_cc().into_iter();
        assert_eq!(pent_i_points_rotate.collect::<Vec<_>>(), [BitGrid8(0x00000008), BitGrid8(0x00000010), BitGrid8(0x00000020), BitGrid8(0x00000040), BitGrid8(0x00000080)]);
        // Do it again to make sure iterator isn't consumed
        assert_eq!(pent_i_points_rotate.collect::<Vec<_>>(), [BitGrid8(0x00000008), BitGrid8(0x00000010), BitGrid8(0x00000020), BitGrid8(0x00000040), BitGrid8(0x00000080)]);
    }

    
    #[test]
    fn test_bounding_box_pentomino() {
        let pentomino = BitGrid8::pentomino_map();
        assert_eq!((&pentomino[&'F']).bounding_box(), (3,3));
        assert_eq!((&pentomino[&'I']).bounding_box(), (1,5));
        assert_eq!((&pentomino[&'L']).bounding_box(), (2,4));
        assert_eq!((&pentomino[&'P']).bounding_box(), (2,3));
        assert_eq!((&pentomino[&'W']).bounding_box(), (3,3));
    }

    #[test]
    fn test_bounding_box() {
        assert_eq!(FULL.bounding_box(), (8,8));
        assert_eq!(LOWER_LEFT.bounding_box(), (4,4));
        assert_eq!(BACKSLASH.bounding_box(), (8,8));
        assert_eq!(HIGHFIVE.bounding_box(), (8,5));
        assert_eq!(SMALL_FIVE.bounding_box(), (4,5));
        assert_eq!(BitGrid8(0).bounding_box(), (0,0));
        assert_eq!(BitGrid8(1).bounding_box(), (1,1));
    }

    #[test]
    fn test_origin_bounding_box_pentomino() {
        let pentomino = BitGrid8::pentomino_map();
        assert_eq!((&pentomino[&'F']).bounding_box(), (3,3));
        assert_eq!((&pentomino[&'I']).bounding_box(), (1,5));
        assert_eq!((&pentomino[&'L']).bounding_box(), (2,4));
        assert_eq!((&pentomino[&'P']).bounding_box(), (2,3));
        assert_eq!((&pentomino[&'W']).bounding_box(), (3,3));
    }

    // #[test]
    // fn test_origin_bounded_shift() {
        // assert_eq!(FULL.origin_bounded_shifts().len(), 1);
        // assert_eq!(UPPER_LEFT.origin_bounded_shifts().len(), 25);
        // assert_eq!(ANTIDIAG.origin_bounded_shifts().len(), 1);
        // assert_eq!(HIGHFIVE.origin_bounded_shifts().len(), 4);
        // assert_eq!(SMALL_FIVE.origin_bounded_shifts().len(), 20);
    // }

    
    // #[test]
    // fn test_origin_bounded_shift() {
        // assert_eq!(FULL.origin_bounded_shifts().len(), 1);
        // assert_eq!(UPPER_LEFT.origin_bounded_shifts().len(), 25);
        // assert_eq!(BACKSLASH.origin_bounded_shifts().len(), 1);
        // assert_eq!(HIGHFIVE.origin_bounded_shifts().len(), 4);
        // assert_eq!(SMALL_FIVE.origin_bounded_shifts().len(), 20);
    // }

    #[test]
    fn test_rotate_cc() {
        assert_eq!(BitGrid8(0x171515151515151d).rotate_cc(), HIGHFIVE);
        assert_eq!(BitGrid8(0x1715151d00000000).rotate_cc(), SMALL_FIVE);
        assert_eq!(FULL.rotate_cc(), FULL);
        println!("{}", UPPER_LEFT);
        println!("{}", UPPER_LEFT.rotate_cc());
        assert_eq!(LOWER_LEFT, UPPER_LEFT.rotate_cc());
        assert_eq!(BACKSLASH, SLASH.rotate_cc());
    }

    #[test]
    fn test_rotate() {
        assert_eq!(HIGHFIVE.rotate(), BitGrid8(0x171515151515151d));
        assert_eq!(SMALL_FIVE.rotate(), BitGrid8(0x1715151d00000000));
        assert_eq!(BACKSLASH, SLASH.rotate());
        assert_eq!(FULL.rotate(), FULL);
        assert_eq!(LOWER_LEFT.rotate(), UPPER_LEFT);
    }

    #[test]
    fn test_rotate_composition() {
        assert_eq!(BitGrid8(0x9288_7746_3521_0076).rotate().rotate_cc(), BitGrid8(0x9288_7746_3521_0076));
        assert_eq!(BitGrid8(0x9288_7746_3521_0076).rotate_cc().rotate(), BitGrid8(0x9288_7746_3521_0076));
    }

    #[test]
    fn test_flip_x() {
        // assert_eq!(SMALL_FIVE.rotate_cc(), BitGrid8(0x1715151d00000000));
        assert_eq!(BACKSLASH, SLASH.flip_x());
        assert_eq!(FULL.flip_x(), FULL);
        println!("{}", UPPER_LEFT);
        println!("{}", UPPER_LEFT.flip_x());
        assert_eq!(UPPER_LEFT.flip_x(), LOWER_LEFT);
        assert_eq!(HIGHFIVE.flip_x(), BitGrid8(0xff01_ff80_ff00_0000));
    }

    #[test]
    fn test_rotate_all_vec() {
        assert_eq!(BitGrid8::rotate_all_vec(CENTER_XY).as_slice(), &[CENTER_XY]);
        assert_eq!(BitGrid8::rotate_all_vec(UPPER_LEFT).as_slice(), &[LOWER_LEFT, LOWER_RIGHT, UPPER_LEFT, UPPER_RIGHT, ]);
        assert_eq!(BitGrid8::rotate_all_vec(SLASH).len(), 2);
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

    #[test]
    fn test_pentomino_map() {
        let pentomino = BitGrid8::pentomino_map();
        // for (key, value) in &pentomino {
            // println!("{}:\n{}", key, value);
        // }
        assert_eq!(&pentomino[&'X'], &pentomino[&'X'].rotate_cc().shift_to_origin());
        assert_eq!(&pentomino[&'X'], &pentomino[&'X'].rotate().shift_to_origin());
        assert_eq!((&pentomino[&'X']).origin_rotate_all().len(), 1);
        assert_eq!((&pentomino[&'F']).origin_rotate_all().len(), 4);
        assert_eq!((&pentomino[&'Z']).origin_rotate_all().len(), 2);
    }

    #[test]
    fn test_blsi() {
        let n: u64 = 0b_01100100;

        assert_eq!(n.isolate_least_significant_one(), 0b_00000100);
        assert_eq!(0_u64.isolate_least_significant_one(), 0);
    }


    // #[test]
    // fn test_shift_w() {
        // assert_eq!(BitGrid8(0xf00f).shift_w(), None);
        // assert_eq!(BitGrid8(0xf00f00).shift_w(), Some(BitGrid8(0xf00f)));
    // }
}
/*

// ---------------------------------------------------------------------
// Bit Permutation over 3 bits represented as three polynomials in a u32
// ---------------------------------------------------------------------

#[derive(PartialEq)]
pub struct BitPermPoly3(u32);

impl From<BitPermTT3> for BitPermPoly3 {
    fn from(bptt3: BitPermTT3) -> Self {
        let mut p = bptt3.0;
        swap_mask_shift_u32(&mut p, 0xf0f0, 12);
        swap_mask_shift_u32(&mut p, 0xff00, 8);
        swap_mask_shift_u32(&mut p, 0xcccc, 14);
        swap_mask_shift_u32(&mut p, 0xff00, 8);
        swap_mask_shift_u32(&mut p, 0xaaaa, 15);
        swap_mask_shift_u32(&mut p, 0xff00, 8);
        BitPermPoly3(p)
    }
}

impl fmt::Debug for BitPermPoly3 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "BitPermTT3({:#010x})", self.0)
    } 
} 

// -----------------------------------------------------------------
// Bit Permutation over 4 bits represented as a truth table in a u64
// -----------------------------------------------------------------

#[derive(PartialEq)]
pub struct BitPermTT4(u64);

#[inline]  // TODO: Make this general for all u16, u32, u64, u128
fn swap_mask_shift_u64(y: &mut u64, mask: u64, shift: usize) -> () {
   *y ^= (*y >> shift) & mask;
   *y ^= (*y & mask) << shift;
   *y ^= (*y >> shift) & mask;
}


impl BitPermTT4 {
    pub const ID:BitPermTT4 = BitPermTT4(0xfedcba9876543210);

    pub fn id() -> BitPermTT4 {
        BitPermTT4(0xfedcba9876543210)
    }

    pub fn increment() -> BitPermTT4 {
        BitPermTT4(0x0fedcba987654321)
    }

    pub fn compose(self, other: Self) -> Self {
        Self(
            (0..16)
            .map(|x| ((self.0 >> (((other.0 >> (x<<2)) & 0xf) << 2)) & 0xf) << (x<<2))
            .sum()
            )
    }

    pub fn inverse(self) -> Self {
        Self(
            (0..16)
            .map(|x| x << (((self.0 >> (x<<2)) & 0xf) << 2))
            .sum()
            )
    }
}

impl From<BitPermTT3> for BitPermTT4 {
    fn from(bptt3: BitPermTT3) -> Self {
        let p = bptt3.0 as u64;
        BitPermTT4(p ^ (p << 32) ^ 0x8888888800000000)
    }
}

impl From<BitMatrix4> for BitPermTT4 {
    fn from(bm4: BitMatrix4) -> Self {
        let x = bm4.0 as u64;
        BitPermTT4(
            ((x & 0xf) * 0x1010101010101010)
            ^ ((x & 0xf0) * 0x0110011001100110)  // because &0xf0 not shifted down four bits
            ^ ((x & 0xf00) * 0x0011110000111100)
            ^ ((x & 0xf000) * 0x0001111111100000)
            )
    }
}

// impl From<BitPermPoly4> for BitPermTT4 {
    // fn from(bpp3: BitPermPoly3) -> Self {
        // let mut p = bpp3.0;
        // swap_mask_shift_u32(&mut p, 0xff00, 8);
        // swap_mask_shift_u32(&mut p, 0xaaaa, 15);
        // swap_mask_shift_u32(&mut p, 0xff00, 8);
        // swap_mask_shift_u32(&mut p, 0xcccc, 14);
        // swap_mask_shift_u32(&mut p, 0xff00, 8);
        // swap_mask_shift_u32(&mut p, 0xf0f0, 12);
        // BitPermTT3(p)
    // }
// }

impl fmt::Debug for BitPermTT4 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "BitPermTT4({:#018x})", self.0)
    } 
} 

// --------------------------------------------------------------------
// Bit Permutation over 4 bits represented as four polynomials in a u64
// --------------------------------------------------------------------

#[derive(PartialEq)]
pub struct BitPermPoly4(u64);

// --------------------------------------------------------------------
// Bit Matrix over 4 bits represented in a u16
// --------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq)]
pub struct BitMatrix4(u16);

impl BitMatrix4 {
    pub const ID:BitMatrix4 = BitMatrix4(0x8421);

    pub fn id() -> Self {
        BitMatrix4(0x8421)
    }

    pub fn reverse() -> Self {
        BitMatrix4(0x1248)
    }

    pub fn transpose(&self) -> Self {
        let mut x = self.0;
        x ^= (x & 0x00cc) << 6;
        x ^= (x & 0x3300) >> 6;
        x ^= (x & 0x00cc) << 6;
        x ^= (x & 0x0a0a) << 3;
        x ^= (x & 0x5050) >> 3;
        x ^= (x & 0x0a0a) << 3;
        BitMatrix4(x)
    }

    pub fn mul(&self, other: Self) -> Self {
        println!("{}", self);
        println!("{}", other);
        let x = self.0;
        let y = other.transpose().0;
        println!("{}", BitMatrix4(x));
        println!("{}", BitMatrix4(y));
        BitMatrix4(
            (0..4)
            .map(|ii| {
                let mut z = x & (((y >> (ii<<2)) & 0xf) * 0x1111);
                z ^= z >> 2;
                z ^= z >> 1;
                z &= 0x1111;
                z << ii
            })
            .sum()
            )
    }

    fn leadz(x:u32) -> u32 {
        for i in 0..32 {
            if (x >> i) & 1 == 1 { return i }
        }
        return 32
    }

    // TODO: Use bitintr and bitwise to clean up
    fn swap_row(mut x:u32, r0:u32, r1:u32) -> u32 {
        if r0 == r1 { return x};
        x ^= ((x.checked_shr(r0<<2).unwrap_or(0)) & 0xf000f).checked_shl(r1<<2).unwrap_or(0);
        x ^= ((x.checked_shr(r1<<2).unwrap_or(0)) & 0xf000f).checked_shl(r0<<2).unwrap_or(0);
        x ^= ((x.checked_shr(r0<<2).unwrap_or(0)) & 0xf000f).checked_shl(r1<<2).unwrap_or(0);
        // x ^= ((x >> (r1<<2)) & 0xf000f).checked_shl(r0<<2).unwrap_or(0);
        // x ^= ((x >> (r0<<2)) & 0xf000f).checked_shl(r1<<2).unwrap_or(0);
        // x ^= ((x >> (r1<<2)) & 0xf000f) << (r0<<2);
        // x ^= ((x >> (r0<<2)) & 0xf000f) << (r1<<2);
        x
    }

    /* This requires bitintr
    pub fn inverse(&self) -> Self {
        let mut x = self.0 as u32;
        x += 0x84210000;
        for i in 0..4 {
            // let pivot = Self::leadz((x>>i) & (0x1111 << (i<<2))) >> 2;
            let pivot = ((x>>i) & (0x1111 << (i<<2))).tzcnt() >> 2;
            x = Self::swap_row(x, i, pivot);
            let pivot_bit = ((x>>i) & (0x1111 << (i<<2))).blsi();
            x ^= ((x>>(i<<2)) & 0xf000f) * ((x>>i) & (0x1111-(1<<(i<<2))));
        }
        BitMatrix4((x >> 16) as u16)
        /*
        // println!("{}", BitMatrix4(x as u16)); // println!("{}", BitMatrix4((x>>16) as u16)); 
        let pivot = Self::leadz(x & 0x1111) >> 2;
        x = Self::swap_row(x, 0, pivot);
        x ^= (x & 0xf000f) * (x & 0x1110);
        // println!("{}", BitMatrix4(x as u16)); // println!("{}", BitMatrix4((x>>16) as u16)); 
        let pivot = Self::leadz((x>>1) & 0x1110) >> 2;
        x = Self::swap_row(x, 1, pivot);
        x ^= ((x>>4) & 0xf000f) * ((x>>1) & 0x1101);
        // println!("{}", BitMatrix4(x as u16)); // println!("{}", BitMatrix4((x>>16) as u16)); 
        let pivot = Self::leadz((x>>2) & 0x1100) >> 2;
        x = Self::swap_row(x, 2, pivot);
        x ^= ((x>>8) & 0xf000f) * ((x>>2) & 0x1011);
        // println!("{}", BitMatrix4(x as u16)); // println!("{}", BitMatrix4((x>>16) as u16)); 
        let pivot = Self::leadz((x>>2) & 0x1000) >> 2;
        x = Self::swap_row(x, 3, pivot);
        x ^= ((x>>12) & 0xf000f) * ((x>>3) & 0x0111);
        println!("{}", BitMatrix4(x as u16)); println!("{}", BitMatrix4((x>>16) as u16)); 
        // println!("{}", BitMatrix4(x as u16)); // println!("{}", BitMatrix4((x>>16) as u16)); 
        BitMatrix4((x >> 16) as u16)
        */
    }
    */

}

impl From<BitPermTT4> for BitMatrix4 {
    fn from(bptt4: BitPermTT4) -> Self {
        let x = bptt4.0 as u64;
        BitMatrix4((((x >> 4) & 0xff) ^ ((x >> 8) & 0xf00) ^ ((x >> 20) & 0xf000)) as u16)
    }
}

impl fmt::Debug for BitMatrix4 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "BitMatrix4({:#06x})", self.0)
    } 
} 

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_bit_perm_poly3_from_bit_perm_tt3() {
        assert_eq!(BitPermTT3::from(BitPermPoly3(0xf0ccaa)), BitPermTT3(0x76543210));
        assert_eq!(BitPermTT3::from(BitPermPoly3(0x786655)), BitPermTT3(0x07654321));
    }

    #[test]
    fn test_bit_perm_tt3_from_bit_perm_poly3() {
        assert_eq!(BitPermPoly3::from(BitPermTT3(0x76543210)), BitPermPoly3(0xf0ccaa));
        assert_eq!(BitPermPoly3::from(BitPermTT3(0x07654321)), BitPermPoly3(0x786655));
    }

    #[test]
    fn test_bit_perm_tt3_compose() {
        assert_eq!(BitPermTT3(0x76543210).compose(BitPermTT3(0x76543210)), BitPermTT3(0x76543210)); // Id * Id == Id
        assert_eq!(BitPermTT3::ID.compose(BitPermTT3::ID), BitPermTT3::ID); // Id * Id == Id
        assert_eq!(BitPermTT3(0x07654321).compose(BitPermTT3(0x07654321)), BitPermTT3(0x10765432)); // Two increments
    }
    
    #[test]
    fn test_bit_perm_tt4_compose() {
        assert_eq!(BitPermTT4::ID.compose(BitPermTT4::ID), BitPermTT4::ID); // id * id == id
        assert_eq!(BitPermTT4::increment().compose(BitPermTT4::increment()), BitPermTT4(0x10fedcba98765432)); // Two increments
        assert_eq!(BitPermTT4(0x0fedcba987654321).compose(BitPermTT4(0x0fedcba987654321)), BitPermTT4(0x10fedcba98765432)); // Two increments
    }

    #[test]
    fn test_bit_perm_tt4_from_bit_perm_tt3() {
        assert_eq!(BitPermTT4::from(BitPermTT3::ID), BitPermTT4::ID);
    }

    #[test]
    fn test_bit_perm_tt4_from_bitmatrix4() {
        assert_eq!(BitPermTT4::from(BitMatrix4::ID), BitPermTT4::ID);
    }

    #[test]
    fn test_bit_matrix4_transpose() {
        assert_eq!(BitMatrix4::ID.transpose(), BitMatrix4::ID);
        assert_eq!(BitMatrix4::reverse().transpose(), BitMatrix4::reverse());
        assert_eq!(BitMatrix4(0xf731).transpose(), BitMatrix4(0x8cef));
        assert_eq!(BitMatrix4(0x73e4).transpose(), BitMatrix4(0x2bec));
    }

    #[test]
    fn test_bit_matrix4_mul() {
        assert_eq!(BitMatrix4::ID.mul(BitMatrix4::ID), BitMatrix4::ID);
        assert_eq!(BitMatrix4::reverse().mul(BitMatrix4::reverse()), BitMatrix4::ID);
        assert_eq!(BitMatrix4(0x73e4).mul(BitMatrix4(0x2bec)), BitMatrix4(0x927b));
    }

    /* TODO: Tests require bitintr
    #[test]
    fn test_bit_perm_tt3_inverse() {
        assert_eq!(BitPermTT3::ID.inverse(), BitPermTT3::ID);  // id^-1 == id
    }

    #[test]
    fn test_bit_perm_tt4_inverse() {
        assert_eq!(BitPermTT4::ID.inverse(), BitPermTT4::ID);  // id^-1 == id
    }

    #[test]
    fn test_bit_matrix4_inverse() {
        assert_eq!(BitMatrix4(0x53e4).inverse(), BitMatrix4(0xe1d9));
        assert_eq!(BitMatrix4(0xe1d9).inverse(), BitMatrix4(0x53e4));
        assert_eq!(BitMatrix4(0x53e4).inverse().mul(BitMatrix4(0x53e4)), BitMatrix4::ID);
        assert_eq!(BitMatrix4::reverse().inverse(), BitMatrix4::reverse());
        assert_eq!(BitMatrix4::ID.inverse(), BitMatrix4::ID);
    }
    */
}
*/
