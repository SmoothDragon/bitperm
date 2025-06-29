use std::fmt;
// use std::ops::*;
use std::collections::HashMap;

use crate::bitgrid8::BitGrid8;

use derive_more::*;
use arrayvec::*;

use crate::bitlib::swap_mask_shift_u64;

// -----------------------------------------------------------------
// 2D geometric operations on an hexagonal grid in a parallelogram
// with side length 8.
//
// 8x8 square space represented by the 64 bits in a u64
// Position at (x,y) = x + 8*y
// The low bit corresponds to the lower left most position.
// The high bit corresponds to the upper right most position.
//
// Rotations will happen from the center of the hexagon.
// -----------------------------------------------------------------
//
// 77777777    7 7 7 7 7 7 7 7
// 66666666     6 6 6 6 6 6 6 6
// 55555555      5 5 5 5 5 5 5 5
// 44444444       4 4 4 4 4 4 4 4
// 33333333   =>   3 3 3 3 3 3 3 3
// 22222222         2 2 2 2 2 2 2 2
// 11111111          1 1 1 1 1 1 1 1
// 00000000           0 0 0 0 0 0 0 0
//
// -----------------------------------------------------------------


// TODO: It seems like we would shift the border box over the designated square in all possible
// ways. For each of these ways, test that the piece in the box overlaps, that the shift is valid,
// that it doesn't overlap with the filled portion.

#[derive(Copy, Clone, Eq, PartialEq, Hash, PartialOrd, Ord,
    BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, 
    )]
pub struct BitPara8(pub u64);

impl fmt::Debug for BitPara8 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "BitGrid8({:#010x})", self.0)
    } 
} 

impl fmt::Display for BitPara8 {
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

pub const HEX4: BitPara8 = BitPara8(0x78_7c7e_7f3f_1f0f);
pub const FULL: BitPara8 = BitPara8(0xffff_ffff_ffff_ffff);
pub const ASTERISK: BitPara8 = BitPara8(0x4828187f0c0a09);
pub const THREE_HEX: BitPara8 = BitPara8(0x6c7e360c0e06);
pub const LARGE_X: BitPara8 = BitPara8(0x8142_2418_1824_4281);
pub const LARGE_Z: BitPara8 = BitPara8(0xff40_2010_0804_02ff);
pub const SLASH: BitPara8 = BitPara8(0x8040_2010_0804_0201);

impl BitPara8 {
    /// Do two BitPara8 objects overlap?
    pub fn has_overlap(self, other: Self) -> bool {
        self.0 & other.0 != 0
    }

    /// Does the BitPara8 contain nothing?
    #[inline(always)]
    pub fn is_empty(self) -> bool {
        self.0 == 0
    }

    /// Produce all rotations of a BitGrid
    /// Prefer a gray code path through all rotations
    pub fn rotate_all_vec(self) -> ArrayVec::<Self, 4> {
        let mut vec = ArrayVec::<Self, 4>::new();
        let mut x = self;
        vec.push(x);
        for _ in 0..2 { x = x.rotate_180(); vec.push(x); }
        vec.sort_unstable();
        let symmetries = vec.partition_dedup().0.len();  // Move duplicates to the end.
        vec.truncate(symmetries);
        vec
    }

    /// Rotate 180 degrees
    #[inline]
    pub fn rotate_180(self) -> Self { 
        // let mut grid: u64 = BitGrid8(self.0).rotate_180().0.unbounded_shr(4);
        let mut grid: u64 = self.0;
        // Swap 4x4 squares
        swap_mask_shift_u64(&mut grid, 0x0f0f_0f0f, 36);
        swap_mask_shift_u64(&mut grid, 0xf0f0_f0f0, 28);
        // Swap 2x2 squares
        swap_mask_shift_u64(&mut grid, 0x0000_3333_0000_3333, 18);
        swap_mask_shift_u64(&mut grid, 0x0000_cccc_0000_cccc, 14);
        // Swap 1x1 squares
        swap_mask_shift_u64(&mut grid, 0x0055_0055_0055_0055, 9);
        swap_mask_shift_u64(&mut grid, 0x00aa_00aa_00aa_00aa, 7);
        Self(grid)
    }

    // Flip along x-axis. For 2D this is the same as mirror.
    pub fn flip_x(self) -> Self { 
        let mut grid = self.0;
        swap_mask_shift_u64(&mut grid, 0xffff_ffff, 32);
        swap_mask_shift_u64(&mut grid, 0xffff_0000_ffff, 16);
        swap_mask_shift_u64(&mut grid, 0x00ff_00ff_00ff_00ff, 8);
        Self(grid)
    }

    // Flip along (1, 1) vector.
    pub fn flip_ne(self) -> Self { 
        let mut grid = self.0;
        // Swap 4x4 squares
        swap_mask_shift_u64(&mut grid, 0x0f0f_0f0f, 36);
        // Swap 2x2 squares
        swap_mask_shift_u64(&mut grid, 0x0000_3333_0000_3333, 18);
        // Swap 1x1 squares
        swap_mask_shift_u64(&mut grid, 0x0055_0055_0055_0055, 9);
        Self(grid)
    }

    // Flip along (-1, 1) vector.
    pub fn flip_nw(self) -> Self { 
        let mut grid = self.0;
        // Swap 4x4 squares
        swap_mask_shift_u64(&mut grid, 0xf0f0_f0f0, 28);
        // Swap 2x2 squares
        swap_mask_shift_u64(&mut grid, 0x0000_cccc_0000_cccc, 14);
        // Swap 1x1 squares
        swap_mask_shift_u64(&mut grid, 0x00aa_00aa_00aa_00aa, 7);
        Self(grid)
    }

    /*
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

    /// Find the (x,y) bounding box of a BitPara8.
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
    */
}


#[cfg(test)]
mod test {
    use super::*;
    
    #[test]
    fn test_bithex8_display() {
        println!("{}", FULL);
        assert_eq!(format!("{}", FULL),
        "🟥🟥🟥🟥🟥🟥🟥🟥\n🟥🟥🟥🟥🟥🟥🟥🟥\n🟥🟥🟥🟥🟥🟥🟥🟥\n🟥🟥🟥🟥🟥🟥🟥🟥\n🟥🟥🟥🟥🟥🟥🟥🟥\n🟥🟥🟥🟥🟥🟥🟥🟥\n🟥🟥🟥🟥🟥🟥🟥🟥\n🟥🟥🟥🟥🟥🟥🟥🟥\n");
        assert_eq!(format!("{}", BitPara8(0x1)), 
            "⬜⬜⬜⬜⬜⬜⬜⬜\n⬜⬜⬜⬜⬜⬜⬜⬜\n⬜⬜⬜⬜⬜⬜⬜⬜\n⬜⬜⬜⬜⬜⬜⬜⬜\n⬜⬜⬜⬜⬜⬜⬜⬜\n⬜⬜⬜⬜⬜⬜⬜⬜\n⬜⬜⬜⬜⬜⬜⬜⬜\n🟥⬜⬜⬜⬜⬜⬜⬜\n");
    }

    #[test]
    fn test_bitpara_rotate_180() {
        // Has 2-fold rotational symmetry
        assert_eq!(FULL, FULL.rotate_180());
        println!("{}", LARGE_Z);
        assert_eq!(LARGE_Z, LARGE_Z.rotate_180());

        // Must rotate twice
        assert_ne!(ASTERISK, ASTERISK.rotate_180());
        assert_eq!(ASTERISK, ASTERISK.rotate_180().rotate_180());
    }

    #[test]
    fn test_bitpara_flip_x() {
        assert_eq!(FULL, FULL.flip_x());
        assert_eq!(LARGE_X, LARGE_X.flip_x());

        // Must flip twice
        assert_ne!(ASTERISK, ASTERISK.flip_x());
        assert_eq!(ASTERISK, ASTERISK.flip_x().flip_x());
        assert_ne!(THREE_HEX, THREE_HEX.flip_x());
        assert_eq!(THREE_HEX, THREE_HEX.flip_x().flip_x());
        assert_ne!(SLASH, SLASH.flip_x());
        assert_eq!(SLASH, SLASH.flip_x().flip_x());

    }

    #[test]
    fn test_bitpara_flip_ne() {
        assert_eq!(FULL, FULL.flip_ne());
        assert_eq!(LARGE_X, LARGE_X.flip_ne());
        assert_eq!(SLASH, SLASH.flip_ne());

        // Must flip twice
        assert_ne!(ASTERISK, ASTERISK.flip_ne());
        assert_eq!(ASTERISK, ASTERISK.flip_ne().flip_ne());
        assert_ne!(THREE_HEX, THREE_HEX.flip_ne());
        assert_eq!(THREE_HEX, THREE_HEX.flip_ne().flip_ne());
    }

    #[test]
    fn test_bitpara_flip_nw() {
        assert_eq!(FULL, FULL.flip_nw());
        assert_eq!(LARGE_X, LARGE_X.flip_nw());
        assert_eq!(SLASH, SLASH.flip_nw());
        assert_eq!(ASTERISK, ASTERISK.flip_nw());

        // Must flip twice
        assert_ne!(LARGE_Z, LARGE_Z.flip_nw());
        assert_eq!(LARGE_Z, LARGE_Z.flip_nw().flip_nw());
        assert_ne!(THREE_HEX, THREE_HEX.flip_nw());
        assert_eq!(THREE_HEX, THREE_HEX.flip_nw().flip_nw());
    }

}
