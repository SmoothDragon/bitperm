use std::fmt;
use std::ops::*;
use flowscad::*;

use crate::bitlib::{swap_mask_shift_u32, swap_mask_shift_u64};
use crate::bitcube4::*;

// use itertools::Itertools;

// -----------------------------------------------------------------
// 3x3x3 cube space represented by 27 bits of a u32
// -----------------------------------------------------------------
// Position at (x,y,z) = x + 3*y + 9*z
// Rotations will happen from the center of the cube

#[derive(Copy, Clone, PartialEq)]
pub struct BitCube3(pub u32);


impl From<u32> for BitCube3 {
    fn from(x: u32) -> BitCube3 {
        BitCube3(x)
    }
}

/// Embedding a BitCube4 into a BitCube3 by truncated the 4-cube indices
/// larger than 3. Does not check for lost bits.
impl From<BitCube4> for BitCube3 {
    fn from(bc4: BitCube4) -> BitCube3 {
        let mut x = bc4.0;
        // Shift the row start index from 0,4,8 to 0,3,6
        x = (x & 0x700070007) ^ ((x>>1) & 0x3800380038) ^ ((x>>2) & 0x01c001c001c0);
        // Shift the plane start index from 0,16,32 to 0,9,18
        x = (x & 0o777) ^ ((x>>7) & 0o777000) ^ ((x>>14) & 0o777000000);
        BitCube3(x as u32)
    }
}
impl Into<D3> for BitCube3 {
    fn into(self) -> D3 {
        let block = D3::cube(1.0);
        (0..27)
            .filter(|ii| (self.0 >> ii) & 1 == 1)
            .map(|ii| v3(ii % 3, (ii/3) % 3, ii / 9))
            .map(|xyz| block.clone().translate(xyz))
            .union()
            // .translate(v3(-1,-1,-1))
            .scale(10)
            .color(ColorEnum::Red)
    }
}



/// 3x3x3 layout of u32 0b00000qponmlkjihgfedcba9876543210
/// 678 | fgh | opq
/// 345 | cde | lmn
/// 012 | 9ab | ijk
impl BitCube3 {

    /// Count the number of cubes (ones) in the BitCube
    pub fn count_cubes(self) -> u32 {
        self.0.count_ones()
    }

    /// Easiest to visualize as a z-rotation, but same idea
    pub fn rotate_x(self) -> Self { 
        let mut cube = self.0;
        // Swap vertical
        swap_mask_shift_u32(&mut cube, 0o777_u32, 18);
        // Swap main diagonal
        swap_mask_shift_u32(&mut cube, 0o700_u32, 12);
        // Swap outer diagonals
        swap_mask_shift_u32(&mut cube, 0o700_070_u32, 6);
        BitCube3(cube)
    }

    /// Easiest to visualize as a z-rotation, but same idea
    pub fn rotate_y(self) -> Self { 
        let mut cube = self.0;
        // Swap vertical
        swap_mask_shift_u32(&mut cube, 0o777_u32, 18);
        // Swap main diagonal
        swap_mask_shift_u32(&mut cube, 0o444_u32, 16);
        // Swap outer diagonals
        swap_mask_shift_u32(&mut cube, 0o444_222_u32, 8);
        BitCube3(cube)
    }

    /// z-rotation done by two swaps
    /// abc      bc.
    /// ... then a.c
    /// abc      .ab
    pub fn rotate_z(self) -> Self { 
        let mut cube = self.0;
        // Swap vertical
        swap_mask_shift_u32(&mut cube, 0o007_007_007_u32, 6);
        // Swap main diagonal
        swap_mask_shift_u32(&mut cube, 0o004_004_004_u32, 4);
        // Swap outer diagonals
        swap_mask_shift_u32(&mut cube, 0o042_042_042_u32, 2);
        BitCube3(cube)
    }

    /// Rotate 120 degrees about the diagonal through the origin and center of the cube.
    /// TODO: Figure out a faster way than using BitCube4
    pub fn rotate_d(self) -> Self { 
        Self::from(BitCube4::from(self).rotate_d())
    }

    pub fn shift_x(self, shift: i8) -> Self { 
        match shift {
            0 => self,
            1 => Self((self.0.unbounded_shl(1)) & 0o666_666_666_u32),
            2 => Self((self.0.unbounded_shl(2)) & 0o444_444_444_u32),
            -1 => Self((self.0.unbounded_shl(1)) & 0o333_333_333_u32),
            -2 => Self((self.0.unbounded_shl(2)) & 0o111_111_111_u32),
            _ => Self(0)
        }
    }

    /// Return none if the x-shift would move part of the polycube past an edge.
    pub fn bounded_shift_x(self, shift: i8) -> Option<Self> { 
        let shifted = self.shift_x(shift);
        if self.count_cubes() == shifted.count_cubes() {
            Some(shifted)
        } else {
            None
        }
    }

    pub fn shift_y(self, shift: i8) -> Self { 
        match shift {
            0 => self,
            1 => Self((self.0.unbounded_shl(3)) & 0o770_770_770_u32),
            2 => Self((self.0.unbounded_shl(6)) & 0o700_700_700_u32),
            -1 => Self((self.0.unbounded_shr(3)) & 0o077_077_077_u32),
            -2 => Self((self.0.unbounded_shr(6)) & 0o007_007_007_u32),
            _ => Self(0)
        }
    }

    /// Return none if the y-shift would move part of the polycube past an edge.
    pub fn bounded_shift_y(self, shift: i8) -> Option<Self> { 
        let shifted = self.shift_y(shift);
        if self.count_cubes() == shifted.count_cubes() {
            Some(shifted)
        } else {
            None
        }
    }

    pub fn shift_z(self, shift: i8) -> Self { 
        match shift {
            0 => self,
            1 => Self((self.0.unbounded_shl(9)) & 0o777_777_000_u32),
            2 => Self((self.0.unbounded_shl(18)) & 0o777_000_000_u32),
            -1 => Self((self.0.unbounded_shr(9)) & 0o000_777_777_u32),
            -2 => Self((self.0.unbounded_shr(18)) & 0o000_000_777_u32),
            _ => Self(0)
        }
    }

    /// Return none if the z-shift would move part of the polycube past an edge.
    pub fn bounded_shift_z(self, shift: i8) -> Option<Self> { 
        let shifted = self.shift_z(shift);
        if self.count_cubes() == shifted.count_cubes() {
            Some(shifted)
        } else {
            None
        }
    }

    /*
    /// Given a piece in the 4-cube, shift it towards the origin so that it touches the x, y, and z
    /// planes
    pub fn shift_to_origin(self) -> Self {
        let mut shape = self.0;
        let z_shift = (shape.trailing_zeros() / 16) * 16;
        shape = shape.unbounded_shr(z_shift);
        let xy_proj = shape | shape.unbounded_shr(32);
        let xy_proj = xy_proj | xy_proj.unbounded_shr(16);
        let y_shift = (xy_proj.trailing_zeros() / 4) * 4;
        shape = shape.unbounded_shr(y_shift);
        let x_shift = xy_proj | xy_proj.unbounded_shr(8);
        let x_shift = x_shift | x_shift.unbounded_shr(4);
        shape = shape.unbounded_shr(x_shift.trailing_zeros());
        Self(shape)
    }
    */

    pub fn overlap(self, other: Self) -> bool {
        self.0 & other.0 != 0
    }
}


impl BitOr for BitCube3 {
    type Output = Self;

    fn bitor(self, other: Self) -> Self::Output {
        Self(self.0 | other.0)
    }
}

impl BitAnd for BitCube3 {
    type Output = Self;

    fn bitand(self, other: Self) -> Self::Output {
        Self(self.0 & other.0)
    }
}

impl Shl<u32> for BitCube3 {
    type Output = Self;

    fn shl(self, rhs: u32) -> Self::Output {
        Self(self.0.unbounded_shl(rhs))
    }
}

impl Shr<u32> for BitCube3 {
    type Output = Self;

    fn shr(self, rhs: u32) -> Self::Output {
        Self(self.0.unbounded_shr(rhs))
    }
}

impl fmt::Debug for BitCube3 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "BitCube3({:#011o})\n{:}", self.0, self)
    } 
} 

impl fmt::Display for BitCube3 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}",
            (0..3)
            .map(|x| { let x = self.0 >> (3 * (2-x));
                (0..3)
                .map(|y| format!("{:03b}", (x >> (9*y)) & 0x7))
                .map(|s| s.chars().rev().collect())
                .collect::<Vec<String>>()
                .join(" ")
            })
            .collect::<Vec<String>>()
            .join("\n")
            )
    } 
} 

#[cfg(test)]
mod test {
    use super::*;
    use crate::cu27;
    use crate::bitcube4::BitCube4;

    #[test]
    fn test_debug() {
        assert_eq!(format!("{:?}", cu27::ORDER),
          "BitCube3(0o076543210)\n010 101 000\n100 001 111\n000 110 011"
        );
    }

    #[test]
    fn test_display() {
        assert_eq!(format!("{:}", cu27::ORDER),
            "010 101 000\n100 001 111\n000 110 011"
        );
    }

    #[test]
    fn test_bitor() {
        assert_eq!(cu27::FULL | cu27::FULL, cu27::FULL);
        assert_eq!(cu27::CENTER_X | cu27::CENTER_Y | cu27::CENTER_Z, cu27::CENTER_ALL);
    }

    #[test]
    fn test_bitand() {
        assert_eq!(cu27::FULL & cu27::FULL, cu27::FULL);
        assert_eq!(cu27::CENTER_X & cu27::CENTER_Y & cu27::CENTER_Z, BitCube3(0o020_000_u32));
    }

    #[test]
    fn test_shift_x() {
        assert_eq!(cu27::FULL.shift_x(1), BitCube3(0o666_666_666_u32));
        assert_eq!(cu27::FULL.shift_x(2), BitCube3(0o444_444_444_u32));
    }

    #[test]
    fn test_bounded_shift_x() {
        assert_eq!(cu27::FULL.bounded_shift_x(1), None);
        assert_eq!(cu27::CENTER_X.bounded_shift_x(1), None);
        assert_eq!(cu27::CENTER_Y.bounded_shift_x(1), Some(BitCube3(0o444000)));
        assert_eq!(cu27::CENTER_Z.bounded_shift_x(1), Some(BitCube3(0o040040040)));
        assert_eq!(cu27::CENTER_Y << 1, BitCube3(0o444000));
        assert_eq!(cu27::CENTER_Z << 1, BitCube3(0o040040040));
    }

    #[test]
    fn test_shift_y() {
        assert_eq!(cu27::FULL.shift_y(1), BitCube3(0o770_770_770_u32));
        assert_eq!(cu27::FULL.shift_y(-2), BitCube3(0o007_007_007_u32));
        assert_eq!(cu27::CENTER_Z >> 3, BitCube3(0o002002002));
    }

    #[test]
    fn test_bounded_shift_y() {
        assert_eq!(cu27::FULL.bounded_shift_y(1), None);
        assert_eq!(cu27::CENTER_X.bounded_shift_y(1), Some(BitCube3(0o700000)));
        assert_eq!(cu27::CENTER_Y.bounded_shift_y(1), None);
        assert_eq!(cu27::CENTER_Z.bounded_shift_y(1), Some(BitCube3(0o200200200)));
    }

    #[test]
    fn test_shift_z() {
        assert_eq!(cu27::FULL.shift_z(1), BitCube3(0o777_777_000_u32));
        assert_eq!(cu27::FULL.shift_z(-2), BitCube3(0o000_000_777_u32));
    }

    #[test]
    fn test_bounded_shift_z() {
        assert_eq!(cu27::FULL.bounded_shift_z(1), None);
        assert_eq!(cu27::CENTER_X.bounded_shift_z(1), Some(BitCube3(0o070000000)));
        assert_eq!(cu27::CENTER_Y.bounded_shift_z(1), Some(BitCube3(0o222000000)));
        assert_eq!(cu27::CENTER_Z.bounded_shift_z(1), None);
    }

    // #[test]
    // fn test_shift_to_origin() {
        // assert_eq!(cu27::FULL.shift_to_origin(), cu27::FULL);
        // assert_eq!((cu27::CENTER_X | cu27::CENTER_Y).shift_to_origin(), BitCube4(0x0000_0000_6ff6_6ff6));
    // }

    #[test]
    fn test_rotate_x() {
        assert_eq!(cu27::FULL.rotate_x(), cu27::FULL);
        assert_eq!(cu27::CENTER.rotate_x(), cu27::CENTER);
        assert_eq!(cu27::CENTER_X.rotate_x(), cu27::CENTER_X);
        assert_eq!(cu27::CENTER_Y.rotate_x(), cu27::CENTER_Z);
        assert_eq!(cu27::CENTER_Z.rotate_x(), cu27::CENTER_Y);
        assert_eq!(BitCube3(0o7).rotate_x(), BitCube3(0o700));
        assert_eq!(BitCube3(0o4017).rotate_x(), BitCube3(0o100740));
    }

    #[test]
    fn test_rotate_y() {
        assert_eq!(cu27::FULL.rotate_y(), cu27::FULL);
        assert_eq!(cu27::CENTER.rotate_y(), cu27::CENTER);
        assert_eq!(cu27::CENTER_X.rotate_y(), cu27::CENTER_Z);
        assert_eq!(cu27::CENTER_Y.rotate_y(), cu27::CENTER_Y);
        assert_eq!(cu27::CENTER_Z.rotate_y(), cu27::CENTER_X);
        assert_eq!(BitCube3(0o7).rotate_y(), BitCube3(0o4004004));
        assert_eq!(BitCube3(0o4017).rotate_y(), BitCube3(0o6004044));
    }

    #[test]
    fn test_rotate_z() {
        assert_eq!(cu27::FULL.rotate_z(), cu27::FULL);
        assert_eq!(cu27::CENTER.rotate_z(), cu27::CENTER);
        assert_eq!(cu27::CENTER_X.rotate_z(), cu27::CENTER_Y);
        assert_eq!(cu27::CENTER_Y.rotate_z(), cu27::CENTER_X);
        assert_eq!(cu27::CENTER_Z.rotate_z(), cu27::CENTER_Z);
        assert_eq!(BitCube3(0o7).rotate_z(), BitCube3(0o444));
        assert_eq!(BitCube3(0o4017).rotate_z(), BitCube3(0o400446));
    }

    #[test]
    fn test_rotate_d() {
        assert_eq!(cu27::FULL.rotate_d(), cu27::FULL);
        assert_eq!(cu27::CENTER_X.rotate_d(), cu27::CENTER_Y);
        assert_eq!(cu27::CENTER_Y.rotate_d(), cu27::CENTER_Z);
        assert_eq!(cu27::CENTER_Z.rotate_d(), cu27::CENTER_X);
        assert_eq!(BitCube3(0o1047).rotate_d(), BitCube3(0o100113));
    }

    #[test]
    fn test_overlap() {
        assert!(cu27::CENTER_X.overlap(cu27::CENTER_Y));
    }

    #[test]
    fn test_from_bitperm4() {
        assert_eq!(BitCube3::from(BitCube4(0x77707770777)), BitCube3(0o777777777));
        assert_eq!(BitCube3::from(BitCube4(0x70000000000)), BitCube3(0o700000000));
        assert_eq!(BitCube3::from(BitCube4(0x7605430210)), BitCube3(0o76543210));
    }
}
