use std::fmt;
use std::ops::*;

use derive_more::*;

use flowscad::*;

use crate::bitlib::swap_mask_shift_u64;
use crate::bitcube3::BitCube3;

// use itertools::Itertools;

// -----------------------------------------------------------------
// 4x4x4 cube space represented by the 64 bits in a u64
// -----------------------------------------------------------------
// Position at (x,y,z) = x + 4*y + 16*z
// Rotations will happen from the center of the cube

#[derive(Copy, Clone, PartialEq, 
    BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, 
    )]
pub struct BitCube4(pub u64);


impl From<u64> for BitCube4 {
    fn from(x: u64) -> BitCube4 {
        BitCube4(x)
    }
}

/// Embedding a BitCube3 into a BitCube4 requires moving the three 3x3
/// planes into the first three 4x4 planes, while adding a bit to extend
/// the row length from 3 to 4.
impl From<BitCube3> for BitCube4 {
    fn from(bc3: BitCube3) -> BitCube4 {
        let mut x = bc3.0 as u64;
        // Shift the plane start index from 0,9,18 to 0,16,32
        x = (x & 0o777) ^ ((x & 0o777000) << 7) ^ ((x & 0o777000000) << 14);
        // Shift the row start index from 0,3,6 to 0,4,8
        x = (x & 0x700070007) ^ ((x & 0x3800380038) << 1) ^ ((x & 0x01c001c001c0) << 2);
        BitCube4(x)
    }
}

impl Into<u64> for BitCube4 {
    fn into(self) -> u64 {
        self.0
    }
}

impl Into<D3> for BitCube4 {
    fn into(self) -> D3 {
        let block = D3::cube(1.0);
        (0..64)
            .filter(|ii| (self.0 >> ii) & 1 == 1)
            .map(|ii| v3(ii&0x3, (ii>>2)&0x3, ii>>4))
            .map(|xyz| block.clone().translate(xyz))
            .union()
            .translate(v3(-2,-2,-2))
            .scale(10)
            .color(ColorEnum::Red)
    }
}



impl BitCube4 {
    /// Count the number of cubes (ones) in the BitCube
    pub fn count_cubes(self) -> u32 {
        self.0.count_ones()
    }

    // 1100
    // 0100
    // 1000
    // 0000
    /// 2x2x2 Example: 01 23 | 45 67 => 45 01 | 67 23 
    pub fn rotate_x(self) -> Self { 
        let mut cube = self.0;
        // Swap 2x2 blocks front <-> back
        swap_mask_shift_u64(&mut cube, 0x00ff_00ff_00ff_00ff_u64, 8);
        // Swap diagonal 2x2 blocks
        swap_mask_shift_u64(&mut cube, 0x0000_0000_00ff_00ff_u64, 40);
        // Within 2x2 blocks swap front <-> back
        swap_mask_shift_u64(&mut cube, 0x0f0f_0f0f_0f0f_0f0f_u64, 4);
        // Within 2x2 blocks swap diagonal entries
        swap_mask_shift_u64(&mut cube, 0x0000_0f0f_0000_0f0f_u64, 20);
        BitCube4(cube)
    }

    /// 2x2x2 Example: 01 23 | 45 67 => 15 37 | 04 26 
    /// 2x2x2 Example: 01 23 | 45 67 => 45 67 | 01 23
    pub fn rotate_y(self) -> Self { 
        let mut cube = self.0;
        // Swap 2x2 blocks up <-> down
        swap_mask_shift_u64(&mut cube, 0x0000_0000_ffff_ffff_u64, 32);
        // Swap diagonal 2x2 blocks
        swap_mask_shift_u64(&mut cube, 0x0000_0000_3333_3333_u64, 34);
        // Within 2x2 blocks swap up <-> down
        swap_mask_shift_u64(&mut cube, 0x0000_ffff_0000_ffff_u64, 16);
        // Within 2x2 blocks swap diagonal entries
        swap_mask_shift_u64(&mut cube, 0x0000_5555_0000_5555_u64, 17);
        BitCube4(cube)
    }

    /// 2x2x2 Example: 01 23 | 45 67 => 20 31 | 64 75 
    /// The z-rotation is the easiest to understand since the rotation happens in the xy-plane and
    /// is copied in the other dimension.
    /// 23 32 31
    /// 01 10 20
    pub fn rotate_z(self) -> Self { 
        let mut cube = self.0;
        // Swap 2x2 squares left <-> right
        swap_mask_shift_u64(&mut cube, 0x3333_3333_3333_3333_u64, 2);
        // Swap diagonal 2x2 squares
        swap_mask_shift_u64(&mut cube, 0x0033_0033_0033_0033_u64, 10);
        // Within 2x2 squares swap left <-> right columns
        swap_mask_shift_u64(&mut cube, 0x5555_5555_5555_5555_u64, 1);
        // Within 2x2 squares swap diagonal entries
        swap_mask_shift_u64(&mut cube, 0x0505_0505_0505_0505_u64, 5);
        BitCube4(cube)
    }

    /// Rotate 120 degrees about the diagonal through the origin and center of the cube.
    /// 2x2x2 Example: 01 23 | 45 67 => 04 15 | 26 37 
    /// Use two position involutions: 2 <-> 4 and 3 <-> 5, then 1 <-> 2 and 5 <-> 6.
    /// For the 4-cube, rotate the position of all the 2-cubes, 
    /// then rotate all the 2-cubes in place.
    pub fn rotate_d(self) -> Self { 
        let mut cube = self.0;
        // Swap sub-cubes 2 <-> 4 and 3 <-> 5
        swap_mask_shift_u64(&mut cube, 0x0000_0000_ff00_ff00_u64, 24);
        // Swap sub-cubes 1 <-> 2 and 5 <-> 6
        swap_mask_shift_u64(&mut cube, 0x00cc_00cc_00cc_00cc_u64, 6);
        // Swap 2 <-> 4 and 3 <-> 5 in each sub-cube
        swap_mask_shift_u64(&mut cube, 0x0000_f0f0_0000_f0f0_u64, 12);
        // Swap 1 <-> 2 and 5 <-> 6 in each sub-cube
        swap_mask_shift_u64(&mut cube, 0x0a0a_0a0a_0a0a_0a0a_u64, 3);
        BitCube4(cube)
    }

    pub fn shift_x(self, shift: i8) -> Self { 
        match shift {
            0 => self,
            1 => (self << 1) & 0xeeee_eeee_eeee_eeee_u64,
            2 => Self((self.0.unbounded_shl(2)) & 0xdddd_dddd_dddd_dddd_u64),
            3 => Self((self.0.unbounded_shl(3)) & 0x8888_8888_8888_8888_u64),
            -1 => Self((self.0.unbounded_shr(1)) & 0x7777_7777_7777_7777_u64),
            -2 => Self((self.0.unbounded_shr(2)) & 0x3333_3333_3333_3333_u64),
            -3 => Self((self.0.unbounded_shr(3)) & 0x1111_1111_1111_1111_u64),
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
            1 => Self((self.0 << 4) & 0xfff0_fff0_fff0_fff0_u64),
            2 => Self((self.0 << 8) & 0xff00_ff00_ff00_ff00_u64),
            3 => Self((self.0 << 12) & 0xf000_f000_f000_f000_u64),
            -1 => Self((self.0 >> 4) & 0x0fff_0fff_0fff_0fff_u64),
            -2 => Self((self.0 >> 8) & 0x00ff_00ff_00ff_00ff_u64),
            -3 => Self((self.0 >> 12) & 0x000f_000f_000f_000f_u64),
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
            1 => Self((self.0 << 16) & 0xffff_ffff_ffff_0000_u64),
            2 => Self((self.0 << 32) & 0xffff_ffff_0000_0000_u64),
            3 => Self((self.0 << 48) & 0xffff_0000_0000_0000_u64),
            -1 => Self((self.0 >> 16) & 0x0000_ffff_ffff_ffff_u64),
            -2 => Self((self.0 >> 32) & 0x0000_0000_ffff_ffff_u64),
            -3 => Self((self.0 >> 48) & 0x0000_0000_0000_ffff_u64),
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

    pub fn overlap(self, other: Self) -> bool {
        self.0 & other.0 != 0
    }
}

/*
impl BitOr for BitCube4 {
    type Output = Self;

    fn bitor(self, other: Self) -> Self::Output {
        Self(self.0 | other.0)
    }
}

impl BitOrAssign for BitCube4 {
    // rhs is the "right-hand side" of the expression `a |= b`
    fn bitor_assign(&mut self, rhs: Self) {
        *self = Self(self.0 | rhs.0)
    }
}


impl BitAnd for BitCube4 {
    type Output = Self;

    fn bitand(self, other: Self) -> Self::Output {
        Self(self.0 & other.0)
    }
}

impl BitAndAssign for BitCube4 {
    // rhs is the "right-hand side" of the expression `a &= b`
    fn bitand_assign(&mut self, rhs: Self) {
        *self = Self(self.0 & rhs.0)
    }
}
*/

impl BitAnd<u64> for BitCube4 {
    type Output = Self;

    fn bitand(self, rhs: u64) -> Self::Output {
        Self(self.0 & rhs)
    }
}

impl Shl<u32> for BitCube4 {
    type Output = Self;

    fn shl(self, rhs: u32) -> Self::Output {
        Self(self.0.unbounded_shl(rhs))
    }
}

impl Shr<u32> for BitCube4 {
    type Output = Self;

    fn shr(self, rhs: u32) -> Self::Output {
        Self(self.0.unbounded_shr(rhs))
    }
}

impl fmt::Debug for BitCube4 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "BitCube4({:#018x})\n{:}", self.0, self)
    } 
} 

impl fmt::Display for BitCube4 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}",
            (0..4)
            .map(|x| { let x = self.0 >> (4 * (3-x));
                (0..4)
                .map(|y| format!("{:04b}", (x >> (16*y)) & 0xf))
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
    use crate::cu64;


    #[test]
    fn test_debug() {
        assert_eq!(format!("{:?}", cu64::ORDER),
            "BitCube4(0xfedcba9876543210)\n1100 1110 1101 1111\n0100 0110 0101 0111\n1000 1010 1001 1011\n0000 0010 0001 0011"
        );

    }

    #[test]
    fn test_display() {
        assert_eq!(format!("{:}", cu64::ORDER),
            "1100 1110 1101 1111\n0100 0110 0101 0111\n1000 1010 1001 1011\n0000 0010 0001 0011"
        );

    }

    #[test]
    fn test_bitor() {
        assert_eq!(cu64::FULL | cu64::FULL, cu64::FULL);
        assert_eq!(cu64::ALL | cu64::ALL, cu64::ALL);
        assert_eq!(cu64::CENTER_X | cu64::CENTER_Y | cu64::CENTER_Z, cu64::CENTER_ALL);
    }

    #[test]
    fn test_shift_x() {
        assert_eq!(cu64::FULL.shift_x(1), 
                   BitCube4(0xeeee_eeee_eeee_eeee_u64)
                   );
    }

    #[test]
    fn test_shift_y() {
        assert_eq!(cu64::FULL.shift_y(1), 
                   BitCube4(0xfff0_fff0_fff0_fff0_u64)
                   );
    }

    #[test]
    fn test_shift_z() {
        assert_eq!(cu64::FULL.shift_z(1), 
                   BitCube4(0xffff_ffff_ffff_0000_u64)
                   );
    }

    #[test]
    fn test_bounded_shift_x() {
        assert_eq!(cu64::FULL.bounded_shift_x(1), None);
        assert_eq!(cu64::CENTER_X.bounded_shift_x(1), None);
        assert_eq!(cu64::CENTER_Y.bounded_shift_x(1), Some(BitCube4(0x0000cccccccc0000)));
        assert_eq!(cu64::CENTER_Z.bounded_shift_x(1), Some(BitCube4(0x0cc00cc00cc00cc0)));
    }

    #[test]
    fn test_bounded_shift_y() {
        assert_eq!(cu64::FULL.bounded_shift_y(1), None);
        assert_eq!(cu64::CENTER_X.bounded_shift_y(1), Some(BitCube4(0x0000ff00ff000000)));
        assert_eq!(cu64::CENTER_Y.bounded_shift_y(1), None);
        assert_eq!(cu64::CENTER_Z.bounded_shift_y(1), Some(BitCube4(0x6600660066006600)));
    }

    #[test]
    fn test_bounded_shift_z() {
        assert_eq!(cu64::FULL.bounded_shift_z(1), None);
        assert_eq!(cu64::CENTER_X.bounded_shift_z(1), Some(BitCube4(0x0ff00ff000000000)));
        assert_eq!(cu64::CENTER_Y.bounded_shift_z(1), Some(BitCube4(0x6666666600000000)));
        assert_eq!(cu64::CENTER_Z.bounded_shift_z(1), None);
    }

    #[test]
    fn test_shift_to_origin() {
        assert_eq!(cu64::FULL.shift_to_origin(), cu64::FULL);
        assert_eq!((cu64::CENTER_X | cu64::CENTER_Y).shift_to_origin(), BitCube4(0x0000_0000_6ff6_6ff6));
    }

    #[test]
    fn test_rotate_x() {
        assert_eq!(cu64::FULL.rotate_x(), cu64::FULL);
        assert_eq!(cu64::CENTER_X.rotate_x(), cu64::CENTER_X);
        assert_eq!(cu64::CENTER_Y.rotate_x(), cu64::CENTER_Z);
        assert_eq!(cu64::CENTER_Z.rotate_x(), cu64::CENTER_Y);
        assert_eq!(BitCube4(0xf).rotate_x(), BitCube4(0xf000));
        assert_eq!(BitCube4(0xf000).rotate_x(), BitCube4(0xf000000000000000));
    }

    #[test]
    fn test_rotate_y() {
        assert_eq!(cu64::FULL.rotate_y(), cu64::FULL);
        assert_eq!(cu64::UPPER_RIGHT_2X4X2.rotate_y(), cu64::LOWER_RIGHT_2X4X2);
        assert_eq!(cu64::LOWER_RIGHT_2X4X2.rotate_y(), cu64::LOWER_LEFT_2X4X2);
        assert_eq!(cu64::CENTER_X.rotate_y(), cu64::CENTER_Z);
        assert_eq!(cu64::CENTER_Y.rotate_y(), cu64::CENTER_Y);
        assert_eq!(cu64::CENTER_Z.rotate_y(), cu64::CENTER_X);
        assert_eq!(BitCube4(0xf).rotate_y(), BitCube4(0x0001000100010001));
    }

    #[test]
    fn test_rotate_z() {
        assert_eq!(cu64::FULL.rotate_z(), cu64::FULL);
        assert_eq!(cu64::CENTER_X.rotate_z(), cu64::CENTER_Y);
        assert_eq!(cu64::CENTER_Y.rotate_z(), cu64::CENTER_X);
        assert_eq!(cu64::CENTER_Z.rotate_z(), cu64::CENTER_Z);
        assert_eq!(BitCube4(0xf).rotate_z(), BitCube4(0x8888));
    }

    #[test]
    fn test_rotate_d() {
        assert_eq!(cu64::FULL.rotate_d(), cu64::FULL);
        assert_eq!(cu64::SUBCUBE_0.rotate_d(), cu64::SUBCUBE_0);
        assert_eq!(cu64::SUBCUBE_1.rotate_d(), cu64::SUBCUBE_2);
        assert_eq!(cu64::SUBCUBE_2.rotate_d(), cu64::SUBCUBE_4);
        assert_eq!(cu64::SUBCUBE_4.rotate_d(), cu64::SUBCUBE_1);
        assert_eq!(cu64::SUBCUBE_3.rotate_d(), cu64::SUBCUBE_6);
        assert_eq!(cu64::SUBCUBE_6.rotate_d(), cu64::SUBCUBE_5);
        assert_eq!(cu64::SUBCUBE_5.rotate_d(), cu64::SUBCUBE_3);
        assert_eq!(cu64::SUBCUBE_7.rotate_d(), cu64::SUBCUBE_7);
        assert_eq!(cu64::CENTER_X.rotate_d(), cu64::CENTER_Y);
        assert_eq!(cu64::CENTER_Y.rotate_d(), cu64::CENTER_Z);
        assert_eq!(cu64::CENTER_Z.rotate_d(), cu64::CENTER_X);
        assert_eq!(BitCube4(0x1011f).rotate_d(), BitCube4(0x0000000100011113));
    }

    #[test]
    fn test_overlap() {
        assert!(cu64::CENTER_X.overlap(cu64::CENTER_Y));
    }

    #[test]
    fn test_from_bitperm3() {
        assert_eq!(BitCube4::from(BitCube3(0o777777777)), BitCube4(0x77707770777));
        assert_eq!(BitCube4::from(BitCube3(0o700000000)), BitCube4(0x70000000000));
        assert_eq!(BitCube4::from(BitCube3(0o76543210)), BitCube4(0x7605430210));

    }

}
