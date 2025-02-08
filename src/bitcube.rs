use std::fmt;
use std::ops::*;

// use itertools::Itertools;

// -----------------------------------------------------------------
// 4x4x4 cube space represented by the 64 bits in a u64
// -----------------------------------------------------------------
// Position at (x,y,z) = x + 4*y + 16*z
// Rotations will happen from the center of the cube

#[derive(Copy, Clone, PartialEq)]
pub struct BitCube4(u64);

#[inline]  // TODO: Make this general for all u16, u32, u64, u128
fn swap_mask_shift_u64(y: &mut u64, mask: u64, shift: u32) -> () {
   *y ^= (*y).unbounded_shr(shift) & mask;
   *y ^= (*y & mask).unbounded_shl(shift);
   *y ^= (*y).unbounded_shr(shift) & mask;
}

impl BitCube4 {
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

    pub fn shift_x(self, shift: i8) -> Self { 
        match shift {
            0 => self,
            1 => Self((self.0.unbounded_shl(1)) & 0xeeee_eeee_eeee_eeee_u64),
            2 => Self((self.0.unbounded_shl(2)) & 0xdddd_dddd_dddd_dddd_u64),
            3 => Self((self.0.unbounded_shl(3)) & 0x8888_8888_8888_8888_u64),
            -1 => Self((self.0.unbounded_shr(1)) & 0x7777_7777_7777_7777_u64),
            -2 => Self((self.0.unbounded_shr(2)) & 0x3333_3333_3333_3333_u64),
            -3 => Self((self.0.unbounded_shr(3)) & 0x1111_1111_1111_1111_u64),
            _ => Self(0)
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

impl const Add for BitCube4 {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        Self(self.0 | other.0)
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

    const FULL: BitCube4 = BitCube4(0xffff_ffff_ffff_ffff_u64);
    const ORDER: BitCube4 = BitCube4(0xfedc_ba98_7654_3210_u64);
    const UPPER_RIGHT_2X4X2: BitCube4 = BitCube4(0xcccc_cccc_0000_0000_u64);
    const LOWER_RIGHT_2X4X2: BitCube4 = BitCube4(0x0000_0000_cccc_cccc_u64);
    const LOWER_LEFT_2X4X2: BitCube4 = BitCube4(0x0000_0000_3333_3333_u64);
    const CENTER_X: BitCube4 = BitCube4(0x0000_0ff0_0ff0_0000_u64);
    const CENTER_Y: BitCube4 = BitCube4(0x0000_6666_6666_0000_u64);
    const CENTER_Z: BitCube4 = BitCube4(0x0660_0660_0660_0660_u64);
    const CENTER_ALL: BitCube4 = CENTER_X + CENTER_Y + CENTER_Z;

    #[test]
    fn test_debug() {
        assert_eq!(format!("{:?}", ORDER),
            "BitCube4(0xfedcba9876543210)\n1100 1110 1101 1111\n0100 0110 0101 0111\n1000 1010 1001 1011\n0000 0010 0001 0011"
        );

    }

    #[test]
    fn test_display() {
        assert_eq!(format!("{:}", ORDER),
            "1100 1110 1101 1111\n0100 0110 0101 0111\n1000 1010 1001 1011\n0000 0010 0001 0011"
        );

    }

    #[test]
    fn test_add() {
        assert_eq!(FULL + FULL, FULL);
        assert_eq!(CENTER_X+CENTER_Y+CENTER_Z, CENTER_ALL);
    }

    #[test]
    fn test_shift_x() {
        assert_eq!(FULL.shift_x(1), 
                   BitCube4(0xeeee_eeee_eeee_eeee_u64)
                   );
    }

    #[test]
    fn test_shift_y() {
        assert_eq!(FULL.shift_y(1), 
                   BitCube4(0xfff0_fff0_fff0_fff0_u64)
                   );
    }

    #[test]
    fn test_shift_z() {
        assert_eq!(FULL.shift_z(1), 
                   BitCube4(0xffff_ffff_ffff_0000_u64)
                   );
    }

    #[test]
    fn test_shift_to_origin() {
        assert_eq!(FULL.shift_to_origin(), FULL);
        assert_eq!((CENTER_X+CENTER_Y).shift_to_origin(), BitCube4(0x0000_0000_6ff6_6ff6));
    }

    #[test]
    fn test_rotate_x() {
        assert_eq!(FULL.rotate_x(), FULL);
        assert_eq!(CENTER_X.rotate_x(), CENTER_X);
        assert_eq!(CENTER_Y.rotate_x(), CENTER_Z);
        assert_eq!(CENTER_Z.rotate_x(), CENTER_Y);
    }

    #[test]
    fn test_rotate_y() {
        assert_eq!(FULL.rotate_y(), FULL);
        assert_eq!(UPPER_RIGHT_2X4X2.rotate_y(), LOWER_RIGHT_2X4X2);
        assert_eq!(LOWER_RIGHT_2X4X2.rotate_y(), LOWER_LEFT_2X4X2);
        assert_eq!(CENTER_X.rotate_y(), CENTER_Z);
        assert_eq!(CENTER_Y.rotate_y(), CENTER_Y);
        assert_eq!(CENTER_Z.rotate_y(), CENTER_X);
    }

    #[test]
    fn test_rotate_z() {
        assert_eq!(FULL.rotate_z(), FULL);
        assert_eq!(CENTER_X.rotate_z(), CENTER_Y);
        assert_eq!(CENTER_Y.rotate_z(), CENTER_X);
        assert_eq!(CENTER_Z.rotate_z(), CENTER_Z);
    }

    #[test]
    fn test_overlap() {
        assert!(CENTER_X.overlap(CENTER_Y));
    }

}
