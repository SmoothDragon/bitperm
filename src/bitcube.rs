use std::fmt;

// use itertools::Itertools;

// -----------------------------------------------------------------
// 4x4x4 cube space represented by the 64 bits in a u64
// -----------------------------------------------------------------
// Position at (x,y,z) = x + 4*y + 16*z
// Rotations will happen from the center of the cube

#[derive(PartialEq, Clone)]
pub struct BitCube4(u64);

// impl From<BitPermPoly3> for BitPermTT3 {
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

#[inline]  // TODO: Make this general for all u16, u32, u64, u128
fn swap_mask_shift_u64(y: &mut u64, mask: u64, shift: usize) -> () {
   *y ^= (*y >> shift) & mask;
   *y ^= (*y & mask) << shift;
   *y ^= (*y >> shift) & mask;
}

impl BitCube4 {
    // pub fn rotate_x(self) -> Self { todo!() }

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
            1 => Self((self.0 << 1) & 0xeeee_eeee_eeee_eeee_u64),
            2 => Self((self.0 << 2) & 0xdddd_dddd_dddd_dddd_u64),
            3 => Self((self.0 << 3) & 0x8888_8888_8888_8888_u64),
            -1 => Self((self.0 >> 1) & 0x7777_7777_7777_7777_u64),
            -2 => Self((self.0 >> 2) & 0x3333_3333_3333_3333_u64),
            -3 => Self((self.0 >> 3) & 0x1111_1111_1111_1111_u64),
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
}


impl fmt::Debug for BitCube4 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "BitCube4({:#018x})", self.0)
    } 
} 

impl fmt::Display for BitCube4 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", 
            (0..4)
            .map(|x| format!("{:#064b}\n", (self.0 >> ((3-x)<<2)) & 0xf))
            .collect::<String>()
            // .join("")
            )
    } 
} 

#[cfg(test)]
mod test {
    use super::*;

    const full: BitCube4 = BitCube4(0xffff_ffff_ffff_ffff_u64);
    const center_x: BitCube4 = BitCube4(0x0000_0ff0_0ff0_0000_u64);
    const center_y: BitCube4 = BitCube4(0x0000_6666_6666_0000_u64);
    const center_z: BitCube4 = BitCube4(0x0660_0660_0660_0660_u64);

    #[test]
    fn test_shift_x() {
        assert_eq!(full.shift_x(1), 
                   BitCube4(0xeeee_eeee_eeee_eeee_u64)
                   );
    }

    #[test]
    fn test_shift_y() {
        assert_eq!(full.shift_y(1), 
                   BitCube4(0xfff0_fff0_fff0_fff0_u64)
                   );
    }

    #[test]
    fn test_shift_z() {
        assert_eq!(full.shift_z(1), 
                   BitCube4(0xffff_ffff_ffff_0000_u64)
                   );
    }

    #[test]
    fn test_rotate_x() {
        assert_eq!(full.rotate_x(), full);
        assert_eq!(center_x.rotate_x(), center_x);
        assert_eq!(center_y.rotate_x(), center_z);
        assert_eq!(center_z.rotate_x(), center_y);
    }

    #[test]
    fn test_rotate_z() {
        assert_eq!(full.rotate_z(), full);
        assert_eq!(center_x.rotate_z(), center_y);
        assert_eq!(center_y.rotate_z(), center_x);
        assert_eq!(center_z.rotate_z(), center_z);
    }

}
