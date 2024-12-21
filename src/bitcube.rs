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
    pub fn rotate_x(self) -> Self { todo!() }
    pub fn rotate_y(self) -> Self { todo!() }
    // 23 32 31
    // 01 10 20
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
            1 => Self((self.0 << 1) & 0xeeee_eeee_eeee_eeee_u64),
            2 => Self((self.0 << 2) & 0xdddd_dddd_dddd_dddd_u64),
            3 => Self((self.0 << 3) & 0x8888_8888_8888_8888_u64),
            -1 => Self((self.0 >> 1) & 0x7777_7777_7777_7777_u64),
            -2 => Self((self.0 >> 2) & 0x3333_3333_3333_3333_u64),
            -3 => Self((self.0 >> 3) & 0x1111_1111_1111_1111_u64),
            _ => Self(0)
        }
    }
    // pub fn shift_y(self, i8) -> Self { todo!() }
    // pub fn shift_z(self, i8) -> Self { todo!() }
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
    fn test_rotate_z() {
        assert_eq!(full.rotate_z(), full);
        assert_eq!(center_x.rotate_z(), center_y);
        assert_eq!(center_y.rotate_z(), center_x);
        assert_eq!(center_z.rotate_z(), center_z);
    }

}
