use std::fmt;
use bitintr::*;

// use itertools::Itertools;

// -----------------------------------------------------------------
// 4x4x4 cube space represented by the 64 bits in a u64
// -----------------------------------------------------------------
// Position at (x,y,z) = x + 4*y + 16*z
// Rotations will happen from the center of the cube

#[derive(PartialEq)]
pub struct BitCube4(u64);

#[inline]  // TODO: Make this general for all u16, u32, u64, u128
fn swap_mask_shift_u32(y: &mut u32, mask: u32, shift: usize) -> () {
   *y ^= (*y >> shift) & mask;
   *y ^= (*y & mask) << shift;
   *y ^= (*y >> shift) & mask;
}

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

impl BitCube4 {
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
    pub fn rotate_x(self) -> Self { todo!() }
    pub fn rotate_y(self) -> Self { todo!() }
    pub fn rotate_z(self) -> Self { 
        // Swap 2x2 squares left <-> right
        // Swap diagonal 2x2 squares
        // Within 2x2 squares swap left <-> right columns
        // Within 2x2 squares swap diagonal entries
        todo!() 
    }
        

    pub fn compose(self, other: Self) -> Self {
        Self(
            (0..8)
            .map(|x| ((self.0 >> (((other.0 >> (x<<2)) & 7) << 2)) & 7) << (x<<2))
            .sum()
            )
    }

    pub fn inverse(self) -> Self {
        Self(
            (0..8)
            .map(|x| x << (((self.0 >> (x<<2)) & 7) << 2))
            .sum()
            )
    }
}


impl fmt::Debug for BitCube4 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "BitMatrix4({:#06x})", self.0)
    } 
} 

impl fmt::Display for BitCube4 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", 
            (0..4)
            .map(|x| format!("{:#06b}\n", (self.0 >> ((3-x)<<2)) & 0xf))
            .collect::<String>()
            // .join("")
            )
    } 
} 

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_shift_x() {
        assert_eq!(BitCube4(0xffff_ffff_ffff_ffff_u64).shift_x(1), 
                   BitCube4(0xeeee_eeee_eeee_eeee_u64)
                   );
    }

}
