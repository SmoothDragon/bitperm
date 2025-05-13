use std::fmt;
use std::ops::*;
// use flowscad::*;

// use crate::bitlib::swap_mask_shift_u64;
// use crate::bitcube3::BitCube3;
use crate::bitcube4::BitCube4;


// -----------------------------------------------------------------
// 4x4x4 rhombic dodecahedron space
// -----------------------------------------------------------------
// Position at (x,y,z) = x + 4*y + 16*z
// Rotations will happen from the center of the cube

#[derive(Copy, Clone, Debug, PartialEq)]
pub struct BitRhombdo4(BitCube4, BitCube4);


impl BitRhombdo4 {
    pub fn rotate_x(self) -> Self { 
        Self(self.0.rotate_x(), self.1.rotate_x())
    }

    pub fn rotate_y(self) -> Self { 
        Self(self.0.rotate_y(), self.1.rotate_y())
    }

    pub fn rotate_z(self) -> Self { 
        Self(self.0.rotate_z(), self.1.rotate_z())
    }

    pub fn rotate_d(self) -> Self { 
        Self(self.0.rotate_d(), self.1.rotate_d())
    }

    pub fn shift_x(self, shift: i8) -> Self { 
        Self(self.0.shift_x(shift), self.1.shift_x(shift))
    }

    pub fn shift_y(self, shift: i8) -> Self { 
        Self(self.0.shift_y(shift), self.1.shift_y(shift))
    }

    pub fn shift_z(self, shift: i8) -> Self { 
        Self(self.0.shift_z(shift), self.1.shift_z(shift))
    }


    /*
    /// Given a piece in the 4-cube, shift it towards the origin so that it touches the x, y, and z
    /// planes
    // pub fn shift_to_origin(self) -> Self {
        // let mut shape = self.0;
        // let z_shift = (shape.trailing_zeros() / 16) * 16;
        // shape = shape.unbounded_shr(z_shift);
        // let xy_proj = shape | shape.unbounded_shr(32);
        // let xy_proj = xy_proj | xy_proj.unbounded_shr(16);
        // let y_shift = (xy_proj.trailing_zeros() / 4) * 4;
        // shape = shape.unbounded_shr(y_shift);
        // let x_shift = xy_proj | xy_proj.unbounded_shr(8);
        // let x_shift = x_shift | x_shift.unbounded_shr(4);
        // shape = shape.unbounded_shr(x_shift.trailing_zeros());
        // Self(shape)
    // }
    */

    // pub fn overlap(self, other: Self) -> bool {
        // self.c4.overlap(other.c4) && self.c3.overlap(other.c3)
    // }
}


impl BitOr for BitRhombdo4 {
    type Output = Self;

    fn bitor(self, other: Self) -> Self::Output {
        Self(self.0 | other.0, self.1 | other.1)
    }
}

impl BitAnd for BitRhombdo4 {
    type Output = Self;

    fn bitand(self, other: Self) -> Self::Output {
        Self(self.0 & other.0, self.1 & other.1)
    }
}

// impl fmt::Debug for BitRhombdo4 {
    // fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // write!(f, "{}\n{}", self.c4, self.c3)
    // } 
// } 

impl fmt::Display for BitRhombdo4 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:}\n{:}", self.0, self.1)
    }
} 

#[cfg(test)]
mod test {
    use super::*;

    // const FULL: BitCube4 = BitCube4(0xffff_ffff_ffff_ffff_u64);
    const FULL: BitRhombdo4 = BitRhombdo4(BitCube4(0xffff_ffff_ffff_ffff_u64),BitCube4(0xffff_ffff_ffff_ffff_u64));
    const ORDER: BitRhombdo4 = BitRhombdo4(BitCube4(0xfedc_ba98_7654_3210_u64), BitCube4(0xfedc_ba98_7654_3210_u64));
    // const UPPER_RIGHT_2X4X2: BitCube4 = BitCube4(0xcccc_cccc_0000_0000_u64);
    // const LOWER_RIGHT_2X4X2: BitCube4 = BitCube4(0x0000_0000_cccc_cccc_u64);
    // const LOWER_LEFT_2X4X2: BitCube4 = BitCube4(0x0000_0000_3333_3333_u64);
    const CENTER_X: BitRhombdo4 = BitRhombdo4(BitCube4(0x0000_0ff0_0ff0_0000_u64), BitCube4(0x0000_0ff0_0ff0_0000_u64));
    // const CENTER_Y: BitCube4 = BitCube4(0x0000_6666_6666_0000_u64);
    // const CENTER_Z: BitCube4 = BitCube4(0x0660_0660_0660_0660_u64);
    // const CENTER_ALL: BitCube4 = BitCube4(CENTER_X.0 | CENTER_Y.0 | CENTER_Z.0);
    // const SUBCUBE_0: BitCube4 = BitCube4(0x0033_0033_u64);
    // const SUBCUBE_1: BitCube4 = BitCube4(0x00cc_00cc_u64);
    // const SUBCUBE_2: BitCube4 = BitCube4(0x3300_3300_u64);
    // const SUBCUBE_3: BitCube4 = BitCube4(0xcc00_cc00_u64);
    // const SUBCUBE_4: BitCube4 = BitCube4(0x0033_0033_0000_0000_u64);
    // const SUBCUBE_5: BitCube4 = BitCube4(0x00cc_00cc_0000_0000_u64);
    // const SUBCUBE_6: BitCube4 = BitCube4(0x3300_3300_0000_0000_u64);
    // const SUBCUBE_7: BitCube4 = BitCube4(0xcc00_cc00_0000_0000_u64);

    #[test]
    fn test_debug() {
        assert_eq!(format!("{:?}", ORDER),
            "BitRhombdo4(BitCube4(0xfedcba9876543210), BitCube4(0xfedcba9876543210))"
        );
    }

    #[test]
    fn test_display() {
        assert_eq!(format!("{:}", ORDER),
            "1100 1110 1101 1111\n0100 0110 0101 0111\n1000 1010 1001 1011\n0000 0010 0001 0011\n1100 1110 1101 1111\n0100 0110 0101 0111\n1000 1010 1001 1011\n0000 0010 0001 0011"
        );

    }

    #[test]
    fn test_bitor() {
        assert_eq!(FULL | FULL, FULL);
        // assert_eq!(CENTER_X | CENTER_Y | CENTER_Z, CENTER_ALL);
    }

    #[test]
    fn test_bitand() {
        assert_eq!(FULL & FULL, FULL);
        // assert_eq!(CENTER_X | CENTER_Y | CENTER_Z, CENTER_ALL);
    }

    /*
    #[test]
    fn test_shift_x() {
        assert_eq!(FULL.shift_x(1), 
                   BitRhombdo4{c4:BitCube4(0xeeee_eeee_eeee_eeee_u64), c3:BitCube3(0o666_666_666)}
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
        assert_eq!((CENTER_X | CENTER_Y).shift_to_origin(), BitCube4(0x0000_0000_6ff6_6ff6));
    }

    #[test]
    fn test_rotate_x() {
        assert_eq!(FULL.rotate_x(), FULL);
        assert_eq!(CENTER_X.rotate_x(), CENTER_X);
        assert_eq!(CENTER_Y.rotate_x(), CENTER_Z);
        assert_eq!(CENTER_Z.rotate_x(), CENTER_Y);
        assert_eq!(BitCube4(0xf).rotate_x(), BitCube4(0xf000));
        assert_eq!(BitCube4(0xf000).rotate_x(), BitCube4(0xf000000000000000));
    }

    #[test]
    fn test_rotate_y() {
        assert_eq!(FULL.rotate_y(), FULL);
        assert_eq!(UPPER_RIGHT_2X4X2.rotate_y(), LOWER_RIGHT_2X4X2);
        assert_eq!(LOWER_RIGHT_2X4X2.rotate_y(), LOWER_LEFT_2X4X2);
        assert_eq!(CENTER_X.rotate_y(), CENTER_Z);
        assert_eq!(CENTER_Y.rotate_y(), CENTER_Y);
        assert_eq!(CENTER_Z.rotate_y(), CENTER_X);
        assert_eq!(BitCube4(0xf).rotate_y(), BitCube4(0x0001000100010001));
    }

    #[test]
    fn test_rotate_z() {
        assert_eq!(FULL.rotate_z(), FULL);
        assert_eq!(CENTER_X.rotate_z(), CENTER_Y);
        assert_eq!(CENTER_Y.rotate_z(), CENTER_X);
        assert_eq!(CENTER_Z.rotate_z(), CENTER_Z);
        assert_eq!(BitCube4(0xf).rotate_z(), BitCube4(0x8888));
    }

    #[test]
    fn test_rotate_d() {
        assert_eq!(FULL.rotate_d(), FULL);
        assert_eq!(SUBCUBE_0.rotate_d(), SUBCUBE_0);
        assert_eq!(SUBCUBE_1.rotate_d(), SUBCUBE_2);
        assert_eq!(SUBCUBE_2.rotate_d(), SUBCUBE_4);
        assert_eq!(SUBCUBE_4.rotate_d(), SUBCUBE_1);
        assert_eq!(SUBCUBE_3.rotate_d(), SUBCUBE_6);
        assert_eq!(SUBCUBE_6.rotate_d(), SUBCUBE_5);
        assert_eq!(SUBCUBE_5.rotate_d(), SUBCUBE_3);
        assert_eq!(SUBCUBE_7.rotate_d(), SUBCUBE_7);
        assert_eq!(CENTER_X.rotate_d(), CENTER_Y);
        assert_eq!(CENTER_Y.rotate_d(), CENTER_Z);
        assert_eq!(CENTER_Z.rotate_d(), CENTER_X);
        assert_eq!(BitCube4(0x1011f).rotate_d(), BitCube4(0x0000000100011113));
    }

    #[test]
    fn test_overlap() {
        assert!(CENTER_X.overlap(CENTER_Y));
    }

    #[test]
    fn test_into_bitperm3() {
        assert_eq!(BitCube4::from(BitCube3(0o777777777)), BitCube4(0x77707770777));
        assert_eq!(BitCube4::from(BitCube3(0o700000000)), BitCube4(0x70000000000));
        assert_eq!(BitCube4::from(BitCube3(0o76543210)), BitCube4(0x7605430210));

    }
    */
}
