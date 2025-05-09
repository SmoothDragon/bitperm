// ----------------------------------
// General bit manipulation functions
// ----------------------------------

// TODO: Add u128 as needed

// #[inline]
pub fn swap_mask_shift_u32(y: &mut u32, mask: u32, shift: u32) {
   *y ^= (*y).unbounded_shr(shift) & mask;
   *y ^= (*y & mask).unbounded_shl(shift);
   *y ^= (*y).unbounded_shr(shift) & mask;
}

#[inline]
pub fn swap_mask_shift_u64(y: &mut u64, mask: u64, shift: u32) {
   *y ^= (*y).unbounded_shr(shift) & mask;
   *y ^= (*y & mask).unbounded_shl(shift);
   *y ^= (*y).unbounded_shr(shift) & mask;
}

struct SwapMaskShiftU32 {
    mask: u32,
    shift: u32,
}

impl SwapMaskShiftU32 {

}

/// Useful constants for 4-cube transformations
pub mod cu64 {
    use crate::bitcube4::BitCube4;

    pub const ALL: u64 = 0xffff_ffff_ffff_ffff;
    pub const FULL: BitCube4 = BitCube4(0xffff_ffff_ffff_ffff_u64);
    pub const ORDER: BitCube4 = BitCube4(0xfedc_ba98_7654_3210_u64);
    pub const UPPER_RIGHT_2X4X2: BitCube4 = BitCube4(0xcccc_cccc_0000_0000_u64);
    pub const LOWER_RIGHT_2X4X2: BitCube4 = BitCube4(0x0000_0000_cccc_cccc_u64);
    pub const LOWER_LEFT_2X4X2: BitCube4 = BitCube4(0x0000_0000_3333_3333_u64);
    pub const CENTER_X: BitCube4 = BitCube4(0x0000_0ff0_0ff0_0000_u64);
    pub const CENTER_Y: BitCube4 = BitCube4(0x0000_6666_6666_0000_u64);
    pub const CENTER_Z: BitCube4 = BitCube4(0x0660_0660_0660_0660_u64);
    pub const CENTER_ALL: BitCube4 = BitCube4(CENTER_X.0 | CENTER_Y.0 | CENTER_Z.0);
    pub const SUBCUBE_0: BitCube4 = BitCube4(0x0033_0033_u64);
    pub const SUBCUBE_1: BitCube4 = BitCube4(0x00cc_00cc_u64);
    pub const SUBCUBE_2: BitCube4 = BitCube4(0x3300_3300_u64);
    pub const SUBCUBE_3: BitCube4 = BitCube4(0xcc00_cc00_u64);
    pub const SUBCUBE_4: BitCube4 = BitCube4(0x0033_0033_0000_0000_u64);
    pub const SUBCUBE_5: BitCube4 = BitCube4(0x00cc_00cc_0000_0000_u64);
    pub const SUBCUBE_6: BitCube4 = BitCube4(0x3300_3300_0000_0000_u64);
    pub const SUBCUBE_7: BitCube4 = BitCube4(0xcc00_cc00_0000_0000_u64);
}

/// Useful constants for 3-cube transformations
pub mod cu27 {
    use crate::bitcube3::BitCube3;

    pub const FULL: BitCube3 = BitCube3(0o777777777_u32);
    pub const ORDER: BitCube3 = BitCube3(0o76543210_u32);
    pub const CENTER: BitCube3 = BitCube3(0o000_020_000_u32);
    pub const CENTER_X: BitCube3 = BitCube3(0o000_070_000_u32);
    pub const CENTER_Y: BitCube3 = BitCube3(0o000_222_000_u32);
    pub const CENTER_Z: BitCube3 = BitCube3(0o020_020_020_u32);
    pub const CENTER_ALL: BitCube3 = BitCube3(CENTER_X.0 | CENTER_Y.0 | CENTER_Z.0);
}
