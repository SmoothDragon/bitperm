// ----------------------------------
// General bit manipulation functions
// ----------------------------------

// TODO: Add u128 as needed

#[inline]
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

pub fn sms64(mask: u64, shift: u32) -> Option<impl Fn(&mut u64) -> ()> {
    if mask.unbounded_shl(shift) & mask == 0 {
        Some(move |y: &mut u64| { swap_mask_shift_u64(y, mask, shift) })
    } else {
        None
    }
}

/*
struct SwapMaskShiftU32 {
    mask: u32,
    shift: u32,
}

impl SwapMaskShiftU32 {

}
*/

/// General constants
pub const ALL: u64 = 0xffff_ffff_ffff_ffff;
pub const FULL: u64 = 0xffff_ffff_ffff_ffff_u64;
pub const ORDER: u64 = 0xfedc_ba98_7654_3210_u64;
pub const REP_01: u64 = 0x0101010101010101u64;
pub const REP_7F: u64 = 0x7f7f7f7f7f7f7f7fu64;

/// BitCube4 constants
pub const UPPER_RIGHT_2X4X2: u64 = 0xcccc_cccc_0000_0000_u64;
pub const LOWER_RIGHT_2X4X2: u64 = 0x0000_0000_cccc_cccc_u64;
pub const LOWER_LEFT_2X4X2: u64 = 0x0000_0000_3333_3333_u64;
pub const BC4_CENTER_X: u64 = 0x0000_0ff0_0ff0_0000_u64;
pub const BC4_CENTER_Y: u64 = 0x0000_6666_6666_0000_u64;
pub const BC4_CENTER_Z: u64 = 0x0660_0660_0660_0660_u64;
pub const BC4_CENTER_ALL: u64 = BC4_CENTER_X | BC4_CENTER_Y | BC4_CENTER_Z;
pub const SUBCUBE_0: u64 = 0x0033_0033_u64;
pub const SUBCUBE_1: u64 = 0x00cc_00cc_u64;
pub const SUBCUBE_2: u64 = 0x3300_3300_u64;
pub const SUBCUBE_3: u64 = 0xcc00_cc00_u64;
pub const SUBCUBE_4: u64 = 0x0033_0033_0000_0000_u64;
pub const SUBCUBE_5: u64 = 0x00cc_00cc_0000_0000_u64;
pub const SUBCUBE_6: u64 = 0x3300_3300_0000_0000_u64;
pub const SUBCUBE_7: u64 = 0xcc00_cc00_0000_0000_u64;

/// 2D BitGrid constants
pub const CENTER_XY: u64 = 0x1818_18ff_ff18_1818;
pub const LOWER_LEFT: u64 = 0x0f0f_0f0f_u64;
pub const LOWER_RIGHT: u64 = 0xf0f0_f0f0_u64;
pub const UPPER_LEFT: u64 = 0x0f0f_0f0f_0000_0000_u64;
pub const UPPER_RIGHT: u64 = 0xf0f0_f0f0_0000_0000_u64;

pub const HIGHFIVE: u64 = 0xff80ff01ff;
pub const SMALL_FIVE: u64 = 0x00f080f010f;
pub const CHECKER2: u64 = 0x0c0c_0303;
pub const SLASH:u64 = 0x8040201008040201;
pub const BACKSLASH:u64 = 0x0102040810204080;
pub const BORDER:u64 = 0xff81_8181_8181_81ff;
pub const IDENTITY:u64 = 0x8040201008040201;
pub const ANTIDIAG:u64 = 0x0102040810204080;

pub const BM8_UPPER_LEFT: u64 = 0x0f0f_0f0f_u64;
pub const BM8_UPPER_RIGHT: u64 = 0xf0f0_f0f0_u64;
pub const BM8_LOWER_LEFT: u64 = 0x0f0f_0f0f_0000_0000_u64;
pub const BM8_LOWER_RIGHT: u64 = 0xf0f0_f0f0_0000_0000_u64;

/// BitCube3 constants
pub const BC3_FULL: u32 = 0o777777777_u32;
pub const BC3_ORDER: u32 = 0o76543210_u32;
pub const BC3_CENTER: u32 = 0o000_020_000_u32;
pub const BC3_CENTER_X: u32 = 0o000_070_000_u32;
pub const BC3_CENTER_Y: u32 = 0o000_222_000_u32;
pub const BC3_CENTER_Z: u32 = 0o020_020_020_u32;
pub const BC3_CENTER_ALL: u32 = BC3_CENTER_X | BC3_CENTER_Y | BC3_CENTER_Z;


#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_sms64(){
        let mut y: u64 = 0xffff_ffff_u64;
        // Swap 4x4 squares top <-> bottom
        swap_mask_shift_u64(&mut y, 0xffff_ffff_u64, 32);
        assert_eq!(y, 0xffff_ffff_0000_0000_u64);

        // Swap back 4x4 squares top <-> bottom
        let func = sms64(0xffff_ffff_u64, 32).unwrap();
        func(&mut y);
        assert_eq!(y, 0xffff_ffff_u64);
    }
}

