// ----------------------------------
// General bit manipulation functions
// ----------------------------------


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

// TODO: Add u128 as needed
