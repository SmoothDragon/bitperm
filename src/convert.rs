use crate::bitcube3::BitCube3;
use crate::bitcube4::BitCube4;

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
