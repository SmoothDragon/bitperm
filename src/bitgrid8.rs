use std::fmt;

// -----------------------------------------------------------------
// 2D geometric operations on an 8x8 grid
// -----------------------------------------------------------------

// -----------------------------------------------------------------
// 8x8 square space represented by the 64 bits in a u64
// -----------------------------------------------------------------
// Position at (x,y) = x + 8*y
// The low bit corresponds to the upper left most position.
// The high bit corresponds to the lower right most position.
// Rotations will happen from the center of the square.


#[derive(PartialEq)]
pub struct Grid8x8(u64);

impl fmt::Debug for Grid8x8 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Grid8x8({:#010x})", self.0)
    } 
} 

impl fmt::Display for Grid8x8 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", 
            (0..64)
            .map(|x| format!("{}{}", if (self.0 >> x) & 0x1 == 1 { "#" } else { "." },
                if x%8 ==7 { "\n" } else { "" }))
            .collect::<String>()
            )

        // let output = (0..64)
            // .fold(f, |mut f, x| {
                // let _ = write!(f, "{}{}", if (self.0 >> x) & 0x1 == 1 { "#" } else { "." },
                // if x%8 ==7 { "\n" } else { "" });
                // f
            // });
        // output
    } 
} 

const REP_01:u64 = 0x0101010101010101u64;
const REP_7F:u64 = 0x7f7f7f7f7f7f7f7fu64;

impl Grid8x8 {
    pub fn unbounded_shift_n(self) -> Self {
        Self(self.0.unbounded_shr(8))
    }

    pub fn unbounded_shift_s(self) -> Self {
        Self(self.0.unbounded_shl(8))
    }

    pub fn checked_shift_n(self) -> Option<Self> {
        let result = self.0.unbounded_shr(8);
        if result.count_ones() == self.0.count_ones() {
            Some(Self(result))
        } else {
            None
        }
    }

    pub fn shift_w(self) -> Option<Self> {
        let result = self.0.rotate_right(1);
        if result & 0x0101010101010101 == 0 {
            Some(Self(result))
        } else {
            None
        }
    }

    pub fn shift_s(self) -> Self {
        Self(self.0 << 8)
    }
    pub fn shift_e(self) -> Self {
        Self(self.0 << 1)
    }
    // pub fn shift_w(self) -> Self {
        // Self(self.0 >> 1)
    // }
    pub fn rank(self) -> u32 {
        let mut m = self.0;
        let mut r = 0u32;
        let mut pivot;
        println!("{}", Self(m));
        while m != 0 {
            pivot = m & REP_01;
            if pivot != 0 {
                r += 1;
                m ^= (m.unbounded_shr(pivot.trailing_zeros()) & 0xff) * pivot;
            }
            m = m.unbounded_shr(1) & REP_7F;
            println!("{}", Self(m));
        }
        r
    }

}

#[cfg(test)]
mod test {
    use super::*;
    
    const IDENTITY:Grid8x8 = Grid8x8(0x8040201008040201);

    #[test]
    fn test_rank() {
        assert_eq!(IDENTITY.rank(), 8);
        assert_eq!(Grid8x8(0xfedcba9876543210u64).rank(), 4);
    }

    #[test]
    fn test_grid8x8_display() {
        assert_eq!(format!("{}", Grid8x8(0x8040201008040201)), 
            "#.......\n.#......\n..#.....\n...#....\n....#...\n.....#..\n......#.\n.......#\n");
        assert_eq!(format!("{}", Grid8x8(0x1)), 
            "#.......\n........\n........\n........\n........\n........\n........\n........\n");
    }

    #[test]
    fn test_unbounded_shift_n() {
        assert_eq!(Grid8x8(0xf00f).unbounded_shift_n(), Grid8x8(0xf0));
        assert_eq!(Grid8x8(0xf00f00).unbounded_shift_n(), Grid8x8(0xf00f));
    }

    fn test_checked_shift_n() {
        assert_eq!(Grid8x8(0xf00f).checked_shift_n(), None);
        assert_eq!(Grid8x8(0xf00f00).checked_shift_n(), Some(Grid8x8(0xf00f)));
    }

    // #[test]
    // fn test_shift_w() {
        // assert_eq!(Grid8x8(0xf00f).shift_w(), None);
        // assert_eq!(Grid8x8(0xf00f00).shift_w(), Some(Grid8x8(0xf00f)));
    // }
}
/*

// ---------------------------------------------------------------------
// Bit Permutation over 3 bits represented as three polynomials in a u32
// ---------------------------------------------------------------------

#[derive(PartialEq)]
pub struct BitPermPoly3(u32);

impl From<BitPermTT3> for BitPermPoly3 {
    fn from(bptt3: BitPermTT3) -> Self {
        let mut p = bptt3.0;
        swap_mask_shift_u32(&mut p, 0xf0f0, 12);
        swap_mask_shift_u32(&mut p, 0xff00, 8);
        swap_mask_shift_u32(&mut p, 0xcccc, 14);
        swap_mask_shift_u32(&mut p, 0xff00, 8);
        swap_mask_shift_u32(&mut p, 0xaaaa, 15);
        swap_mask_shift_u32(&mut p, 0xff00, 8);
        BitPermPoly3(p)
    }
}

impl fmt::Debug for BitPermPoly3 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "BitPermTT3({:#010x})", self.0)
    } 
} 

// -----------------------------------------------------------------
// Bit Permutation over 4 bits represented as a truth table in a u64
// -----------------------------------------------------------------

#[derive(PartialEq)]
pub struct BitPermTT4(u64);

#[inline]  // TODO: Make this general for all u16, u32, u64, u128
fn swap_mask_shift_u64(y: &mut u64, mask: u64, shift: usize) -> () {
   *y ^= (*y >> shift) & mask;
   *y ^= (*y & mask) << shift;
   *y ^= (*y >> shift) & mask;
}


impl BitPermTT4 {
    pub const ID:BitPermTT4 = BitPermTT4(0xfedcba9876543210);

    pub fn id() -> BitPermTT4 {
        BitPermTT4(0xfedcba9876543210)
    }

    pub fn increment() -> BitPermTT4 {
        BitPermTT4(0x0fedcba987654321)
    }

    pub fn compose(self, other: Self) -> Self {
        Self(
            (0..16)
            .map(|x| ((self.0 >> (((other.0 >> (x<<2)) & 0xf) << 2)) & 0xf) << (x<<2))
            .sum()
            )
    }

    pub fn inverse(self) -> Self {
        Self(
            (0..16)
            .map(|x| x << (((self.0 >> (x<<2)) & 0xf) << 2))
            .sum()
            )
    }
}

impl From<BitPermTT3> for BitPermTT4 {
    fn from(bptt3: BitPermTT3) -> Self {
        let p = bptt3.0 as u64;
        BitPermTT4(p ^ (p << 32) ^ 0x8888888800000000)
    }
}

impl From<BitMatrix4> for BitPermTT4 {
    fn from(bm4: BitMatrix4) -> Self {
        let x = bm4.0 as u64;
        BitPermTT4(
            ((x & 0xf) * 0x1010101010101010)
            ^ ((x & 0xf0) * 0x0110011001100110)  // because &0xf0 not shifted down four bits
            ^ ((x & 0xf00) * 0x0011110000111100)
            ^ ((x & 0xf000) * 0x0001111111100000)
            )
    }
}

// impl From<BitPermPoly4> for BitPermTT4 {
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

impl fmt::Debug for BitPermTT4 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "BitPermTT4({:#018x})", self.0)
    } 
} 

// --------------------------------------------------------------------
// Bit Permutation over 4 bits represented as four polynomials in a u64
// --------------------------------------------------------------------

#[derive(PartialEq)]
pub struct BitPermPoly4(u64);

// --------------------------------------------------------------------
// Bit Matrix over 4 bits represented in a u16
// --------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq)]
pub struct BitMatrix4(u16);

impl BitMatrix4 {
    pub const ID:BitMatrix4 = BitMatrix4(0x8421);

    pub fn id() -> Self {
        BitMatrix4(0x8421)
    }

    pub fn reverse() -> Self {
        BitMatrix4(0x1248)
    }

    pub fn transpose(&self) -> Self {
        let mut x = self.0;
        x ^= (x & 0x00cc) << 6;
        x ^= (x & 0x3300) >> 6;
        x ^= (x & 0x00cc) << 6;
        x ^= (x & 0x0a0a) << 3;
        x ^= (x & 0x5050) >> 3;
        x ^= (x & 0x0a0a) << 3;
        BitMatrix4(x)
    }

    pub fn mul(&self, other: Self) -> Self {
        println!("{}", self);
        println!("{}", other);
        let x = self.0;
        let y = other.transpose().0;
        println!("{}", BitMatrix4(x));
        println!("{}", BitMatrix4(y));
        BitMatrix4(
            (0..4)
            .map(|ii| {
                let mut z = x & (((y >> (ii<<2)) & 0xf) * 0x1111);
                z ^= z >> 2;
                z ^= z >> 1;
                z &= 0x1111;
                z << ii
            })
            .sum()
            )
    }

    fn leadz(x:u32) -> u32 {
        for i in 0..32 {
            if (x >> i) & 1 == 1 { return i }
        }
        return 32
    }

    // TODO: Use bitintr and bitwise to clean up
    fn swap_row(mut x:u32, r0:u32, r1:u32) -> u32 {
        if r0 == r1 { return x};
        x ^= ((x.checked_shr(r0<<2).unwrap_or(0)) & 0xf000f).checked_shl(r1<<2).unwrap_or(0);
        x ^= ((x.checked_shr(r1<<2).unwrap_or(0)) & 0xf000f).checked_shl(r0<<2).unwrap_or(0);
        x ^= ((x.checked_shr(r0<<2).unwrap_or(0)) & 0xf000f).checked_shl(r1<<2).unwrap_or(0);
        // x ^= ((x >> (r1<<2)) & 0xf000f).checked_shl(r0<<2).unwrap_or(0);
        // x ^= ((x >> (r0<<2)) & 0xf000f).checked_shl(r1<<2).unwrap_or(0);
        // x ^= ((x >> (r1<<2)) & 0xf000f) << (r0<<2);
        // x ^= ((x >> (r0<<2)) & 0xf000f) << (r1<<2);
        x
    }

    /* This requires bitintr
    pub fn inverse(&self) -> Self {
        let mut x = self.0 as u32;
        x += 0x84210000;
        for i in 0..4 {
            // let pivot = Self::leadz((x>>i) & (0x1111 << (i<<2))) >> 2;
            let pivot = ((x>>i) & (0x1111 << (i<<2))).tzcnt() >> 2;
            x = Self::swap_row(x, i, pivot);
            let pivot_bit = ((x>>i) & (0x1111 << (i<<2))).blsi();
            x ^= ((x>>(i<<2)) & 0xf000f) * ((x>>i) & (0x1111-(1<<(i<<2))));
        }
        BitMatrix4((x >> 16) as u16)
        /*
        // println!("{}", BitMatrix4(x as u16)); // println!("{}", BitMatrix4((x>>16) as u16)); 
        let pivot = Self::leadz(x & 0x1111) >> 2;
        x = Self::swap_row(x, 0, pivot);
        x ^= (x & 0xf000f) * (x & 0x1110);
        // println!("{}", BitMatrix4(x as u16)); // println!("{}", BitMatrix4((x>>16) as u16)); 
        let pivot = Self::leadz((x>>1) & 0x1110) >> 2;
        x = Self::swap_row(x, 1, pivot);
        x ^= ((x>>4) & 0xf000f) * ((x>>1) & 0x1101);
        // println!("{}", BitMatrix4(x as u16)); // println!("{}", BitMatrix4((x>>16) as u16)); 
        let pivot = Self::leadz((x>>2) & 0x1100) >> 2;
        x = Self::swap_row(x, 2, pivot);
        x ^= ((x>>8) & 0xf000f) * ((x>>2) & 0x1011);
        // println!("{}", BitMatrix4(x as u16)); // println!("{}", BitMatrix4((x>>16) as u16)); 
        let pivot = Self::leadz((x>>2) & 0x1000) >> 2;
        x = Self::swap_row(x, 3, pivot);
        x ^= ((x>>12) & 0xf000f) * ((x>>3) & 0x0111);
        println!("{}", BitMatrix4(x as u16)); println!("{}", BitMatrix4((x>>16) as u16)); 
        // println!("{}", BitMatrix4(x as u16)); // println!("{}", BitMatrix4((x>>16) as u16)); 
        BitMatrix4((x >> 16) as u16)
        */
    }
    */

}

impl From<BitPermTT4> for BitMatrix4 {
    fn from(bptt4: BitPermTT4) -> Self {
        let x = bptt4.0 as u64;
        BitMatrix4((((x >> 4) & 0xff) ^ ((x >> 8) & 0xf00) ^ ((x >> 20) & 0xf000)) as u16)
    }
}

impl fmt::Debug for BitMatrix4 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "BitMatrix4({:#06x})", self.0)
    } 
} 

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_bit_perm_poly3_from_bit_perm_tt3() {
        assert_eq!(BitPermTT3::from(BitPermPoly3(0xf0ccaa)), BitPermTT3(0x76543210));
        assert_eq!(BitPermTT3::from(BitPermPoly3(0x786655)), BitPermTT3(0x07654321));
    }

    #[test]
    fn test_bit_perm_tt3_from_bit_perm_poly3() {
        assert_eq!(BitPermPoly3::from(BitPermTT3(0x76543210)), BitPermPoly3(0xf0ccaa));
        assert_eq!(BitPermPoly3::from(BitPermTT3(0x07654321)), BitPermPoly3(0x786655));
    }

    #[test]
    fn test_bit_perm_tt3_compose() {
        assert_eq!(BitPermTT3(0x76543210).compose(BitPermTT3(0x76543210)), BitPermTT3(0x76543210)); // Id * Id == Id
        assert_eq!(BitPermTT3::ID.compose(BitPermTT3::ID), BitPermTT3::ID); // Id * Id == Id
        assert_eq!(BitPermTT3(0x07654321).compose(BitPermTT3(0x07654321)), BitPermTT3(0x10765432)); // Two increments
    }
    
    #[test]
    fn test_bit_perm_tt4_compose() {
        assert_eq!(BitPermTT4::ID.compose(BitPermTT4::ID), BitPermTT4::ID); // id * id == id
        assert_eq!(BitPermTT4::increment().compose(BitPermTT4::increment()), BitPermTT4(0x10fedcba98765432)); // Two increments
        assert_eq!(BitPermTT4(0x0fedcba987654321).compose(BitPermTT4(0x0fedcba987654321)), BitPermTT4(0x10fedcba98765432)); // Two increments
    }

    #[test]
    fn test_bit_perm_tt4_from_bit_perm_tt3() {
        assert_eq!(BitPermTT4::from(BitPermTT3::ID), BitPermTT4::ID);
    }

    #[test]
    fn test_bit_perm_tt4_from_bitmatrix4() {
        assert_eq!(BitPermTT4::from(BitMatrix4::ID), BitPermTT4::ID);
    }

    #[test]
    fn test_bit_matrix4_transpose() {
        assert_eq!(BitMatrix4::ID.transpose(), BitMatrix4::ID);
        assert_eq!(BitMatrix4::reverse().transpose(), BitMatrix4::reverse());
        assert_eq!(BitMatrix4(0xf731).transpose(), BitMatrix4(0x8cef));
        assert_eq!(BitMatrix4(0x73e4).transpose(), BitMatrix4(0x2bec));
    }

    #[test]
    fn test_bit_matrix4_mul() {
        assert_eq!(BitMatrix4::ID.mul(BitMatrix4::ID), BitMatrix4::ID);
        assert_eq!(BitMatrix4::reverse().mul(BitMatrix4::reverse()), BitMatrix4::ID);
        assert_eq!(BitMatrix4(0x73e4).mul(BitMatrix4(0x2bec)), BitMatrix4(0x927b));
    }

    /* TODO: Tests require bitintr
    #[test]
    fn test_bit_perm_tt3_inverse() {
        assert_eq!(BitPermTT3::ID.inverse(), BitPermTT3::ID);  // id^-1 == id
    }

    #[test]
    fn test_bit_perm_tt4_inverse() {
        assert_eq!(BitPermTT4::ID.inverse(), BitPermTT4::ID);  // id^-1 == id
    }

    #[test]
    fn test_bit_matrix4_inverse() {
        assert_eq!(BitMatrix4(0x53e4).inverse(), BitMatrix4(0xe1d9));
        assert_eq!(BitMatrix4(0xe1d9).inverse(), BitMatrix4(0x53e4));
        assert_eq!(BitMatrix4(0x53e4).inverse().mul(BitMatrix4(0x53e4)), BitMatrix4::ID);
        assert_eq!(BitMatrix4::reverse().inverse(), BitMatrix4::reverse());
        assert_eq!(BitMatrix4::ID.inverse(), BitMatrix4::ID);
    }
    */
}
*/
