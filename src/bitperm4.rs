#[derive(Debug, Clone, Copy, PartialEq)]
struct Bitperm4(u64);

/// Default is the identity permutation
impl Default for BitPerm4 {
    fn default() -> Self {
        Bitperm4(0xff00_f0f0_cccc_aaaa_u64)
    }
}

#[allow(dead_code)]
impl Bitperm4 {
    fn cnot(self, control: usize, target: usize) -> Self {
        Bitperm4(self.0 ^ (((self.0 >> (control << 4)) & 0xffff) << (target << 4)))
    }

    fn compose(self, other: Self) -> Self {
        let mut result: u64 = 0;
        let idx_self = Self::tt2idx(self.0);
        let idx_other = Self::tt2idx(other.0);
        for i in 0..16 {
            result ^= (idx_self >> (((idx_other >> (i<<2)) & 0xf) << 2) & 0xf) << (i<<2)
        }
        Bitperm4(Self::idx2tt(result))
    }

    fn tt2idx(tt: u64) -> u64 {
        let mut result: u64 = 0;
        let mut idx: u64;
        for i in 0..16 {
            idx = (tt >> i) & 0x1000100010001;
            idx ^= idx >> 30;
            idx ^= idx >> 15;
            result ^= (idx & 0xf) << (i<<2);
        }
        result
    }

    fn idx2tt(idx: u64) -> u64 {
        let mut result: u64 = 0;
        let mut tt: u64;
        for i in 0..16 {
            tt = (idx >> (i<<2)) & 0xf;
            tt ^= tt >> 15;
            tt ^= tt >> 30;
            result ^= (tt & 0x1000100010001) << i;
        }
        result
    }
}

fn compress_u64(x: u64, m: u64) -> u64 {
    let mut m: u64 = m;
    let mut x: u64 = x & m;
    let mut mk: u64 = !m << 1;
    let mut mp: u64;
    let mut mv: u64;
    let mut t: u64;

    for i in 0..6 {
        mp = mk ^ (mk << 1);
        mp = mp ^ (mp << 2);
        mp = mp ^ (mp << 4);
        mp = mp ^ (mp << 8);
        mp = mp ^ (mp << 16);
        mp = mp ^ (mp << 32);
        mv = mp & m;
        m = m ^ mv | (mv >> (1 << i));
        t = x & mv;
        x = x ^ t | (t >> (1 << i));
        mk = mk & !mp;
    }
    x
}

fn compress_u32(x: u32, m: u32) -> u32 {
    let mut m: u32 = m;
    let mut x: u32 = x & m;
    let mut mk: u32 = !m << 1;
    let mut mp: u32;
    let mut mv: u32;
    let mut t: u32;

    for i in 0..6 {
        mp = mk ^ (mk << 1);
        mp = mp ^ (mp << 2);
        mp = mp ^ (mp << 4);
        mp = mp ^ (mp << 8);
        mp = mp ^ (mp << 16);
        mv = mp & m;
        m = m ^ mv | (mv >> (1 << i));
        t = x & mv;
        x = x ^ t | (t >> (1 << i));
        mk = mk & !mp;
    }
    x
}

// compress_left compress_u32(x,m) << (32-popcnt(m))
// SAG(x,m) = compress_left(x,m) | compress(x,!m)

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bitperm4_default() {
        let identity = Bitperm4::default();
        assert_eq!(identity.0, 0xff00f0f0ccccaaaa_u64);
    }

    #[test]
    fn test_bitperm4_cnot() {
        let identity = Bitperm4::default();
        assert_eq!(identity.cnot(0,1).cnot(0,1), identity);
    }

    #[test]
    fn test_bitperm4_compose() {
        let identity = Bitperm4::default();
        assert_eq!(identity.compose(identity), identity);
    }

    #[test]
    fn test_bitperm4_tt2idx() {
        let identity = Bitperm4::default();
        assert_eq!(Bitperm4::tt2idx(identity.0), 0xfedcba9876543210);
    }

    #[test]
    fn test_bitperm4_idx2tt() {
        let identity = Bitperm4::default();
        // TODO
        assert_eq!(Bitperm4::tt2idx(identity.0), 0xfedcba9876543210);
    }

    #[test]
    fn test_compress() {
        let identity = Bitperm4::default();
        assert_eq!(compress_u64(identity.0, identity.0), 0xffffffff_u64);
        assert_eq!(compress_u32(0xfedcba98, 0xfedcba98), 0xfffff_u32);
    }
}
