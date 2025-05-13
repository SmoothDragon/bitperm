# bitperm
Bit Permutations in Rust

# Construction
cargo add derive_more -F add,add_assign,from
cargo bench --baseline


# TODO BitGrid:
Extend bit operations to 8-bit matrices over u64.
Separate OriginBitGrid8 from BitGrid8 (different files that respect boundary and use deref)

# General TODO
Benchmark inversions
Understand how to use Nonzero to make Option<matrix> only take up u64 space.
BitTrocCube3 - 2 cube offset inside 3 cube
BitTrocCube4 - 3 cube offset inside 4 cube
BitTrocOcta2 - 1x1 plates extending through each face of 2x2x2 cube
BitTrocOcta3 - 2x2 plates extending through each face of 3x3x3 cube
Add to_scad for BitTrocs


# Notes of things to be done for useful BitPerm library
# TODO BitPerm:
Trait BitPerm
- identity
- inverse
- composition
- display, debug
- tryFromArray
- Double coset equivalence
- toArray


Convert from truth table to polynomials for 4 bit perms
Convert from truth table to polynomials for 5 bit perms

Bit Permutation:
basis fixing
Exhaust of affine conjugation that fixes as many weight 2 vectors as possible.
6-bit permutation with [u64; 6]

TODO:
4 bit interleave - 

x = 0x00ff&x + (0xff00)<<(32-8)
x = 0x0f0f&x + (0xf0f0)<<(16-4)
x = 0x3333&x + (0xcccc)<<(8-2)
x = 0x5555&x + (0xaaaa)<<(4-1)

13 ops for lookup
p[a] = (p4.0 >> (4*a)) & 1
p[a] ^= ((p4.1 >> (4*a)) & 1) << 1
p[a] ^= ((p4.2 >> (4*a)) & 1) << 2
p[a] ^= ((p4.3 >> (4*a)) & 1) << 3
