# bitperm
Bit Permutations in Rust

cargo bench --baseline

TODO:
Extend bit operations to 8-bit matrices over u64.
Benchmark inversions
Understand how to use Nonzero to make Option<matrix> only take up u64 space.

Convert from truth table to polynomials for 4 bit perms
Convert from truth table to polynomials for 5 bit perms

BitTrocCube3 - 2 cube offset inside 3 cube
BitTrocCube4 - 3 cube offset inside 4 cube
BitTrocOcta2 - 1x1 plates extending through each face of 2x2x2 cube
BitTrocOcta3 - 2x2 plates extending through each face of 3x3x3 cube
Add to_scad for BitTrocs
