// -----------------------------------------------------------------
// Shared API for bit-packed 2D grids (single bit per cell).
// -----------------------------------------------------------------

use core::cmp::{Ord, PartialOrd};
use core::hash::Hash;
use core::ops::{
    BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign,
};

/// Operations on a finite grid where each cell is 0 or 1 and geometry is 2D.
///
/// Iterator outputs use **associated types** so each implementor can name its
/// concrete iterator (trait methods cannot return `impl Iterator` without
/// return-position `impl Trait` in traits, which is newer and still awkward for
/// multiple methods).
///
/// Supertraits match [`crate::bitgrid_8x8::BitGrid8x8`]'s derives so generic code can
/// rely on the same comparisons, hashing, ordering, and bitwise grid algebra.
pub trait BitGrid:
    Copy
    + Clone
    + PartialEq
    + Eq
    + Hash
    + PartialOrd
    + Ord
    + BitAnd<Output = Self>
    + BitAndAssign
    + BitOr<Output = Self>
    + BitOrAssign
    + BitXor<Output = Self>
    + BitXorAssign
{
    /// Yields each **set** cell as a grid value containing exactly one bit
    /// (same convention as `BitGrid8x8::into_iter()`).
    type BitsIter: Iterator<Item = Self>;

    /// Yields `(x, y)` coordinates of each **set** cell, with origin at the
    /// lower-left (same indexing as `BitGrid8x8`: bit index `x + 8 * y`).
    type CoordsIter: Iterator<Item = (usize, usize)>;

    fn mirror_x(&self) -> Self;
    fn mirror_y(&self) -> Self;
    fn rotate_c4(&self, steps: isize) -> Self;
    fn shift_x(&self, shift: isize) -> Self;
    fn shift_y(&self, shift: isize) -> Self;

    /// Cyclic (torus) shift along **x**: each row rotates independently.
    fn cycle_x(&self, shift: isize) -> Self;

    /// Cyclic (torus) shift along **y**: each column rotates independently.
    fn cycle_y(&self, shift: isize) -> Self;

    fn iterate_bits(&self) -> Self::BitsIter;
    fn iterate_coords(&self) -> Self::CoordsIter;
}
