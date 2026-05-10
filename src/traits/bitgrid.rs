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
///
/// **Half-turn** ([`BitGrid::rotate_c2`]) is about the **center of the full grid** for
/// [`crate::bitgrid_8x8::BitGrid8x8`] and [`crate::bitgrid_4x16::BitGrid4x16`].
///
/// **Quarter-turns** ([`BitGrid::try_rotate_c4`]) depend on the type: on a square grid they are
/// in-place about the center; on [`crate::bitgrid_4x16::BitGrid4x16`] they rotate the horizontally
/// centered 4×4 and return [`None`] if any bit lies outside that block. Two successful quarter turns
/// match [`BitGrid::rotate_c2`] on that type. Square grids always return [`Some`] for quarter-turns.
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
    /// lower-left (`BitGrid8x8`: index `x + 8 * y`; `BitGrid4x16`: index `x + 16 * y`).
    type CoordsIter: Iterator<Item = (usize, usize)>;

    /// Grid with exactly one **set** bit at `(x, y)` (`iterate_coords()` convention).
    fn bit_at(x: usize, y: usize) -> Self;

    fn mirror_x(&self) -> Self;
    fn mirror_y(&self) -> Self;

    /// Half-turn (180°) about the grid center; always defined for rectangular grids.
    fn rotate_c2(&self) -> Self;

    /// Net quarter-turns: `steps` modulo 4, CCW positive. Semantics are type-specific (see trait
    /// docs). [`None`] when the operation is not defined for the current pattern (e.g. bits outside
    /// the rotatable region on [`crate::bitgrid_4x16::BitGrid4x16`]).
    fn try_rotate_c4(&self, steps: isize) -> Option<Self>;

    fn shift_x(&self, shift: isize) -> Self;
    fn shift_y(&self, shift: isize) -> Self;

    /// Cyclic (torus) shift along **x**: each row rotates independently.
    fn cycle_x(&self, shift: isize) -> Self;

    /// Cyclic (torus) shift along **y**: each column rotates independently.
    fn cycle_y(&self, shift: isize) -> Self;

    fn iterate_bits(&self) -> Self::BitsIter;
    fn iterate_coords(&self) -> Self::CoordsIter;
}
