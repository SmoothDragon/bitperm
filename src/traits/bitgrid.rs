// -----------------------------------------------------------------
// Shared API for bit-packed 2D grids (single bit per cell).
// -----------------------------------------------------------------

/// Operations on a finite grid where each cell is 0 or 1 and geometry is 2D.
///
/// Iterator outputs use **associated types** so each implementor can name its
/// concrete iterator (trait methods cannot return `impl Iterator` without
/// return-position `impl Trait` in traits, which is newer and still awkward for
/// multiple methods).
pub trait BitGrid: Copy + Clone + Eq {
    /// Yields each **set** cell as a grid value containing exactly one bit
    /// (same convention as `BitGrid8::into_iter()`).
    type BitsIter: Iterator<Item = Self>;

    /// Yields `(x, y)` coordinates of each **set** cell, with origin at the
    /// lower-left (same indexing as `BitGrid8`: bit index `x + 8 * y`).
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
