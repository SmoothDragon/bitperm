// -----------------------------------------------------------------
// 2D geometric operations on a 4×16 grid (four rows, sixteen columns)
// -----------------------------------------------------------------
// Position at (x, y) = x + 16 * y, with 0 <= x < 16 and 0 <= y < 4.
// The low bit is the lower-left cell; increasing x moves right, y moves up.

use std::fmt;

use derive_more::*;

use crate::traits::BitGrid;

pub const BITGRID_4X16_WIDTH: usize = 16;
pub const BITGRID_4X16_HEIGHT: usize = 4;

/// First column `x` of the horizontally centered 4×4 (`x` in `6..10`, all rows).
pub const BITGRID_4X16_CENTER_4X4_X0: usize = (BITGRID_4X16_WIDTH - 4) / 2;

/// Bits **outside** the center 4×4 (columns `x < 6` or `x > 9`). Quarter-turns are [`None`] if
/// `(grid & this).count_ones() != 0`.
pub const BITGRID_4X16_OUTSIDE_CENTER_4X4_MASK: u64 = 0xfc3f_fc3f_fc3f_fc3f_u64;

#[derive(
    Copy,
    Clone,
    Eq,
    PartialEq,
    Hash,
    PartialOrd,
    Ord,
    BitAnd,
    BitAndAssign,
    BitOr,
    BitOrAssign,
    BitXor,
    BitXorAssign,
)]
pub struct BitGrid4x16(pub u64);

impl core::ops::Shr<isize> for BitGrid4x16 {
    type Output = Self;

    fn shr(self, shift: isize) -> Self {
        let positive = shift >= 0;
        let shift: u32 = shift.unsigned_abs() as u32;
        if positive {
            Self(self.0.unbounded_shr(shift))
        } else {
            Self(self.0.unbounded_shl(shift))
        }
    }
}

impl core::ops::Shl<isize> for BitGrid4x16 {
    type Output = Self;

    fn shl(self, shift: isize) -> Self {
        let positive = shift >= 0;
        let shift: u32 = shift.unsigned_abs() as u32;
        if positive {
            Self(self.0.unbounded_shl(shift))
        } else {
            Self(self.0.unbounded_shr(shift))
        }
    }
}

impl core::ops::Not for BitGrid4x16 {
    type Output = Self;

    fn not(self) -> Self {
        Self(!self.0)
    }
}

impl core::ops::BitAnd<u64> for BitGrid4x16 {
    type Output = Self;

    fn bitand(self, rhs: u64) -> Self {
        Self(self.0 & rhs)
    }
}

impl core::ops::BitOr<u64> for BitGrid4x16 {
    type Output = Self;

    fn bitor(self, rhs: u64) -> Self {
        Self(self.0 | rhs)
    }
}

impl core::ops::BitXor<u64> for BitGrid4x16 {
    type Output = Self;

    fn bitxor(self, rhs: u64) -> Self {
        Self(self.0 ^ rhs)
    }
}

impl fmt::Debug for BitGrid4x16 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "BitGrid4x16({:#018x})", self.0)
    }
}

impl fmt::Display for BitGrid4x16 {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let s = (0..BITGRID_4X16_HEIGHT)
            .rev()
            .map(|y| {
                (0..BITGRID_4X16_WIDTH)
                    .map(|x| {
                        if (self.0 >> (x + BITGRID_4X16_WIDTH * y)) & 1 == 1 {
                            "🟥"
                        } else {
                            "⬜"
                        }
                    })
                    .collect::<String>()
                    + "\n"
            })
            .collect::<String>();
        write!(f, "{s}")
    }
}

impl From<u64> for BitGrid4x16 {
    fn from(raw_grid: u64) -> Self {
        BitGrid4x16(raw_grid)
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct BitGrid4x16PointsIter {
    remaining: u64,
}

impl Iterator for BitGrid4x16PointsIter {
    type Item = BitGrid4x16;

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None;
        }
        let bit = self.remaining.isolate_lowest_one();
        self.remaining ^= bit;
        Some(BitGrid4x16(bit))
    }
}

impl IntoIterator for BitGrid4x16 {
    type Item = BitGrid4x16;
    type IntoIter = BitGrid4x16PointsIter;

    fn into_iter(self) -> Self::IntoIter {
        BitGrid4x16PointsIter { remaining: self.0 }
    }
}

impl IntoIterator for &BitGrid4x16 {
    type Item = BitGrid4x16;
    type IntoIter = BitGrid4x16PointsIter;

    fn into_iter(self) -> Self::IntoIter {
        BitGrid4x16PointsIter { remaining: self.0 }
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct BitGrid4x16PointCoordsIter {
    remaining: u64,
}

impl Iterator for BitGrid4x16PointCoordsIter {
    type Item = (usize, usize);

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining == 0 {
            return None;
        }
        let bit = self.remaining.isolate_lowest_one();
        self.remaining ^= bit;
        let idx = bit.trailing_zeros() as usize;
        Some((idx % BITGRID_4X16_WIDTH, idx / BITGRID_4X16_WIDTH))
    }
}

impl BitGrid for BitGrid4x16 {
    type BitsIter = BitGrid4x16PointsIter;
    type CoordsIter = BitGrid4x16PointCoordsIter;

    fn bit_at(x: usize, y: usize) -> Self {
        Self(1_u64 << (x + BITGRID_4X16_WIDTH * y))
    }

    /// Flip across the horizontal midline: `y -> 3 - y`.
    fn mirror_x(&self) -> Self {
        let mut out = 0_u64;
        for y in 0..BITGRID_4X16_HEIGHT {
            let row = (self.0 >> (BITGRID_4X16_WIDTH * y)) & 0xffff;
            let ny = BITGRID_4X16_HEIGHT - 1 - y;
            out |= row << (BITGRID_4X16_WIDTH * ny);
        }
        Self(out)
    }

    /// Mirror across the vertical midline: `x -> 15 - x` (per row).
    fn mirror_y(&self) -> Self {
        let mut out = 0_u64;
        for y in 0..BITGRID_4X16_HEIGHT {
            let row = ((self.0 >> (BITGRID_4X16_WIDTH * y)) & 0xffff) as u16;
            let row = row.reverse_bits() as u64;
            out |= row << (BITGRID_4X16_WIDTH * y);
        }
        Self(out)
    }

    fn rotate_c2(&self) -> Self {
        let mut out = 0_u64;
        let mut g = self.0;
        while g != 0 {
            let bit = g.isolate_lowest_one();
            g ^= bit;
            let i = bit.trailing_zeros() as usize;
            let x = i % BITGRID_4X16_WIDTH;
            let y = i / BITGRID_4X16_WIDTH;
            let nx = BITGRID_4X16_WIDTH - 1 - x;
            let ny = BITGRID_4X16_HEIGHT - 1 - y;
            out |= 1_u64 << (nx + BITGRID_4X16_WIDTH * ny);
        }
        Self(out)
    }

    fn try_rotate_c4(&self, steps: isize) -> Option<Self> {
        match steps.rem_euclid(4) {
            0 => Some(*self),
            2 => Some(self.rotate_c2()),
            1 => self.try_quarter_ccw(),
            3 => self.try_quarter_cw(),
            _ => unreachable!(),
        }
    }

    fn shift_x(&self, shift: isize) -> Self {
        if !(-15..=15).contains(&shift) {
            return Self(0);
        }
        if shift == 0 {
            return *self;
        }
        let sign = shift > 0;
        let shift: u32 = shift.unsigned_abs() as u32;
        let row_mask = (1_u64 << (BITGRID_4X16_WIDTH as u32 - shift)) - 1;
        let mut mask = 0_u64;
        for y in 0..BITGRID_4X16_HEIGHT {
            mask |= row_mask << (BITGRID_4X16_WIDTH * y);
        }
        if sign {
            Self((mask & self.0).unbounded_shl(shift))
        } else {
            Self(mask & self.0.unbounded_shr(shift))
        }
    }

    fn shift_y(&self, shift: isize) -> Self {
        if !(-3..=3).contains(&shift) {
            return Self(0);
        }
        if shift == 0 {
            return *self;
        }
        let sign = shift > 0;
        let shift_bits: u32 = (shift.unsigned_abs() as u32).saturating_mul(BITGRID_4X16_WIDTH as u32);
        let mask: u64 = u64::MAX.unbounded_shr(shift_bits);
        if sign {
            Self((mask & self.0).unbounded_shl(shift_bits))
        } else {
            Self(mask & self.0.unbounded_shr(shift_bits))
        }
    }

    fn cycle_x(&self, shift: isize) -> Self {
        let shift = shift.rem_euclid(BITGRID_4X16_WIDTH as isize) as u32;
        if shift == 0 {
            return *self;
        }
        let mut out = 0_u64;
        for y in 0..BITGRID_4X16_HEIGHT {
            let row = ((self.0 >> (BITGRID_4X16_WIDTH * y)) & 0xffff) as u16;
            let rotated = row.rotate_left(shift);
            out |= (rotated as u64) << (BITGRID_4X16_WIDTH * y);
        }
        Self(out)
    }

    fn cycle_y(&self, shift: isize) -> Self {
        let shift = shift.rem_euclid(BITGRID_4X16_HEIGHT as isize) as u32;
        if shift == 0 {
            return *self;
        }
        let mut out = 0_u64;
        for x in 0..BITGRID_4X16_WIDTH {
            let mut col = 0_u8;
            for y in 0..BITGRID_4X16_HEIGHT {
                if (self.0 >> (x + BITGRID_4X16_WIDTH * y)) & 1 != 0 {
                    col |= 1 << y;
                }
            }
            let rotated = ((col << shift) | (col >> (BITGRID_4X16_HEIGHT as u32 - shift))) & 0xf;
            for y in 0..BITGRID_4X16_HEIGHT {
                if (rotated >> y) & 1 != 0 {
                    out |= 1_u64 << (x + BITGRID_4X16_WIDTH * y);
                }
            }
        }
        Self(out)
    }

    fn iterate_bits(&self) -> Self::BitsIter {
        BitGrid4x16PointsIter { remaining: self.0 }
    }

    fn iterate_coords(&self) -> Self::CoordsIter {
        BitGrid4x16PointCoordsIter { remaining: self.0 }
    }
}

impl BitGrid4x16 {
    /// `true` if any set bit lies outside the center 4×4 (`x < 6` or `x > 9`).
    #[inline]
    pub fn has_bits_outside_center_4x4(self) -> bool {
        (self.0 & BITGRID_4X16_OUTSIDE_CENTER_4X4_MASK).count_ones() != 0
    }

    /// 90° counterclockwise within the **center** 4×4 ([`BITGRID_4X16_CENTER_4X4_X0`]..). [`None`]
    /// if any bit lies outside that block ([`Self::has_bits_outside_center_4x4`]).
    ///
    /// Two successful CCW quarter turns match [`BitGrid::rotate_c2`] on the same pattern.
    pub fn try_quarter_ccw(self) -> Option<Self> {
        if self.has_bits_outside_center_4x4() {
            return None;
        }
        let x0 = BITGRID_4X16_CENTER_4X4_X0;
        let mut out = 0_u64;
        let mut g = self.0;
        while g != 0 {
            let bit = g.isolate_lowest_one();
            g ^= bit;
            let i = bit.trailing_zeros() as usize;
            let x = i % BITGRID_4X16_WIDTH;
            let y = i / BITGRID_4X16_WIDTH;
            let rx = x - x0;
            debug_assert!(rx < 4);
            // Local CCW on 4×4: (rx, y) -> (y, 3 - rx); `nx = x0 + y`, `ny = 3 - (x - x0)`.
            let nx = x0 + y;
            let ny = x0 + 3 - x;
            out |= 1_u64 << (nx + BITGRID_4X16_WIDTH * ny);
        }
        Some(Self(out))
    }

    /// 90° clockwise within the center 4×4. [`None`] if any bit lies outside that block.
    pub fn try_quarter_cw(self) -> Option<Self> {
        if self.has_bits_outside_center_4x4() {
            return None;
        }
        let x0 = BITGRID_4X16_CENTER_4X4_X0;
        let mut out = 0_u64;
        let mut g = self.0;
        while g != 0 {
            let bit = g.isolate_lowest_one();
            g ^= bit;
            let i = bit.trailing_zeros() as usize;
            let x = i % BITGRID_4X16_WIDTH;
            let y = i / BITGRID_4X16_WIDTH;
            let rx = x - x0;
            debug_assert!(rx < 4);
            // Local CW: (rx, y) -> (3 - y, rx); absolute x = x0 + (3 - y).
            let nx = x0 + 3 - y;
            let ny = x - x0;
            out |= 1_u64 << (nx + BITGRID_4X16_WIDTH * ny);
        }
        Some(Self(out))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::traits::BitGrid;

    #[inline]
    fn bit_at(x: usize, y: usize) -> BitGrid4x16 {
        <BitGrid4x16 as BitGrid>::bit_at(x, y)
    }

    #[test]
    fn rotate_c2_involution() {
        let g = bit_at(0, 0) | bit_at(15, 3);
        assert_eq!(g.rotate_c2().rotate_c2(), g);
        assert_eq!(bit_at(0, 0).rotate_c2(), bit_at(15, 3));
    }

    #[test]
    fn try_quarter_ccw_fails_when_bits_outside_center_4x4() {
        assert!(bit_at(0, 0).try_rotate_c4(1).is_none());
        assert!(bit_at(5, 0).try_rotate_c4(1).is_none());
        assert!(bit_at(10, 0).try_rotate_c4(1).is_none());
        assert!(bit_at(15, 3).try_rotate_c4(1).is_none());
        assert_eq!(bit_at(6, 0).try_rotate_c4(1), Some(bit_at(6, 3)));
    }

    #[test]
    fn try_quarter_ccw_center_4x4() {
        // (7, 0): local (1,0) --CCW--> (0, 2) -> absolute (6, 2).
        let c = bit_at(7, 0);
        assert_eq!(c.try_rotate_c4(1).unwrap(), bit_at(6, 2));
    }

    #[test]
    fn try_rotate_c4_two_steps_matches_rotate_c2() {
        let c = bit_at(8, 1);
        assert_eq!(c.try_rotate_c4(2), Some(c.rotate_c2()));
        assert_eq!(
            c.try_rotate_c4(1).and_then(|d| d.try_rotate_c4(1)),
            Some(c.rotate_c2())
        );
    }

    #[test]
    fn try_quarter_cw_ccw_roundtrip_center_4x4() {
        let g = bit_at(7, 0) | bit_at(8, 1);
        assert_eq!(
            g.try_quarter_cw()
                .and_then(|h| h.try_quarter_ccw()),
            Some(g)
        );
    }

    #[test]
    fn cycle_x_wraps_row() {
        assert_eq!(bit_at(0, 0).cycle_x(-1), bit_at(15, 0));
        assert_eq!(bit_at(15, 0).cycle_x(1), bit_at(0, 0));
    }

    #[test]
    fn cycle_y_wraps_column() {
        assert_eq!(bit_at(0, 0).cycle_y(-1), bit_at(0, 3));
        assert_eq!(bit_at(0, 3).cycle_y(1), bit_at(0, 0));
    }

    #[test]
    fn mirror_x_y() {
        let g = bit_at(0, 0) | bit_at(15, 3);
        assert_eq!(g.mirror_x(), bit_at(0, 3) | bit_at(15, 0));
        assert_eq!(bit_at(0, 0).mirror_y(), bit_at(15, 0));
    }

    #[test]
    fn shift_clips() {
        assert_eq!(bit_at(15, 0).shift_x(1), BitGrid4x16(0));
        assert_eq!(bit_at(0, 3).shift_y(1), BitGrid4x16(0));
    }
}
