use std::fmt;
use std::ops::*;

use flowscad::*;

use crate::bitlib::*;
use crate::bitcube4::BitCube4;

// -----------------------------------------------------------------
// Simple cubic lattice trait
// -----------------------------------------------------------------

pub trait LatticeCuboidCubicSimple {
    // type Space;

    fn rotate_x(&self) -> Self;
    fn shift_x(&self, shift: isize) -> Self;
    fn shift_y(&self, shift: isize) -> Self;
    fn shift_z(&self, shift: isize) -> Self;
    fn shift_xyz(&self, shift: [isize; 3]) -> Self;
    // fn cycle_x(&self) -> Self;
    // fn mirror_x(&self) -> Self;
    // fn min_corner(&self) -> [usize; 3];

}


#[derive(Copy, Clone, PartialEq)]
pub struct BC3(pub u32);

impl Iterator for BC3 {
    type Item = Self;

    fn next(&mut self) -> Option<Self::Item> {
        let grid:u64 = self.0.into();
        if grid != 0 {
            let bit:u64 = grid.isolate_lowest_one();
            *self = Self((grid ^ bit).try_into().unwrap());
            Some(Self(bit.try_into().unwrap()))
        } else {
            None
        }
    }
}

impl LatticeCuboidCubicSimple for BC3 {

    /// Easiest to visualize as a z-rotation, but same idea
    fn rotate_x(&self) -> Self { 
        let mut cube = self.0;
        // Swap vertical
        swap_mask_shift_u32(&mut cube, 0o777_u32, 18);
        // Swap main diagonal
        swap_mask_shift_u32(&mut cube, 0o700_u32, 12);
        // Swap outer diagonals
        swap_mask_shift_u32(&mut cube, 0o700_070_u32, 6);
        Self(cube)
    }

    fn shift_x(&self, shift: isize) -> Self { 
        match shift {
            0 => Self(self.0),
            1 => Self((self.0.unbounded_shl(1)) & 0o666_666_666_u32),
            2 => Self((self.0.unbounded_shl(2)) & 0o444_444_444_u32),
            -1 => Self((self.0.unbounded_shl(1)) & 0o333_333_333_u32),
            -2 => Self((self.0.unbounded_shl(2)) & 0o111_111_111_u32),
            _ => Self(0)
        }
    }

    fn shift_y(&self, shift: isize) -> Self { todo!() }
    fn shift_z(&self, shift: isize) -> Self { todo!() }
    fn shift_xyz(&self, shift: [isize; 3]) -> Self { todo!() }
}
