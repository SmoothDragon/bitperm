#![feature(const_trait_impl)]
#![feature(slice_partition_dedup)]
#![feature(isolate_most_least_significant_one)]

#[allow(dead_code)]
fn print_type<T: std::fmt::Display>(x: &T) { 
    println!("{} {:?}", x, std::any::type_name::<T>());
}


pub mod bitlib;
pub mod bitperm;

pub mod bitcube3;
pub mod bitcube4;
pub mod bitcube8;

pub mod bitrhombdo4;
pub use crate::bitrhombdo4::*;

pub mod bittroc4;
pub use bittroc4::BitTroc4;
pub mod bittroc4_full;

pub mod bitgrid8;
pub mod piece_bitgrid8;
pub mod pack_bitgrid8;

pub mod bitmatrix8;

mod convert;
mod traits;
pub use traits::lattice_cubic_simple::LatticeCuboidCubicSimple;

pub use bitcube3::BitCube3;
pub use bitcube4::BitCube4;

// TODO: activate these
// mod bithex8;
// pub use crate::bithex8::*;

// mod bitpara8;
// pub use crate::bitpara8::*;

