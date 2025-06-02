#![feature(const_trait_impl)]
#![feature(slice_partition_dedup)]
#![feature(isolate_most_least_significant_one)]


mod bitlib;
pub use crate::bitlib::*;

mod bitperm;
pub use crate::bitperm::*;

mod bitcube3;
pub use crate::bitcube3::*;

mod bitcube4;
pub use crate::bitcube4::*;

mod bittroc4;
pub use crate::bittroc4::*;

mod bitrhombdo4;
pub use crate::bitrhombdo4::*;

mod bitgrid8;
pub use crate::bitgrid8::*;

mod piece_bitgrid8;
pub use crate::piece_bitgrid8::*;
