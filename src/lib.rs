#![feature(iter_next_chunk)]
// This is *just* for testing
// TODO: Move tests so this doesn't have to be in the main crate
#![feature(internal_output_capture)]
mod allocator;
mod errors;
mod memory;
pub mod vm;
