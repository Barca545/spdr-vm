use std::{
  mem::transmute,
  ops::{Index, Not},
};

use spdr_isa::memory::STACK_SIZE;
#[derive(Debug, Clone, Copy, PartialEq,)]
/// Struct representing a 32bit or 4 byte block of memory in the
/// [`VM`](crate::vm::VM).
pub struct Memory(pub(crate) [u8; 4],);

impl Memory {
  /// Create a new `Memory`.
  pub const fn new() -> Self {
    Memory([0; 4],)
  }

  /// Translate the underlying bits of the input into an [`f32`].
  pub fn as_f32(self,) -> f32 {
    f32::from_bytes(self.0,)
  }

  /// Translate the underlying bits of the input into a [`bool`].
  pub fn as_bool(self,) -> bool {
    !([0; 4] == self.0)
  }

  /// Translate the underlying bits of the input into a [`u32`].
  pub fn as_u32(self,) -> u32 {
    u32::from_bytes(self.0,)
  }

  pub fn as_slab(self,) -> Slab {
    Slab::from_bytes(self.0,)
  }
}

impl From<f32,> for Memory {
  fn from(value:f32,) -> Self {
    Memory(value.to_le_bytes(),)
  }
}

impl From<u32,> for Memory {
  fn from(value:u32,) -> Self {
    Memory(value.to_le_bytes(),)
  }
}

impl From<bool,> for Memory {
  fn from(value:bool,) -> Self {
    match value {
      true => Memory([255; 4],),
      false => Memory([0; 4],),
    }
  }
}

impl From<usize,> for Memory {
  fn from(value:usize,) -> Self {
    Memory((value as u32).to_le_bytes(),)
  }
}

impl From<Slab,> for Memory {
  fn from(value:Slab,) -> Self {
    let ptr = value.addr.to_le_bytes();
    let meta = value.metadata;
    Memory([ptr[0], ptr[1], meta.size, meta.offset_excluded,],)
  }
}

impl Not for Memory {
  type Output = Memory;

  fn not(self,) -> Self::Output {
    match self.as_bool() {
      true => Memory([0; 4],),
      false => Memory([1; 4],),
    }
  }
}

impl Index<usize,> for Memory {
  type Output = u8;

  fn index(&self, index:usize,) -> &Self::Output {
    &self.0[index]
  }
}

/// A [contiguous piece of memory](https://en.wikipedia.org/wiki/Slab_allocation#Implementation_techniques) which stores address and metadata about a chunk of [`Memory`].
/// A Slab — this data structure not underlying allocation it owns — is sized
/// [u32;4] so it can fit in a single [`Memory`] cell.
#[derive(Debug, Clone, Copy, PartialEq,)]
pub struct Slab {
  /// The memory address of the first 32bit [memory cell](https://en.wikipedia.org/wiki/Memory_cell_(computing)) in the slab.
  pub(crate) addr:u16,
  /// The number of cells in the `Slab`'s underlying allocation.
  /// Stores the number as the underlying power of 2.
  pub(crate) metadata:SlabMetadata,
}

// TODO: The metadata should be a size and then another byte explaining

impl Slab {
  /// The largest number of cells a slab can hold.
  const MAX_SIZE:u16 = 256;

  /// Generate a new [`Slab`] which includes the stack offset
  /// as part of its pointer.
  pub fn new_with_offset_pointer(addr:u16, size:u16,) -> Self {
    // Reject as slab if the requested size is larger than the slab max size
    if size > Self::MAX_SIZE {
      panic!("The largest size as slab can be is 256 memory cells. {} is too big.", size)
    }

    // Convert the provided size into a power of 2
    // TODO: Is there a more efficent way to get the power of two corresponding to
    // the size?
    let size = size.ilog2() as u8;
    Self {
      addr,
      metadata:SlabMetadata { size, offset_excluded:0, },
    }
  }

  /// Generate a new [`Slab`] which includes the stack offset
  /// as a part of its metadata.
  pub fn new_with_meta_offset(addr:u16, size:u16,) -> Self {
    // Reject as slab if the requested size is larger than the slab max size
    if size > Self::MAX_SIZE {
      panic!("The largest size as slab can be is 256 memory cells. {} is too big.", size)
    }

    // Convert the provided size into a power of 2
    let size = size.ilog2() as u8;

    Slab {
      addr,
      metadata:SlabMetadata { size, offset_excluded:1, },
    }
  }

  /// Generate a new [`Slab`] which owns a single cell (a pointer);
  pub fn new_as_pointer(addr:u16,) -> Self {
    Self {
      addr,
      // Zero because the real size is 2^size and a pointer points to a single cell i.e. 2^1
      metadata:SlabMetadata { size:0, offset_excluded:0, },
    }
  }

  /// Return the address of the first cell in the underlying allocation the
  /// [`Slab`] owns.
  pub const fn ptr(&self,) -> usize {
    // Since the offset is stored as a 1 for true and 0 for false STACK_SIZE can
    // just be multiplied by it to avoid using an if statement
    self.addr as usize + STACK_SIZE * self.metadata.offset_excluded as usize
  }

  /// Return the size of the underlying allocation owned by the [`Slab`].
  pub fn size(&self,) -> usize {
    2u32.pow(self.metadata.size as u32,) as usize
  }
}

#[derive(Debug, Clone, Copy, PartialEq,)]
pub(crate) struct SlabMetadata {
  /// The size of the allocation the slab owns. Stored as "n" in the expression
  /// 2<sup>n</sup> = size.
  size:u8,
  /// A bool indicating whether the address in the Slab's associated pointer
  /// includes the stack offset. `true` if the pointer accounts for the stack
  /// offset, `false` otherwise.
  offset_excluded:u8,
}

/// Implemented by types which can be created from a [`Memory`] block.
pub trait FromBytes: Sized {
  /// Convert a bloc of memory into the target type.
  fn from_bytes(bytes:[u8; 4],) -> Self;
}

impl FromBytes for u32 {
  fn from_bytes(bytes:[u8; 4],) -> Self {
    u32::from_le_bytes(bytes,)
  }
}

impl FromBytes for f32 {
  fn from_bytes(bytes:[u8; 4],) -> Self {
    f32::from_le_bytes(bytes,)
  }
}

impl FromBytes for [u8; 4] {
  fn from_bytes(bytes:[u8; 4],) -> Self {
    bytes
  }
}

impl FromBytes for usize {
  fn from_bytes(bytes:[u8; 4],) -> Self {
    f32::from_le_bytes(bytes,) as usize
  }
}

impl FromBytes for Slab {
  fn from_bytes(bytes:[u8; 4],) -> Self {
    unsafe {
      Slab {
        addr:transmute::<[u8; 2], u16,>([bytes[0], bytes[1],],),
        metadata:SlabMetadata {
          size:bytes[2],
          offset_excluded:bytes[3],
        },
      }
    }
  }
}

#[cfg(test)]
mod test {
  use super::Slab;

  #[test]
  fn test_slab_size_is_correct() {
    let slab_1 = Slab::new_with_meta_offset(0, 16,);
    let slab_2 = Slab::new_with_meta_offset(0, 64,);
    let slab_3 = Slab::new_with_meta_offset(0, 128,);
    let slab_4 = Slab::new_with_meta_offset(0, 256,);

    assert_eq!(slab_1.size(), 16);
    assert_eq!(slab_2.size(), 64);
    assert_eq!(slab_3.size(), 128);
    assert_eq!(slab_4.size(), 256);
  }

  #[test]
  fn test_slab_pointer_is_correct() {
    let slab_1 = Slab::new_with_meta_offset(0, 16,);
    let slab_2 = Slab::new_with_offset_pointer(20, 16,);

    assert_eq!(slab_1.ptr(), 20);
    assert_eq!(slab_2.ptr(), 20);
  }

  #[test]
  fn test_slab_as_single_cell_pointer() {
    let slab = Slab::new_as_pointer(10,);
    assert_eq!(slab.ptr(), 10);
    assert_eq!(slab.size(), 1);
  }
}
