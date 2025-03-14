use std::{mem::transmute, ops::Not};
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
    f32::from_le_bytes(self.0,)
  }

  /// Translate the underlying bits of the input into a [`bool`].
  pub fn as_bool(self,) -> bool {
    !([0; 4] == self.0)
  }

  /// Translate the underlying bits of the input into a [`u32`].
  pub fn as_u32(self,) -> u32 {
    u32::from_le_bytes(self.0,)
  }

  /// Translate the underlying bits of the input into a [`usize`].
  pub fn as_usize(self,) -> usize {
    u32::from_le_bytes(self.0,) as usize
  }

  pub fn as_ptr(self,) -> Slab {
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
    Memory([ptr[0], ptr[1], 0, 0,],)
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

/// A [contiguous piece of memory](https://en.wikipedia.org/wiki/Slab_allocation#Implementation_techniques) which stores address and metadata about a chunk of [`Memory`].
/// A Slab — this data structure not underlying allocation it owns — is sized
/// [u32;4] so it can fit in a single [`Memory`] cell.
#[derive(Debug, Clone, Copy, PartialEq,)]
pub struct Slab {
  /// The memory address of the first 32bit [memory cell](https://en.wikipedia.org/wiki/Memory_cell_(computing)) in the slab.
  pub(crate) addr:u16,
  /// The number of cells in the `Slab`'s underlying allocation.
  pub(crate) metadata:u16,
}

impl Slab {
  /// Return the address of the first cell in the underlying allocation the
  /// [`Slab`] owns.
  pub const fn ptr(&self,) -> usize {
    // Add a 20 offset to account for the stack
    // Can't have it as a par of a constant in the allocator or slabs because they
    // need to be u16s so the higher end address values can't hold u16::MAX + 20
    self.addr as usize + 20
  }

  /// Return the size of the underlying allocation owned by the [`Slab`].
  pub fn size(&self,) -> usize {
    self.metadata as usize
  }
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
        metadata:transmute::<[u8; 2], u16,>([bytes[2], bytes[3],],),
      }
    }
  }
}
