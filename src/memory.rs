use std::ops::Not;

#[derive(Debug, Clone, Copy, PartialEq,)]
/// Struct representing a 32bit or 4 byte block of memory in the
/// [`VM`](crate::vm::VM).
pub(crate) struct Memory(pub(crate) [u8; 4],);

impl Memory {
  /// Create a new `Memory`.
  pub(crate) fn new() -> Self {
    Memory([0; 4],)
  }

  /// Translate the underlying bits of the input into an [`f32`].
  pub(crate) fn as_f32(self,) -> f32 {
    f32::from_le_bytes(self.0,)
  }

  /// Translate the underlying bits of the input into a [`bool`].
  pub(crate) fn as_bool(self,) -> bool {
    !([0; 4] == self.0)
  }

  /// Translate the underlying bits of the input into a [`u32`].
  pub(crate) fn as_u32(self,) -> u32 {
    u32::from_le_bytes(self.0,)
  }

  /// Translate the underlying bits of the input into a [`usize`].
  pub(crate) fn as_usize(self,) -> usize {
    self.0[0] as usize
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

impl Not for Memory {
  type Output = Memory;

  fn not(self,) -> Self::Output {
    match self.as_bool() {
      true => Memory([0; 4],),
      false => Memory([1; 4],),
    }
  }
}

/// Implemented by types which can be created from a [`Memory`] block.
pub(crate) trait FromBytes: Sized {
  /// Convert a bloc of memory into the target type.
  fn from(bytes:[u8; 4],) -> Self;
}

impl FromBytes for u32 {
  fn from(bytes:[u8; 4],) -> Self {
    u32::from_le_bytes(bytes,)
  }
}

impl FromBytes for f32 {
  fn from(bytes:[u8; 4],) -> Self {
    f32::from_le_bytes(bytes,)
  }
}

impl FromBytes for [u8; 4] {
  fn from(bytes:[u8; 4],) -> Self {
    bytes
  }
}

impl FromBytes for usize {
  fn from(bytes:[u8; 4],) -> Self {
    f32::from_le_bytes(bytes,) as usize
  }
}
