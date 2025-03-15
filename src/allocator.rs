use crate::memory::{Memory, Slab};

// Refactor:
// - Could do a linked list where each pointer is stored in the VM memory aside
// from head
// - Merge with the buddy system somehow? https://en.wikipedia.org/wiki/Buddy_memory_allocation
// - Could also explore using a bitmap?
// - Could use a more custom data struct than a vector. I am concerned about the
//   risk they might allocate multiple times.

/// Amount of [`Memory`] cells each [`Slab`] in the [`Allocator] owns.
pub(crate) const SLAB_SIZES:[u16; 4] = [16, 64, 128, 256,];

/// Number of [`Slab`]s in the [`Pool`] containing `Slab`s which own 16
/// [`Memory`] cells.
pub(crate) const POOL_16_SIZE:u16 = u16::MAX / 4;

/// Number of [`Slab`]s in the [`Pool`] containing `Slab`s which own 64
/// [`Memory`] cells.
pub(crate) const POOL_64_SIZE:u16 = u16::MAX / 2;

/// Number of [`Slab`]s in the [`Pool`] containing `Slab`s which own 128
/// [`Memory`] cells.
pub(crate) const POOL_128_SIZE:u16 = u16::MAX / 8;

/// Number of [`Slab`]s in the [`Pool`] containing `Slab`s which own 256
/// [`Memory`] cells.
pub(crate) const POOL_256_SIZE:u16 = u16::MAX / 8;

#[derive(Debug, Clone,)]
pub(crate) struct Pool {
  // TODO: I don't love using a vector instead of some sort of statically generated array
  // TODO: Ideally this could eventually be stored in the VM memory itself as a linked list or something
  inner:Vec<Slab,>,
}

impl Pool {
  // TODO: It occurs to me these don't need to be constants these could just be
  // arguments. Although, since they are constants doing it this way lets me
  // gaurantee they will be compiled that way.
  fn new<const CELL_SIZE: u16, const POOL_SIZE: u16,>(pool_offset:&mut u16,) -> Self {
    // Reversing it like this ensures the lower addressed slabs are at the beginning
    // of the pool. I don't think it matters much in the VM but in theory I believe
    // this is ideal.
    // TODO:They cannot all start with 0. Maybe make the function that gives the
    // index a public function and use it here
    let mut inner = Vec::with_capacity((POOL_SIZE / CELL_SIZE) as usize,);
    for addr in (*pool_offset..POOL_SIZE + *pool_offset).step_by(CELL_SIZE as usize,).rev() {
      inner.push(Slab::new_with_meta_offset(addr, CELL_SIZE,),);
    }

    // Add the new ammount the offset
    *pool_offset += POOL_SIZE;

    Pool { inner, }
  }

  /// Returns a [`Slab`] to the next free slab of the requested size.
  fn pop(&mut self,) -> Option<Slab,> {
    self.inner.pop()
  }

  fn push(&mut self, ptr:Slab,) {
    self.inner.push(ptr,);
  }

  #[cfg(test)]
  pub fn inner(&self,) -> Vec<Slab,> {
    self.inner.clone()
  }
}

/// `Allocator` stores 5 linked lists of [`Slab`]s to
/// [`Memory`](crate::memory::Memory) chunks of varied sizes.
/// - 16,384 16 cell chunks.
/// - 32,768 64 cell chunks.
/// - 81,92 128 cell chunks.
/// - 81,92 256 cell chunks.
/// The `Allocator` maintains a [free list](https://en.wikipedia.org/wiki/Free_list) for each [memory pool](https://en.wikipedia.org/wiki/Memory_pool).
#[derive(Debug,)]
pub struct Allocator {
  /// Array containing the [`Pool`]s of [`Slab`]s the `Allocator` will use.
  pools:[Pool; SLAB_SIZES.len()],
}

impl Allocator {
  /// Create a new [`Allocator`].
  pub fn new() -> Self {
    // Because each pool needs to be offset from the begining of the memory array by
    // the amount reserved for the previous pools
    let mut pool_offset = 0;
    Allocator {
      pools:[
        Pool::new::<16, POOL_16_SIZE,>(&mut pool_offset,),
        Pool::new::<64, POOL_64_SIZE,>(&mut pool_offset,),
        Pool::new::<128, POOL_128_SIZE,>(&mut pool_offset,),
        Pool::new::<256, POOL_256_SIZE,>(&mut pool_offset,),
      ],
    }
  }

  /// Allocate a [`Slab`] capable of holdin the requested amount of [`Memory`].
  pub fn alloc(&mut self, requested_size:u16,) -> Slab {
    let mut idx = match self.get_slab_index(requested_size,) {
      Some(idx,) => idx,
      None => panic!("Requested slab size {} does not exist. Max size is 256 cells.", requested_size),
    };
    while idx <= SLAB_SIZES.len() {
      match self.pools[idx].pop() {
        Some(ptr,) => return ptr,
        None => idx += 1,
      }
    }
    // If this point is reached it means there was no requested slab found
    panic!("No slabs found")
  }

  /// Move an existing allocation to a new [`Slab`] of [`Memory`].
  pub fn realloc(&mut self, mem:&mut [Memory], slab:&mut Slab, requested_size:u16,) {
    // Get a new slab
    let new_slab = self.alloc(requested_size,);

    mem.copy_within(slab.ptr()..slab.ptr() + slab.size(), new_slab.ptr(),);

    // Deallocate the old slab back
    self.dealloc(*slab,);

    // Update the slab to equal the new slab
    *slab = new_slab
  }

  /// Deallocate a [`Slab`]. Add it back to its [`Pool`] so it can be reused.
  pub fn dealloc(&mut self, slab:Slab,) {
    let idx = self.get_slab_index(slab.size() as u16,).unwrap();
    self.pools[idx].push(slab,);
  }

  /// Returns the index in [`SLAB_SIZES`] corresponding to the smallest [slab](https://en.wikipedia.org/wiki/Memory_pool) which can fit the requested allocation.
  fn get_slab_index(&self, requested_size:u16,) -> Option<usize,> {
    SLAB_SIZES.iter().position(|s| *s >= requested_size,)
  }

  #[cfg(test)]
  /// A function for accessing the private inner field of pools during testing.
  pub fn pools(&self,) -> [Pool; SLAB_SIZES.len()] {
    self.pools.clone()
  }
}

#[cfg(test)]
mod test {
  use super::Allocator;
  use crate::{
    allocator::{POOL_128_SIZE, POOL_16_SIZE, POOL_256_SIZE, POOL_64_SIZE},
    memory::{Memory, Slab},
    vm::VM,
  };

  const OFFSET_16:u16 = 0;
  const OFFSET_64:u16 = OFFSET_16 + POOL_16_SIZE;
  const OFFSET_128:u16 = OFFSET_64 + POOL_64_SIZE;
  const OFFSET_256:u16 = OFFSET_128 + POOL_128_SIZE;

  #[test]
  fn start_and_end_addresses_of_pools_are_correct() {
    let a = Allocator::new();

    // NOTE: Look the math here is correct a +1 is needed. I know if I don't say
    // this explicitly you will think it is a mistake and end up spending the 30min
    // I just did verifying that again.

    // NOTE: The +20 is needed because of the offset caused by the stack

    // Todo: Check the start addresses are correct
    assert_eq!(a.pools[0].inner.last().unwrap().ptr() as u32, OFFSET_16 as u32 + 20);
    assert_eq!(a.pools[1].inner.last().unwrap().ptr() as u32, OFFSET_64 as u32 + 20);
    assert_eq!(a.pools[2].inner.last().unwrap().ptr() as u32, OFFSET_128 as u32 + 20);
    assert_eq!(a.pools[3].inner.last().unwrap().ptr() as u32, OFFSET_256 as u32 + 20);

    // Check the end addresses are correct
    // NOTE: Subtract the slab size to get the addr of the start of the last slab
    assert_eq!(a.pools[0].inner[0].ptr() as u32, OFFSET_16 as u32 + POOL_16_SIZE as u32 - 16 + 1 + 20);
    assert_eq!(a.pools[1].inner[0].ptr() as u32, OFFSET_64 as u32 + POOL_64_SIZE as u32 - 64 + 1 + 20);
    assert_eq!(a.pools[2].inner[0].ptr() as u32, OFFSET_128 as u32 + POOL_128_SIZE as u32 - 128 + 1 + 20);
    assert_eq!(a.pools[3].inner[0].ptr() as u32, OFFSET_256 as u32 + POOL_256_SIZE as u32 - 256 + 1 + 20);
  }

  #[test]
  fn pools_have_correct_size() {
    let a = Allocator::new();
    assert_eq!((a.pools[0].inner.len() - 1) as u16, POOL_16_SIZE / 16);
    assert_eq!((a.pools[1].inner.len() - 1) as u16, POOL_64_SIZE / 64);
    assert_eq!((a.pools[2].inner.len() - 1) as u16, POOL_128_SIZE / 128);
    assert_eq!((a.pools[3].inner.len() - 1) as u16, POOL_256_SIZE / 256);
  }

  #[test]
  fn allocation_works_for_same_size() {
    let mut a = Allocator::new();
    // Try to get 3 slabs of the same size use innexact sizes to ensure the
    // bucketing works correctly
    let slab_1 = a.alloc(15,);
    let slab_2 = a.alloc(14,);
    let slab_3 = a.alloc(1,);

    assert_eq!(slab_1, Slab::new_with_meta_offset(0, 16));
    assert_eq!(slab_2, Slab::new_with_meta_offset(16, 16));
    assert_eq!(slab_3, Slab::new_with_meta_offset(32, 16));
  }

  // Try to get 2 slabs of differing sizes
  #[test]
  fn test_allocations_of_different_sizes() {
    let mut a = Allocator::new();

    let slab_1 = a.alloc(2,);
    let slab_2 = a.alloc(62,);
    let slab_3 = a.alloc(119,);
    let slab_4 = a.alloc(247,);

    // Check the correct slabs have been allocated
    assert_eq!(slab_1, Slab::new_with_meta_offset(OFFSET_16, 16));
    assert_eq!(slab_2, Slab::new_with_meta_offset(OFFSET_64, 64));
    assert_eq!(slab_3, Slab::new_with_meta_offset(OFFSET_128, 128));
    assert_eq!(slab_4, Slab::new_with_meta_offset(OFFSET_256, 256));
  }

  // Allocate 1 slabs from each pool to ensure they're removed
  #[test]
  fn allocation_removes_from_pool() {
    let mut a = Allocator::new();
    let _ = a.alloc(2,);
    let _ = a.alloc(62,);
    let _ = a.alloc(119,);
    let _ = a.alloc(247,);

    // Check the length of the slab pools to confirm they decreased
    assert_eq!((a.pools[0].inner.len() as u16), POOL_16_SIZE / 16);
    assert_eq!((a.pools[1].inner.len() as u16), POOL_64_SIZE / 64);
    assert_eq!((a.pools[2].inner.len() as u16), POOL_128_SIZE / 128);
    assert_eq!((a.pools[3].inner.len() as u16), POOL_256_SIZE / 256);
  }

  // Try to add one of the 3 slabs back to the pool (deallocate) and ensure
  // it is fetched correct
  #[test]
  fn deallocation_adds_to_the_pool() {
    let mut a = Allocator::new();

    let slab_1 = a.alloc(17,);

    a.dealloc(slab_1,);

    assert_eq!(a.pools[1].inner.last(), Some(&slab_1));
    assert_eq!(a.pools[1].inner.len() - 1, POOL_64_SIZE as usize / 64);
  }

  #[test]
  fn bits() {
    dbg!(u8::MAX.to_le_bytes());
    dbg!(u8::MAX);
    dbg!(u16::MAX);
  }

  #[test]
  fn reallocation_shifts_cells_properly() {
    let mut vm = VM::new();
    let mut a = Allocator::new();

    let mut slab = a.alloc(10,);

    // Confirm slab is correct
    assert_eq!(slab, Slab::new_with_meta_offset(0, 16));

    // Add data to the allocation
    vm.mem[slab.ptr()..slab.ptr() + 16].copy_from_slice(&[Memory(32.0f32.to_le_bytes(),); 16],);

    // Reallocate
    a.realloc(&mut vm.mem, &mut slab, 200,);

    // Confirm slab changed
    assert_eq!(slab, Slab::new_with_meta_offset(OFFSET_256, 256));

    // Confirm the new slab's allocation contains the correct, data
    assert_eq!(vm.mem[slab.ptr()..slab.ptr() + 16], [Memory(32.0f32.to_le_bytes(),); 16]);
  }

  #[test]
  #[should_panic = "Requested slab size 300 does not exist. Max size is 256 cells."]
  fn allocation_fails_when_requested_size_too_big() {
    let mut a = Allocator::new();

    let _ = a.alloc(300,);
  }
}
