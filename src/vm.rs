use crate::{
  allocator::Allocator,
  errors::VMErrors,
  memory::{FromBytes, Memory},
};
use eyre::Result;
use num_traits::FromPrimitive;
use spdr_isa::{
  memory::{MEM_SIZE, STACK_SIZE},
  opcodes::{CmpFlag, OpCode},
  program::Program,
  registers::{EQ, PC, REG_COUNT, SP},
};
use std::{any::Any, io::Write, mem::transmute};

// Refactor:
// - I either need to add GEQ/LEQ opcodes or just have one CMP instruction which
//   takes a flag to indicate which operation it is doing.

/// # The Galaxy Virtual Machine
///
/// ## Specs
/// - Little endian.
/// - 255 four (4) byte registers.
/// - Memory with a 20 byte stack.
/// - Program counter register indexed by [`PC`], a `u32` value.
/// - Stack pointer register indexed by [`SP`], a `u32` value.
/// - Stack grows downwards.
/// - 16bit address space meaning 254Kb of total memory.
///
/// ## Calling convention
/// - Caller cleans: The caller is responsible for placing arguments on the
///   stack and removing any arguments and returns from the stack.
/// - For non-recursive functions, the first ten (10) arguments are passed into
///   the function registers. After the first ten, the registers are pushed onto
///   the stack.
/// - For recursive functions, all arguments are pushed onto the stack.
///
/// ### Using a stack frame
/// - [`Push`](OpCode::Push) the arguments onto the stack right to left.
/// - Before using [`Call`](OpCode::Call), `Push` the return address onto the
///   stack.
/// - Arguments are fetched from the stack by adding their distance from the
///   stack pointer e.g. `arg_1 = sp + 1`.
/// - [`Pop`](OpCode::Pop) the args off the stack and `Push` any return values
///   onto the stack in right to left order
///
/// ### Clearing a stack frame
/// [`Ret`](OpCode::Ret) accepts the number of items to pop from the stack.
pub struct VM {
  /// Tracks whether the VM is running a script.
  running:bool,
  /// An array of 255 4 byte registers.
  /// - R0 is the [`Program Counter`](https://en.wikipedia.org/wiki/Program_counter).
  /// - R1 is the [`Stack Pointer`](https://en.wikipedia.org/wiki/Stack_register).
  /// - R2 stores the result of equality checks.
  /// - R4-R14 store function arguments and returns. Functions with more than
  ///   ten (10) arguments or returns should place their arguments/returns on
  ///   the stack.
  reg:[Memory; REG_COUNT as usize],
  /// Memory holding 4 bytes per slot.
  ///
  /// The Stack is slots MEM19-MEM0. Grows downwards.
  pub(crate) mem:[Memory; MEM_SIZE],
  allocator:Allocator,
  /// The currently executing program.
  program:Program,
  /// External function pointers used for [`OpCode::SysCall`]s.
  externs:Vec<fn(vm:&mut VM, &mut dyn Any,),>,
}

impl VM {
  pub fn new() -> Self {
    let mut vm = VM {
      running:false,
      reg:[Memory::new(); REG_COUNT as usize],
      mem:[Memory::new(); MEM_SIZE],
      allocator:Allocator::new(),
      program:Program::new(),
      // Free starts on the 20th slot in memory because the first 19 are taken
      // up by the stack
      externs:Vec::new(),
    };

    // Update the stack pointer in the VM since it needs to start at 20 (Empty
    // stack)
    vm.reg[SP] = Memory::from(20u32,);

    // Return the VM
    vm
  }

  /// Return a reference to the VM's `running` field.
  pub fn running(&self,) -> &bool {
    &self.running
  }

  /// Return a reference to the VM's registers.
  pub fn reg(&self,) -> &[Memory; REG_COUNT] {
    &self.reg
  }

  /// Return a reference to the VM's mem.
  pub fn mem(&self,) -> &[Memory; MEM_SIZE] {
    &self.mem
  }

  /// Get an immutable reference to the PC register [`PC`].
  #[inline(always)]
  pub fn pc(&self,) -> &Memory {
    &self.reg[PC]
  }

  /// Get a mutable reference to the PC register [`PC`].
  #[inline(always)]
  fn pc_mut(&mut self,) -> &mut Memory {
    &mut self.reg[PC]
  }

  /// Get an immutable reference to the SP register [`SP`].
  #[inline(always)]
  pub fn sp(&self,) -> &Memory {
    &self.reg[SP]
  }

  /// Helper function to manage decrementing the stack pointer.
  #[inline(always)]
  fn stack_dec(&mut self, amt:u32,) -> Result<(),> {
    // Stack underflow occurs if we try to remove from an empty stack
    if self.sp().as_u32() == STACK_SIZE as u32 {
      return Err(VMErrors::EmptyStack.into(),);
    }
    // Decrement the SP (grows downards so add amt)
    self.reg[SP] = Memory::from(self.sp().as_u32() + amt,);
    Ok((),)
  }

  #[inline(always)]
  /// Helper function to manage incrementing the stack pointer.
  fn stack_inc(&mut self, amt:u32,) -> Result<(),> {
    if self.sp().as_u32() == 0 {
      return Err(VMErrors::StackOverflow.into(),);
    }
    // Increment the SP (grows downards so subtract one)
    self.reg[SP] = Memory::from(self.sp().as_u32() - amt,);

    Ok((),)
  }

  /// Retrieves the next byte in the program.
  fn next_byte(&mut self,) -> u8 {
    let byte = self.program[self.pc().as_u32()];

    *self.pc_mut() = Memory::from(self.pc().as_u32() + 1,);

    byte
  }

  fn next_4_bytes<T:FromBytes,>(&mut self,) -> T {
    let bytes = [
      self.program[self.pc().as_u32()],
      self.program[self.pc().as_u32() + 1],
      self.program[self.pc().as_u32() + 2],
      self.program[self.pc().as_u32() + 3],
    ];

    // Increment the pc
    *self.pc_mut() = Memory::from(self.pc().as_u32() + 4,);

    // Return the bytes
    T::from_bytes(bytes,)
  }

  /// Place an external value onto the top of the [`VM`]'s stack.
  pub fn extern_push<V,>(&mut self, value:V,)
  where Memory: From<V,> {
    // Get increment the SP to the next open slot
    self.stack_inc(1,).unwrap();
    // Place the value where SP points
    self.mem[self.sp().as_u32() as usize] = value.into();
  }

  /// Remove a value from the [`VM`]'s stack and return it or [`None`] if the
  /// stack was empty.
  ///
  /// # Warning
  ///
  /// This will almost certainly cause errors if used. SPDR uses a caller-cleans
  /// calling convention so it does not expect a function to remove
  /// from the stack.
  pub fn extern_pop(&mut self,) -> Option<Memory,> {
    let sp = self.sp().as_u32();
    // If the SP is at the top of the stack the stack is empty.
    if sp == STACK_SIZE as u32 {
      None
    }
    else {
      // Return the value at the current SP then decrement it to point at the next
      // item on the stack
      let val = self.mem[sp as usize];
      Some(val,)
    }
  }

  /// Read a value from the [`VM`]'s stack and return it or [`None`] if the
  /// stack was empty or `loc` exceeds the bounds of the stack. `loc` indicates
  /// where in the stack to read from.
  ///
  /// # Warning
  ///
  /// Does not actually mutate the stack because SPDR uses a caller-cleans
  /// calling convention so it does not expect a function to remove
  /// from the stack.
  pub fn extern_read(&mut self, loc:usize,) -> Option<Memory,> {
    // Confirm loc is within the bounds of the stack
    if loc >= STACK_SIZE {
      None
    }
    else {
      // Return the value at the current SP then decrement it to point at the next
      // item on the stack
      let val = self.mem[loc];
      Some(val,)
    }
  }

  fn decode(&mut self,) -> OpCode {
    let op_byte = self.program[self.pc().as_u32()];
    let op = OpCode::from_u8(op_byte,).expect(&format!("{}", VMErrors::UnknownOpcode(op_byte, self.pc().as_u32(),)),);

    *self.pc_mut() = Memory::from(self.pc().as_u32() + 1,);
    op
  }

  /// Register an external function in the `VM`.
  pub fn register_extern(&mut self, ext_fn:fn(vm:&mut VM, &mut dyn Any,),) {
    self.externs.push(ext_fn,);
  }

  /// Execute the next instruction of the [`Program`].
  fn execute(&mut self,) {
    match self.decode() {
      OpCode::Hlt => self.running = false,
      OpCode::Load => self.load(),
      OpCode::Copy => self.copy(),
      OpCode::AddRI => self.add_ri(),
      OpCode::SubRI => self.sub_ri(),
      OpCode::RvSubRI => self.rvsub_ri(),
      OpCode::MulRI => self.mul_ri(),
      OpCode::DivRI => self.div_ri(),
      OpCode::RvDivRI => self.rvdiv_ri(),
      OpCode::PowRI => self.pow_ri(),
      OpCode::RvPowRI => self.rvpow_ri(),
      OpCode::AddRR => self.add_rr(),
      OpCode::SubRR => self.sub_rr(),
      OpCode::MulRR => self.mul_rr(),
      OpCode::DivRR => self.div_rr(),
      OpCode::PowRR => self.pow_rr(),
      OpCode::CmpRI => self.cmp_ri(),
      OpCode::CmpRR => self.cmp_rr(),
      OpCode::Not => self.not(),
      OpCode::Jmp => self.jmp(),
      OpCode::Jnz => self.jnz(),
      OpCode::Jz => self.jz(),
      OpCode::Call => self.call(),
      OpCode::SysCall => self.sys_call(),
      OpCode::Ret => self.ret(),
      OpCode::Alloc => self.alloc(),
      OpCode::Realloc => self.realloc(),
      OpCode::Dealloc => self.dealloc(),
      OpCode::RMem => self.rmem(),
      OpCode::WMem => self.wmem(),
      OpCode::WriteStr => self.write_str(),
      OpCode::MemCpy => self.memcpy(),
      OpCode::Push => self.vm_push(),
      OpCode::Pop => self.vm_pop(),
      OpCode::PopR => self.vm_pop_r(),
      OpCode::Noop => {}
    }
  }

  /// Execute the next instruction of the [`Program`].
  fn execute_with(&mut self, opaque:&mut dyn Any,) {
    match self.decode() {
      OpCode::Hlt => self.running = false,
      OpCode::Load => self.load(),
      OpCode::Copy => self.copy(),
      OpCode::AddRI => self.add_ri(),
      OpCode::SubRI => self.sub_ri(),
      OpCode::RvSubRI => self.rvsub_ri(),
      OpCode::MulRI => self.mul_ri(),
      OpCode::DivRI => self.div_ri(),
      OpCode::RvDivRI => self.rvdiv_ri(),
      OpCode::PowRI => self.pow_ri(),
      OpCode::RvPowRI => self.rvpow_ri(),
      OpCode::AddRR => self.add_rr(),
      OpCode::SubRR => self.sub_rr(),
      OpCode::MulRR => self.mul_rr(),
      OpCode::DivRR => self.div_rr(),
      OpCode::PowRR => self.pow_rr(),
      OpCode::CmpRI => self.cmp_ri(),
      OpCode::CmpRR => self.cmp_rr(),
      OpCode::Not => self.not(),
      OpCode::Jmp => self.jmp(),
      OpCode::Jnz => self.jnz(),
      OpCode::Jz => self.jz(),
      OpCode::Noop => {}
      OpCode::Call => self.call(),
      OpCode::SysCall => self.sys_call_with(opaque,),
      OpCode::Ret => self.ret(),
      OpCode::Alloc => self.alloc(),
      OpCode::Realloc => self.realloc(),
      OpCode::Dealloc => self.dealloc(),
      OpCode::RMem => self.rmem(),
      OpCode::WMem => self.wmem(),
      OpCode::WriteStr => self.write_str(),
      OpCode::MemCpy => self.memcpy(),
      OpCode::Push => self.vm_push(),
      OpCode::Pop => self.vm_pop(),
      OpCode::PopR => self.vm_pop_r(),
    }
  }

  /// Run the currently loaded VM program.
  pub fn run(&mut self,) {
    self.running = true;
    while self.running {
      self.execute();
    }
  }

  /// Run the currently loaded VM program.
  pub fn run_with(&mut self, opaque:&mut dyn Any,) {
    self.running = true;
    while self.running {
      self.execute_with(opaque,);
    }
  }

  /// Load a [`Program`] into the VM.
  pub fn upload<P,>(&mut self, program:P,)
  where Program: From<P,> {
    let program = Program::from(program,);
    if program.len() >= u32::MAX as usize {
      panic!("{}", VMErrors::ProgramToLong(program.len()))
    }
    self.program = program;
    self.reg[PC] = Memory([0, 0, 0, 0,],);
  }

  /// Implementation of [`OpCode::Load`].
  #[inline(always)]
  fn load(&mut self,) {
    // Get the target register
    let target = self.next_byte();
    // Get the value to load into the register
    let value = self.next_4_bytes();
    self.reg[target as usize] = Memory(value,);
  }

  /// Implementation of [`OpCode::Copy`].
  #[inline(always)]
  fn copy(&mut self,) {
    // Get the target register
    let target = self.next_byte();
    // Get the value to copy into the register
    let value = self.next_byte();
    self.reg[target as usize] = self.reg[value as usize];
  }

  /// Implementation of [`OpCode::AddRI`].
  #[inline(always)]
  fn add_ri(&mut self,) {
    // Get the target register
    let target = self.next_byte() as usize;

    // Get the operand stored in a register
    let reg = self.next_byte() as usize;
    let a = self.reg[reg].as_f32();
    // Get the immediate f32 value
    let b = self.next_4_bytes::<f32>();

    // Store the result of the operation in the target register
    self.reg[target] = Memory::from(a + b,);
  }

  /// Implementation of [`OpCode::RvSubRI`].
  #[inline(always)]
  fn sub_ri(&mut self,) {
    // Get the target register
    let target = self.next_byte() as usize;

    // Get the operand stored in a register
    let reg = self.next_byte() as usize;
    let a = self.reg[reg].as_f32();
    // Get the immediate f32 value
    let b = self.next_4_bytes::<f32>();

    // Store the result of the operation in the target register
    self.reg[target] = Memory::from(a - b,);
  }

  /// Implementation of [`OpCode::RSubRI`].
  #[inline(always)]
  fn rvsub_ri(&mut self,) {
    // Get the target register
    let target = self.next_byte() as usize;

    // Get the operand stored in a register
    let reg = self.next_byte() as usize;
    let a = self.reg[reg].as_f32();
    // Get the immediate f32 value
    let b = self.next_4_bytes::<f32>();

    // Store the result of the operation in the target register
    self.reg[target] = Memory::from(b - a,);
  }

  /// Implementation of [`OpCode::MulRI`].
  #[inline(always)]
  fn mul_ri(&mut self,) {
    // Get the target register
    let target = self.next_byte() as usize;

    // Get the operand stored in a register
    let reg = self.next_byte() as usize;
    let a = self.reg[reg].as_f32();
    // Get the immediate f32 value
    let b = self.next_4_bytes::<f32>();

    // Store the result of the operation in the target register
    self.reg[target] = Memory::from(a * b,);
  }

  /// Implementation of [`OpCode::DivRI`].
  #[inline(always)]
  fn div_ri(&mut self,) {
    // Get the target register
    let target = self.next_byte() as usize;

    // Get the operand stored in a register
    let reg = self.next_byte() as usize;
    let a = self.reg[reg].as_f32();
    // Get the immediate f32 value
    let b = self.next_4_bytes::<f32>();

    // Store the result of the operation in the target register
    self.reg[target] = Memory::from(a / b,);
  }

  /// Implementation of [`OpCode::RvDivRI`].
  #[inline(always)]
  fn rvdiv_ri(&mut self,) {
    // Get the target register
    let target = self.next_byte() as usize;

    // Get the operand stored in a register
    let reg = self.next_byte() as usize;
    let a = self.reg[reg].as_f32();
    // Get the immediate f32 value
    let b = self.next_4_bytes::<f32>();

    // Store the result of the operation in the target register
    self.reg[target] = Memory::from(b / a,);
  }

  /// Implementation of [`OpCode::PowRI`].
  #[inline(always)]
  fn pow_ri(&mut self,) {
    // Get the target register
    let target = self.next_byte() as usize;

    // Get the operand stored in a register
    let reg = self.next_byte() as usize;
    let a = self.reg[reg].as_f32();
    // Get the immediate f32 value
    let b = self.next_4_bytes::<f32>();

    // Store the result of the operation in the target register
    self.reg[target] = Memory::from(a.powf(b,),);
  }

  /// Implementation of [`OpCode::RvPowRI`].
  #[inline(always)]
  fn rvpow_ri(&mut self,) {
    // Get the target register
    let target = self.next_byte() as usize;

    // Get the operand stored in a register
    let reg = self.next_byte() as usize;
    let a = self.reg[reg].as_f32();
    // Get the immediate f32 value
    let b = self.next_4_bytes::<f32>();

    // Store the result of the operation in the target register
    self.reg[target] = Memory::from(b.powf(a,),);
  }

  /// Implementation of [`OpCode::AddRR`].
  #[inline(always)]
  fn add_rr(&mut self,) {
    // Get the target register
    let target = self.next_byte() as usize;

    // Get the operands R0 is the next by and R1 is the subsequent byte
    let a = self.reg[self.next_byte() as usize].as_f32();
    let b = self.reg[self.next_byte() as usize].as_f32();

    // Store the result of the operation in the target register
    self.reg[target] = Memory::from(a + b,);
  }

  /// Implementation of [`OpCode::SubRR`].
  #[inline(always)]
  fn sub_rr(&mut self,) {
    // Get the target register
    let target = self.next_byte() as usize;

    // Get the operands R0 is the next by and R1 is the subsequent byte
    let a = self.reg[self.next_byte() as usize].as_f32();
    let b = self.reg[self.next_byte() as usize].as_f32();

    // Store the result of the operation in the target register
    self.reg[target] = Memory::from(a - b,);
  }

  /// Implementation of [`OpCode::MulRR`].
  #[inline(always)]
  fn mul_rr(&mut self,) {
    // Get the target register
    let target = self.next_byte() as usize;

    // Get the operands R0 is the next by and R1 is the subsequent byte
    let a = self.reg[self.next_byte() as usize].as_f32();
    let b = self.reg[self.next_byte() as usize].as_f32();

    // Store the result of the operation in the target register
    self.reg[target] = Memory::from(a * b,);
  }

  /// Implementation of [`OpCode::DivRR`].
  #[inline(always)]
  fn div_rr(&mut self,) {
    // Get the target register
    let target = self.next_byte() as usize;

    // Get the operands R0 is the next by and R1 is the subsequent byte
    let a = self.reg[self.next_byte() as usize].as_f32();
    let b = self.reg[self.next_byte() as usize].as_f32();

    // Store the result of the operation in the target register
    self.reg[target] = Memory::from(a / b,);
  }

  /// Implementation of [`OpCode::PowRR`].
  #[inline(always)]
  fn pow_rr(&mut self,) {
    // Get the target register
    let target = self.next_byte() as usize;

    // Get the operands R0 is the next by and R1 is the subsequent byte
    let a = self.reg[self.next_byte() as usize].as_f32();
    let b = self.reg[self.next_byte() as usize].as_f32();

    // Store the result of the operation in the target register
    self.reg[target] = Memory::from(a.powf(b,),);
  }

  #[inline(always)]
  /// Implementation of [`OpCode::CmpRI`].
  fn cmp_ri(&mut self,) {
    // Get the Cmp Flag
    let flag = CmpFlag::from(self.next_byte(),);

    // Get the operand stored in a register
    let a = self.reg[self.next_byte() as usize].as_f32();

    // Get the immediate f32 value
    let b = self.next_4_bytes::<f32>();

    // Store the result of the operation in the target register
    match flag {
      CmpFlag::Eq => self.reg[EQ] = Memory::from(a == b,),
      CmpFlag::Gt => self.reg[EQ] = Memory::from(a > b,),
      CmpFlag::Lt => self.reg[EQ] = Memory::from(a < b,),
      CmpFlag::Geq => self.reg[EQ] = Memory::from(a >= b,),
      CmpFlag::Leq => self.reg[EQ] = Memory::from(a <= b,),
    }
  }

  #[inline(always)]
  /// Implementation of [`OpCode::CmpRR`].
  fn cmp_rr(&mut self,) {
    // Get the Cmp Flag
    let flag = CmpFlag::from(self.next_byte(),);

    // Get the operands R0 is the next by and R1 is the subsequent byte
    let a = self.reg[self.next_byte() as usize].as_f32();
    let b = self.reg[self.next_byte() as usize].as_f32();

    // Store the result of the operation in the target register
    match flag {
      CmpFlag::Eq => self.reg[EQ] = Memory::from(a == b,),
      CmpFlag::Gt => self.reg[EQ] = Memory::from(a > b,),
      CmpFlag::Lt => self.reg[EQ] = Memory::from(a < b,),
      CmpFlag::Geq => self.reg[EQ] = Memory::from(a >= b,),
      CmpFlag::Leq => self.reg[EQ] = Memory::from(a <= b,),
    }
  }

  /// Implementation of [`OpCode::Not`].
  #[inline(always)]
  fn not(&mut self,) {
    let target_reg = self.next_byte() as usize;
    let src_reg = self.next_byte() as usize;

    self.reg[target_reg] = !self.reg[src_reg]
  }

  /// Implementation of [`OpCode::Jmp`].
  #[inline(always)]
  fn jmp(&mut self,) {
    let target = self.next_4_bytes();

    self.reg[PC] = Memory(target,)
  }

  /// Implementation of [`OpCode::Jnz`].
  #[inline(always)]
  fn jnz(&mut self,) {
    let cond = self.reg[self.next_byte() as usize];
    let target = self.next_4_bytes();

    if cond.as_bool() {
      *self.pc_mut() = Memory(target,)
    }
  }

  /// Implementation of [`OpCode::Jz`].
  #[inline(always)]
  fn jz(&mut self,) {
    let cond = self.reg[self.next_byte() as usize];
    let target = self.next_4_bytes();

    if !cond.as_bool() {
      *self.pc_mut() = Memory(target,)
    }
  }

  /// Implementation of [`OpCode::Call`].
  #[inline(always)]
  fn call(&mut self,) {
    // Get the function ptr
    let fn_ptr = self.next_byte() as usize;

    // Increment the SP (grows downards so subtract one)
    self.stack_inc(1,).unwrap();

    // Store the pc of the next instruction (the return site) on the stack
    self.mem[self.sp().as_u32() as usize] = Memory::from(self.pc().as_u32(),);

    // Set the pc to the function pointer
    *self.pc_mut() = Memory::from(fn_ptr,);
  }

  /// Implementation of [`OpCode::SysCall`].
  #[inline(always)]
  fn sys_call(&mut self,) {
    let fn_index = self.next_byte() as usize;
    let ptr = self.externs[fn_index];
    ptr(self, &mut (),)
  }

  /// Implementation of [`OpCode::SysCall`] which takes external arguments.
  #[inline(always)]
  fn sys_call_with(&mut self, opaque:&mut dyn Any,) {
    let fn_index = self.next_byte() as usize;
    let ptr = self.externs[fn_index];
    ptr(self, opaque,)
  }

  /// Implementation of [`OpCode::Ret`].
  #[inline(always)]
  fn ret(&mut self,) {
    // Get the number of arguments to clean up
    let arg_num = self.next_byte() as u32;

    // Set the program counter to the return value popped from the stack
    *self.pc_mut() = Memory::from(self.mem[self.sp().as_u32() as usize].as_u32(),);

    // Decrement the SP (grows downards so add one)
    self.stack_dec(arg_num + 1,).unwrap();
  }

  /// Implementation of [`OpCode::Alloc`].
  #[inline(always)]
  fn alloc(&mut self,) {
    // Get the register where the slab will be stored
    let reg = self.next_byte() as usize;

    // Get the number size of the requested chunk
    let size = self.reg[self.next_byte() as usize].as_f32() as u16;

    // Update the address of the next free address
    let slab = self.allocator.alloc(size,);

    // Store the slab in the target register
    self.reg[reg] = Memory::from(slab,);
  }

  /// Implementation of [`OpCode::Realloc`].
  #[inline(always)]
  fn realloc(&mut self,) {
    let slab_reg = self.next_byte() as usize;
    let mut slab = self.reg[slab_reg].as_slab();

    let size = self.reg[self.next_byte() as usize].as_f32() as u16;

    self.allocator.realloc(&mut self.mem, &mut slab, size,);

    self.reg[slab_reg] = Memory::from(slab,);
  }

  /// Implementation of [`OpCode::Dealloc`].
  #[inline(always)]
  fn dealloc(&mut self,) {
    let slab = self.reg[self.next_byte() as usize].as_slab();
    self.allocator.dealloc(slab,);
  }

  /// Implementation of [`OpCode::RMem`].
  #[inline(always)]
  fn rmem(&mut self,) {
    // Rd: Register the data will be stored
    let dst = self.next_byte() as usize;

    // Register storing the source memory address
    let slab = self.reg[self.next_byte() as usize].as_slab();

    let immediate_offset = self.next_4_bytes::<usize>();
    // Address of the register storing an offset
    // If the address is zero there is no offset.
    // If it is not zero there is a register offset.
    // Zero is used because R0 will never store an offset
    let register_addr = self.next_byte() as usize;
    let register_offset = if register_addr != 0 { self.reg[register_addr].as_f32() } else { 0.0 } as usize;

    let value = self.mem[slab.ptr() + immediate_offset + register_offset];

    self.reg[dst] = value;
  }

  /// Implementation of [`OpCode::WMem`].
  #[inline(always)]
  fn wmem(&mut self,) {
    // Get the pointer to a memory address from the register holding it
    let slab = self.reg[self.next_byte() as usize].as_slab();

    // Get the register holding the pointer (slab owning) to the data to store.
    let src = self.next_byte() as usize;

    let immediate_offset = self.next_4_bytes::<usize>();
    // Address of the register storing an offset
    // If the address is zero there is no offset.
    // If it is not zero there is a register offset.
    // Zero is used because R0 will never store an offset
    let register_addr = self.next_byte() as usize;
    let register_offset = if register_addr != 0 { self.reg[register_addr].as_f32() } else { 0.0 } as usize;
    self.mem[slab.ptr() + immediate_offset + register_offset] = self.reg[src];
  }

  /// Implementation of [`OpCode::MemCpy`].
  #[inline(always)]
  fn memcpy(&mut self,) {
    // Get the pointer to the target memory address from the register holding it
    let dst = self.reg[self.next_byte() as usize].as_slab();

    // Get the pointer to a memory address from the register holding it
    let src = self.reg[self.next_byte() as usize].as_slab();

    self.mem[dst.ptr()] = self.mem[src.ptr()]
  }

  /// Implementation of [`OpCode::Push`].
  #[inline(always)]
  fn vm_push(&mut self,) {
    // Get the value from the register
    let val = self.reg[self.next_byte() as usize];
    self.stack_inc(1,).unwrap();

    // Place the value into the stack
    self.mem[self.sp().as_u32() as usize] = val;
  }

  /// Implementation of [`OpCode::Pop`].
  #[inline(always)]
  fn vm_pop(&mut self,) {
    self.stack_dec(1,).unwrap();
  }

  /// Implementation of [`OpCode::PopR`].
  #[inline(always)]
  fn vm_pop_r(&mut self,) {
    // Place the value in the current slot the SP points to into the return
    // register
    self.reg[self.next_byte() as usize] = self.mem[self.sp().as_u32() as usize];
    self.stack_dec(1,).unwrap();
  }

  /// Takes a pointer and a len. Reads bytes from the pointer to the output
  /// until the len is reached.
  #[inline(always)]
  fn write_str(&mut self,) {
    let ptr = self.reg[self.next_byte() as usize].as_u32() as usize;
    let len = self.reg[self.next_byte() as usize].as_u32() as usize;

    let mut string = String::new();

    while string.len() < len {
      let string_bytes:&[u8] = unsafe { transmute(&self.mem[ptr..ptr + len],) };
      for byte in string_bytes {
        string.push(*byte as char,);
      }
    }

    print!("{}", string);
  }
}

pub const DBG_OPCODES:u8 = 1 << 0;
pub const DBG_PC:u8 = 1 << 1;
pub const DBG_REG:u8 = 1 << 2;
pub const DBG_STACK:u8 = 1 << 3;
/// Pause after each instruction and wait for user input
pub const STEP_RUN:u8 = 1 << 7;

// Debugging implementations
impl VM {
  /// Write each instruction into the provided [writer](Write) before executing
  /// it.
  pub fn dbg_run<W:Write,>(&mut self, mut w:W, dbg_flag:u8,) {
    self.running = true;
    while self.running {
      let op_byte = self.program[self.pc().as_u32()];
      let op = OpCode::from_u8(op_byte,).ok_or(VMErrors::UnknownOpcode(op_byte, self.pc().as_u32(),),).unwrap();
      if dbg_flag & DBG_OPCODES != 0 {
        write!(w, "OpCode: {}, ", op).unwrap();
      }
      if dbg_flag & DBG_PC != 0 {
        write!(w, "PC: {}, ", self.pc().as_u32()).unwrap();
      }
      if dbg_flag & DBG_REG != 0 {
        write!(w, "Regs: {:?}, ", self.reg).unwrap();
      }
      if dbg_flag & DBG_STACK != 0 {
        write!(w, "Stack: {:?}, ", &self.mem[0..20]).unwrap();
      }
      if dbg_flag & STEP_RUN != 0 {
        todo!()
      }
      self.execute();
    }
  }
}

#[cfg(test)]
mod test {
  use super::OpCode;
  use crate::{
    allocator::{POOL_128_SIZE, POOL_16_SIZE, POOL_64_SIZE},
    memory::Slab,
    vm::{Memory, DBG_OPCODES, STACK_SIZE, VM},
  };
  use spdr_isa::{
    opcodes::CmpFlag,
    registers::{EQ, FIRST_FREE_REGISTER, SP},
  };
  use std::{any::Any, cell::RefCell, ptr::copy_nonoverlapping, rc::Rc, sync::Arc};

  // Use these for the memory tests
  const OFFSET_16:u16 = 0;
  const OFFSET_64:u16 = OFFSET_16 + POOL_16_SIZE;
  const OFFSET_128:u16 = OFFSET_64 + POOL_64_SIZE;
  const OFFSET_256:u16 = OFFSET_128 + POOL_128_SIZE;

  #[test]
  fn test_add_instructions() {
    #[rustfmt::skip]
    let program = vec![
      // Load 15 into R1
      OpCode::Load.into(), 10, 0, 0, 112, 65,
      // Add R1 and 10 together and store in R2
      OpCode::AddRI.into(), 20, 10, 0, 0, 32, 65,
      // Add R1 and R2 together and store in R3
      OpCode::AddRR.into(), 30, 10, 20,
      // End the program
      OpCode::Hlt.into(),
    ];

    let mut vm = VM::new();

    vm.upload(program,);

    vm.run();

    assert_eq!(vm.reg[10].as_f32(), 15.0);
    assert_eq!(vm.reg[20].as_f32(), 25.0);
    assert_eq!(vm.reg[30].as_f32(), 40.0);
  }

  #[test]
  fn test_sub_instructions() {
    #[rustfmt::skip]
    let program = vec![
      // Load 15 into R10
      OpCode::Load.into(), 10, 0, 0, 112, 65,
      // Sub 10 from R10 and store in R20
      OpCode::SubRI.into(), 20, 10, 0, 0, 32, 65,
      // Sub R20 from R10 and store in R30
      OpCode::SubRR.into(), 30, 10, 20,
      // Sub R30 from 15 and store in R40
      OpCode::RvSubRI.into(), 40, 30, 0, 0, 112, 65,
      // End the program
      OpCode::Hlt.into(),
    ];

    let mut vm = VM::new();

    vm.upload(program,);

    vm.run();

    assert_eq!(vm.reg[10].as_f32(), 15.0);
    assert_eq!(vm.reg[20].as_f32(), 5.0);
    assert_eq!(vm.reg[30].as_f32(), 10.0);
    assert_eq!(vm.reg[40].as_f32(), 15.0 - 10.0)
  }

  #[test]
  fn test_mul_instructions() {
    #[rustfmt::skip]
    let program = vec![
      // Load 15 into R1
      OpCode::Load.into(), 10, 0, 0, 112, 65,
      // Mul R1 and 10 together and store in R2
      OpCode::MulRI.into(), 20, 10, 0, 0, 32, 65,
      // Mul R1 and R2 together and store in R3
      OpCode::MulRR.into(), 30, 10, 20,
      // End the program
      OpCode::Hlt.into(),
    ];

    let mut vm = VM::new();

    vm.upload(program,);

    vm.run();

    assert_eq!(vm.reg[10].as_f32(), 15.0);
    assert_eq!(vm.reg[20].as_f32(), 150.0);
    assert_eq!(vm.reg[30].as_f32(), 150.0 * 15.0);
  }

  #[test]
  fn test_div_instructions() {
    #[rustfmt::skip]
    let program = vec![
      // Load 15 into R10
      OpCode::Load.into(), 10, 0, 0, 112, 65,
      // Div R10 by 10 and store in R20
      OpCode::DivRI.into(), 20, 10, 0, 0, 32, 65,
      // Div R10 by R20 and store in R30
      OpCode::DivRR.into(), 30, 10, 20,
      // Divide 15 by R30 and store in R40
      OpCode::RvDivRI.into(), 40, 30, 0, 0, 112, 65,
      // End the program
      OpCode::Hlt.into(),
    ];

    let mut vm = VM::new();

    vm.upload(program,);

    vm.run();

    assert_eq!(vm.reg[10].as_f32(), 15.0);
    assert_eq!(vm.reg[20].as_f32(), 15.0 / 10.0);
    assert_eq!(vm.reg[30].as_f32(), 15.0 / (15.0 / 10.0));
    assert_eq!(vm.reg[40].as_f32(), 15.0 / (vm.reg[30].as_f32()));
  }

  #[test]
  fn test_pow_instructions() {
    #[rustfmt::skip]
    let program = [
      // Load 15 into R10
      OpCode::Load.into(), 10, 0, 0, 112, 65,
      // Raise R10 to the 10 power together and store in R20
      OpCode::PowRI.into(), 20, 10, 0, 0, 32, 65,
      // Raise R10 to the R20 power and store in R30
      OpCode::PowRR.into(), 30, 10, 20,
      // Raise 15 to the R10 power and store in R40
      OpCode::PowRI.into(), 40, 10, 0, 0, 112, 65,
      // End the program
      OpCode::Hlt.into(),
    ];

    let mut vm = VM::new();

    vm.upload(program,);

    vm.run();

    assert_eq!(vm.reg[10].as_f32(), 15.0);
    assert_eq!(vm.reg[20].as_f32(), 15.0f32.powf(10.0));
    assert_eq!(vm.reg[30].as_f32(), 15.0f32.powf(15.0f32.powf(10.0)));
    assert_eq!(vm.reg[40].as_f32(), 15.0f32.powf(vm.reg[10].as_f32()));
  }

  #[test]
  fn test_eq_and_not_instructions() {
    #[rustfmt::skip]
    let program = [
      // Load 15 into R20
      OpCode::Load.into(), 20, 0, 0, 112, 65,
      // Compare R20 and 10
      OpCode::CmpRI.into(), CmpFlag::Eq.into(), 20, 0, 0, 32, 65,
      // Move the result into R30
      OpCode::Copy.into(), 30, EQ as u8,
      // Load 15 into R10
      OpCode::Load.into(), 10, 0, 0, 112, 65,
      // Compare R10 and R20
      OpCode::CmpRR.into(), CmpFlag::Eq.into(), 10, 20,
      // Store Not EQ in R40
      OpCode::Not.into(), 40, EQ as u8,
      // End the program
      OpCode::Hlt.into(),
    ];

    let mut vm = VM::new();

    vm.upload(program,);

    vm.run();

    assert_eq!(vm.reg[10].as_f32(), 15.0);
    assert_eq!(vm.reg[20].as_f32(), 15.0);
    assert_eq!(vm.reg[30].as_bool(), false);
    assert_eq!(vm.reg[EQ].as_bool(), true);
    assert_eq!(vm.reg[40].as_bool(), false);
  }

  #[test]
  fn test_allocation() {
    #[rustfmt::skip]
    // for some reason the value in R40 is overwriting the wrong mem cell
    let program = [
      // Load 4 into R10
      OpCode::Load.into(), 10, 0, 0, 128, 64,
      // Load 5.0 into R20, 32.5 into R30, 4.0 into R40, and 656.89 into R50
      OpCode::Load.into(), 20, 0, 0, 160, 64,
      OpCode::Load.into(), 30, 0, 0, 2, 66,
      OpCode::Load.into(), 40, 0, 0, 128, 64,
      OpCode::Load.into(), 50, 246, 56, 36, 68,
      // Alloc space for a array the size of the value in R10 (4 cells) and store its pointer in R60
      OpCode::Alloc.into(), 60, 10,
      // Stop the program
      OpCode::Hlt.into(),
    ];

    let mut vm = VM::new();
    vm.upload(program,);
    vm.run();

    // Check Alloc actually leads to a slab being stored
    assert_eq!(vm.reg[60].as_slab(), Slab::new_with_meta_offset(0, 16));
  }

  #[test]
  fn test_reallocation() {
    #[rustfmt::skip]
    // for some reason the value in R40 is overwriting the wrong mem cell
    let program = vec![
      // Load 5.0 into R20, 32.5 into R30, 4.0 into R40, and 656.89 into R50
      OpCode::Load.into(), 20, 0, 0, 160, 64,
      // Load 4 into R10, this will be the size of the requested allocation
      OpCode::Load.into(), 10, 0, 0, 128, 64,
      // Alloc space for a array the size of the value in R10 (4 cells) and store its pointer in R60
      OpCode::Alloc.into(), 60, 10,
      // Load 200 into R200, this will be the size of the requested allocation
      OpCode::Load.into(), 200, 0, 0, 72, 67,
      // Realloc space for a array the size of the value in R200 (200 cells) and store its pointer in R80
      OpCode::Realloc.into(), 80, 200,
      // Stop the program
      OpCode::Hlt.into(),
    ];

    let mut vm = VM::new();
    vm.upload(program,);
    vm.run();

    // Confirm Alloc actually leads to a slab being stored
    assert_eq!(vm.reg[60].as_slab(), Slab::new_with_meta_offset(0, 16));

    let offset = POOL_16_SIZE + POOL_64_SIZE + POOL_128_SIZE;
    // Confirm Realloc actually leads to a slab being stored
    assert_eq!(vm.reg[80].as_slab(), Slab::new_with_meta_offset(offset, 256));
  }

  #[test]
  fn test_deallocation() {
    #[rustfmt::skip]
    // for some reason the value in R40 is overwriting the wrong mem cell
    let program = vec![
      // Load 5.0 into R20, 32.5 into R30, 4.0 into R40, and 656.89 into R50
      OpCode::Load.into(), 20, 0, 0, 160, 64,
      // Load 4 into R10, this will be the size of the requested allocation
      OpCode::Load.into(), 10, 0, 0, 128, 64,
      // Alloc space for a array the size of the value in R10 (4 cells) and store its pointer in R60
      OpCode::Alloc.into(), 60, 10,
      // Deallocate the slab stored in R60
      OpCode::Dealloc.into(), 60,
      OpCode::Hlt.into(),
    ];

    let mut vm = VM::new();
    vm.upload(program,);
    vm.run();

    // Confirm Alloc actually leads to a slab being stored
    assert_eq!(vm.reg[60].as_slab(), Slab::new_with_meta_offset(0, 16));
    // Confirm the deallocation results in a pool of the correct length
    assert_eq!(vm.allocator.pools()[0].clone().inner().len() - 1, POOL_16_SIZE as usize / 16);
  }

  #[test]
  fn test_wmem() {
    #[rustfmt::skip]
    let program = [
      // Load 5.0 into R20, 32.5 into R30, 4.0 into R40, and 656.89 into R50
      OpCode::Load.into(), 20, 0, 0, 160, 64,
      OpCode::Load.into(), 30, 0, 0, 2, 66,
      OpCode::Load.into(), 40, 0, 0, 128, 64,
      OpCode::Load.into(), 50, 246, 56, 36, 68,
      // Load 4 into R10
      OpCode::Load.into(), 10, 0, 0, 72, 67,
      // Alloc space for a array the size of the value in R10 (4 cells) and store its pointer in R60
      OpCode::Alloc.into(), 60, 10, 
      // Write memory in R30, R40, and R50 into the allocated block
      // Test works with no offset
      OpCode::WMem.into(), 60, 20, 0, 0, 0, 0, 0,
      // Test works with immediate offset of 1
      OpCode::WMem.into(), 60, 30, 0, 0, 128, 63, 0,
      // Store 2 in R70
      OpCode::Load.into(), 70, 0, 0, 0, 64,
      // Test works with register offset of 2 which is stored in R70
      OpCode::WMem.into(), 60, 40, 0, 0, 0, 0, 70,
      // Test works with an immediate offset of 2 and register offset of 1 
      OpCode::Load.into(), 80, 0, 0, 128, 63,
      OpCode::WMem.into(), 60, 50, 0, 0, 0, 64, 80,
      OpCode::Hlt.into(),
    ];

    let mut vm = VM::new();
    vm.upload(program,);
    vm.run();

    // Check the loads store the proper values
    assert_eq!(vm.reg[20].as_f32(), 5.0);
    assert_eq!(vm.reg[30].as_f32(), 32.5);
    assert_eq!(vm.reg[40].as_f32(), 4.0);
    assert_eq!(vm.reg[50].as_f32(), 656.89);

    // Check the values are written from registers into the "array"
    // Have to use the OFFSET_256 because the requested slab is 200 cells
    assert_eq!(vm.mem[STACK_SIZE + OFFSET_256 as usize].as_f32(), 5.0);
    assert_eq!(vm.mem[STACK_SIZE + OFFSET_256 as usize + 1].as_f32(), 32.5,);
    assert_eq!(vm.mem[STACK_SIZE + OFFSET_256 as usize + 2].as_f32(), 4.0);
    assert_eq!(vm.mem[STACK_SIZE + OFFSET_256 as usize + 3].as_f32(), 656.89);
  }

  #[test]
  fn test_rmem() {
    let mut vm = VM::new();
    // Load values into mem[20-23]
    vm.mem[20] = Memory::from(30.0,);
    vm.mem[21] = Memory::from(31.0,);
    vm.mem[22] = Memory::from(32.0,);
    vm.mem[23] = Memory::from(33.0,);

    #[rustfmt::skip]
    let program = [
    // Get an allocation for 4 bytes and store it in R200
    OpCode::Load.into(), 50, 0, 0, 0, 64,
    OpCode::Alloc.into(), 27, 50,
    // Read the memory from mem[20] into R200
    OpCode::RMem.into(), 200, 27, 0, 0, 0, 0, 0,
    // Read the memory from mem[20 + I0] into R200 I0 = 1
    OpCode::RMem.into(), 201, 27, 0, 0, 128, 63, 0, 
    // Read the memory from mem[20 + R0] into R200: R0 = 51 = 3
    OpCode::Load.into(), 51, 0, 0, 0, 64, // 3 in LE bytes
    OpCode::RMem.into(), 202, 27, 0, 0, 0, 0, 51,
    // Read the memory from mem[20 + I0 + R0] into R200: R0 = 51 = 3, I0 = 1
    OpCode::RMem.into(), 203, 27, 0, 0, 128, 63, 51,
    OpCode::Hlt.into(),
    ];

    vm.upload(program,);
    vm.run();

    assert_eq!(vm.reg[200].as_f32(), 30.0);
    assert_eq!(vm.reg[201].as_f32(), 31.0);
    assert_eq!(vm.reg[202].as_f32(), 32.0);
    assert_eq!(vm.reg[203].as_f32(), 33.0);
  }

  #[test]
  fn test_memcpy() {
    let src = Memory::from(Slab::new_as_pointer(22,),);
    let dst = Memory::from(Slab::new_as_pointer(39,),);

    let mut vm = VM::new();
    // Load 4 into mem[22]
    vm.mem[22] = Memory::from(4.0,);

    #[rustfmt::skip]
    let program = [
    // Copy mem[22] to mem[39] 
    OpCode::Load.into(), 200, src[0], src[1], src[2], src[3], // This is the pointer to 22  
    OpCode::Load.into(), 201, dst[0], dst[1], dst[2], dst[3], // This is the pointer to 39
    OpCode::MemCpy.into(), 201, 200,
    OpCode::Hlt.into(),
    ];

    vm.upload(program,);
    vm.run();

    // Check the pointers are stored correctly
    assert_eq!(vm.reg[200].as_slab(), Slab::new_as_pointer(22,));
    assert_eq!(vm.reg[201].as_slab(), Slab::new_as_pointer(39,));

    // Check MemCpy copies from mem[22] to mem[39]
    assert_eq!(vm.mem[STACK_SIZE + 19].as_f32(), 4.0);
    assert_eq!(vm.mem[STACK_SIZE + 19].as_f32(), vm.mem[39].as_f32());
  }

  #[test]
  fn call_fn_using_regs() {
    // Address of the test function's beginning
    const TEST_1:u8 = 5;

    // Args for the function as Memory
    let a = Memory(5f32.to_le_bytes(),);
    let b = Memory(4f32.to_le_bytes(),);
    let c = Memory(32.5f32.to_le_bytes(),);
    let d = Memory(656.89f32.to_le_bytes(),);
    // TEST FUNCTION is basically:
    fn test_fn(a:f32, b:f32, c:f32, d:f32,) -> f32 {
      let t1 = a + b;
      let t2 = c + d;
      t1 + t2
    }

    #[rustfmt::skip]
    let program = [
      // Jump to main at 19
      OpCode::Jmp.into(), 19, 0, 0, 0,
      // TEST FUNCTION 
      // let t1 = a + b
      OpCode::AddRR.into(), 220, 220, 221,
      // let t2 = c + d
      OpCode::AddRR.into(), 222, 222, 223,
      // let foo = t1 + t2
      OpCode::AddRR.into(), 220, 220, 222,
      // Return
      OpCode::Ret.into(), 0,

      // Beginning of MAIN

      // Load 5.0 into R20
      OpCode::Load.into(), 20, a[0], a[1], a[2], a[3],
      // Load 32.5 into R21
      OpCode::Load.into(), 21, b[0], b[1], b[2], b[3],
      // Load 4.0 into R22 
      OpCode::Load.into(), 22, c[0], c[1], c[2], c[3],
      // Load 656.89 into R23
      OpCode::Load.into(), 23, d[0], d[1], d[2], d[3],
      // Copy the four arguments into the function's registers
      OpCode::Copy.into(), 220, 20,
      OpCode::Copy.into(), 221, 21,
      OpCode::Copy.into(), 222, 22,
      OpCode::Copy.into(), 223, 23,
      // Call test_1 to test pure register based function calling
      OpCode::Call.into(), TEST_1,
      // Move the return value from R220 into R30
      OpCode::Copy.into(), 30, 220,
      OpCode::Hlt.into(),
    ];

    let mut vm = VM::new();
    vm.upload(program,);
    vm.run();

    assert_eq!(vm.reg[30].as_f32(), test_fn(a.as_f32(), b.as_f32(), c.as_f32(), d.as_f32()));
  }

  #[test]
  fn call_fn_using_stack() {
    // Address of the test function's beginning
    const TEST_2:u8 = 5;

    // Args for the function as Memory
    let a = Memory(5f32.to_le_bytes(),);
    let b = Memory(4f32.to_le_bytes(),);
    let c = Memory(32.5f32.to_le_bytes(),);
    let d = Memory(656.89f32.to_le_bytes(),);
    // TEST FUNCTION is basically:
    fn test_fn(a:f32, b:f32, c:f32, d:f32,) -> f32 {
      let t1 = a + b;
      let t2 = c + d;
      t1 + t2
    }

    #[rustfmt::skip]
    let program = [
      // Jump to main at 51
      OpCode::Jmp.into(), 51, 0, 0, 0,
      // TEST FUNCTION 
      // Read the arguments from the stack 
      // There is a by one offset from the SP because the top of the stack holds the return pointer
      OpCode::RMem.into(), 230, SP as u8, 0, 0, 128, 63, 0,
      OpCode::RMem.into(), 231, SP as u8, 0, 0, 0, 64, 0, 
      OpCode::RMem.into(), 232, SP as u8, 0, 0, 64, 64, 0,
      OpCode::RMem.into(), 233, SP as u8, 0, 0, 128, 64, 0,   
      // let t1 = a + b
      OpCode::AddRR.into(), 230, 230, 231,
      // let t2 = c + d
      OpCode::AddRR.into(), 232, 232, 233,
      // // let foo = t1 + t2
      OpCode::AddRR.into(), 230, 230, 232,
      // Return the function and pop the arguments off the stack
      OpCode::Ret.into(), 4,

      // START OF MAIN

      // Load 5.0 into R20
      OpCode::Load.into(), 20, a[0], a[1], a[2], a[3],
      // Load 32.5 into R21
      OpCode::Load.into(), 21, b[0], b[1], b[2], b[3],
      // Load 4.0 into R22 
      OpCode::Load.into(), 22, c[0], c[1], c[2], c[3],
      // Load 656.89 into R23
      OpCode::Load.into(), 23, d[0], d[1], d[2], d[3],

      // Push the arguments for TEST FUNCTION onto the stack Right to Left
      OpCode::Push.into(), 23,
      OpCode::Push.into(), 22,
      OpCode::Push.into(), 21,
      OpCode::Push.into(), 20,
      // Call test_2 to test stackcall
      OpCode::Call.into(), TEST_2,
      OpCode::Copy.into(), 30, 230,
      // Stop the program
      OpCode::Hlt.into(),
    ];

    let mut vm = VM::new();
    vm.upload(&program,);
    vm.run();

    // Check the return value is correct
    assert_eq!(vm.reg[30].as_f32(), test_fn(a.as_f32(), b.as_f32(), c.as_f32(), d.as_f32()));
    // Check the stack pointer is correct
    assert_eq!(vm.reg[SP].as_u32() as usize, 20);
  }

  #[test]
  fn test_jmp_jnz_jz() {
    // Loads are to test lines are skipped
    #[rustfmt::skip]
    let program = &[
      OpCode::Jmp.into(), 35, 0, 0, 0, // Jump to 35
      // 2nd jump target
      OpCode::Load.into(), EQ as u8, 1, 0, 0, 0,
      OpCode::Jnz.into(), EQ as u8, 53, 0, 0, 0, // Jump to 53
      OpCode::Load.into(), 16 as u8, 0, 0, 128, 63, // Load 1 into 16
      OpCode::Load.into(), 17 as u8, 0, 0, 128, 63, // Load 1 into 17
      OpCode::Load.into(), 18 as u8, 0, 0, 128, 63, // Load 1 into 18
      // 1st jump target
      OpCode::Jz.into(), EQ as u8, 5, 0, 0, 0, // Jump to 5
      OpCode::Load.into(), 14 as u8, 14, 0, 0, 0, // Load 1 into 14
      OpCode::Load.into(), 19 as u8, 0, 0, 128, 63, // Load 1 into 19
      // 3rd jump target
      OpCode::Hlt.into(),
    ];

    let mut vm = VM::new();

    vm.upload(program,);
    let mut w = Vec::new();
    vm.dbg_run(&mut w, DBG_OPCODES,);

    assert_eq!(vm.reg[EQ].as_bool(), true);
    assert_eq!(vm.reg[14].as_f32(), 0.0);
    assert_eq!(vm.reg[16].as_f32(), 0.0);
    assert_eq!(vm.reg[17].as_f32(), 0.0);
    assert_eq!(vm.reg[18].as_f32(), 0.0);
    assert_eq!(vm.reg[19].as_f32(), 0.0);
    // Check the correct instructions executed
    assert_eq!(
      String::from_utf8(w).unwrap().trim(),
      "OpCode: Jmp, OpCode: Jz, OpCode: Load, OpCode: Jnz, OpCode: Hlt,".to_owned()
    );
  }

  #[test]
  fn external_fn_call_and_extern_w_opaque() {
    struct Opaque {
      data:f32,
      hard_to_reach:Rc<RefCell<Vec<u32,>,>,>,
    }

    fn test_1(data:&mut Opaque, add:f32, sub:f32,) -> f32 {
      data.data += add - sub;
      data.data
    }

    fn test_1_wrapper(vm:&mut VM, data:&mut dyn Any,) {
      // Get the value to add from the top of the stack
      let add = vm.extern_read(vm.sp().as_u32() as usize,).unwrap().as_f32();

      // Get the value to sub from the top of the stack
      let sub = vm.extern_read(vm.sp().as_u32() as usize + 1,).unwrap().as_f32();

      // Convert the external data to the external function's expected type.
      let data = data.downcast_mut::<Opaque>().unwrap();

      let ret = test_1(data, add, sub,) as f32;

      // Push to the top of the stack
      vm.extern_push(Memory(ret.to_le_bytes(),),);
    }

    fn test_2(data:&mut Opaque, add:f32, push_val:f32,) {
      let mut data = data.hard_to_reach.borrow_mut();

      data[0] += add as u32;

      data.push(push_val as u32,);
    }

    fn test_2_wrapper(vm:&mut VM, data:&mut dyn Any,) {
      // Get the value to add from the top of the stack
      let add = vm.extern_read(vm.sp().as_u32() as usize,).unwrap().as_f32();

      // Get the value to sub from the top of the stack
      let push_val = vm.extern_read(vm.sp().as_u32() as usize + 1,).unwrap().as_f32();

      // Convert the external data to the external function's expected type.
      let data = data.downcast_mut::<Opaque>().unwrap();

      test_2(data, add, push_val,);
    }

    let mut opaque = Opaque {
      data:90.0,
      hard_to_reach:Rc::new(RefCell::new(vec![13, 99, 45],),),
    };

    #[rustfmt::skip]
    let program = vec![
      // Load 32.5 into R13, this will be the number to add
      OpCode::Load.into(), 13, 0, 0, 2, 66,
      // Load 5.0 into R14, this will be the number to sub
      OpCode::Load.into(), 14, 0, 0, 160, 64,
      // Push R13 and R14 onto the stack
      OpCode::Push.into(), 14,
      OpCode::Push.into(), 13,
      // Call test_1 idx 0
      OpCode::SysCall.into(), 0,
      // Pop the value of test_1 into R3
      OpCode::PopR.into(), 3,
      // Pop the function args off the stack
      OpCode::Pop.into(),
      OpCode::Pop.into(),
      // Load 15 into R15, this will be the number to add
      OpCode::Load.into(), 15, 0, 0, 112, 65,
      // Push 5 from R14 onto the stack
      OpCode::Push.into(), 14,
      // Push 15 from R15 onto the stack
      OpCode::Push.into(), 15,
      // Call test_2 idx 1
      OpCode::SysCall.into(), 1,
      // Pop the function args off the stack
      OpCode::Pop.into(),
      OpCode::Pop.into(),
      OpCode::Hlt.into(),
    ];

    // Set up the VM and run the program
    let mut vm = VM::new();
    vm.register_extern(test_1_wrapper,);
    vm.register_extern(test_2_wrapper,);
    vm.upload(program,);

    // Ensuring the VM can borrow the Rc even when another thing owns it
    let _extra_borrow = opaque.hard_to_reach.clone();

    vm.run_with(&mut opaque,);

    assert_eq!(vm.reg[3].as_f32(), 90.0 + 32.5 - 5.0);
    assert_eq!(*opaque.hard_to_reach.borrow(), vec![13 + 15, 99, 45, 5]);
    assert_eq!(vm.sp().as_u32() as usize, 20);
  }

  #[test]
  #[should_panic(expected = "EMPTY STACK: Tried to remove a value from the stack when the stack was empty.")]
  fn panics_on_stack_underflow() {
    // Test Underflow
    let underflow = vec![OpCode::Pop.into()];

    // Set up the VM and run the program
    let mut vm = VM::new();
    vm.upload(underflow,);
    vm.run();
  }

  #[test]
  #[should_panic(expected = "STACK OVERFLOW: Tried to add a value to the stack when the stack was full.")]
  fn panics_on_stack_overflow() {
    // Test OverFlow
    #[rustfmt::skip]
    let overflow = vec![
      OpCode::Push.into(), 0,
      OpCode::Push.into(), 0,
      OpCode::Push.into(), 0,
      OpCode::Push.into(), 0,
      OpCode::Push.into(), 0,
      OpCode::Push.into(), 0,
      OpCode::Push.into(), 0,
      OpCode::Push.into(), 0,
      OpCode::Push.into(), 0,
      OpCode::Push.into(), 0,
      OpCode::Push.into(), 0,
      OpCode::Push.into(), 0,
      OpCode::Push.into(), 0,
      OpCode::Push.into(), 0,
      OpCode::Push.into(), 0,
      OpCode::Push.into(), 0,
      OpCode::Push.into(), 0,
      OpCode::Push.into(), 0,
      OpCode::Push.into(), 0,
      OpCode::Push.into(), 0,
      // This is the point it should overflow
      OpCode::Push.into(), 0,
    ];

    // Set up the VM and run the program
    let mut vm = VM::new();
    vm.upload(overflow,);
    vm.run();
  }

  #[test]
  #[rustfmt::skip]
  fn write_line() {
    let mut vm = VM::new();

    // Not sure how this works but took this code from here: https://stackoverflow.com/questions/72185130/how-to-capture-the-content-of-stdout-stderr-when-i-cannot-change-the-code-that-p
    // Captures the print so it can be tested
    std::io::set_output_capture(Some(Default::default()));

    // Copy the string into the VM
    let string = "Hello World\n";
    let len:usize = string.len();
    let dst = &vm.mem[STACK_SIZE] as *const Memory as *mut u8;
    unsafe { copy_nonoverlapping(string as *const str as *const u8, dst, len,) };

    // Load the string info into the VM registers
    vm.reg[FIRST_FREE_REGISTER] = Memory::from(STACK_SIZE);
    vm.reg[FIRST_FREE_REGISTER + 1] = Memory::from(len);

    let program = [OpCode::WriteStr.into(), FIRST_FREE_REGISTER as u8, FIRST_FREE_REGISTER as u8 + 1,];
    vm.upload(program,);

    vm.execute();

    // Finish capturing the output
    let captured = std::io::set_output_capture(None);
    let captured = captured.unwrap();
    let captured = Arc::try_unwrap(captured).unwrap();
    let captured = captured.into_inner().unwrap();
    let captured = String::from_utf8(captured).unwrap();

    assert_eq!(captured, string);
  }
}
