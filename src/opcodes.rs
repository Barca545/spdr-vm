use num_derive::FromPrimitive;

#[derive(FromPrimitive, Debug, PartialEq, Clone, Copy,)]
pub enum OpCode {
  /// # Halt program execution
  Hlt,
  /// # Load Data
  ///
  /// Load the immediate `I` into register `R0`.
  ///
  /// Format: `LOAD R0 I`
  ///
  /// Arguments:
  /// - `R0`: Target register
  /// - `I`: Source immediate
  Load,
  /// # Copy Memory
  ///
  /// Copy the value in `R1` into `R0`.
  ///
  /// Format: COPY R0 R1
  ///
  /// Arguments:
  /// - `R0`: Target register
  /// - `R1`: Source register
  Copy,
  /// # Memory Copy
  ///
  /// Writes the value stored in the memory address stored in `R1` into the
  /// memory address stored in `R0`.
  ///
  /// Format:`MEMCPY R0 R1`
  ///
  /// Arguments:
  /// - `R0`: Target memory address
  /// - `R1`: Source memory address
  MemCpy,
  /// # Add Register and Immediate
  ///
  /// Format: `ADD R0, R1, I`
  ///
  /// Arguments:
  /// - `R0`: Storage target
  /// - `R1`: Register operand
  /// - `I`: Immediate operand
  AddRI,
  /// # Subtract Register and Immediate
  ///
  /// Format: `SUB R0, R1, I`
  ///
  /// Arguments:
  /// - `R0`: Storage target
  /// - `R1`: Register operand
  /// - `I`: Immediate operand
  SubRI,
  /// # Multiply Register and Immediate
  ///
  /// Format: `MUL R0, R1, I`
  ///
  /// Arguments:
  /// - `R0`: Storage target
  /// - `R1`: Register operand
  /// - `I`: Immediate operand
  MulRI,
  /// # Divide Register by Immediate
  ///
  /// Format: `DIV R0, R1, I`
  ///
  /// Arguments:
  /// - `R0`: Storage target
  /// - `R1`: Register operand
  /// - `I`: Immediate operand
  DivRI,
  /// # Raise Register by Immediate
  ///
  /// Format: `POW R0, R1, I`
  ///
  /// Arguments:
  /// - `R0`: Storage target
  /// - `R1`: Register operand
  /// - `I`: Immediate operand
  PowRI,
  /// # Add Register and Register
  ///
  /// Format: `ADD R0, R1, R2`
  ///
  /// Arguments:
  /// - `R0`: Storage target
  /// - `R1`: Register operand
  /// - `R2`: Register operand
  AddRR,
  /// # Subtract Register and Register
  ///
  /// Format: `SUB R0, R1, R2`
  ///
  /// Arguments:
  /// - `R0`: Storage target
  /// - `R1`: Register operand
  /// - `R2`: Immediate operand
  SubRR,
  /// # Multiply Register and Register
  ///
  /// Format: `MUL R0, R1, R2`
  ///
  /// Arguments:
  /// - `R0`: Storage target
  /// - `R1`: Register operand
  /// - `R2`: Register operand
  MulRR,
  /// # Divide Register and Register
  ///
  /// Format: `DIV R0, R1, R2`
  ///
  /// Arguments:
  /// - `R0`: Storage target
  /// - `R1`: Register operand
  /// - `R2`: Register operand
  DivRR,
  /// # Raise Register by Register
  ///
  /// Format: `POW R0, R1, R2`
  ///
  /// Arguments:
  /// - `R0`: Storage target
  /// - `R1`: Memory operand
  /// - `R2`: Register operand
  PowRR,
  /// # Equality Check Memory and Immediate
  ///
  /// Checks whether two values are equal and stores the result in [`VM::EQ`]
  ///
  /// Format: `EQ R0 I`
  ///
  /// Arguments:
  /// - `R0`: Memory operand
  /// - `I`: Immediate operand
  EqRI,
  /// # Greater Than Check Memory and Immediate
  ///
  /// Checks whether `R0` > `I` and stores the result in [`VM::EQ`]
  ///
  /// Format: `EQ R0 I`
  ///
  /// Arguments:
  /// - `R0`: Memory operand
  /// - `I`: Immediate operand
  GtRI,
  /// # Equality Check Register and Register
  ///
  /// Checks whether `R0` == `R1` and stores the result in [`VM::EQ`]
  ///
  /// Format: `EQ R0 `R1`
  ///
  /// Arguments:
  /// - `R0`: Register operand
  /// - `R1`: Register operand
  EqRR,
  /// # Greater Than Check Register and Register
  ///
  /// Checks whether `R0` > `R1` and stores the result in [`VM::EQ`]
  ///
  /// Format: `EQ R0 `R1`
  ///
  /// Arguments:
  /// - `R0`: Register operand
  /// - `R1`: Register operand
  GtRR,
  /// # Bitwise Not
  ///
  /// Format:`NOT R0 R1`
  ///
  /// Arguments:
  /// - `R0`: Storage target
  /// - `R1`: value being negated
  Not,
  /// # Unconditional Jump
  ///
  /// Format: JMP a
  ///
  /// Arguments:
  /// - `a`: Target index.
  Jmp,
  /// # Jump if Not Zero
  ///
  /// Format: `JNZ IDX R0`
  ///
  /// Arguments:
  /// - `Idx`: Target program index
  /// - `R0`: Register holding the check
  Jnz,
  /// # Call a Function
  ///
  /// Format: `CALL IDX`
  ///
  /// Arguments:
  /// - `IDX`: Location of the function pointer.
  Call,
  /// # System call
  ///
  /// Call an external function.
  ///
  /// Format: `SYSCALL I0`
  ///
  /// Arguments:
  /// - `I0`: Index of the external function being called.
  SysCall,
  /// # Return from a function call
  ///
  /// Pop the return address of the top of the stack and set the PC equal to it.
  /// Pop the function's arguments from the stack.
  ///
  /// Format: `RET I`
  ///
  /// Arguments:
  /// - `I`: The number of function arguments to clean up.
  Ret,
  /// # Allocate Heap
  ///
  /// Allocates a chunk of memory capable of holding `R1` values. Returns a
  /// pointer to the allocation to `R0`.
  ///
  /// Format: `ALLOC R0 R1`
  ///
  /// Arguments:
  /// - `R0`: Target register
  /// - `R1`: Memory storing the number of values to be stored
  Alloc,
  /// # Deallocate Heap
  ///
  /// CURRENTLY A NOOP
  Dealloc,
  /// # Read Memory
  ///
  /// Loads the value stored at the pointer in `R1` into `R0`.
  ///
  /// Format:`RMEM R0 R1 I0 R2`
  ///
  /// Arguments:
  /// - `R0`: Target Memory
  /// - `R1`: Memory storing the pointer to the source memory
  /// - `I0`: Offset stored as an immediate
  /// - `R2`: Offset stored in a register
  ///
  /// Note: If there is no register offset, R2 will be zero and ignored. Zero
  /// (REQ) is used because it will never store an offset.
  RMem,
  /// # Write Memory
  ///
  /// Writes the value stored in `R1` into the memory address stored in `R0`.
  ///
  /// Format:`RMEM R0 R1 I R2`
  ///
  /// Arguments:
  /// - `R0`: Register storing the target memory address
  /// - `R1`: Register storing the data to write to memory
  /// - `I`: Offset stored as an immediate
  /// - `R2`: Offset stored in a register
  ///
  /// Note: If there is no register offset, R2 will be zero and ignored. Zero
  /// (REQ) is used because it will never store an offset.
  WMem,
  /// # Push to Stack
  ///
  /// Pushes the argument onto the top of stack.
  ///
  /// Format: `PUSH R1`
  ///
  /// Arguments:
  /// - `R1`: Register holding the value to push.
  Push,
  /// # Pop From Stack
  ///
  /// Removes the item on the top of the stack.
  Pop,
  /// # Pop Read From Stack
  ///
  /// Removes the item on the top of the stack and places it into a register.
  ///
  /// Format: `POPR R0`
  ///
  /// Arguments:
  /// `R0`: The register to place the popped value.
  PopR,
  /// # No Operation
  Noop,
}

impl From<OpCode,> for u8 {
  fn from(val:OpCode,) -> Self {
    val as u8
  }
}

impl From<u8,> for OpCode {
  fn from(value:u8,) -> Self {
    value.into()
  }
}
