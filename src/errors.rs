use thiserror::Error;

#[derive(Error, Debug,)]
pub enum VMErrors {
  #[error("UNKNOWN OPCODE: `{0}`. PC = {1}")]
  UnknownOpcode(u8, u32,),
  #[error("EMPTY STACK: Tried to remove a value from the stack when the stack was empty.")]
  EmptyStack,
  #[error("STACK OVERFLOW: Tried to add a value to the stack when the stack was full.")]
  StackOverflow,
  #[error("PROGRAM LENGTH: Program is too long. Max length is {} but the program was {0}.", u32::MAX)]
  ProgramToLong(usize,),
}
