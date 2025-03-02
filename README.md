# The SPDR Virtual Machine

A register based virtual machine written in Rust. Intended for running scripts in a game I am developing.

## Specs
- Little endian.
- 255 four (4) byte registers.
- `u16::MAX` memory with a 20 byte stack.
- Program counter register indexed by `VM::PC`.
- Stack pointer register indexed by `VM::SP`.
- Relies on the [spider_isa](https://github.com/Barca545/spdr_isa).

## Calling convention
- Caller cleans meaning the caller is responsible for placing arguments on the stack and removing any arguments and returns from the stack.
- For non-recursive functions, the first ten (10) arguments are passed into the function via registers 3-12. After the first ten, the arguments are pushed onto the stack.
- For recursive functions, all arguments are pushed onto the stack.

### Using a stack frame
- `Push` the arguments onto the stack right to left.
- Before using `Call`, `Push` the return address onto the stack.
- Arguments are fetched from the stack by adding their distance from the stack pointer e.g. `arg_1 = sp + 1`.
- `Pop` the args off the stack and `Push` any return values onto the stack in right to left order

### Clearing a stack frame
`Ret` accepts the number of items to pop from the stack.
