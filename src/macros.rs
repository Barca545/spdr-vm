// // TODO: Might be better to make the VM accept a pointer or something so the
// // passed value does not have to be boxed. Something to explore when I build
// the // macro

// // This should be a proc macro.

// // Then the user can just define the function normally and register it

// macro_rules! declare_external_function {
//   (fn $name:ident ($concrete:ident : $concrete_ty:ty, $($arg:ident :
// $arg_type:ty),* $(,)?) $(-> $ret:ty)? {$($body:stmt)*}; ) => {
//     fn $name(vm:&mut crate::vm::VM, opaque:&mut dyn std::any::Any,) {

//       // Downcast the opaque type into the concrete type
//       let $concrete = opaque.downcast_mut::<$concrete_ty>();
//       // Might be a better way to do this but this tracks how deep a given
// variable is in the stack       let mut stack_loc = 0;
//       $(
//         let $arg = vm.extern_read(vm.sp().as_u32() as usize +
// stack_loc).unwrap();         stack_loc += 1;
//       )*
//       $($body)*

//       // Still need to make it so it captures the return value and pushes it
// onto the stack     }
//   };
// }

// #[cfg(test)]
// mod test {
//   use crate::vm::VM;

//   #[test]
//   fn test_wrapper_macro() {
//     declare_external_function!(
//       fn foo(opaque:f32, arg:i32, s:i32,) -> f32 {
//         println!("{}",arg.as_f32());
//         println!("{}", s.as_f32());

//       };
//     );

//     let mut vm = VM::new();
//     vm.extern_push(14.0,);
//     vm.extern_push(17.9,);

//     foo(&mut vm, &mut (),);
//   }
// }
