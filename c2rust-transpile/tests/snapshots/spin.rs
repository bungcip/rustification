#![allow(
    dead_code,
    mutable_transmutes,
    non_camel_case_types,
    non_snake_case,
    non_upper_case_globals,
    path_statements,
    unsafe_op_in_unsafe_fn,
    unused_assignments,
    unused_mut,
    unused_unsafe,
    unused_variables
)]
use core::ffi;
#[unsafe(no_mangle)]
pub unsafe extern "C" fn spin() {
    ::core::hint::spin_loop();
}
