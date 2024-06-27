//! extern_crate_c2rust_asm_casts

use crate::asm::rust_entry;
use libc::{c_int, c_uint};

#[link(name = "test")]
extern "C" {
    fn entry(_: c_uint, _: *mut c_int);
}

const BUFFER_SIZE: usize = 6;

pub fn test_buffer() {
    let mut buffer = [0; BUFFER_SIZE];
    let mut rust_buffer = [0; BUFFER_SIZE];
    let expected_buffer = [37, 12, 25, 6, 37, -90];

    unsafe {
        entry(BUFFER_SIZE as u32, buffer.as_mut_ptr());
        rust_entry(BUFFER_SIZE as u32, rust_buffer.as_mut_ptr());
    }

    assert_eq!(buffer, rust_buffer);
    assert_eq!(buffer, expected_buffer);
}
