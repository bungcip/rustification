//! feature_thread_local

use crate::thread_locals::rust_thread_entry;
use core::ffi::{c_int, c_uint};
use std::thread;

#[link(name = "test")]
unsafe extern "C" {
    fn thread_entry(_: c_uint, _: *mut c_int);
}

#[unsafe(no_mangle)]
static mut gesi: u32 = 71;
#[unsafe(no_mangle)]
static mut rust_gesi: u32 = 71;
#[unsafe(no_mangle)]
static mut fesi: u32 = 113;
#[unsafe(no_mangle)]
static mut rust_fesi: u32 = 113;
#[unsafe(no_mangle)]
#[thread_local]
static mut geti: u32 = 147;
#[unsafe(no_mangle)]
#[thread_local]
static mut rust_geti: u32 = 147;
#[unsafe(no_mangle)]
#[thread_local]
static mut feti: u32 = 237;
#[unsafe(no_mangle)]
#[thread_local]
static mut rust_feti: u32 = 237;

const BUFFER_SIZE: usize = 16;

fn run_test() {
    let mut buffer = [0; BUFFER_SIZE];
    let mut rust_buffer = [0; BUFFER_SIZE];
    unsafe {
        thread_entry(BUFFER_SIZE as u32, buffer.as_mut_ptr());
        rust_thread_entry(BUFFER_SIZE as u32, rust_buffer.as_mut_ptr());
    }

    assert_eq!(buffer, rust_buffer);
    unsafe {
        assert_eq!(*&raw const gesi, *&raw const rust_gesi);
        assert_eq!(*&raw const fesi, *&raw const rust_fesi);
        assert_eq!(*&raw const geti, *&raw const rust_geti);
        assert_eq!(*&raw const feti, *&raw const rust_feti);
    }
}

pub fn test_thread_locals() {
    run_test();
    run_test();
    let t = thread::spawn(|| {
        run_test();
        run_test();
        run_test();
    });
    let _ = t.join().unwrap();
    run_test();
    run_test();
}
