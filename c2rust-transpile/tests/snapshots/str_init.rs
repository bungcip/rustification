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
#[derive(Copy, Clone)]
#[repr(C)]
pub struct s {
    pub entries: [[ffi::c_char; 10]; 3],
}
#[derive(Copy, Clone)]
#[repr(C)]
pub struct alpn_spec {
    pub entries: [[ffi::c_char; 10]; 3],
    pub count: ffi::c_uint,
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn ptr() {
    let mut _s: *const ffi::c_char = c"hello".as_ptr();
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn array_deduced_length() {
    let mut _s: [ffi::c_char; 6] = *::core::mem::transmute::<
        &[u8; 6],
        &mut [ffi::c_char; 6],
    >(b"hello\0");
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn array() {
    let mut _s: [ffi::c_char; 10] = *::core::mem::transmute::<
        &[u8; 10],
        &mut [ffi::c_char; 10],
    >(b"hello\0\0\0\0\0");
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn int_array_extra_braces() {
    let mut _a: [[ffi::c_int; 10]; 3] = [
        [1 as ffi::c_int, 2 as ffi::c_int, 3 as ffi::c_int, 0, 0, 0, 0, 0, 0, 0],
        [0; 10],
        [0; 10],
    ];
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn ptr_extra_braces() {
    let mut _s: *const ffi::c_char = c"hello".as_ptr();
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn array_extra_braces() {
    let _s: [ffi::c_char; 10] = *::core::mem::transmute::<
        &[u8; 10],
        &[ffi::c_char; 10],
    >(b"hello\0\0\0\0\0");
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn array_of_ptrs() {
    let mut _s: [*const ffi::c_char; 3] = [
        c"hello".as_ptr(),
        0 as *const ffi::c_char,
        0 as *const ffi::c_char,
    ];
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn array_of_arrays() {
    let mut _s: [[ffi::c_char; 10]; 3] = [
        *::core::mem::transmute::<&[u8; 10], &mut [ffi::c_char; 10]>(b"hello\0\0\0\0\0"),
        [0; 10],
        [0; 10],
    ];
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn array_of_arrays_static() {
    static _S: [[ffi::c_char; 10]; 3] = unsafe {
        [
            *::core::mem::transmute::<&[u8; 10], &[ffi::c_char; 10]>(b"hello\0\0\0\0\0"),
            [0; 10],
            [0; 10],
        ]
    };
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn array_of_arrays_static_struct() {
    static _S: s = unsafe {
        {
            let mut init = s {
                entries: [
                    *::core::mem::transmute::<
                        &[u8; 10],
                        &mut [ffi::c_char; 10],
                    >(b"hello\0\0\0\0\0"),
                    [0; 10],
                    [0; 10],
                ],
            };
            init
        }
    };
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn curl_alpn_spec() {
    static _ALPN_SPEC_H11: alpn_spec = unsafe {
        {
            let mut init = alpn_spec {
                entries: [
                    *::core::mem::transmute::<
                        &[u8; 10],
                        &mut [ffi::c_char; 10],
                    >(b"http/1.1\0\0"),
                    [0; 10],
                    [0; 10],
                ],
                count: 1 as ffi::c_int as ffi::c_uint,
            };
            init
        }
    };
}
