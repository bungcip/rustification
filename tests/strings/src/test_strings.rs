use crate::strings::{rust_string_length, rust_mutable_string_array, rust_const_string_array};
use crate::static_string::rust_static_length;
use core::ffi::c_int;

#[link(name = "test")]
unsafe extern "C" {
    fn string_length(buf: *mut c_int) -> c_int;
    fn static_length() -> c_int;
    fn mutable_string_array() -> c_int;
    fn const_string_array() -> c_int;
}

#[test]
pub fn test_string_length() {
    let mut c_buf: [c_int; 4] = [0, 0, 0, 0];
    let mut r_buf: [c_int; 4] = [0, 0, 0, 0];

    unsafe {
        let c_len = string_length(c_buf.as_mut_ptr());
        let r_len = rust_string_length(r_buf.as_mut_ptr());

        println!("C buffer: {:?}", c_buf);
        println!("C length: {}", c_len);

        println!("R buffer: {:?}", r_buf);
        println!("R length: {}", r_len);

        assert_eq!(c_buf, r_buf);
        assert_eq!(c_len, r_len);
    }
}

#[test]
pub fn test_static_length() {
    let c_len : c_int;
    let r_len : c_int;
    unsafe {
        c_len = static_length();
        r_len = rust_static_length();
    }

    assert_eq!(c_len, r_len);

}

#[test]
pub fn test_mutable_string_array() {
    let result: c_int = 6;
    unsafe {
        assert_eq!(mutable_string_array(), result);
        assert_eq!(rust_mutable_string_array(), result);
    }
}

#[test]
pub fn test_const_string_array() {
    unsafe {
        assert_eq!(const_string_array(), rust_const_string_array());
    }
}