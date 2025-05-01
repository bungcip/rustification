use crate::anonymous_decls::rust_k;
use libc::{c_int, c_uint};

pub fn test_anonymous_decl() {
    unsafe {
        assert_eq!((*&raw const rust_k).j.l, 0);
    }
}
