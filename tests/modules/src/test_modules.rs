use crate::modules::rust_modules;
use libc::c_uint;

#[link(name = "test")]
unsafe extern "C" {
    fn modules();
}

pub fn test_modules() {}
