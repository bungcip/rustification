//! feature_register_tool,
use crate::modules::rust_modules;

#[link(name = "test")]
unsafe extern "C" {
    fn modules();
}

pub fn test_modules() {}
