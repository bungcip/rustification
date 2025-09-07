use c2rust_ast_builder::{Builder, mk};

/// Generate link attributes needed to ensure that the generated Rust libraries
/// have the right symbol values.
///
/// `in_extern_block` should be true if the item is in an `extern "C"` block.
/// `new_name` is the Rust name of the item.
/// `old_name` is the original C name of the item.
///
/// This function generates the following attributes:
///  - `#[no_mangle]` if the item is not in an `extern` block and its name
///    is unchanged.
///  - `#[link_name = "..."]` if the item is in an `extern` block and its name
///    has been changed.
///  - `#[export_name = "..."]` if the item is not in an `extern` block and
///    its name has been changed.
pub fn mk_linkage(in_extern_block: bool, new_name: &str, old_name: &str) -> Builder {
    if new_name == old_name {
        if in_extern_block {
            mk() // There is no mangling by default in extern blocks anymore
        } else {
            mk().call_attr("unsafe", vec!["no_mangle"]) // Don't touch my name Rust!
        }
    } else if in_extern_block {
        mk().str_attr("link_name", old_name) // Look for this name
    } else {
        mk().str_attr("export_name", old_name) // Make sure you actually name it this
    }
}
