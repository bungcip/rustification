//! The main library for `c2rust-transpile`.
//!
//! This library provides the main entry point for the transpiler, and it
//! re-exports a number of items from other modules.

#![allow(clippy::too_many_arguments)]

mod config;
mod diagnostics;
mod driver;
mod reorganize;

pub mod build_files;
pub mod c_ast;
pub mod cfg;
mod compile_cmds;
pub mod convert_type;
pub mod renamer;
pub mod rust_ast;
pub mod transform;
pub mod translator;
pub mod with_stmts;

use std::fs::{self, File};
use std::io::prelude::*;
use std::path::{Path, PathBuf};

use crate::compile_cmds::CompileCmd;
use serde_derive::Serialize;
pub use tempfile::TempDir;

pub use crate::diagnostics::Diagnostic;

use crate::convert_type::RESERVED_NAMES;
pub use crate::translator::ReplaceMode;
use std::prelude::v1::Vec;

pub use config::TranspilerConfig;
pub use driver::transpile;
pub use reorganize::reorganize_definitions;

type PragmaVec = Vec<(&'static str, Vec<&'static str>)>;
type PragmaSet = indexmap::IndexSet<(&'static str, &'static str)>;
type CrateSet = indexmap::IndexSet<ExternCrate>;
/// The Rust channel to use for the transpiled code.
#[derive(PartialEq, Eq, Clone, Copy)]
pub enum RustChannel {
    /// The stable Rust channel.
    Stable,
    /// The nightly Rust channel.
    Nightly,
}

/// How to translate macros.
#[derive(Default, Debug)]
pub enum TranslateMacros {
    /// Don't translate any macros.
    None,

    /// Translate the conservative subset of macros known to always work.
    #[default]
    Conservative,

    /// Try to translate more, but this is experimental and not guaranteed to work.
    ///
    /// For const-like macros, this works in some cases.
    /// For function-like macros, this doesn't really work at all yet.
    Experimental,
}

/// The maximum nightly version that c2rust-transpile can compile without
/// a compile error or segfault. Unfortunately, the resulting transpiled code
/// cannot be compiled on recent nightly due to various reasons.
pub const MAX_NIGHTLY_VERSION: &str = "2025-04-19";

/// An extern crate that may be required by the transpiled code.
#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum ExternCrate {
    /// The `c2rust-bitfields` crate.
    C2RustBitfields,
    /// The `c2rust-asm-casts` crate.
    C2RustAsmCasts,
    /// The `f128` crate.
    F128,
    /// The `num-traits` crate.
    NumTraits,
    /// The `memoffset` crate.
    Memoffset,
    /// The `libc` crate.
    Libc,
}

/// Details about an extern crate.
#[derive(Serialize)]
pub struct ExternCrateDetails {
    /// The name of the crate.
    pub name: &'static str,
    /// The identifier of the crate.
    pub ident: String,
    /// Whether the crate should be imported with `#[macro_use]`.
    pub macro_use: bool,
    /// The version of the crate.
    pub version: &'static str,
}

impl ExternCrateDetails {
    /// Creates a new `ExternCrateDetails`.
    pub fn new(name: &'static str, version: &'static str, macro_use: bool) -> Self {
        Self {
            name,
            ident: name.replace('-', "_"),
            macro_use,
            version,
        }
    }
}

impl From<ExternCrate> for ExternCrateDetails {
    fn from(extern_crate: ExternCrate) -> Self {
        match extern_crate {
            ExternCrate::C2RustBitfields => Self::new("c2rust-bitfields", "0.3", true),
            ExternCrate::C2RustAsmCasts => Self::new("c2rust-asm-casts", "0.2", true),
            ExternCrate::F128 => Self::new("f128", "0.2", false),
            ExternCrate::NumTraits => Self::new("num-traits", "0.2", true),
            ExternCrate::Memoffset => Self::new("memoffset", "0.5", true),
            ExternCrate::Libc => Self::new("libc", "0.2", false),
        }
    }
}

fn char_to_ident(c: char) -> char {
    if c.is_alphanumeric() { c } else { '_' }
}

fn str_to_ident<S: AsRef<str>>(s: S) -> String {
    s.as_ref().chars().map(char_to_ident).collect()
}

/// Make sure that name:
/// - does not contain illegal characters,
/// - does not clash with reserved keywords.
fn str_to_ident_checked(filename: &Option<String>, check_reserved: bool) -> Option<String> {
    // module names cannot contain periods or dashes
    filename.as_ref().map(str_to_ident).map(|module| {
        // make sure the module name does not clash with keywords
        if check_reserved && RESERVED_NAMES.contains(&module.as_str()) {
            format!("r#{module}")
        } else {
            module
        }
    })
}

/// Get the module name for a given file path.
///
/// # Arguments
///
/// * `file` - The path to the file.
/// * `check_reserved` - Whether to check for reserved keywords.
/// * `keep_extension` - Whether to keep the file extension.
/// * `full_path` - Whether to return the full path.
pub fn get_module_name(
    file: &Path,
    check_reserved: bool,
    keep_extension: bool,
    full_path: bool,
) -> Option<String> {
    let is_rs = file.extension().map(|ext| ext == "rs").unwrap_or(false);
    let fname = if is_rs {
        file.file_stem()
    } else {
        file.file_name()
    };
    let fname = &fname.unwrap().to_str().map(String::from);
    let mut name = str_to_ident_checked(fname, check_reserved).unwrap();
    if keep_extension && is_rs {
        name.push_str(".rs");
    }
    let file = if full_path {
        file.with_file_name(name)
    } else {
        Path::new(&name).to_path_buf()
    };
    file.to_str().map(String::from)
}

/// Create a temporary `compile_commands.json` file.
///
/// # Arguments
///
/// * `sources` - A list of source files to include in the compilation database.
///
/// # Returns
///
/// A tuple containing the temporary directory and the path to the
/// `compile_commands.json` file.
pub fn create_temp_compile_commands(sources: &[PathBuf]) -> (TempDir, PathBuf) {
    // If we generate the same path here on every run, then we can't run
    // multiple transpiles in parallel, so we need a unique path. But clang
    // won't read this file unless it is named exactly "compile_commands.json",
    // so we can't change the filename. Instead, create a temporary directory
    // with a unique name, and put the file there.
    let temp_dir = tempfile::Builder::new()
        .prefix("c2rust-")
        .tempdir()
        .expect("Failed to create temporary directory for compile_commands.json");
    let temp_path = temp_dir.path().join("compile_commands.json");

    let compile_commands: Vec<CompileCmd> = sources
        .iter()
        .map(|source_file| {
            let absolute_path = fs::canonicalize(source_file)
                .unwrap_or_else(|_| panic!("Could not canonicalize {}", source_file.display()));

            CompileCmd {
                directory: PathBuf::from("."),
                file: absolute_path.clone(),
                arguments: vec![
                    "clang".to_string(),
                    absolute_path.to_str().unwrap().to_owned(),
                ],
                command: None,
                output: None,
            }
        })
        .collect();

    let json_content = serde_json::to_string(&compile_commands).unwrap();
    let mut file =
        File::create(&temp_path).expect("Failed to create temporary compile_commands.json");
    file.write_all(json_content.as_bytes())
        .expect("Failed to write to temporary compile_commands.json");

    (temp_dir, temp_path)
}
