use crate::TranslateMacros;
use crate::diagnostics::Diagnostic;
use crate::driver::ReplaceMode;
use crate::get_module_name;
use itertools::Itertools;
use log::{info, warn};
use regex::Regex;
use std::collections::HashSet;
use std::path::{Path, PathBuf};

/// Configuration settings for the translation process
#[derive(Debug)]
pub struct TranspilerConfig {
    // Debug output options
    /// Dump the untyped AST context.
    pub dump_untyped_context: bool,
    /// Dump the typed AST context.
    pub dump_typed_context: bool,
    /// Pretty-print the typed AST context.
    pub pretty_typed_context: bool,
    /// Dump the CFGs of all functions.
    pub dump_function_cfgs: bool,
    /// Dump the CFGs of all functions as JSON.
    pub json_function_cfgs: bool,
    /// Dump the liveness information of the CFGs.
    pub dump_cfg_liveness: bool,
    /// Dump the intermediate structures produced by the relooper.
    pub dump_structures: bool,
    /// Enable verbose output.
    pub verbose: bool,
    /// Enable debug output for the AST exporter.
    pub debug_ast_exporter: bool,

    // Options that control translation
    /// Use the incremental relooper.
    pub incremental_relooper: bool,
    /// Fail on multiple CFG exits.
    pub fail_on_multiple: bool,
    /// Only translate files that match this filter.
    pub filter: Option<Regex>,
    /// Use debug labels for the relooper.
    pub debug_relooper_labels: bool,
    /// Add a prefix to all function names.
    pub prefix_function_names: Option<String>,
    /// Translate `asm!` expressions.
    pub translate_asm: bool,
    /// Use C loop information.
    pub use_c_loop_info: bool,
    /// Use C multiple-exit information.
    pub use_c_multiple_info: bool,
    /// Simplify structures.
    pub simplify_structures: bool,
    /// Panic on translator failure.
    pub panic_on_translator_failure: bool,
    /// Emit `.rs` files as modules.
    pub emit_modules: bool,
    /// Fail on error.
    pub fail_on_error: bool,
    /// How to replace unsupported declarations.
    pub replace_unsupported_decls: ReplaceMode,
    /// Translate `va_list` expressions.
    pub translate_valist: bool,
    /// Overwrite existing files.
    pub overwrite_existing: bool,
    /// Reduce type annotations.
    pub reduce_type_annotations: bool,
    /// Reorganize definitions.
    pub reorganize_definitions: bool,
    /// The set of enabled warnings.
    pub enabled_warnings: HashSet<Diagnostic>,
    /// Emit `#![no_std]` in the translated code.
    pub emit_no_std: bool,
    /// The output directory.
    pub output_dir: Option<PathBuf>,
    /// How to translate `const` macros.
    pub translate_const_macros: TranslateMacros,
    /// How to translate function-like macros.
    pub translate_fn_macros: TranslateMacros,
    /// Disable the refactoring tool.
    pub disable_refactoring: bool,
    /// Preserve unused functions.
    pub preserve_unused_functions: bool,
    /// The logging level.
    pub log_level: log::LevelFilter,

    // Options that control build files
    /// Emit `Cargo.toml` and `lib.rs`
    pub emit_build_files: bool,
    /// Names of translation units containing main functions that we should make
    /// into binaries
    pub binaries: Vec<String>,
}

impl TranspilerConfig {
    pub fn binary_name_from_path(file: &Path) -> String {
        let file = Path::new(file.file_stem().unwrap());
        get_module_name(file, false, false, false).unwrap()
    }

    pub fn is_binary(&self, file: &Path) -> bool {
        let module_name = Self::binary_name_from_path(file);
        self.binaries.contains(&module_name)
    }

    pub fn check_if_all_binaries_used(
        &self,
        transpiled_modules: impl IntoIterator<Item = impl AsRef<Path>>,
    ) -> bool {
        let module_names = transpiled_modules
            .into_iter()
            .map(|module| Self::binary_name_from_path(module.as_ref()))
            .collect::<HashSet<_>>();
        let mut ok = true;
        for binary in &self.binaries {
            if !module_names.contains(binary) {
                ok = false;
                warn!("binary not used: {binary}");
            }
        }
        if !ok {
            let module_names = module_names.iter().format(", ");
            info!("candidate modules for binaries are: {module_names}");
        }
        ok
    }

    pub fn crate_name(&self) -> String {
        self.output_dir
            .as_ref()
            .and_then(|x| x.file_name().map(|x| x.to_string_lossy().into_owned()))
            .unwrap_or_else(|| "c2rust_out".into())
    }
}
