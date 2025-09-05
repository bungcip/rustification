use std::collections::HashSet;
use std::path::{Path, PathBuf};
use itertools::Itertools;
use log::{info, warn};
use regex::Regex;
use crate::diagnostics::Diagnostic;
use crate::translator::ReplaceMode;
use crate::get_module_name;
use crate::TranslateMacros;

/// Configuration settings for the translation process
#[derive(Debug)]
pub struct TranspilerConfig {
    // Debug output options
    pub dump_untyped_context: bool,
    pub dump_typed_context: bool,
    pub pretty_typed_context: bool,
    pub dump_function_cfgs: bool,
    pub json_function_cfgs: bool,
    pub dump_cfg_liveness: bool,
    pub dump_structures: bool,
    pub verbose: bool,
    pub debug_ast_exporter: bool,

    // Options that control translation
    pub incremental_relooper: bool,
    pub fail_on_multiple: bool,
    pub filter: Option<Regex>,
    pub debug_relooper_labels: bool,
    pub prefix_function_names: Option<String>,
    pub translate_asm: bool,
    pub use_c_loop_info: bool,
    pub use_c_multiple_info: bool,
    pub simplify_structures: bool,
    pub panic_on_translator_failure: bool,
    pub emit_modules: bool,
    pub fail_on_error: bool,
    pub replace_unsupported_decls: ReplaceMode,
    pub translate_valist: bool,
    pub overwrite_existing: bool,
    pub reduce_type_annotations: bool,
    pub reorganize_definitions: bool,
    pub enabled_warnings: HashSet<Diagnostic>,
    pub emit_no_std: bool,
    pub output_dir: Option<PathBuf>,
    pub translate_const_macros: TranslateMacros,
    pub translate_fn_macros: TranslateMacros,
    pub disable_refactoring: bool,
    pub preserve_unused_functions: bool,
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
