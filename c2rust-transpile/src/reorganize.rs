use crate::config::TranspilerConfig;
use anyhow::Error;
use log::warn;
use std::path::{Path, PathBuf};
use std::process;

fn invoke_refactor(_build_dir: &Path) -> Result<(), Error> {
    Ok(())
}

pub fn reorganize_definitions(
    tcfg: &TranspilerConfig,
    build_dir: &Path,
    crate_file: Option<PathBuf>,
) -> Result<(), Error> {
    // We only run the reorganization refactoring if we emitted a fresh crate file
    if crate_file.is_none() || tcfg.disable_refactoring || !tcfg.reorganize_definitions {
        return Ok(());
    }

    invoke_refactor(build_dir)?;
    // fix the formatting of the output of `c2rust-refactor`
    let status = process::Command::new("cargo")
        .args(["fmt"])
        .current_dir(build_dir)
        .status()?;
    if !status.success() {
        warn!("cargo fmt failed, code may not be well-formatted");
    }
    Ok(())
}
