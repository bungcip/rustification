use std::fs::{self, File};
use std::io;
use std::io::prelude::*;
use std::path::{Path, PathBuf};
use std::process;

use log::warn;

use crate::build_files::{emit_build_files, get_build_dir, CrateConfig};
use crate::c_ast::Printer;
use crate::c_ast::{ConversionContext};
use crate::compile_cmds::get_compile_commands;
use crate::diagnostics;
use crate::{
    get_module_name, reorganize_definitions, CrateSet, PragmaSet, PragmaVec, RustChannel,
    TranspilerConfig,
};
use c2rust_ast_exporter as ast_exporter;

type TranspileResult = Result<(PathBuf, PragmaVec, CrateSet, RustChannel), ()>;

/// Main entry point to transpiler. Called from CLI tools with the result of
/// clap::App::get_matches().
/// return RustChannel indicating the Rust channel used for transpilation.
pub fn transpile(tcfg: TranspilerConfig, cc_db: &Path, extra_clang_args: &[&str]) -> RustChannel {
    diagnostics::init(tcfg.enabled_warnings.clone(), tcfg.log_level);

    let build_dir = get_build_dir(&tcfg, cc_db);

    let lcmds = get_compile_commands(cc_db, &tcfg.filter).unwrap_or_else(|_| {
        panic!(
            "Could not parse compile commands from {}",
            cc_db.to_string_lossy()
        )
    });

    // Specify path to system include dir on macOS 10.14 and later. Disable the blocks extension.
    let clang_args: Vec<String> = get_extra_args_macos();
    let mut clang_args: Vec<&str> = clang_args.iter().map(AsRef::as_ref).collect();
    clang_args.extend_from_slice(extra_clang_args);

    let mut top_level_ccfg = None;
    let mut workspace_members = vec![];
    let mut num_transpiled_files = 0;
    let mut transpiled_modules = Vec::new();
    let mut use_nightly = false;

    for lcmd in &lcmds {
        let cmds = &lcmd.cmd_inputs;
        let lcmd_name = lcmd
            .output
            .as_ref()
            .map(|output| {
                let output_path = Path::new(output);
                output_path
                    .file_stem()
                    .unwrap()
                    .to_str()
                    .unwrap()
                    .to_owned()
            })
            .unwrap_or_else(|| tcfg.crate_name());
        let build_dir = if lcmd.top_level {
            build_dir.to_path_buf()
        } else {
            build_dir.join(&lcmd_name)
        };

        // Compute the common ancestor of all input files
        // FIXME: this is quadratic-time in the length of the ancestor path
        let mut ancestor_path = cmds
            .first()
            .map(|cmd| {
                let mut dir = cmd.abs_file();
                dir.pop(); // discard the file part
                dir
            })
            .unwrap_or_else(PathBuf::new);
        if cmds.len() > 1 {
            for cmd in &cmds[1..] {
                let cmd_path = cmd.abs_file();
                ancestor_path = ancestor_path
                    .ancestors()
                    .find(|a| cmd_path.starts_with(a))
                    .map(ToOwned::to_owned)
                    .unwrap_or_else(PathBuf::new);
            }
        }

        let results = cmds
            .iter()
            .map(|cmd| {
                transpile_single(
                    &tcfg,
                    cmd.abs_file(),
                    &ancestor_path,
                    &build_dir,
                    cc_db,
                    &clang_args,
                )
            })
            .collect::<Vec<TranspileResult>>();
        let mut modules = vec![];
        let mut modules_skipped = false;
        let mut pragmas = PragmaSet::new();
        let mut crates = CrateSet::new();
        for res in results {
            match res {
                Ok((module, pragma_vec, crate_set, channel)) => {
                    modules.push(module);
                    crates.extend(crate_set);

                    num_transpiled_files += 1;
                    for (key, vals) in pragma_vec {
                        for val in vals {
                            pragmas.insert((key, val));
                        }
                    }

                    if channel == RustChannel::Nightly {
                        use_nightly = true;
                    }
                }
                Err(_) => {
                    modules_skipped = true;
                }
            }
        }
        pragmas.sort();
        crates.sort();

        transpiled_modules.extend(modules.iter().cloned());

        if tcfg.emit_build_files {
            if modules_skipped {
                // If we skipped a file, we may not have collected all required pragmas
                warn!("Can't emit build files after incremental transpiler run; skipped.");
                return RustChannel::Stable;
            }

            let ccfg = CrateConfig {
                crate_name: lcmd_name.clone(),
                modules,
                pragmas,
                crates,
                link_cmd: lcmd,
            };
            if lcmd.top_level {
                top_level_ccfg = Some(ccfg);
            } else {
                let crate_file = emit_build_files(&tcfg, &build_dir, Some(ccfg), None, use_nightly);
                reorganize_definitions(&tcfg, &build_dir, crate_file)
                    .unwrap_or_else(|e| warn!("Reorganizing definitions failed: {e}"));
                workspace_members.push(lcmd_name);
            }
        }
    }

    if num_transpiled_files == 0 {
        warn!("No C files found in compile_commands.json; nothing to do.");
        return RustChannel::Stable;
    }

    if tcfg.emit_build_files {
        let crate_file = emit_build_files(
            &tcfg,
            &build_dir,
            top_level_ccfg,
            Some(workspace_members),
            use_nightly,
        );
        reorganize_definitions(&tcfg, &build_dir, crate_file)
            .unwrap_or_else(|e| warn!("Reorganizing definitions failed: {e}"));
    }

    tcfg.check_if_all_binaries_used(&transpiled_modules);

    if use_nightly {
        RustChannel::Nightly
    } else {
        RustChannel::Stable
    }
}

/// Ensure that clang can locate the system headers on macOS 10.14+.
///
/// MacOS 10.14 does not have a `/usr/include` folder even if Xcode
/// or the command line developer tools are installed as explained in
/// this [thread](https://forums.developer.apple.com/thread/104296).
/// It is possible to install a package which puts the headers in
/// `/usr/include` but the user doesn't have to since we can find
/// the system headers we need by running `xcrun --show-sdk-path`.
fn get_extra_args_macos() -> Vec<String> {
    let mut args = vec![];
    if cfg!(target_os = "macos") {
        let usr_incl = Path::new("/usr/include");
        if !usr_incl.exists() {
            let output = process::Command::new("xcrun")
                .args(["--show-sdk-path"])
                .output()
                .expect("failed to run `xcrun` subcommand");
            let mut sdk_path = String::from_utf8(output.stdout).unwrap();
            let olen = sdk_path.len();
            sdk_path.truncate(olen - 1);
            sdk_path.push_str("/usr/include");

            args.push("-isystem".to_owned());
            args.push(sdk_path);
        }

        // disable Apple's blocks extension; see https://github.com/immunant/c2rust/issues/229
        args.push("-fno-blocks".to_owned());
    }
    args
}

fn transpile_single(
    tcfg: &TranspilerConfig,
    input_path: PathBuf,
    ancestor_path: &Path,
    build_dir: &Path,
    cc_db: &Path,
    extra_clang_args: &[&str],
) -> TranspileResult {
    let output_path = get_output_path(tcfg, input_path.clone(), ancestor_path, build_dir);
    if output_path.exists() && !tcfg.overwrite_existing {
        warn!("Skipping existing file {}", output_path.display());
        return Err(());
    }

    let file = input_path.file_name().unwrap().to_str().unwrap();
    if !input_path.exists() {
        warn!(
            "Input C file {} does not exist, skipping!",
            input_path.display()
        );
        return Err(());
    }

    if tcfg.verbose {
        println!("Additional Clang arguments: {}", extra_clang_args.join(" "));
    }

    // Extract the untyped AST from the CBOR file
    let untyped_context = match ast_exporter::get_untyped_ast(
        input_path.as_path(),
        cc_db,
        extra_clang_args,
        tcfg.debug_ast_exporter,
    ) {
        Err(e) => {
            warn!(
                "Error: {}. Skipping {}; is it well-formed C?",
                e,
                input_path.display()
            );
            return Err(());
        }
        Ok(cxt) => cxt,
    };

    println!("Transpiling {file}");

    if tcfg.dump_untyped_context {
        println!("CBOR Clang AST");
        println!("{untyped_context:#?}");
    }

    // Convert this into a typed AST
    let typed_context = {
        let conv = ConversionContext::new(&untyped_context);
        if conv.invalid_clang_ast && tcfg.fail_on_error {
            panic!("Clang AST was invalid");
        }
        conv.into_typed_context()
    };

    if tcfg.dump_typed_context {
        println!("Clang AST");
        println!("{typed_context:#?}");
    }

    if tcfg.pretty_typed_context {
        println!("Pretty-printed Clang AST");
        println!("{:#?}", Printer::new(io::stdout()).print(&typed_context));
    }

    // Perform the translation
    let (translated_string, pragmas, crates, channel) =
        crate::translator::translate(typed_context, tcfg, input_path);

    let mut file = match File::create(&output_path) {
        Ok(file) => file,
        Err(e) => panic!(
            "Unable to open file {} for writing: {}",
            output_path.display(),
            e
        ),
    };

    match file.write_all(translated_string.as_bytes()) {
        Ok(()) => (),
        Err(e) => panic!(
            "Unable to write translation to file {}: {}",
            output_path.display(),
            e
        ),
    };

    Ok((output_path, pragmas, crates, channel))
}

fn get_output_path(
    tcfg: &TranspilerConfig,
    mut input_path: PathBuf,
    ancestor_path: &Path,
    build_dir: &Path,
) -> PathBuf {
    // When an output file name is not explicitly specified, we should convert files
    // with dashes to underscores, as they are not allowed in rust file names.
    let file_name = input_path
        .file_name()
        .unwrap()
        .to_str()
        .unwrap()
        .replace('-', "_");

    input_path.set_file_name(file_name);
    input_path.set_extension("rs");

    if tcfg.output_dir.is_some() {
        let path_buf = input_path
            .strip_prefix(ancestor_path)
            .expect("Couldn't strip common ancestor path");

        // Place the source files in build_dir/src/
        let mut output_path = build_dir.to_path_buf();
        output_path.push("src");
        for elem in path_buf.iter() {
            let path = Path::new(elem);
            let name = get_module_name(path, false, true, false).unwrap();
            output_path.push(name);
        }

        // Create the parent directory if it doesn't exist
        let parent = output_path.parent().unwrap();
        if !parent.exists() {
            fs::create_dir_all(parent).unwrap_or_else(|_| {
                panic!("couldn't create source directory: {}", parent.display())
            });
        }
        output_path
    } else {
        input_path
    }
}
