use std::collections::BTreeMap;
use std::fs::{self, File};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::str::FromStr;

use handlebars::Handlebars;
use pathdiff::diff_paths;
use serde_derive::Serialize;
use serde_json::json;

use super::TranspilerConfig;
use super::compile_cmds::LinkCmd;
use crate::CrateSet;
use crate::ExternCrateDetails;
use crate::PragmaSet;
use crate::get_module_name;

#[derive(Debug, Copy, Clone)]
pub enum BuildDirectoryContents {
    Nothing,
    Minimal,
    Full,
}

impl FromStr for BuildDirectoryContents {
    type Err = ();

    fn from_str(s: &str) -> Result<BuildDirectoryContents, ()> {
        match s {
            "nothing" => Ok(BuildDirectoryContents::Nothing),
            "minimal" => Ok(BuildDirectoryContents::Minimal),
            "full" => Ok(BuildDirectoryContents::Full),
            _ => Err(()),
        }
    }
}

/// Create the build directory
pub fn get_build_dir(tcfg: &TranspilerConfig, cc_db: &Path) -> PathBuf {
    let cc_db_dir = cc_db
        .parent() // get directory of `compile_commands.json`
        .unwrap();

    match &tcfg.output_dir {
        Some(dir) => {
            let output_dir = dir.clone();
            if !output_dir.exists() {
                fs::create_dir(&output_dir).unwrap_or_else(|_| {
                    panic!("couldn't create build directory: {}", output_dir.display())
                });
            }
            output_dir
        }
        None => cc_db_dir.into(),
    }
}

pub struct CrateConfig<'lcmd> {
    pub crate_name: String,
    pub modules: Vec<PathBuf>,
    pub pragmas: PragmaSet,
    pub crates: CrateSet,
    pub link_cmd: &'lcmd LinkCmd,
}

/// Emit `Cargo.toml` and `lib.rs` for a library or `main.rs` for a binary.
/// Returns the path to `lib.rs` or `main.rs` (or `None` if the output file
/// existed already).
pub fn emit_build_files(
    tcfg: &TranspilerConfig,
    build_dir: &Path,
    crate_cfg: Option<CrateConfig<'_>>,
    workspace_members: Option<Vec<String>>,
    use_nightly: bool,
) -> Option<PathBuf> {
    let mut reg = Handlebars::new();

    reg.register_template_string("Cargo.toml", include_str!("Cargo.toml.hbs"))
        .unwrap();
    reg.register_template_string("lib.rs", include_str!("lib.rs.hbs"))
        .unwrap();
    reg.register_template_string("build.rs", include_str!("build.rs.hbs"))
        .unwrap();

    if !build_dir.exists() {
        fs::create_dir_all(build_dir)
            .unwrap_or_else(|_| panic!("couldn't create build directory: {}", build_dir.display()));
    }

    emit_cargo_toml(tcfg, &reg, build_dir, &crate_cfg, workspace_members);
    if tcfg.translate_valist || use_nightly {
        emit_rust_toolchain(tcfg, build_dir);
    }
    crate_cfg.and_then(|ccfg| {
        emit_build_rs(tcfg, &reg, build_dir, ccfg.link_cmd);
        emit_lib_rs(
            tcfg,
            &reg,
            build_dir,
            ccfg.modules,
            ccfg.pragmas,
            &ccfg.crates,
        )
    })
}

#[derive(Serialize)]
struct Module {
    path: Option<String>,
    name: String,
    open: bool,
    close: bool,
}

#[derive(Debug, Default)]
struct ModuleTree(BTreeMap<String, ModuleTree>);

impl ModuleTree {
    /// Convert the tree representation into a linear vector
    /// and push it into `res`
    fn linearize(&self, res: &mut Vec<Module>) {
        for (name, child) in self.0.iter() {
            child.linearize_internal(name, res);
        }
    }

    fn linearize_internal(&self, name: &str, res: &mut Vec<Module>) {
        if self.0.is_empty() {
            res.push(Module {
                name: name.to_string(),
                path: None,
                open: false,
                close: false,
            });
        } else {
            res.push(Module {
                name: name.to_string(),
                path: None,
                open: true,
                close: false,
            });
            self.linearize(res);
            res.push(Module {
                name: name.to_string(),
                path: None,
                open: false,
                close: true,
            });
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
enum ModuleSubset {
    Binaries,
    Libraries,
    //Both,
}

fn convert_module_list(
    tcfg: &TranspilerConfig,
    build_dir: &Path,
    mut modules: Vec<PathBuf>,
    module_subset: ModuleSubset,
) -> Vec<Module> {
    modules.retain(|m| {
        let is_binary = tcfg.is_binary(m);
        let is_binary_subset = module_subset == ModuleSubset::Binaries;
        // Don't add binary modules to lib.rs, these are emitted to
        // standalone, separate binary modules.
        is_binary == is_binary_subset
    });

    let mut res = vec![];
    let mut module_tree = ModuleTree(BTreeMap::new());
    for m in &modules {
        match m.strip_prefix(build_dir) {
            Ok(relpath) if !tcfg.is_binary(m) => {
                // The module is inside the build directory, use nested modules
                let mut cur = &mut module_tree;
                for sm in relpath.iter() {
                    let path = Path::new(sm);
                    let name = get_module_name(path, true, false, false).unwrap();
                    cur = cur.0.entry(name).or_default();
                }
            }
            _ => {
                let relpath = diff_paths(m, build_dir).unwrap();
                let path = Some(relpath.to_str().unwrap().to_string());
                let name = get_module_name(m, true, false, false).unwrap();
                res.push(Module {
                    path,
                    name,
                    open: false,
                    close: false,
                });
            }
        }
    }
    module_tree.linearize(&mut res);
    res
}

fn convert_dependencies_list(crates: CrateSet) -> Vec<ExternCrateDetails> {
    crates.into_iter().map(|dep| dep.into()).collect()
}

fn get_lib_rs_file_name(tcfg: &TranspilerConfig) -> &str {
    if tcfg.output_dir.is_some() {
        "lib.rs"
    } else {
        "c2rust-lib.rs"
    }
}

/// Emit `build.rs` to make it easier to link in native libraries
fn emit_build_rs(
    tcfg: &TranspilerConfig,
    reg: &Handlebars,
    build_dir: &Path,
    link_cmd: &LinkCmd,
) -> Option<PathBuf> {
    let json = json!({
        "libraries": link_cmd.libs,
    });
    let output = reg.render("build.rs", &json).unwrap();
    let output_path = build_dir.join("build.rs");
    maybe_write_to_file(&output_path, output, tcfg.overwrite_existing)
}

/// Emit lib.rs (main.rs) for a library (binary). Returns `Some(path)`
/// to the generated file or `None` if the output file exists.
fn emit_lib_rs(
    tcfg: &TranspilerConfig,
    reg: &Handlebars,
    build_dir: &Path,
    modules: Vec<PathBuf>,
    pragmas: PragmaSet,
    crates: &CrateSet,
) -> Option<PathBuf> {
    let modules = convert_module_list(tcfg, build_dir, modules, ModuleSubset::Libraries);
    let crates = convert_dependencies_list(crates.clone());
    let file_name = get_lib_rs_file_name(tcfg);
    let json = json!({
        "lib_rs_file": file_name,
        "reorganize_definitions": tcfg.reorganize_definitions,
        "translate_valist": tcfg.translate_valist,
        "modules": modules,
        "pragmas": pragmas,
        "crates": crates,
    });

    let output_path = build_dir.join(file_name);
    let output = reg.render("lib.rs", &json).unwrap();

    maybe_write_to_file(&output_path, output, tcfg.overwrite_existing)
}

/// If we translate variadic functions, the output will only compile
/// on a nightly toolchain until the `c_variadics` feature is stable.
fn emit_rust_toolchain(tcfg: &TranspilerConfig, build_dir: &Path) {
    let output = r#"
    [toolchain]
    channel = "nightly"
    "#;

    let output_path = build_dir.join("rust-toolchain.toml");
    maybe_write_to_file(&output_path, output.to_string(), tcfg.overwrite_existing);
}

fn emit_cargo_toml(
    tcfg: &TranspilerConfig,
    reg: &Handlebars,
    build_dir: &Path,
    crate_cfg: &Option<CrateConfig<'_>>,
    workspace_members: Option<Vec<String>>,
) {
    // rust_checks_path is gone because we don't want to refer to the source
    // path but instead want the cross-check libs to be installed via cargo.
    let mut json = json!({
        "is_workspace": workspace_members.is_some(),
        "is_crate": crate_cfg.is_some(),
        "workspace_members": workspace_members.unwrap_or_default(),
    });
    if let Some(ccfg) = crate_cfg {
        let binaries = convert_module_list(
            tcfg,
            build_dir,
            ccfg.modules.to_owned(),
            ModuleSubset::Binaries,
        );
        let dependencies = convert_dependencies_list(ccfg.crates.clone());
        let crate_json = json!({
            "crate_name": ccfg.crate_name,
            "crate_rust_name": ccfg.crate_name.replace('-', "_"),
            "crate_types": ccfg.link_cmd.r#type.as_cargo_types(),
            "is_library": ccfg.link_cmd.r#type.is_library(),
            "lib_rs_file": get_lib_rs_file_name(tcfg),
            "binaries": binaries,
            "dependencies": dependencies,
        });
        json.as_object_mut().unwrap().extend(
            crate_json
                .as_object()
                .cloned() // FIXME: we need to clone it because there's no `into_object`
                .unwrap(),
        );
    }

    let file_name = "Cargo.toml";
    let output_path = build_dir.join(file_name);
    let output = reg.render(file_name, &json).unwrap();
    maybe_write_to_file(&output_path, output, tcfg.overwrite_existing);
}

fn maybe_write_to_file(output_path: &Path, output: String, overwrite: bool) -> Option<PathBuf> {
    if output_path.exists() && !overwrite {
        eprintln!("Skipping existing file {}", output_path.display());
        return None;
    }

    let mut file = match File::create(output_path) {
        Ok(file) => file,
        Err(e) => panic!("Unable to open file for writing: {}", e),
    };
    match file.write_all(output.as_bytes()) {
        Ok(()) => (),
        Err(e) => panic!("Unable to write translation to file: {}", e),
    };

    Some(PathBuf::from(output_path))
}
