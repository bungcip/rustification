use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::process;

use log::warn;

use crate::build_files::{CrateConfig, create_dir_all_or_panic, emit_build_files, get_build_dir};
use crate::c_ast::ConversionContext;
use crate::c_ast::Printer;
use crate::compile_cmds::get_compile_commands;
use crate::diagnostics;
use crate::generic_err;
use crate::reorganize::reorganize_definitions;
use crate::rust_ast::SpanExt;
use crate::rust_ast::set_span::SetSpan;
use crate::translator::pointer_wrappers::generate_global_pointer_wrapper_struct;
use crate::{
    CrateSet, PragmaSet, PragmaVec, RustChannel, TranspilerConfig, c_ast::*, translator::*,
    with_stmts::WithStmts,
};
use c2rust_ast_builder::mk;
use c2rust_ast_exporter as ast_exporter;
use c2rust_ast_printer::pprust;
use indexmap::{IndexMap, IndexSet};
use log::error;
use proc_macro2::Span;
use std::cell::RefCell;
use std::collections::HashMap;
use syn::{self, BinOp, Expr, Ident, Item, ReturnType, Stmt, Type, spanned::Spanned};

use crate::c_ast::get_node::GetNode;
use crate::c_ast::iterators::SomeId;
use crate::convert_type::TypeConverter;
use crate::diagnostics::TranslationResult;
use crate::get_module_name;
use crate::renamer::Renamer;
use crate::rust_ast::comment_store::CommentStore;
use crate::rust_ast::item_store::ItemStore;
use crate::translator::context::{ExprContext, FuncContext, MacroExpansion};
use crate::translator::{declaration_converter, preprocess};
use c2rust_ast_builder::properties::Mutability;

type TranspileResult = Result<(PathBuf, String, PragmaVec, CrateSet, RustChannel), ()>;

impl<'c> Translation<'c> {
    pub fn convert_main(&self, main_id: CDeclId) -> TranslationResult<Box<Item>> {
        if let CDeclKind::Function {
            ref parameters,
            typ,
            ..
        } = main_id.get_node(&self.ast_context).kind
        {
            let ret: CTypeKind = match self.ast_context.resolve_type(typ).kind {
                CTypeKind::Function(ret, _, _, _, _) => {
                    self.ast_context.resolve_type(ret.ctype).kind.clone()
                }
                ref k => {
                    return Err(generic_err!(
                        "Type of main function {:?} was not a function type, got {:?}",
                        main_id,
                        k
                    ));
                }
            };

            let main_fn_name = self
                .renamer
                .borrow()
                .get(&main_id)
                .expect("Could not find main function in renamer");

            let decl = mk().fn_decl("main", vec![], None, ReturnType::Default);

            let main_fn = mk().ident_expr(main_fn_name);

            let exit_fn = mk().abs_path_expr(vec!["std", "process", "exit"]);
            let args_fn = mk().abs_path_expr(vec!["std", "env", "args"]);
            let vars_fn = mk().abs_path_expr(vec!["std", "env", "vars"]);

            let no_args: Vec<Box<Expr>> = vec![];

            let mut stmts: Vec<Stmt> = vec![];
            let mut main_args: Vec<Box<Expr>> = vec![];

            let n = parameters.len();

            if n >= 2 {
                // `argv` and `argc`

                stmts.push(mk().local_stmt(Box::new(mk().local(
                    mk().mutbl().ident_pat("args"),
                    Some(mk().path_ty(vec![mk().path_segment_with_args(
                        "Vec",
                        mk().angle_bracketed_args(vec![
                            mk().mutbl().ptr_ty(mk().path_ty(vec!["ffi", "c_char"])),
                        ]),
                    )])),
                    Some(mk().call_expr(mk().path_expr(vec!["Vec", "new"]), vec![])),
                ))));
                stmts.push(mk().semi_stmt(mk().for_expr(
                    mk().ident_pat("arg"),
                    mk().call_expr(args_fn, vec![]),
                    mk().block(vec![mk().semi_stmt(mk().method_call_expr(
                        mk().ident_expr("args"),
                        "push",
                        vec![mk().method_call_expr(
                            mk().method_call_expr(
                                mk().call_expr(
                                    // TODO(kkysen) change `"std"` to `"alloc"` after `#![feature(alloc_c_string)]` is stabilized in `1.63.0`
                                    mk().abs_path_expr(vec!["std", "ffi", "CString", "new"]),
                                    vec![mk().ident_expr("arg")],
                                ),
                                "expect",
                                vec![mk().lit_expr("Failed to convert argument into CString.")],
                            ),
                            "into_raw",
                            vec![],
                        )],
                    ))]),
                    None::<Ident>,
                )));
                stmts.push(mk().semi_stmt(mk().method_call_expr(
                    mk().ident_expr("args"),
                    "push",
                    vec![
                        mk().call_expr(mk().abs_path_expr(vec!["core", "ptr", "null_mut"]), vec![]),
                    ],
                )));

                let argc_ty: Box<Type> = match parameters[0].get_node(&self.ast_context).kind {
                    CDeclKind::Variable { ref typ, .. } => self.convert_type(typ.ctype),
                    _ => Err(generic_err!(
                        "Cannot find type of 'argc' argument in main function",
                    )),
                }?;
                let argv_ty: Box<Type> = match parameters[1].get_node(&self.ast_context).kind {
                    CDeclKind::Variable { ref typ, .. } => self.convert_type(typ.ctype),
                    _ => Err(generic_err!(
                        "Cannot find type of 'argv' argument in main function",
                    )),
                }?;

                let args = mk().ident_expr("args");
                let argc = mk().binary_expr(
                    BinOp::Sub(Default::default()),
                    mk().method_call_expr(args.clone(), "len", no_args.clone()),
                    mk().lit_expr(1),
                );
                let argv = mk().method_call_expr(args, "as_mut_ptr", no_args.clone());

                main_args.push(mk().cast_expr(argc, argc_ty));
                main_args.push(mk().cast_expr(argv, argv_ty));
            }

            if n >= 3 {
                // non-standard `envp`

                stmts.push(mk().local_stmt(Box::new(mk().local(
                    mk().mutbl().ident_pat("vars"),
                    Some(mk().path_ty(vec![mk().path_segment_with_args(
                        "Vec",
                        mk().angle_bracketed_args(vec![
                            mk().mutbl().ptr_ty(mk().path_ty(vec!["ffi", "c_char"])),
                        ]),
                    )])),
                    Some(mk().call_expr(mk().path_expr(vec!["Vec", "new"]), vec![])),
                ))));
                let var_name_ident = mk().ident("var_name");
                let var_value_ident = mk().ident("var_value");
                stmts.push(mk().semi_stmt(mk().for_expr(
                    mk().tuple_pat(vec![
                        mk().ident_pat("var_name"),
                        mk().ident_pat("var_value"),
                    ]),
                    mk().call_expr(vars_fn, vec![]),
                    mk().block(vec![
                        mk().local_stmt(Box::new(mk().local(
                            mk().ident_pat("var"),
                            Some(mk().path_ty(vec!["String"])),
                            Some(mk().mac_expr(mk().call_mac(
                                "format",
                                vec![
                                    mk().lit_tt("{}={}"),
                                    mk().ident_tt(var_name_ident),
                                    mk().ident_tt(var_value_ident),
                                ],
                            ))),
                        ))),
                        mk().semi_stmt(mk().method_call_expr(
                            mk().ident_expr("vars"),
                            "push",
                            vec![mk().method_call_expr(
                                mk().method_call_expr(
                                    mk().call_expr(
                                        mk().abs_path_expr(vec![
                                            // TODO(kkysen) change `"std"` to `"alloc"` after `#![feature(alloc_c_string)]` is stabilized in `1.63.0`
                                            "std", "ffi", "CString", "new",
                                        ]),
                                        vec![mk().ident_expr("var")],
                                    ),
                                    "expect",
                                    vec![mk().lit_expr(
                                        "Failed to convert environment variable into CString.",
                                    )],
                                ),
                                "into_raw",
                                vec![],
                            )],
                        )),
                    ]),
                    None as Option<Ident>,
                )));
                stmts.push(mk().semi_stmt(mk().method_call_expr(
                    mk().ident_expr("vars"),
                    "push",
                    vec![
                        mk().call_expr(mk().abs_path_expr(vec!["core", "ptr", "null_mut"]), vec![]),
                    ],
                )));

                let envp_ty: Box<Type> = match parameters[2].get_node(&self.ast_context).kind {
                    CDeclKind::Variable { ref typ, .. } => self.convert_type(typ.ctype),
                    _ => Err(generic_err!(
                        "Cannot find type of 'envp' argument in main function",
                    )),
                }?;

                let envp = mk().method_call_expr(mk().ident_expr("vars"), "as_mut_ptr", no_args);

                main_args.push(mk().cast_expr(envp, envp_ty));
            }

            // Check `main` has the right form
            if n != 0 && n != 2 && n != 3 {
                return Err(generic_err!(
                    "Main function should have 0, 2, or 3 parameters, not {}.",
                    n
                ));
            };

            if let CTypeKind::Void = ret {
                let call_main = mk().call_expr(main_fn, main_args);
                let unsafe_block = mk().unsafe_block(vec![mk().expr_stmt(call_main)]);

                stmts.push(mk().expr_stmt(mk().unsafe_block_expr(unsafe_block)));

                let exit_arg = mk().lit_expr(mk().int_lit_with_suffix(0, "i32"));
                let call_exit = mk().call_expr(exit_fn, vec![exit_arg]);

                stmts.push(mk().semi_stmt(call_exit));
            } else {
                let call_main = mk().cast_expr(
                    mk().call_expr(main_fn, main_args),
                    mk().path_ty(vec!["i32"]),
                );

                let call_exit = mk().call_expr(exit_fn, vec![call_main]);
                let unsafe_block = mk().unsafe_block(vec![mk().expr_stmt(call_exit)]);

                stmts.push(mk().expr_stmt(mk().unsafe_block_expr(unsafe_block)));
            };

            let block = mk().block(stmts);
            Ok(mk().pub_().fn_item(decl, block))
        } else {
            Err(generic_err!(
                "Cannot translate non-function main entry point",
            ))
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum DecayRef {
    Yes,
    Default,
    No,
}

impl DecayRef {
    // Here we give intrinsic meaning to default to equate to yes/true
    // when actually evaluated
    pub fn is_yes(&self) -> bool {
        match self {
            DecayRef::Yes => true,
            DecayRef::Default => true,
            DecayRef::No => false,
        }
    }

    #[inline]
    pub fn is_no(&self) -> bool {
        !self.is_yes()
    }

    pub fn set_default_to_no(&mut self) {
        if *self == DecayRef::Default {
            *self = DecayRef::No;
        }
    }
}

impl From<bool> for DecayRef {
    fn from(b: bool) -> Self {
        match b {
            true => DecayRef::Yes,
            false => DecayRef::No,
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub enum ReplaceMode {
    None,
    Extern,
}

pub struct Translation<'c> {
    // Translation environment
    pub ast_context: TypedAstContext,
    pub tcfg: &'c TranspilerConfig,

    // Accumulated outputs
    pub features: RefCell<IndexSet<&'static str>>,
    pub sectioned_static_initializers: RefCell<Vec<Stmt>>,
    pub extern_crates: RefCell<CrateSet>,
    pub global_uses: RefCell<indexmap::IndexSet<Box<Item>>>, // contains global 'use' declarations which be emitted in submodule and main module
    pub need_pointer_wrapper: RefCell<bool>, // flag which used to generate associated struct definition

    // Translation state and utilities
    pub type_converter: RefCell<TypeConverter>,
    pub renamer: RefCell<Renamer<CDeclId>>,
    pub zero_inits: RefCell<IndexMap<CDeclId, WithStmts<Box<Expr>>>>,
    pub function_context: RefCell<FuncContext>,
    pub potential_flexible_array_members: RefCell<IndexSet<CDeclId>>,
    pub macro_expansions: RefCell<IndexMap<CDeclId, Option<MacroExpansion>>>,

    // Comment support
    pub comment_context: CommentContext,      // Incoming comments
    pub comment_store: RefCell<CommentStore>, // Outgoing comments

    pub spans: HashMap<SomeId, Span>,

    // Items indexed by file id of the source
    pub items: RefCell<IndexMap<FileId, ItemStore>>,

    // Mod names to try to stop collisions from happening
    pub mod_names: RefCell<IndexMap<String, PathBuf>>,

    // The main file id that the translator is operating on
    pub main_file: FileId,

    // While expanding an item, store the current file id that item is
    // expanded from. This is needed in order to note imports in items when
    // encountering DeclRefs.
    pub cur_file: RefCell<Option<FileId>>,
}

pub fn translate_failure(tcfg: &TranspilerConfig, msg: &str) {
    error!("{msg}");
    if tcfg.fail_on_error {
        error!("Translation failed, exiting");
        std::process::exit(1);
    }
}

/// This is the main entry point for the C-to-Rust translation process.
///
/// It takes a `TypedAstContext` (which contains the C AST) and a
/// `TranspilerConfig` and returns a string containing the translated Rust
/// code, along with some metadata.
///
/// The translation process is as follows:
///
/// 1.  **Initialization:** A `Translation` context is created, which holds
///     the state for the translation.
///
/// 2.  **AST Preprocessing:** The C AST is preprocessed to make it more
///     amenable to translation. This includes:
///     - Sorting top-level declarations by source location.
///     - Pruning unused declarations.
///     - Normalizing types.
///     - Collapsing unnamed structs/unions/enums with their typedefs.
///
/// 3.  **Name Generation:** Top-level names are populated into the renamer.
///
/// 4.  **Declaration Conversion:** All C declarations (types, functions,
///     variables) are converted to Rust items. This is the core of the
///     translation process.
///
/// 5.  **Main Function Conversion:** The C `main` function is converted to a
///     Rust `main` function.
///
/// 6.  **Static Initializers:** Global static initializers are generated if
///     needed.
///
/// 7.  **Module Generation:** If the `--reorganize-modules` flag is used,
///     the translated items are organized into submodules based on the
///     original C header files.
///
/// 8.  **Pretty-Printing:** The translated Rust items are pretty-printed
///     to a string.
pub fn translate(
    ast_context: TypedAstContext,
    tcfg: &TranspilerConfig,
    main_file: PathBuf,
) -> (String, PragmaVec, CrateSet, RustChannel) {
    let mut t = Translation::new(ast_context, tcfg, main_file.as_path());
    let ctx = ExprContext {
        used: true,
        is_static: false,
        is_const: false,
        decay_ref: DecayRef::Default,
        is_bitfield_write: false,
        inside_init_list_aop: false,
        needs_address: false,
        expecting_valistimpl: false,
        ternary_needs_parens: false,
        expanding_macro: None,
    };

    {
        // we convert libc type to core:ffi
        t.use_mod(vec!["core", "ffi"]);

        preprocess::preprocess_ast(&mut t);

        declaration_converter::convert_declarations(&mut t, ctx);

        // Add the main entry point
        if let Some(main_id) = t.ast_context.c_main {
            match t.convert_main(main_id) {
                Ok(item) => t.items.borrow_mut()[&t.main_file].add_item(item),
                Err(e) => {
                    let msg = format!("Failed to translate main: {e}");
                    translate_failure(t.tcfg, &msg)
                }
            }
        }

        // Initialize global statics when necessary
        if !t.sectioned_static_initializers.borrow().is_empty() {
            let (initializer_fn, initializer_static) = t.generate_global_static_init();
            let store = &mut t.items.borrow_mut()[&t.main_file];

            store.add_item(initializer_fn);
            store.add_item(initializer_static);
        }

        // generate struct for wrapping pointer for static variable
        if *t.need_pointer_wrapper.borrow() {
            let mut_decls_items = generate_global_pointer_wrapper_struct(Mutability::Mutable);
            let const_decls_items = generate_global_pointer_wrapper_struct(Mutability::Immutable);
            let store = &mut t.items.borrow_mut()[&t.main_file];

            store.add_item(mut_decls_items.0);
            store.add_item(mut_decls_items.1);

            store.add_item(const_decls_items.0);
            store.add_item(const_decls_items.1);
        }

        let pragmas = t.get_pragmas();
        let crates = t.extern_crates.borrow().clone();
        let global_uses = t.global_uses.borrow_mut().clone();

        let mut mod_items: Vec<Box<Item>> = Vec::new();

        // Keep track of new uses we need while building header submodules
        let mut new_uses = ItemStore::new();

        // Header Reorganization: Submodule Item Stores
        for (file_id, ref mut mod_item_store) in t.items.borrow_mut().iter_mut() {
            if *file_id != t.main_file {
                if tcfg.reorganize_definitions {
                    t.use_feature("register_tool");
                }
                let mut submodule = make_submodule(
                    &t.ast_context,
                    mod_item_store,
                    *file_id,
                    &mut new_uses,
                    &t.mod_names,
                    &t.global_uses,
                    tcfg.reorganize_definitions,
                    *t.need_pointer_wrapper.borrow(),
                );
                let comments = t.comment_context.get_remaining_comments(*file_id);
                submodule.set_span(match t.comment_store.borrow_mut().add_comments(&comments) {
                    Some(pos) => submodule.span().with_hi(pos),
                    None => submodule.span(),
                });
                mod_items.push(submodule);
            }
        }

        // Main file item store
        let (items, foreign_items, uses) = t.items.borrow_mut()[&t.main_file].drain();

        // Re-order comments
        // FIXME: We shouldn't have to replace with an empty comment store here, that's bad design
        let traverser = t
            .comment_store
            .replace(CommentStore::new())
            .into_comment_traverser();

        /*
        // Add a comment mapping span to each node that should have a
        // comment printed before it. The pretty printer picks up these
        // spans and uses them to decide when to emit comments.
        mod_items = mod_items
            .into_iter()
            .map(|i| traverser.traverse_item(*i)).map(Box::new)
            .collect();
        let foreign_items: Vec<ForeignItem> = foreign_items
            .into_iter()
            .map(|fi| traverser.traverse_foreign_item(fi))
            .collect();
        let items: Vec<Box<Item>> = items
            .into_iter()
            .map(|i| traverser.traverse_item(*i)).map(Box::new)
            .collect();
        */

        let mut reordered_comment_store = traverser.into_comment_store();
        let remaining_comments = t.comment_context.get_remaining_comments(t.main_file);
        reordered_comment_store.add_comments(&remaining_comments);

        // We need a dummy SourceMap with a dummy file so that pprust can try to
        // look up source line numbers for Spans. This is needed to be able to
        // print trailing comments after exprs/stmts/etc. on the same line. The
        // SourceMap will think that all Spans are invalid, but will return line
        // 0 for all of them.

        // FIXME: Use or delete this code
        // let comments = Comments::new(reordered_comment_store.into_comments());

        // pass all converted items to the Rust pretty printer
        let translation = pprust::to_string(|| {
            let (attrs, mut all_items) = arrange_header(&t, t.tcfg.is_binary(main_file.as_path()));

            // global uses before everything else
            all_items.extend(global_uses);

            all_items.extend(mod_items);

            // This could have been merged in with items below; however, it's more idiomatic to have
            // imports near the top of the file than randomly scattered about. Also, there is probably
            // no reason to have comments associated with imports so it doesn't need to go through
            // the above comment store process
            all_items.extend(uses.into_items());

            // Print new uses from submodules
            let (_, _, new_uses) = new_uses.drain();
            all_items.extend(new_uses.into_items());

            if !foreign_items.is_empty() {
                // in rust edition 2024, extern blocks must be unsafe
                all_items.push(mk().extern_("C").unsafe_().foreign_items(foreign_items));
            }

            // Add the items accumulated
            all_items.extend(items);

            //s.print_remaining_comments();
            syn::File {
                shebang: None,
                attrs,
                items: all_items.into_iter().map(|x| *x).collect(),
            }
        });

        // use nightly if translation has feature gate
        let channel = if !t.features.borrow().is_empty() {
            RustChannel::Nightly
        } else {
            RustChannel::Stable
        };

        (translation, pragmas, crates, channel)
    }
}

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
                Ok((module, translated_string, pragma_vec, crate_set, channel)) => {
                    write_module(&module, &translated_string);
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
                run_refactoring(&tcfg, &build_dir, crate_file);
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
        run_refactoring(&tcfg, &build_dir, crate_file);
    }

    tcfg.check_if_all_binaries_used(&transpiled_modules);

    if use_nightly {
        RustChannel::Nightly
    } else {
        RustChannel::Stable
    }
}

fn run_refactoring(tcfg: &TranspilerConfig, build_dir: &Path, crate_file: Option<PathBuf>) {
    if tcfg.reorganize_definitions {
        reorganize_definitions(tcfg, build_dir, crate_file)
            .unwrap_or_else(|e| warn!("Reorganizing definitions failed: {e}"));
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
    let (translated_string, pragmas, crates, channel) = translate(typed_context, tcfg, input_path);

    Ok((output_path, translated_string, pragmas, crates, channel))
}

fn write_module<P: AsRef<Path>>(path: P, content: &str) {
    let path = path.as_ref();
    let mut file = match fs::File::create(path) {
        Ok(file) => file,
        Err(e) => panic!("Unable to open file {} for writing: {}", path.display(), e),
    };

    use std::io::Write;
    if let Err(e) = file.write_all(content.as_bytes()) {
        panic!(
            "Unable to write translation to file {}: {}",
            path.display(),
            e
        );
    }
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
            create_dir_all_or_panic(parent);
        }
        output_path
    } else {
        input_path
    }
}
