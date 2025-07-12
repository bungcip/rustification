use std::cell::RefCell;
use std::char;
use std::collections::HashMap;
use std::ops::Index;
use std::path::{self, PathBuf};
use std::result::Result; // To override syn::Result from glob import

use context::{ExprContext, FuncContext};
use decls::ConvertedDecl;
use dtoa;

use indexmap::indexmap;
use indexmap::{IndexMap, IndexSet};
use log::{error, trace, warn};
use proc_macro2::{Punct, Spacing::*, Span, TokenStream, TokenTree};
use syn::spanned::Spanned as _;
use syn::*;
use syn::{BinOp, UnOp}; // To override c_ast::{BinOp,UnOp} from glob import

use crate::diagnostics::TranslationResult;
use crate::rust_ast::comment_store::CommentStore;
use crate::rust_ast::item_store::ItemStore;
use crate::rust_ast::set_span::SetSpan;
use crate::rust_ast::{SpanExt, pos_to_span};
use crate::transform;
use crate::translator::named_references::NamedReference;
use c2rust_ast_builder::{Builder, mk, properties::*};
use c2rust_ast_printer::pprust::{self};

use crate::c_ast;
use crate::c_ast::iterators::{DFExpr, SomeId};
use crate::cfg;
use crate::convert_type::TypeConverter;
use crate::renamer::Renamer;
use crate::with_stmts::WithStmts;
use crate::{ExternCrate, ExternCrateDetails, TranspilerConfig};
use crate::{RustChannel, c_ast::*, generic_err};
use c2rust_ast_exporter::clang_ast::LRValue;

mod assembly;
mod atomics;
mod builtins;
mod casts;
mod comments;
pub mod context;
mod decls;
mod exprs;
mod literals;
mod macros;
mod main_function;
mod named_references;
mod operators;
mod pointer_wrappers;
mod simd;
mod structs;
mod types;
mod variadic;

use crate::CrateSet;
use crate::PragmaVec;
pub use crate::diagnostics::{TranslationError, TranslationErrorKind};

pub const INNER_SUFFIX: &str = "_Inner";
pub const PADDING_SUFFIX: &str = "_PADDING";

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

#[derive(Clone)]
struct MacroExpansion {
    ty: CTypeId,
}

pub struct Translation<'c> {
    // Translation environment
    pub ast_context: TypedAstContext,
    pub tcfg: &'c TranspilerConfig,

    // Accumulated outputs
    pub features: RefCell<IndexSet<&'static str>>,
    sectioned_static_initializers: RefCell<Vec<Stmt>>,
    extern_crates: RefCell<CrateSet>,
    global_uses: RefCell<indexmap::IndexSet<Box<Item>>>, // contains global 'use' declarations which be emitted in submodule and main module
    has_static_array_of_pointer: RefCell<bool>, // flag which used to generate associated struct definition

    // Translation state and utilities
    type_converter: RefCell<TypeConverter>,
    renamer: RefCell<Renamer<CDeclId>>,
    zero_inits: RefCell<IndexMap<CDeclId, WithStmts<Box<Expr>>>>,
    function_context: RefCell<FuncContext>,
    potential_flexible_array_members: RefCell<IndexSet<CDeclId>>,
    macro_expansions: RefCell<IndexMap<CDeclId, Option<MacroExpansion>>>,

    // Comment support
    pub comment_context: CommentContext,      // Incoming comments
    pub comment_store: RefCell<CommentStore>, // Outgoing comments

    spans: HashMap<SomeId, Span>,

    // Items indexed by file id of the source
    items: RefCell<IndexMap<FileId, ItemStore>>,

    // Mod names to try to stop collisions from happening
    mod_names: RefCell<IndexMap<String, PathBuf>>,

    // The main file id that the translator is operating on
    main_file: FileId,

    // While expanding an item, store the current file id that item is
    // expanded from. This is needed in order to note imports in items when
    // encountering DeclRefs.
    cur_file: RefCell<Option<FileId>>,
}

/// Pointer offset that casts its argument to isize
fn pointer_offset(
    ptr: Box<Expr>,
    offset: Box<Expr>,
    multiply_by: Option<Box<Expr>>,
    neg: bool,
    mut deref: bool,
) -> Box<Expr> {
    let mut offset = transform::cast_int(offset, "isize", false);

    if let Some(mul) = multiply_by {
        let mul = transform::cast_int(mul, "isize", false);
        offset = mk().binary_expr(BinOp::Mul(Default::default()), offset, mul);
        deref = false;
    }

    if neg {
        offset = mk().unary_expr(UnOp::Neg(Default::default()), offset);
    }

    let res = mk().method_call_expr(ptr, "offset", vec![offset]);
    if deref {
        mk().unary_expr(UnOp::Deref(Default::default()), res)
    } else {
        res
    }
}

/// Given an expression with type Option<fn(...)->...>, unwrap
/// the Option and return the function.
fn unwrap_function_pointer(ptr: Box<Expr>) -> Box<Expr> {
    let err_msg = mk().lit_expr("non-null function pointer");
    mk().method_call_expr(ptr, "expect", vec![err_msg])
}

fn transmute_expr(source_ty: Box<Type>, target_ty: Box<Type>, expr: Box<Expr>) -> Box<Expr> {
    let type_args = match (&*source_ty, &*target_ty) {
        (Type::Infer(_), Type::Infer(_)) => Vec::new(),
        _ => vec![source_ty, target_ty],
    };
    let mut path = vec![mk().path_segment("core"), mk().path_segment("mem")];

    if type_args.is_empty() {
        path.push(mk().path_segment("transmute"));
    } else {
        path.push(mk().path_segment_with_args("transmute", mk().angle_bracketed_args(type_args)));
    }

    mk().call_expr(mk().abs_path_expr(path), vec![expr])
}

fn vec_expr(val: Box<Expr>, count: Box<Expr>) -> Box<Expr> {
    let from_elem = mk().abs_path_expr(vec!["std", "vec", "from_elem"]);
    mk().call_expr(from_elem, vec![val, count])
}

pub fn stmts_block(mut stmts: Vec<Stmt>) -> Block {
    match stmts.pop() {
        None => {}
        Some(Stmt::Expr(
            Expr::Block(ExprBlock {
                block, label: None, ..
            }),
            _semi,
        )) if stmts.is_empty() => return block,
        Some(mut s) => {
            if let Stmt::Expr(e, _semi) = s {
                s = Stmt::Expr(e, _semi);
            }
            stmts.push(s);
        }
    }
    mk().block(stmts)
}

/// Generate link attributes needed to ensure that the generated Rust libraries have the right symbol values.
fn mk_linkage(in_extern_block: bool, new_name: &str, old_name: &str) -> Builder {
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

// This should only be used for tests
fn prefix_names(translation: &mut Translation, prefix: &str) {
    for (&decl_id, ref mut decl) in translation.ast_context.iter_mut_decls() {
        match decl.kind {
            CDeclKind::Function {
                ref mut name,
                ref body,
                ..
            } if body.is_some() => {
                // SIMD types are imported and do not need to be renamed
                if name.starts_with("_mm") {
                    continue;
                }

                name.insert_str(0, prefix);

                translation.renamer.borrow_mut().insert(decl_id, name);
            }
            CDeclKind::Variable {
                ref mut ident,
                has_static_duration,
                has_thread_duration,
                ..
            } if has_static_duration || has_thread_duration => ident.insert_str(0, prefix),
            _ => (),
        }
    }
}

// This function is meant to create module names, for modules being created with the
// `--reorganize-modules` flag. So what is done is, change '.' && '-' to '_', and depending
// on whether there is a collision or not prepend the prior directory name to the path name.
// To check for collisions, a IndexMap with the path name(key) and the path(value) associated with
// the name. If the path name is in use, but the paths differ there is a collision.
pub(crate) fn clean_path(
    mod_names: &RefCell<IndexMap<String, PathBuf>>,
    path: Option<&path::Path>,
) -> String {
    fn path_to_str(path: &path::Path) -> String {
        path.file_name()
            .unwrap()
            .to_str()
            .unwrap()
            .replace(['.', '-'], "_")
    }

    let mut file_path: String = path.map_or("internal".to_string(), path_to_str);
    let path = path.unwrap_or_else(|| path::Path::new(""));
    let mut mod_names = mod_names.borrow_mut();
    if !mod_names.contains_key(&file_path.clone()) {
        mod_names.insert(file_path.clone(), path.to_path_buf());
    } else {
        let mod_path = mod_names.get(&file_path.clone()).unwrap();
        // A collision in the module names has occurred.
        // Ex: types.h can be included from
        // /usr/include/bits and /usr/include/sys
        if mod_path != path {
            let split_path: Vec<PathBuf> = path
                .to_path_buf()
                .parent()
                .unwrap()
                .iter()
                .map(PathBuf::from)
                .collect();

            let mut to_prepend = path_to_str(split_path.last().unwrap());
            to_prepend.push('_');
            file_path.insert_str(0, &to_prepend);
        }
    }
    file_path
}

pub fn translate_failure(tcfg: &TranspilerConfig, msg: &str) {
    error!("{msg}");
    if tcfg.fail_on_error {
        panic!("Translation failed, see error above");
    }
}

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

        // Sort the top-level declarations by file and source location so that we
        // preserve the ordering of all declarations in each file.
        t.ast_context.sort_top_decls();

        t.locate_comments();

        // Headers often pull in declarations that are unused;
        // we simplify the translator output by omitting those.
        t.ast_context
            .prune_unwanted_decls(tcfg.preserve_unused_functions);

        enum Name<'a> {
            Var(&'a str),
            Type(&'a str),
            Anonymous,
            None,
        }

        fn some_type_name(s: Option<&str>) -> Name {
            match s {
                None => Name::Anonymous,
                Some(r) => Name::Type(r),
            }
        }

        // Used for testing; so that we don't overlap with C function names
        if let Some(ref prefix) = t.tcfg.prefix_function_names {
            prefix_names(&mut t, prefix);
        }

        // Identify typedefs that name unnamed types and collapse the two declarations
        // into a single name and declaration, eliminating the typedef altogether.
        let mut prenamed_decls: IndexMap<CDeclId, CDeclId> = IndexMap::new();
        for (&decl_id, decl) in t.ast_context.iter_decls() {
            if let CDeclKind::Typedef { ref name, typ, .. } = decl.kind {
                if let Some(subdecl_id) = t
                    .ast_context
                    .resolve_type(typ.ctype)
                    .kind
                    .as_underlying_decl()
                {
                    use CDeclKind::*;
                    let is_unnamed = match t.ast_context[subdecl_id].kind {
                        Struct { name: None, .. }
                        | Union { name: None, .. }
                        | Enum { name: None, .. } => true,

                        // Detect case where typedef and struct share the same name.
                        // In this case the purpose of the typedef was simply to eliminate
                        // the need for the 'struct' tag when referring to the type name.
                        Struct {
                            name: Some(ref target_name),
                            ..
                        }
                        | Union {
                            name: Some(ref target_name),
                            ..
                        }
                        | Enum {
                            name: Some(ref target_name),
                            ..
                        } => name == target_name,

                        _ => false,
                    };

                    if is_unnamed
                        && !prenamed_decls
                            .values()
                            .any(|decl_id| *decl_id == subdecl_id)
                    {
                        prenamed_decls.insert(decl_id, subdecl_id);

                        t.type_converter
                            .borrow_mut()
                            .declare_decl_name(decl_id, name);
                        t.type_converter
                            .borrow_mut()
                            .alias_decl_name(subdecl_id, decl_id);
                    }
                }
            }
        }

        t.ast_context.prenamed_decls = prenamed_decls;

        // Helper function that returns true if there is either a matching typedef or its
        // corresponding struct/union/enum
        fn contains(prenamed_decls: &IndexMap<CDeclId, CDeclId>, decl_id: &CDeclId) -> bool {
            prenamed_decls.contains_key(decl_id)
                || prenamed_decls.values().any(|id| *id == *decl_id)
        }

        // Populate renamer with top-level names
        for (&decl_id, decl) in t.ast_context.iter_decls() {
            use CDeclKind::*;
            let decl_name = match decl.kind {
                _ if contains(&t.ast_context.prenamed_decls, &decl_id) => Name::None,
                Struct { ref name, .. } => some_type_name(name.as_ref().map(String::as_str)),
                Enum { ref name, .. } => some_type_name(name.as_ref().map(String::as_str)),
                Union { ref name, .. } => some_type_name(name.as_ref().map(String::as_str)),
                Typedef { ref name, .. } => Name::Type(name),
                Function { ref name, .. } => Name::Var(name),
                EnumConstant { ref name, .. } => Name::Var(name),
                Variable { ref ident, .. } if t.ast_context.c_decls_top.contains(&decl_id) => {
                    Name::Var(ident)
                }
                MacroObject { ref name, .. } => Name::Var(name),
                _ => Name::None,
            };
            match decl_name {
                Name::None => (),
                Name::Anonymous => {
                    t.type_converter
                        .borrow_mut()
                        .declare_decl_name(decl_id, "C2RustUnnamed");
                }
                Name::Type(name) => {
                    t.type_converter
                        .borrow_mut()
                        .declare_decl_name(decl_id, name);
                }
                Name::Var(name) => {
                    t.renamer.borrow_mut().insert(decl_id, name);
                }
            }
        }

        {
            let convert_type = |decl_id: CDeclId, decl: &CDecl| {
                let decl_file_id = t.ast_context.file_id(decl);
                if t.tcfg.reorganize_definitions {
                    *t.cur_file.borrow_mut() = decl_file_id;
                }
                match t.convert_decl(ctx, decl_id) {
                    Err(e) => {
                        let k = &t.ast_context.get_decl(&decl_id).map(|x| &x.kind);
                        let msg = format!("Skipping declaration {k:?} due to error: {e}");
                        translate_failure(t.tcfg, &msg);
                    }
                    Ok(converted_decl) => match converted_decl {
                        ConvertedDecl::Item(item) => {
                            t.insert_item(item, decl);
                        }
                        ConvertedDecl::ForeignItem(item) => {
                            t.insert_foreign_item(*item, decl);
                        }
                        ConvertedDecl::Items(items) => {
                            for item in items {
                                t.insert_item(Box::new(item), decl);
                            }
                        }
                        ConvertedDecl::NoItem => {}
                    },
                }
                t.cur_file.borrow_mut().take();

                if t.tcfg.reorganize_definitions && decl_file_id.is_some_and(|id| id != t.main_file)
                {
                    t.generate_submodule_imports(decl_id, decl_file_id);
                }
            };

            // Export all types
            for (&decl_id, decl) in t.ast_context.iter_decls() {
                use CDeclKind::*;
                let needs_export = match decl.kind {
                    Struct { .. } => true,
                    Enum { .. } => true,
                    EnumConstant { .. } => true,
                    Union { .. } => true,
                    Typedef { .. } => {
                        // Only check the key as opposed to `contains`
                        // because the key should be the typedef id
                        !t.ast_context.prenamed_decls.contains_key(&decl_id)
                    }
                    _ => false,
                };
                if needs_export {
                    convert_type(decl_id, decl);
                }
            }
        }

        // Export top-level value declarations
        for top_id in &t.ast_context.c_decls_top {
            use CDeclKind::*;
            let needs_export = match t.ast_context[*top_id].kind {
                Function { is_implicit, .. } => !is_implicit,
                Variable { .. } => true,
                MacroObject { .. } => tcfg.translate_const_macros,
                MacroFunction { .. } => tcfg.translate_fn_macros,
                _ => false,
            };
            if needs_export {
                let decl_opt = t.ast_context.get_decl(top_id);
                let decl = decl_opt.as_ref().unwrap();
                let decl_file_id = t.ast_context.file_id(decl);

                if t.tcfg.reorganize_definitions && decl_file_id.is_some_and(|id| id != t.main_file)
                {
                    *t.cur_file.borrow_mut() = decl_file_id;
                }
                match t.convert_decl(ctx, *top_id) {
                    Err(e) => {
                        let decl = &t.ast_context.get_decl(top_id);
                        let msg = match decl {
                            Some(decl) => {
                                let decl_identifier = decl.kind.get_name().map_or_else(
                                    || {
                                        t.ast_context
                                            .display_loc(&decl.loc)
                                            .map_or("Unknown".to_string(), |l| format!("at {l}"))
                                    },
                                    |name| name.clone(),
                                );
                                format!("Failed to translate {decl_identifier}: {e}")
                            }
                            _ => format!("Failed to translate declaration: {e}",),
                        };
                        translate_failure(t.tcfg, &msg);
                    }
                    Ok(converted_decl) => match converted_decl {
                        ConvertedDecl::Item(item) => {
                            t.insert_item(item, decl);
                        }
                        ConvertedDecl::ForeignItem(item) => {
                            t.insert_foreign_item(*item, decl);
                        }
                        ConvertedDecl::Items(items) => {
                            for item in items {
                                t.insert_item(Box::new(item), decl);
                            }
                        }
                        ConvertedDecl::NoItem => {}
                    },
                }
                t.cur_file.borrow_mut().take();

                if t.tcfg.reorganize_definitions && decl_file_id.is_some_and(|id| id != t.main_file)
                {
                    t.generate_submodule_imports(*top_id, decl_file_id);
                }
            }
        }

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
        if *t.has_static_array_of_pointer.borrow() {
            let mut_decls_items = t.generate_global_pointer_wrapper_struct(Mutability::Mutable);
            let const_decls_items = t.generate_global_pointer_wrapper_struct(Mutability::Immutable);
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
        let channel = if t.features.borrow().is_empty() == false {
            RustChannel::Nightly
        } else {
            RustChannel::Stable
        };

        (translation, pragmas, crates, channel)
    }
}

fn item_ident(i: &Item) -> Option<&Ident> {
    use Item::*;
    Some(match i {
        Const(ic) => &ic.ident,
        Enum(ie) => &ie.ident,
        ExternCrate(iec) => &iec.ident,
        Fn(ifn) => &ifn.sig.ident,
        ForeignMod(_ifm) => return None,
        Impl(_ii) => return None,
        Macro(im) => return im.ident.as_ref(),
        Mod(im) => &im.ident,
        Static(is) => &is.ident,
        Struct(is) => &is.ident,
        Trait(it) => &it.ident,
        TraitAlias(ita) => &ita.ident,
        Type(it) => &it.ident,
        Union(iu) => &iu.ident,
        Use(ItemUse { tree: _, .. }) => unimplemented!(),
        Verbatim(_tokenstream) => {
            warn!("cannot determine name of tokenstream item");
            return None;
        }
        _ => {
            warn!("cannot determine name of unknown item kind");
            return None;
        }
    })
}

fn item_vis(i: &Item) -> Option<Visibility> {
    use Item::*;
    Some(
        match i {
            Const(ic) => &ic.vis,
            Enum(ie) => &ie.vis,
            ExternCrate(iec) => &iec.vis,
            Fn(ifn) => &ifn.vis,
            ForeignMod(_ifm) => return None,
            Impl(_ii) => return None,
            Macro(_im) => return None,
            Mod(im) => &im.vis,
            Static(is) => &is.vis,
            Struct(is) => &is.vis,
            Trait(it) => &it.vis,
            TraitAlias(ita) => &ita.vis,
            Type(it) => &it.vis,
            Union(iu) => &iu.vis,
            Use(ItemUse { vis, .. }) => vis,
            Verbatim(_tokenstream) => {
                warn!("cannot determine visibility of tokenstream item");
                return None;
            }
            _ => {
                warn!("cannot determine visibility of unknown item kind");
                return None;
            }
        }
        .clone(),
    )
}

fn foreign_item_ident_vis(fi: &ForeignItem) -> Option<(&Ident, Visibility)> {
    use ForeignItem::*;
    Some(match fi {
        Fn(ifn) => (&ifn.sig.ident, ifn.vis.clone()),
        Static(is) => (&is.ident, is.vis.clone()),
        Type(it) => (&it.ident, it.vis.clone()),
        Macro(_im) => return None,
        Verbatim(_tokenstream) => {
            warn!("cannot determine name and visibility of tokenstream foreign item");
            return None;
        }
        _ => {
            warn!("cannot determine name and visibility of unknown foreign item kind");
            return None;
        }
    })
}

fn make_submodule(
    ast_context: &TypedAstContext,
    item_store: &mut ItemStore,
    file_id: FileId,
    use_item_store: &mut ItemStore,
    mod_names: &RefCell<IndexMap<String, PathBuf>>,
    global_uses: &RefCell<indexmap::IndexSet<Box<Item>>>,
    reorganize_definitions: bool,
) -> Box<Item> {
    let (mut items, foreign_items, uses) = item_store.drain();
    let file_path = ast_context.get_file_path(file_id);
    let include_line_number = ast_context
        .get_file_include_line_number(file_id)
        .unwrap_or(0);
    let mod_name = clean_path(mod_names, file_path);

    for item in items.iter() {
        let ident_name = match item_ident(item) {
            Some(i) => i.to_string(),
            None => continue,
        };
        let use_path = vec!["self".into(), mod_name.clone()];

        let vis = match item_vis(item) {
            Some(Visibility::Public(_)) => mk().pub_(),
            Some(_) => mk(),
            None => continue,
        };

        use_item_store.add_use_with_attr(use_path, &ident_name, vis);
    }

    for foreign_item in foreign_items.iter() {
        let ident_name = match foreign_item_ident_vis(foreign_item) {
            Some((ident, _vis)) => ident.to_string(),
            None => continue,
        };
        let use_path = vec!["self".into(), mod_name.clone()];

        use_item_store.add_use(use_path, &ident_name);
    }

    // add global uses
    for item in global_uses.borrow().iter() {
        items.push(item.clone());
    }

    for item in uses.into_items() {
        items.push(item);
    }

    if !foreign_items.is_empty() {
        items.push(mk().unsafe_().extern_("C").foreign_items(foreign_items));
    }

    let module_builder = mk().vis("pub");
    let module_builder = if reorganize_definitions {
        let file_path_str = file_path.map_or(mod_name.as_str(), |path| {
            path.to_str().expect("Found invalid unicode")
        });
        module_builder.str_attr(
            vec!["c2rust", "header_src"],
            format!("{file_path_str}:{include_line_number}"),
        )
    } else {
        module_builder
    };
    module_builder.mod_item(mod_name, Some(mk().mod_(items)))
}

// TODO(kkysen) shouldn't need `extern crate`
/// Pretty-print the leading pragmas and extern crate declarations
// Fixing this would require major refactors for marginal benefit.
#[allow(clippy::vec_box)]
fn arrange_header(t: &Translation, is_binary: bool) -> (Vec<syn::Attribute>, Vec<Box<Item>>) {
    let mut out_attrs = vec![];
    let mut out_items = vec![];
    if t.tcfg.emit_modules && !is_binary {
        for c in t.extern_crates.borrow().iter() {
            out_items.push(mk().use_simple_item(
                mk().abs_path(vec![ExternCrateDetails::from(*c).ident]),
                None::<Ident>,
            ))
        }
    } else {
        let pragmas = t.get_pragmas();
        for (key, mut values) in pragmas {
            values.sort_unstable();
            // generate #[key(values)]
            let meta = mk().meta_list(vec![key], values);
            let attr = mk().attribute(AttrStyle::Inner(Default::default()), meta);
            out_attrs.push(attr);
        }

        if t.tcfg.emit_no_std {
            let meta = mk().meta_path("no_std");
            let attr = mk().attribute(AttrStyle::Inner(Default::default()), meta);
            out_attrs.push(attr);
        }

        if is_binary {
            // TODO(kkysen) shouldn't need `extern crate`
            // Add `extern crate X;` to the top of the file
            for extern_crate in t.extern_crates.borrow().iter() {
                let extern_crate = ExternCrateDetails::from(*extern_crate);
                if extern_crate.macro_use {
                    out_items.push(
                        mk().single_attr("macro_use")
                            .extern_crate_item(extern_crate.ident.clone(), None),
                    );
                }
            }

            out_items.push(mk().use_glob_item(mk().abs_path(vec![&t.tcfg.crate_name()])));
        }
    }
    (out_attrs, out_items)
}

/// Add a src_loc = "line:col" attribute to an item/foreign_item
fn add_src_loc_attr(attrs: &mut Vec<syn::Attribute>, src_loc: &Option<SrcLoc>) {
    if let Some(src_loc) = src_loc.as_ref() {
        let loc_str = format!("{}:{}", src_loc.line, src_loc.column);
        let meta = mk().meta_namevalue(vec!["c2rust", "src_loc"], loc_str);
        // let prepared = mk().prepare_meta(meta);
        let attr = mk().attribute(AttrStyle::Outer, meta);
        attrs.push(attr);
    }
}

/// Get a mutable reference to the attributes of a ForeignItem
fn foreign_item_attrs(item: &mut ForeignItem) -> Option<&mut Vec<syn::Attribute>> {
    use ForeignItem::*;
    Some(match item {
        Fn(ForeignItemFn { attrs, .. }) => attrs,
        Static(ForeignItemStatic { attrs, .. }) => attrs,
        Type(ForeignItemType { attrs, .. }) => attrs,
        Macro(ForeignItemMacro { attrs, .. }) => attrs,
        Verbatim(TokenStream { .. }) => return None,
        _ => return None,
    })
}

/// Get a mutable reference to the attributes of an Item
fn item_attrs(item: &mut Item) -> Option<&mut Vec<syn::Attribute>> {
    use Item::*;
    Some(match item {
        Const(ItemConst { attrs, .. }) => attrs,
        Enum(ItemEnum { attrs, .. }) => attrs,
        ExternCrate(ItemExternCrate { attrs, .. }) => attrs,
        Fn(ItemFn { attrs, .. }) => attrs,
        ForeignMod(ItemForeignMod { attrs, .. }) => attrs,
        Impl(ItemImpl { attrs, .. }) => attrs,
        Macro(ItemMacro { attrs, .. }) => attrs,
        Mod(ItemMod { attrs, .. }) => attrs,
        Static(ItemStatic { attrs, .. }) => attrs,
        Struct(ItemStruct { attrs, .. }) => attrs,
        Trait(ItemTrait { attrs, .. }) => attrs,
        TraitAlias(ItemTraitAlias { attrs, .. }) => attrs,
        Type(ItemType { attrs, .. }) => attrs,
        Union(ItemUnion { attrs, .. }) => attrs,
        Use(ItemUse { attrs, .. }) => attrs,
        Verbatim(TokenStream { .. }) => return None,
        _ => return None,
    })
}

struct ConvertedVariable {
    pub ty: Box<Type>,
    pub mutbl: Mutability,
    pub init: TranslationResult<WithStmts<Box<Expr>>>,
}

impl<'c> Translation<'c> {
    pub fn new(
        mut ast_context: TypedAstContext,
        tcfg: &'c TranspilerConfig,
        main_file: &path::Path,
    ) -> Self {
        let comment_context = CommentContext::new(&mut ast_context);
        let mut type_converter = TypeConverter::new();

        if tcfg.translate_valist {
            type_converter.translate_valist = true
        }

        let main_file = ast_context.find_file_id(main_file).unwrap_or(0);
        let items = indexmap! {main_file => ItemStore::new()};

        Translation {
            features: RefCell::new(IndexSet::new()),
            type_converter: RefCell::new(type_converter),
            ast_context,
            tcfg,
            renamer: RefCell::new(Renamer::new(&[
                // Keywords currently in use
                "as", "break", "const", "continue", "crate", "else", "enum", "extern", "false",
                "fn", "for", "if", "impl", "in", "let", "loop", "match", "mod", "move", "mut",
                "pub", "ref", "return", "Self", "self", "static", "struct", "super", "trait",
                "true", "type", "unsafe", "use", "where", "while", "dyn",
                // Keywords reserved for future use
                "abstract", "alignof", "become", "box", "do", "final", "macro", "offsetof",
                "override", "priv", "proc", "pure", "sizeof", "typeof", "unsized", "virtual",
                "async", "try", "yield", // Prevent use for other reasons
                "main",  // prelude names
                "drop", "ffi", "Some", "None", "Ok", "Err",
            ])),
            zero_inits: RefCell::new(IndexMap::new()),
            function_context: RefCell::new(FuncContext::new()),
            potential_flexible_array_members: RefCell::new(IndexSet::new()),
            macro_expansions: RefCell::new(IndexMap::new()),
            has_static_array_of_pointer: RefCell::new(false),
            comment_context,
            comment_store: RefCell::new(CommentStore::new()),
            spans: HashMap::new(),
            sectioned_static_initializers: RefCell::new(Vec::new()),
            items: RefCell::new(items),
            mod_names: RefCell::new(IndexMap::new()),
            main_file,
            extern_crates: RefCell::new(IndexSet::new()),
            global_uses: RefCell::new(IndexSet::new()),
            cur_file: RefCell::new(None),
        }
    }

    fn use_crate(&self, extern_crate: ExternCrate) {
        self.extern_crates.borrow_mut().insert(extern_crate);
    }

    /// Add a new use to the current file in top of file
    /// ex: use ::core:ffi;
    fn use_mod(&self, mod_name: Vec<&'static str>) {
        let decl = mk().use_simple_item(mod_name, None::<String>);
        self.global_uses.borrow_mut().insert(decl);
    }

    pub fn cur_file(&self) -> FileId {
        if let Some(cur_file) = *self.cur_file.borrow() {
            cur_file
        } else {
            self.main_file
        }
    }

    fn with_cur_file_item_store<F, T>(&self, f: F) -> T
    where
        F: FnOnce(&mut ItemStore) -> T,
    {
        let mut item_stores = self.items.borrow_mut();
        let item_store = item_stores.entry(Self::cur_file(self)).or_default();
        f(item_store)
    }

    /// Called when translation makes use of a language feature that will require a feature-gate.
    pub fn use_feature(&self, feature: &'static str) {
        self.features.borrow_mut().insert(feature);
    }

    pub fn get_pragmas(&self) -> PragmaVec {
        let mut features = vec![];
        features.extend(self.features.borrow().iter());
        features.extend(self.type_converter.borrow().features_used());
        let mut pragmas: PragmaVec = vec![(
            "allow",
            vec![
                "non_upper_case_globals",
                "non_camel_case_types",
                "non_snake_case",
                "dead_code",
                "mutable_transmutes",
                "unused_mut",
                "unused_assignments",
                "unused_unsafe",
                "unused_variables",
                "unsafe_op_in_unsafe_fn",
                "path_statements",
            ],
        )];

        if self.features.borrow().contains("register_tool") {
            pragmas.push(("register_tool", vec!["c2rust"]));
        }

        if !features.is_empty() {
            pragmas.push(("feature", features));
        }
        pragmas
    }

    // This node should _never_ show up in the final generated code. This is an easy way to notice
    // if it does.
    pub fn panic_or_err(&self, msg: &str) -> Box<Expr> {
        self.panic_or_err_helper(msg, self.tcfg.panic_on_translator_failure)
    }

    pub fn panic(&self, msg: &str) -> Box<Expr> {
        self.panic_or_err_helper(msg, true)
    }

    fn panic_or_err_helper(&self, msg: &str, panic: bool) -> Box<Expr> {
        let macro_name = if panic { "panic" } else { "compile_error" };
        let macro_msg = vec![TokenTree::Literal(proc_macro2::Literal::string(msg))]
            .into_iter()
            .collect::<TokenStream>();
        mk().mac_expr(mk().mac(
            mk().path(vec![macro_name]),
            macro_msg,
            MacroDelimiter::Paren(Default::default()),
        ))
    }

    fn static_initializer_is_unsafe(&self, expr_id: Option<CExprId>, qty: CQualTypeId) -> bool {
        // SIMD types are always unsafe in statics
        match self.ast_context.resolve_type(qty.ctype).kind {
            CTypeKind::Vector(..) => return true,
            CTypeKind::ConstantArray(ctype, ..) => {
                let kind = &self.ast_context.resolve_type(ctype).kind;

                if let CTypeKind::Vector(..) = kind {
                    return true;
                }
            }
            _ => {}
        }

        // Get the initializer if there is one
        let expr_id = match expr_id {
            Some(expr_id) => expr_id,
            None => return false,
        };

        // Look for code which can only be translated unsafely
        let iter = DFExpr::new(&self.ast_context, expr_id.into());

        for i in iter {
            let expr_id = match i {
                SomeId::Expr(expr_id) => expr_id,
                _ => unreachable!("Found static initializer type other than expr"),
            };

            use CExprKind::*;
            match self.ast_context[expr_id].kind {
                DeclRef(_, _, LRValue::LValue) => return true,
                ImplicitCast(_, _, cast_kind, _, _) | ExplicitCast(_, _, cast_kind, _, _) => {
                    use CastKind::*;
                    match cast_kind {
                        IntegralToPointer | FunctionToPointerDecay | PointerToIntegral => {
                            return true;
                        }
                        _ => {}
                    }
                }
                _ => {}
            }
        }

        false
    }

    /// The purpose of this function is to decide on whether or not a static initializer's
    /// translation is able to be compiled as a valid rust static initializer
    fn static_initializer_is_uncompilable(
        &self,
        expr_id: Option<CExprId>,
        qtype: CQualTypeId,
    ) -> bool {
        use crate::c_ast::BinOp::{Add, Divide, Modulus, Multiply, Subtract};
        use crate::c_ast::CastKind::{IntegralToPointer, PointerToIntegral};
        use crate::c_ast::UnOp::{AddressOf, Negate};

        let expr_id = match expr_id {
            Some(expr_id) => expr_id,
            None => return false,
        };

        // The f128 crate doesn't currently provide a way to const initialize
        // values, except for common mathematical constants
        if let CTypeKind::LongDouble = self.ast_context[qtype.ctype].kind {
            return true;
        }

        let iter = DFExpr::new(&self.ast_context, expr_id.into());

        for i in iter {
            let expr_id = match i {
                SomeId::Expr(expr_id) => expr_id,
                _ => unreachable!("Found static initializer type other than expr"),
            };

            use CExprKind::*;
            match self.ast_context[expr_id].kind {
                // Technically we're being conservative here, but it's only the most
                // contrived array indexing initializers that would be accepted
                ArraySubscript(..) => return true,
                Member(..) => return true,

                Conditional(..) => return true,
                Unary(typ, Negate, _, _) => {
                    if self
                        .ast_context
                        .resolve_type(typ.ctype)
                        .kind
                        .is_unsigned_integral_type()
                    {
                        return true;
                    }
                }

                // PointerToIntegral is no longer allowed, const-eval throws an
                // error: "pointer-to-integer cast" needs an rfc before being
                // allowed inside constants
                ImplicitCast(_, _, PointerToIntegral, _, _)
                | ExplicitCast(_, _, PointerToIntegral, _, _) => return true,

                Binary(typ, op, _, _, _, _) => {
                    let problematic_op = matches!(op, Add | Subtract | Multiply | Divide | Modulus);

                    if problematic_op {
                        let k = &self.ast_context.resolve_type(typ.ctype).kind;
                        if k.is_unsigned_integral_type() || k.is_pointer() {
                            return true;
                        }
                    }
                }
                Unary(_, AddressOf, expr_id, _) => {
                    if let Member(_, expr_id, _, _, _) = self.ast_context[expr_id].kind {
                        if let DeclRef(..) = self.ast_context[expr_id].kind {
                            return true;
                        }
                    }
                }
                InitList(qtype, _, _, _) => {
                    let ty = &self.ast_context.resolve_type(qtype.ctype).kind;

                    if let &CTypeKind::Struct(decl_id) = ty {
                        let decl = &self.ast_context[decl_id].kind;

                        if let CDeclKind::Struct {
                            fields: Some(fields),
                            ..
                        } = decl
                        {
                            for field_id in fields {
                                let field_decl = &self.ast_context[*field_id].kind;

                                if let CDeclKind::Field {
                                    bitfield_width: Some(_),
                                    ..
                                } = field_decl
                                {
                                    return true;
                                }
                            }
                        }
                    }
                }
                ImplicitCast(qtype, _, IntegralToPointer, _, _)
                | ExplicitCast(qtype, _, IntegralToPointer, _, _) => {
                    if let CTypeKind::Pointer(qtype) =
                        self.ast_context.resolve_type(qtype.ctype).kind
                    {
                        if let CTypeKind::Function(..) =
                            self.ast_context.resolve_type(qtype.ctype).kind
                        {
                            return true;
                        }
                    }
                }
                _ => {}
            }
        }

        false
    }

    fn add_static_initializer_to_section(
        &self,
        name: &str,
        typ: CQualTypeId,
        init: &mut Box<Expr>,
    ) -> TranslationResult<()> {
        let mut default_init = self
            .implicit_default_expr(typ.ctype, true, false)?
            .to_expr();

        std::mem::swap(init, &mut default_init);

        let root_lhs_expr = mk().path_expr(vec![name]);
        let assign_expr = mk().assign_expr(root_lhs_expr, default_init);
        let stmt = mk().expr_stmt(assign_expr);

        self.sectioned_static_initializers.borrow_mut().push(stmt);

        Ok(())
    }

    fn generate_global_static_init(&mut self) -> (Box<Item>, Box<Item>) {
        // If we don't want to consume self.sectioned_static_initializers for some reason, we could clone the vec
        let sectioned_static_initializers = self.sectioned_static_initializers.replace(Vec::new());

        let fn_name = self
            .renamer
            .borrow_mut()
            .pick_name("run_static_initializers");
        let fn_ty = ReturnType::Default;
        let fn_decl = mk().fn_decl(fn_name.clone(), vec![], None, fn_ty.clone());
        let fn_bare_decl = (vec![], None, fn_ty);
        let fn_block = mk().block(sectioned_static_initializers);
        let fn_item = mk().unsafe_().extern_("C").fn_item(fn_decl, fn_block);

        let static_attributes = mk()
            .single_attr("used")
            .call_attr(
                "cfg_attr",
                vec![
                    mk().meta_namevalue("target_os", "linux"),
                    mk().meta_list(
                        "unsafe",
                        vec![mk().meta_namevalue("link_section", ".init_array")],
                    ),
                ],
            )
            .call_attr(
                "cfg_attr",
                vec![
                    mk().meta_namevalue("target_os", "windows"),
                    mk().meta_list(
                        "unsafe",
                        vec![mk().meta_namevalue("link_section", ".CRT$XIB")],
                    ),
                ],
            )
            .call_attr(
                "cfg_attr",
                vec![
                    mk().meta_namevalue("target_os", "macos"),
                    mk().meta_list(
                        "unsafe",
                        vec![mk().meta_namevalue("link_section", ".__DATA,__mod_init_func")],
                    ),
                ],
            );
        let static_array_size = mk().lit_expr(1);
        let static_ty = mk().array_ty(
            mk().unsafe_().extern_("C").barefn_ty(fn_bare_decl),
            static_array_size,
        );
        let static_val = mk().array_expr(vec![mk().path_expr(vec![fn_name])]);
        let static_item = static_attributes.static_item("INIT_ARRAY", static_ty, static_val);

        (fn_item, static_item)
    }

    fn canonical_macro_replacement(
        &self,
        ctx: ExprContext,
        replacements: &[CExprId],
    ) -> TranslationResult<(Box<Expr>, CTypeId)> {
        let (val, ty) = replacements
            .iter()
            .try_fold::<Option<(WithStmts<Box<Expr>>, CTypeId)>, _, _>(None, |canonical, id| {
                let ty = self.ast_context[*id]
                    .kind
                    .get_type()
                    .ok_or_else(|| generic_err!("Invalid expression type"))?;
                let (expr_id, ty) = self
                    .ast_context
                    .resolve_expr_type_id(*id)
                    .unwrap_or((*id, ty));
                let expr = self.convert_expr(ctx, expr_id)?;

                // Join ty and cur_ty to the smaller of the two types. If the
                // types are not cast-compatible, abort the fold.
                let ty_kind = self.ast_context.resolve_type(ty).kind.clone();
                if let Some((canon_val, canon_ty)) = canonical {
                    let canon_ty_kind = self.ast_context.resolve_type(canon_ty).kind.clone();
                    if let Some(smaller_ty) =
                        CTypeKind::smaller_compatible_type(canon_ty_kind.clone(), ty_kind)
                    {
                        if smaller_ty == canon_ty_kind {
                            Ok(Some((canon_val, canon_ty)))
                        } else {
                            Ok(Some((expr, ty)))
                        }
                    } else {
                        Err(generic_err!(
                            "Not all macro expansions are compatible types"
                        ))
                    }
                } else {
                    Ok(Some((expr, ty)))
                }
            })?
            .ok_or_else(|| generic_err!("Could not find a valid type for macro"))?;

        val.to_unsafe_pure_expr()
            .map(|val| (val, ty))
            .ok_or_else(|| generic_err!("Macro expansion is not a pure expression"))

        // TODO: Validate that all replacements are equivalent and pick the most
        // common type to minimize casts.
    }

    pub fn convert_cfg(
        &self,
        name: &str,
        graph: cfg::Cfg<cfg::Label, cfg::StmtOrDecl>,
        store: cfg::DeclStmtStore,
        live_in: IndexSet<CDeclId>,
        cut_out_trailing_ret: bool,
    ) -> TranslationResult<Vec<Stmt>> {
        if self.tcfg.dump_function_cfgs {
            graph
                .dump_dot_graph(
                    &self.ast_context,
                    &store,
                    self.tcfg.dump_cfg_liveness,
                    self.tcfg.use_c_loop_info,
                    format!("{}_{}.dot", "cfg", name),
                )
                .expect("Failed to write CFG .dot file");
        }
        if self.tcfg.json_function_cfgs {
            graph
                .dump_json_graph(&store, format!("{}_{}.json", "cfg", name))
                .expect("Failed to write CFG .json file");
        }

        let (lifted_stmts, relooped) = cfg::relooper::reloop(
            graph,
            store,
            self.tcfg.simplify_structures,
            self.tcfg.use_c_loop_info,
            self.tcfg.use_c_multiple_info,
            live_in,
        );

        if self.tcfg.dump_structures {
            eprintln!("Relooped structures:");
            for s in &relooped {
                eprintln!("  {s:#?}");
            }
        }

        let current_block_ident = self.renamer.borrow_mut().pick_name("current_block");
        let current_block = mk().ident_expr(&current_block_ident);
        let mut stmts: Vec<Stmt> = lifted_stmts;
        if cfg::structures::has_multiple(&relooped) {
            if self.tcfg.fail_on_multiple {
                panic!("Uses of `current_block' are illegal with `--fail-on-multiple'.");
            }

            let current_block_ty = if self.tcfg.debug_relooper_labels {
                mk().ref_lt_ty("static", mk().path_ty(vec!["str"]))
            } else {
                mk().path_ty(vec!["u64"])
            };

            let local = mk().local(
                mk().mutbl().ident_pat(current_block_ident),
                Some(current_block_ty),
                None,
            );
            stmts.push(mk().local_stmt(Box::new(local)))
        }

        stmts.extend(cfg::structures::structured_cfg(
            &relooped,
            &mut self.comment_store.borrow_mut(),
            current_block,
            self.tcfg.debug_relooper_labels,
            cut_out_trailing_ret,
        )?);
        Ok(stmts)
    }

    fn convert_function_body(
        &self,
        ctx: ExprContext,
        name: &str,
        body_ids: &[CStmtId],
        ret: cfg::ImplicitReturnType,
    ) -> TranslationResult<Vec<Stmt>> {
        // Function body scope
        self.with_scope(|| {
            let (graph, store) = cfg::Cfg::from_stmts(self, ctx, body_ids, ret)?;
            self.convert_cfg(name, graph, store, IndexSet::new(), true)
        })
    }

    /// Search for references to the given declaration in a value position
    /// inside the given expression. Uses of the declaration inside typeof
    /// operations are ignored because our translation will ignore them
    /// and use the computed types instead.
    fn has_decl_reference(&self, decl_id: CDeclId, expr_id: CExprId) -> bool {
        let mut iter = DFExpr::new(&self.ast_context, expr_id.into());
        while let Some(x) = iter.next() {
            match x {
                SomeId::Expr(e) => match self.ast_context[e].kind {
                    CExprKind::DeclRef(_, d, _) if d == decl_id => return true,
                    CExprKind::UnaryType(_, _, Some(_), _) => iter.prune(1),
                    _ => {}
                },
                SomeId::Type(t) => {
                    if let CTypeKind::TypeOfExpr(_) = self.ast_context[t].kind {
                        iter.prune(1);
                    }
                }
                _ => {}
            }
        }
        false
    }

    pub fn convert_decl_stmt_info(
        &self,
        ctx: ExprContext,
        decl_id: CDeclId,
    ) -> TranslationResult<cfg::DeclStmtInfo> {
        if let CDeclKind::Variable {
            ref ident,
            has_static_duration: true,
            is_externally_visible: false,
            is_defn: true,
            initializer,
            typ,
            ..
        } = self.ast_context.index(decl_id).kind
        {
            if self.static_initializer_is_uncompilable(initializer, typ) {
                let ident2 = self
                    .renamer
                    .borrow_mut()
                    .insert_root(decl_id, ident)
                    .ok_or_else(|| {
                        generic_err!("Unable to rename function scoped static initializer",)
                    })?;
                let ConvertedVariable { ty, mutbl: _, init } =
                    self.convert_variable(ctx.static_(), initializer, typ)?;
                let default_init = self
                    .implicit_default_expr(typ.ctype, true, ctx.inside_init_list_aop)?
                    .to_expr();
                let comment = String::from("// Initialized in run_static_initializers");
                let span = self
                    .comment_store
                    .borrow_mut()
                    .add_comments(&[comment])
                    .map(pos_to_span)
                    .unwrap_or_else(Span::call_site);
                let static_item = mk()
                    .span(span)
                    .mutbl()
                    .static_item(&ident2, ty, default_init);
                let mut init = init?;
                init.set_unsafe();
                let mut init = init.to_expr();

                self.add_static_initializer_to_section(&ident2, typ, &mut init)?;
                self.items.borrow_mut()[&self.main_file].add_item(static_item);

                return Ok(cfg::DeclStmtInfo::empty());
            }
        };

        match self.ast_context.index(decl_id).kind {
            CDeclKind::Variable {
                has_static_duration: false,
                has_thread_duration: false,
                is_externally_visible: false,
                is_defn,
                ref ident,
                initializer,
                typ,
                ..
            } => {
                assert!(
                    is_defn,
                    "Only local variable definitions should be extracted"
                );

                let rust_name = self
                    .renamer
                    .borrow_mut()
                    .insert(decl_id, ident)
                    .unwrap_or_else(|| panic!("Failed to insert variable '{ident}'"));

                if self.ast_context.is_va_list(typ.ctype) {
                    // translate `va_list` variables to `VaListImpl`s and omit the initializer.
                    let pat_mut = mk().set_mutbl("mut").ident_pat(rust_name);
                    let ty = {
                        let path = vec!["core", "ffi", "VaListImpl"];
                        mk().path_ty(mk().abs_path(path))
                    };
                    let local_mut = mk().local(pat_mut, Some(ty), None);

                    return Ok(cfg::DeclStmtInfo::new(
                        vec![],                                     // decl
                        vec![],                                     // assign
                        vec![mk().local_stmt(Box::new(local_mut))], // decl_and_assign
                    ));
                }

                let has_self_reference = if let Some(expr_id) = initializer {
                    self.has_decl_reference(decl_id, expr_id)
                } else {
                    false
                };

                let mut stmts = self.compute_variable_array_sizes(ctx, typ.ctype)?;

                let ConvertedVariable { ty, mutbl, init } =
                    self.convert_variable(ctx, initializer, typ)?;
                let mut init = init?;

                stmts.append(init.stmts_mut());
                let init = init.into_value();

                let zeroed = self.implicit_default_expr(typ.ctype, false, false)?;
                let zeroed = if ctx.is_const {
                    zeroed.to_unsafe_pure_expr()
                } else {
                    zeroed.to_pure_expr()
                }
                .expect("Expected decl initializer to not have any statements");
                let pat_mut = mk().set_mutbl("mut").ident_pat(rust_name.clone());
                let local_mut = mk().local(pat_mut, Some(ty.clone()), Some(zeroed));
                if has_self_reference {
                    let assign = mk().assign_expr(mk().ident_expr(rust_name), init);

                    let mut assign_stmts = stmts.clone();
                    assign_stmts.push(mk().semi_stmt(assign.clone()));

                    let mut decl_and_assign = vec![mk().local_stmt(Box::new(local_mut.clone()))];
                    decl_and_assign.append(&mut stmts);
                    decl_and_assign.push(mk().expr_stmt(assign));

                    Ok(cfg::DeclStmtInfo::new(
                        vec![mk().local_stmt(Box::new(local_mut))],
                        assign_stmts,
                        decl_and_assign,
                    ))
                } else {
                    let pat = mk().set_mutbl(mutbl).ident_pat(rust_name.clone());

                    let type_annotation = if self.tcfg.reduce_type_annotations
                        && !self.should_assign_type_annotation(typ.ctype, initializer)
                    {
                        None
                    } else {
                        Some(ty)
                    };

                    let local = mk().local(pat, type_annotation, Some(init.clone()));
                    let assign = mk().assign_expr(mk().ident_expr(rust_name), init);

                    let mut assign_stmts = stmts.clone();
                    assign_stmts.push(mk().semi_stmt(assign));

                    let mut decl_and_assign = stmts;
                    decl_and_assign.push(mk().local_stmt(Box::new(local)));

                    Ok(cfg::DeclStmtInfo::new(
                        vec![mk().local_stmt(Box::new(local_mut))],
                        assign_stmts,
                        decl_and_assign,
                    ))
                }
            }

            ref decl => {
                let inserted = if let Some(ident) = decl.get_name() {
                    self.renamer.borrow_mut().insert(decl_id, ident).is_some()
                } else {
                    false
                };

                // TODO: We need this because we can have multiple 'extern' decls of the same variable.
                //       When we do, we must make sure to insert into the renamer the first time, and
                //       then skip subsequent times.
                use CDeclKind::*;
                let skip = match decl {
                    Variable { .. } => !inserted,
                    Struct { .. } => true,
                    Union { .. } => true,
                    Enum { .. } => true,
                    Typedef { .. } => true,
                    _ => false,
                };

                if skip {
                    Ok(cfg::DeclStmtInfo::new(vec![], vec![], vec![]))
                } else {
                    let items = match self.convert_decl(ctx, decl_id)? {
                        ConvertedDecl::Item(item) => vec![*item],
                        ConvertedDecl::ForeignItem(item) => {
                            vec![*mk().unsafe_().extern_("C").foreign_items(vec![*item])]
                        }
                        ConvertedDecl::Items(items) => items,
                        ConvertedDecl::NoItem => return Ok(cfg::DeclStmtInfo::empty()),
                    };

                    let item_stmt = |item| mk().item_stmt(Box::new(item));
                    Ok(cfg::DeclStmtInfo::new(
                        items.iter().cloned().map(item_stmt).collect(),
                        vec![],
                        items.into_iter().map(item_stmt).collect(),
                    ))
                }
            }
        }
    }

    fn should_assign_type_annotation(
        &self,
        ctypeid: CTypeId,
        initializer: Option<CExprId>,
    ) -> bool {
        let initializer_kind = initializer.map(|expr_id| &self.ast_context[expr_id].kind);

        // If the RHS is a func call, we should be able to skip type annotation
        // because we get a type from the function return type
        if let Some(CExprKind::Call(_, _, _)) = initializer_kind {
            return false;
        }

        use CTypeKind::*;
        match self.ast_context.resolve_type(ctypeid).kind {
            Pointer(CQualTypeId { ctype, .. }) => {
                match self.ast_context.resolve_type(ctype).kind {
                    Function(..) => {
                        // Fn pointers need to be type annotated if null
                        if initializer.is_none() {
                            return true;
                        }

                        // None assignments don't provide enough type information unless there are follow-up assignments
                        if let Some(CExprKind::ImplicitCast(_, _, CastKind::NullToPointer, _, _)) =
                            initializer_kind
                        {
                            return true;
                        }

                        // We could set this to false and skip non null fn ptr annotations. This will work
                        // 99% of the time, however there is a strange case where fn ptr comparisons
                        // complain PartialEq is not implemented for the type inferred function type,
                        // but the identical type that is explicitly defined doesn't seem to have that issue
                        // Probably a rustc bug. See https://github.com/rust-lang/rust/issues/53861
                        true
                    }
                    _ => {
                        // Non function null ptrs provide enough information to skip
                        // type annotations; ie `= 0 as *const MyStruct;`
                        if initializer.is_none() {
                            return false;
                        }

                        if let Some(CExprKind::ImplicitCast(_, _, cast_kind, _, _)) =
                            initializer_kind
                        {
                            match cast_kind {
                                CastKind::NullToPointer => return false,
                                CastKind::ConstCast => return true,
                                _ => {}
                            };
                        }

                        // ref decayed ptrs generally need a type annotation
                        if let Some(CExprKind::Unary(_, c_ast::UnOp::AddressOf, _, _)) =
                            initializer_kind
                        {
                            return true;
                        }

                        false
                    }
                }
            }
            // For some reason we don't seem to apply type suffixes when 0-initializing
            // so type annotation is need for 0-init ints and floats at the moment, but
            // they could be simplified in favor of type suffixes
            Bool | Char | SChar | Short | Int | Long | LongLong | UChar | UShort | UInt | ULong
            | ULongLong | LongDouble | Int128 | UInt128 => initializer.is_none(),
            Float | Double => initializer.is_none(),
            Struct(_) | Union(_) | Enum(_) => false,
            Function(..) => unreachable!("Can't have a function directly as a type"),
            Typedef(_) => unreachable!("Typedef should be expanded though resolve_type"),
            _ => true,
        }
    }

    fn convert_variable(
        &self,
        ctx: ExprContext,
        initializer: Option<CExprId>,
        typ: CQualTypeId,
    ) -> TranslationResult<ConvertedVariable> {
        let type_kind = self.ast_context.resolve_type(typ.ctype).kind.clone();

        let ty = match type_kind {
            // Variable declarations for variable-length arrays use the type of a pointer to the
            // underlying array element
            CTypeKind::VariableArray(mut elt, _) => {
                elt = self.variable_array_base_type(elt);
                let ty = self.convert_type(elt)?;
                mk().path_ty(vec![
                    mk().path_segment_with_args("Vec", mk().angle_bracketed_args(vec![ty])),
                ])
            }

            CTypeKind::ConstantArray(_, size) if ctx.is_static => {
                // for other array of pointer, we use PointerMut or PointerConst to wrap it
                if let Some(cqt) = self.check_type_is_constant_aop(typ.ctype) {
                    // need to generate PointerMut struct
                    *self.has_static_array_of_pointer.borrow_mut() = true;

                    let name = if cqt.qualifiers.is_const {
                        "Pointer"
                    } else {
                        "PointerMut"
                    };

                    let rtype = self.convert_type(cqt.ctype)?;

                    let pointer_type =
                        mk().path_ty(vec![mk().path_segment_with_args(
                            name,
                            mk().angle_bracketed_args(vec![rtype]),
                        )]);
                    let size = mk().lit_expr(mk().int_lit(size as u64));
                    mk().array_ty(pointer_type, size)
                } else {
                    self.convert_type(typ.ctype)?
                }
            }

            _ => self.convert_type(typ.ctype)?,
        };

        let init = match initializer {
            Some(x) => self.convert_expr(ctx.used(), x),
            None => self.implicit_default_expr(typ.ctype, ctx.is_static, ctx.inside_init_list_aop),
        };

        let mutbl = if typ.qualifiers.is_const {
            Mutability::Immutable
        } else {
            Mutability::Mutable
        };

        Ok(ConvertedVariable { ty, mutbl, init })
    }

    /// Construct an expression for a NULL at any type, including forward declarations,
    /// function pointers, and normal pointers.
    fn null_ptr(
        &self,
        type_id: CTypeId,
        is_static: bool,
        inside_init_list_aop: bool,
    ) -> TranslationResult<Box<Expr>> {
        if self.ast_context.is_function_pointer(type_id) {
            return Ok(mk().path_expr(vec!["None"]));
        }

        let pointee = match self.ast_context.resolve_type(type_id).kind {
            CTypeKind::Pointer(pointee) => pointee,
            _ => return Err(generic_err!("null_ptr requires a pointer")),
        };
        let ty = self.convert_type(type_id)?;
        let mut zero = mk().lit_expr(0);
        if is_static && pointee.qualifiers.is_const == false {
            let mut qtype = pointee;
            qtype.qualifiers.is_const = true;
            let ty_ = self
                .type_converter
                .borrow_mut()
                .convert_pointer(&self.ast_context, qtype)?;
            zero = mk().cast_expr(zero, ty_);
        }

        let mut cast = mk().cast_expr(zero, ty);

        // wrap it in a PointerMut or Pointer if it is a static array of pointers
        if is_static && inside_init_list_aop {
            let name = if pointee.qualifiers.is_const {
                "Pointer"
            } else {
                "PointerMut"
            };

            cast = mk().call_expr(mk().ident_expr(name), vec![cast]);
        }

        Ok(cast)
    }
    /// Variable element arrays are represented by a flat array of non-variable-length array
    /// elements. This function traverses potentially multiple levels of variable-length array
    /// to find the underlying element type.
    fn variable_array_base_type(&self, mut elt: CTypeId) -> CTypeId {
        while let CTypeKind::VariableArray(elt_, _) = self.ast_context.resolve_type(elt).kind {
            elt = elt_;
        }
        elt
    }

    /// This generates variables that store the computed sizes of the variable-length arrays in
    /// the given type.
    pub fn compute_variable_array_sizes(
        &self,
        ctx: ExprContext,
        mut type_id: CTypeId,
    ) -> TranslationResult<Vec<Stmt>> {
        let mut stmts = vec![];

        loop {
            match self.ast_context.resolve_type(type_id).kind {
                CTypeKind::Pointer(elt) => type_id = elt.ctype,
                CTypeKind::ConstantArray(elt, _) => type_id = elt,
                CTypeKind::VariableArray(elt, Some(expr_id)) => {
                    type_id = elt;

                    // Convert this expression
                    let expr = self.convert_expr(ctx.used(), expr_id)?.and_then(|expr| {
                        let name = self
                            .renamer
                            .borrow_mut()
                            .insert(CDeclId(expr_id.0), "vla")
                            .unwrap(); // try using declref name?
                        // TODO: store the name corresponding to expr_id

                        let local = mk().local(
                            mk().ident_pat(name),
                            None,
                            Some(mk().cast_expr(expr, mk().path_ty(vec!["usize"]))),
                        );

                        let res: TranslationResult<WithStmts<()>> =
                            Ok(WithStmts::new(vec![mk().local_stmt(Box::new(local))], ()));
                        res
                    })?;

                    stmts.extend(expr.into_stmts());
                }
                _ => break,
            }
        }

        Ok(stmts)
    }

    // Compute the size of a type
    // Rust type: usize
    pub fn compute_size_of_type(
        &self,
        ctx: ExprContext,
        type_id: CTypeId,
    ) -> TranslationResult<WithStmts<Box<Expr>>> {
        if let CTypeKind::VariableArray(elts, len) = self.ast_context.resolve_type(type_id).kind {
            let len = len.expect("Sizeof a VLA type with count expression omitted");

            let elts = self.compute_size_of_type(ctx, elts)?;
            return elts.and_then(|lhs| {
                let len = self.convert_expr(ctx.used().not_static(), len)?;
                Ok(len.map(|len| {
                    let rhs = transform::cast_int(len, "usize", true);
                    mk().binary_expr(BinOp::Mul(Default::default()), lhs, rhs)
                }))
            });
        }
        let ty = self.convert_type(type_id)?;
        self.mk_size_of_ty_expr(ty)
    }

    fn mk_size_of_ty_expr(&self, ty: Box<Type>) -> TranslationResult<WithStmts<Box<Expr>>> {
        let name = "size_of";
        let params = mk().angle_bracketed_args(vec![ty]);
        let path = vec![
            mk().path_segment("core"),
            mk().path_segment("mem"),
            mk().path_segment_with_args(name, params),
        ];
        let call = mk().call_expr(mk().abs_path_expr(path), vec![]);

        Ok(WithStmts::new_val(call))
    }

    pub fn compute_align_of_type(
        &self,
        mut type_id: CTypeId,
        preferred: bool,
    ) -> TranslationResult<WithStmts<Box<Expr>>> {
        type_id = self.variable_array_base_type(type_id);

        let ty = self.convert_type(type_id)?;
        let tys = vec![ty];
        let mut path = vec![mk().path_segment("core")];
        if preferred {
            self.use_feature("core_intrinsics");
            path.push(mk().path_segment("intrinsics"));
            path.push(mk().path_segment_with_args("pref_align_of", mk().angle_bracketed_args(tys)));
        } else {
            path.push(mk().path_segment("mem"));
            path.push(mk().path_segment_with_args("align_of", mk().angle_bracketed_args(tys)));
        }
        let call = mk().call_expr(mk().abs_path_expr(path), vec![]);
        Ok(WithStmts::new_val(call))
    }

    pub fn convert_constant(&self, constant: ConstIntExpr) -> TranslationResult<Box<Expr>> {
        let expr = match constant {
            ConstIntExpr::U(n) => mk().lit_expr(mk().int_lit(n)),
            ConstIntExpr::I(n) => mk().lit_expr(mk().int_lit(n)),
        };
        Ok(expr)
    }

    /// If `ctx` is unused, convert `expr` to a semi statement, otherwise return
    /// `expr`.
    fn convert_side_effects_expr(
        &self,
        ctx: ExprContext,
        expr: WithStmts<Box<Expr>>,
        panic_msg: &str,
    ) -> TranslationResult<WithStmts<Box<Expr>>> {
        if ctx.is_unused() {
            // Recall that if `used` is false, the `stmts` field of the output must contain
            // all side-effects (and a function call can always have side-effects)
            expr.and_then(|expr| {
                Ok(WithStmts::new(
                    vec![mk().semi_stmt(expr)],
                    self.panic_or_err(panic_msg),
                ))
            })
        } else {
            Ok(expr)
        }
    }

    fn convert_statement_expression(
        &self,
        ctx: ExprContext,
        compound_stmt_id: CStmtId,
    ) -> TranslationResult<WithStmts<Box<Expr>>> {
        fn as_semi_break_stmt(stmt: &Stmt, lbl: &cfg::Label) -> Option<Option<Box<Expr>>> {
            if let Stmt::Expr(
                Expr::Break(ExprBreak {
                    label: Some(blbl),
                    expr: ret_val,
                    ..
                }),
                _,
            ) = stmt
            {
                if blbl.ident == mk().label(lbl.pretty_print()).name.ident {
                    return Some(ret_val.clone());
                }
            }
            None
        }

        match self.ast_context[compound_stmt_id].kind {
            CStmtKind::Compound(ref substmt_ids) if !substmt_ids.is_empty() => {
                let n = substmt_ids.len();
                let result_id = substmt_ids[n - 1];

                let name = format!("<stmt-expr_{compound_stmt_id:?}>");
                let lbl = cfg::Label::FromC(compound_stmt_id, None);

                let mut stmts = match self.ast_context[result_id].kind {
                    CStmtKind::Expr(expr_id) => {
                        let ret = cfg::ImplicitReturnType::StmtExpr(ctx, expr_id, lbl.clone());
                        self.convert_function_body(ctx, &name, &substmt_ids[0..(n - 1)], ret)?
                    }

                    _ => self.convert_function_body(
                        ctx,
                        &name,
                        substmt_ids,
                        cfg::ImplicitReturnType::Void,
                    )?,
                };

                if let Some(stmt) = stmts.pop() {
                    match as_semi_break_stmt(&stmt, &lbl) {
                        Some(val) => {
                            let block = mk().block_expr(match val {
                                None => mk().block(stmts),
                                Some(val) => WithStmts::new(stmts, val).to_block(),
                            });

                            // enclose block in parentheses to work around
                            // https://github.com/rust-lang/rust/issues/54482
                            let val = mk().paren_expr(block);
                            let stmts = if ctx.is_unused() {
                                vec![mk().semi_stmt(val.clone())]
                            } else {
                                Vec::new()
                            };

                            return Ok(WithStmts::new(stmts, val));
                        }
                        _ => stmts.push(stmt),
                    }
                }

                let block_body = mk().block(stmts.clone());
                let val: Box<Expr> = mk().labelled_block_expr(block_body, lbl.pretty_print());

                Ok(WithStmts::new(stmts, val))
            }
            _ => {
                if ctx.is_unused() {
                    let val =
                        self.panic_or_err("Empty statement expression is not supposed to be used");
                    Ok(WithStmts::new_val(val))
                } else {
                    Err(generic_err!("Bad statement expression"))
                }
            }
        }
    }

    /// Produce zero-initializers for structs/unions/enums, looking them up when possible.
    fn zero_initializer(
        &self,
        decl_id: CDeclId,
        type_id: CTypeId,
        is_static: bool,
    ) -> TranslationResult<WithStmts<Box<Expr>>> {
        if let Some(file_id) = self.cur_file.borrow().as_ref() {
            self.import_type(type_id, *file_id);
        }

        // Look up the decl in the cache and return what we find (if we find anything)
        if let Some(init) = self.zero_inits.borrow().get(&decl_id) {
            return Ok(init.clone());
        }

        let name_decl_id = match self.ast_context.index(type_id).kind {
            CTypeKind::Typedef(decl_id) => decl_id,
            _ => decl_id,
        };

        // Otherwise, construct the initializer
        let mut init = match self.ast_context.index(decl_id).kind {
            // Zero initialize all of the fields
            CDeclKind::Struct {
                fields: Some(ref fields),
                platform_byte_size,
                ..
            } => {
                let name = self.resolve_decl_inner_name(name_decl_id);
                self.convert_struct_zero_initializer(
                    name,
                    decl_id,
                    fields,
                    platform_byte_size,
                    is_static,
                )?
            }

            CDeclKind::Struct { fields: None, .. } => {
                return Err(generic_err!(
                    "Attempted to zero-initialize forward-declared struct",
                ));
            }

            // Zero initialize the first field
            CDeclKind::Union { ref fields, .. } => {
                let name = self
                    .type_converter
                    .borrow()
                    .resolve_decl_name(decl_id)
                    .unwrap();

                let fields = match *fields {
                    Some(ref fields) => fields,
                    None => {
                        return Err(generic_err!(
                            "Attempted to zero-initialize forward-declared struct",
                        ));
                    }
                };

                let &field_id = fields
                    .first()
                    .ok_or_else(|| generic_err!("A union should have a field"))?;

                let field = match self.ast_context.index(field_id).kind {
                    CDeclKind::Field { typ, .. } => self
                        .implicit_default_expr(typ.ctype, is_static, false)?
                        .map(|field_init| {
                            let name = self
                                .type_converter
                                .borrow()
                                .resolve_field_name(Some(decl_id), field_id)
                                .unwrap();

                            mk().field(name, field_init)
                        }),
                    _ => {
                        return Err(generic_err!("Found non-field in record field list",));
                    }
                };

                field.map(|field| mk().struct_expr(vec![name], vec![field]))
            }

            // Transmute the number `0` into the enum type
            CDeclKind::Enum { .. } => WithStmts::new_val(self.enum_for_i64(type_id, 0)),

            _ => {
                return Err(generic_err!("Declaration is not associated with a type",));
            }
        };

        if self.ast_context.has_inner_struct_decl(name_decl_id) {
            // If the structure is split into an outer/inner,
            // wrap the inner initializer using the outer structure
            let outer_name = self
                .type_converter
                .borrow()
                .resolve_decl_name(name_decl_id)
                .unwrap();

            let outer_path = mk().path_expr(vec![outer_name]);
            init = init.map(|i| mk().call_expr(outer_path, vec![i]));
        };

        if init.is_pure() {
            // Insert the initializer into the cache, then return it
            self.zero_inits.borrow_mut().insert(decl_id, init.clone());
            Ok(init)
        } else {
            Err(generic_err!("Expected no statements in zero initializer",))
        }
    }

    /// Resolve the inner name of a structure declaration
    /// if there is one (if the structure was split),
    /// otherwise just return the normal name
    fn resolve_decl_inner_name(&self, decl_id: CDeclId) -> String {
        if self.ast_context.has_inner_struct_decl(decl_id) {
            self.type_converter
                .borrow_mut()
                .resolve_decl_suffix_name(decl_id, INNER_SUFFIX)
                .to_owned()
        } else {
            self.type_converter
                .borrow()
                .resolve_decl_name(decl_id)
                .unwrap()
        }
    }

    /// Convert a boolean expression to a boolean for use in && or || or if
    fn match_bool(&self, target: bool, ty_id: CTypeId, val: Box<Expr>) -> Box<Expr> {
        let ty = &self.ast_context.resolve_type(ty_id).kind;

        if self.ast_context.is_function_pointer(ty_id) {
            if target {
                mk().method_call_expr(val, "is_some", vec![])
            } else {
                mk().method_call_expr(val, "is_none", vec![])
            }
        } else if ty.is_pointer() {
            let mut res = mk().method_call_expr(val, "is_null", vec![]);
            if target {
                res = mk().unary_expr(UnOp::Not(Default::default()), res)
            }
            res
        } else if ty.is_bool() {
            if target {
                val
            } else {
                mk().unary_expr(UnOp::Not(Default::default()), val)
            }
        } else {
            // One simplification we can make at the cost of inspecting `val` more closely: if `val`
            // is already in the form `(x <op> y) as <ty>` where `<op>` is a Rust operator
            // that returns a boolean, we can simple output `x <op> y` or `!(x <op> y)`.
            if let Expr::Cast(ExprCast { expr: ref arg, .. }) = *transform::unparen(&val) {
                #[allow(clippy::collapsible_match)]
                if let Expr::Binary(ExprBinary { op, .. }) = *transform::unparen(arg) {
                    match op {
                        BinOp::Or(_)
                        | BinOp::And(_)
                        | BinOp::Eq(_)
                        | BinOp::Ne(_)
                        | BinOp::Lt(_)
                        | BinOp::Le(_)
                        | BinOp::Gt(_)
                        | BinOp::Ge(_) => {
                            if target {
                                // If target == true, just return the argument
                                return Box::new(transform::unparen(arg).clone());
                            } else {
                                // If target == false, return !arg
                                return mk().unary_expr(
                                    UnOp::Not(Default::default()),
                                    Box::new(transform::unparen(arg).clone()),
                                );
                            }
                        }
                        _ => {}
                    }
                }
            }

            let val = if ty.is_enum() {
                mk().cast_expr(val, mk().path_ty(vec!["u64"]))
            } else {
                val
            };

            // The backup is to just compare against zero
            let zero = if ty.is_floating_type() {
                mk().lit_expr(mk().float_lit("0.0"))
            } else {
                mk().lit_expr(0)
            };

            if target {
                mk().binary_expr(BinOp::Ne(Default::default()), val, zero)
            } else {
                mk().binary_expr(BinOp::Eq(Default::default()), val, zero)
            }
        }
    }

    pub fn with_scope<F, A>(&self, f: F) -> A
    where
        F: FnOnce() -> A,
    {
        self.renamer.borrow_mut().add_scope();
        let result = f();
        self.renamer.borrow_mut().drop_scope();
        result
    }
}
