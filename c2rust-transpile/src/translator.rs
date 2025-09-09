use std::cell::RefCell;
use std::char;
use std::collections::HashMap;
use std::path::{self, PathBuf};
// To override syn::Result from glob import

use self::decls::ConvertedDecl;
use context::{ExprContext, FuncContext};

use indexmap::indexmap;
use indexmap::{IndexMap, IndexSet};
use log::{trace, warn};
use proc_macro2::{Spacing::*, Span, TokenStream};
use syn::BinOp;
use syn::*; // To override c_ast::BinOp from glob import

use crate::diagnostics::TranslationResult;
use crate::rust_ast::comment_store::CommentStore;
use crate::rust_ast::item_store::ItemStore;
use crate::rust_ast::pos_to_span;
use crate::transform;
use c2rust_ast_builder::{mk, properties::*};

use crate::c_ast;
use crate::c_ast::iterators::{DFExpr, SomeId};
use crate::cfg;
use crate::convert_type::TypeConverter;
use crate::renamer::Renamer;
use crate::with_stmts::WithStmts;
use crate::{
    ExternCrate, ExternCrateDetails, TranspilerConfig,
    driver::{Translation, translate_failure},
};
use crate::{TranslateMacros, c_ast::get_node::GetNode, c_ast::*, generic_err};
use c2rust_ast_exporter::clang_ast::LRValue;

mod assembly;
mod atomics;
mod builtins;
mod casts;
mod comments;
pub mod context;
pub(crate) mod declaration_converter;
pub(crate) mod decls;
mod exprs;
mod linkage;
mod literals;
mod macros;
mod named_references;
mod operators;
mod pointer_wrappers;
pub(crate) mod preprocess;
mod simd;
mod statics;
mod structs;
mod types;
mod utils;
pub(crate) mod variadic;

use crate::PragmaVec;
pub use crate::diagnostics::{TranslationError, TranslationErrorKind};

pub const INNER_SUFFIX: &str = "_Inner";
pub const PADDING_SUFFIX: &str = "_PADDING";

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

/// Create a Rust submodule from the items in a C header file.
///
/// `ast_context` is the AST context.
/// `item_store` contains the items that were translated from the header file.
/// `file_id` is the ID of the header file.
/// `use_item_store` is an item store to which `use` statements will be added
/// for all of the public items in the submodule.
/// `mod_names` is a map of module names to paths, used to avoid collisions.
/// `global_uses` is a set of `use` statements that should be added to every
/// submodule.
/// `reorganize_definitions` is true if the `--reorganize-modules` flag is
/// used.
/// `need_pointer_wrapper` is true if the `Pointer` and `PointerMut` structs
/// need to be imported into the submodule.
///
/// This function creates a `mod` item containing all of the items from the
/// header file. It also adds `use` statements to the `use_item_store` for
/// all of the public items in the submodule, so that they can be imported
/// into the main crate.
pub(crate) fn make_submodule(
    ast_context: &TypedAstContext,
    item_store: &mut ItemStore,
    file_id: FileId,
    use_item_store: &mut ItemStore,
    mod_names: &RefCell<IndexMap<String, PathBuf>>,
    global_uses: &RefCell<indexmap::IndexSet<Box<Item>>>,
    reorganize_definitions: bool,
    need_pointer_wrapper: bool,
) -> Box<Item> {
    let (mut items, foreign_items, uses) = item_store.drain();
    let file_path = ast_context.get_file_path(file_id);
    let include_line_number = ast_context
        .get_file_include_line_number(file_id)
        .unwrap_or(0);
    let mod_name = utils::clean_path(mod_names, file_path);

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

    // if reorganize_definitions is true, we add use statement for PointerWrapper struct
    if reorganize_definitions && need_pointer_wrapper {
        items.push(mk().use_simple_item(vec!["super", "Pointer"], None::<Ident>));
        items.push(mk().use_simple_item(vec!["super", "PointerMut"], None::<Ident>));
    }

    let module_builder = mk().pub_();
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
pub(crate) fn arrange_header(
    t: &Translation,
    is_binary: bool,
) -> (Vec<syn::Attribute>, Vec<Box<Item>>) {
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
            need_pointer_wrapper: RefCell::new(false),
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
    pub(crate) fn use_mod(&self, mod_name: Vec<&'static str>) {
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

    /// helper function to get the current file item store
    fn with_cur_file_item_store<F, T>(&self, f: F) -> T
    where
        F: FnOnce(&mut ItemStore) -> T,
    {
        self.with_item_store(Self::cur_file(self), f)
    }

    /// helper function to get item store from file_id
    fn with_item_store<F, T>(&self, file_id: usize, f: F) -> T
    where
        F: FnOnce(&mut ItemStore) -> T,
    {
        let mut item_stores = self.items.borrow_mut();
        let item_store = item_stores.entry(file_id).or_default();
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
        let macro_msg = vec![mk().lit_tt(msg)];
        mk().mac_expr(mk().call_mac(macro_name, macro_msg))
    }

    /// Determine if we're able to convert this const macro expansion.
    fn can_convert_const_macro_expansion(&self, expr_id: CExprId) -> TranslationResult<()> {
        match self.tcfg.translate_const_macros {
            TranslateMacros::None => Err(generic_err!("translate_const_macros is None"))?,
            TranslateMacros::Conservative => {
                // TODO We still allow `CExprKind::ExplicitCast`s
                // even though they're broken (see #853).

                // This is a top-down, pessimistic/conservative analysis.
                // This is somewhat duplicative of `fn convert_expr` simply checking
                // `ExprContext::is_const` and returning errors where the expr is not `const`,
                // which is an non-conservative analysis scattered across all of the `fn convert_*`s.
                // That's what's done for `TranslateMacros::Experimental`,
                // as opposed to the conservative analysis done here for `TranslateMacros::Conservative`.
                // When the conservative analysis is incomplete,
                // it won't translate the macro, but the result will compile.
                // But when the non-conservative analysis is incomplete,
                // the resulting code may not transpile,
                // which is why the conservative analysis is used for `TranslateMacros::Conservative`.
                if !self.ast_context.is_const_expr(expr_id) {
                    Err(generic_err!("non-const expr {expr_id:?}"))?;
                }
                Ok(())
            }
            TranslateMacros::Experimental => Ok(()),
        }
    }

    /// Given all of the expansions of a const macro,
    /// try to recreate a Rust `const` translation
    /// that is equivalent to every expansion.
    ///
    /// This may fail, in which case we simply don't emit a `const`
    /// and leave all of the expansions as fully inlined
    /// instead of referencing this `const`.
    ///
    /// For example, if the types of the macro expansion have no common type,
    /// which is required for a Rust `const` but not a C const macro,
    /// this can fail.  Or there could just be a feature we don't yet support.
    fn recreate_const_macro_from_expansions(
        &self,
        ctx: ExprContext,
        expansions: &[CExprId],
    ) -> TranslationResult<(Box<Expr>, CTypeId)> {
        let (mut val, ty) = expansions
            .iter()
            .try_fold::<Option<(WithStmts<Box<Expr>>, CTypeId)>, _, _>(None, |canonical, &id| {
                self.can_convert_const_macro_expansion(id)?;

                let ty = self.ast_context[id]
                    .kind
                    .get_type()
                    .ok_or_else(|| generic_err!("Invalid expression type"))?;
                let (expr_id, ty) = self
                    .ast_context
                    .resolve_expr_type_id(id)
                    .unwrap_or((id, ty));
                let expr = self.convert_expr(ctx, expr_id, None)?;

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

        val.set_unsafe();
        val.to_unsafe_pure_expr()
            .map(|val| (val, ty))
            .ok_or_else(|| generic_err!("Macro expansion is not a pure expression"))

        // TODO: Validate that all replacements are equivalent and pick the most
        // common type to minimize casts.
    }

    fn convert_function_body(
        &self,
        ctx: ExprContext,
        name: &str,
        body_ids: &[CStmtId],
        ret_ty: Option<CQualTypeId>,
        ret: cfg::ImplicitReturnType,
    ) -> TranslationResult<Vec<Stmt>> {
        // Function body scope
        self.with_scope(|| {
            let (graph, store) = cfg::Cfg::from_stmts(self, ctx, body_ids, ret, ret_ty)?;
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
                    if let CTypeKind::TypeOfExpr(_) = t.get_node(&self.ast_context).kind {
                        iter.prune(1);
                    }
                }
                _ => {}
            }
        }
        false
    }

    /// Convert a C `DeclStmt` into a `cfg::DeclStmtInfo`.
    ///
    /// A `DeclStmt` is a statement that contains a declaration, such as
    /// `int x = 5;`.
    ///
    /// This function handles a few different cases:
    ///
    /// -   **Function-scoped statics:** If the declaration is a `static`
    ///     variable, it is converted to a Rust `static` item. If the
    ///     initializer is not a compile-time constant, it is moved to a
    ///     special `run_static_initializers` function that is called at the
    ///     beginning of `main`.
    ///
    /// -   **`va_list`:** If the declaration is a `va_list`, it is converted
    ///     to a `VaListImpl` and the initializer is omitted.
    ///
    /// -   **Normal local variables:** Other local variables are converted to
    ///     Rust `let` statements. If the variable has an initializer that
    ///     refers to the variable itself (e.g., `int x = x + 1;`), it is
    ///     split into a declaration and a separate assignment.
    ///
    /// -   **Other declarations:** Other declarations (e.g., `struct` or
    ///     `enum` declarations) are converted to Rust items.
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
        } = decl_id.get_node(&self.ast_context).kind
            && self.static_initializer_is_uncompilable(initializer, typ)
        {
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
        };

        match decl_id.get_node(&self.ast_context).kind {
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
                    let pat_mut = mk().mutbl().ident_pat(rust_name);
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
                let pat_mut = mk().mutbl().ident_pat(rust_name.clone());
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
                let skip = match *decl {
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
        let pointer_wrapper_type = |pointee: Box<Type>, mutbl: Mutability| -> Box<Type> {
            // need to generate PointerMut struct
            *self.need_pointer_wrapper.borrow_mut() = true;

            let name = match mutbl {
                Mutability::Immutable => "Pointer",
                Mutability::Mutable => "PointerMut",
            };

            mk().path_ty(vec![mk().path_segment_with_args(
                name,
                mk().angle_bracketed_args(vec![pointee]),
            )])
        };

        let mut need_pointer_wrapper = false;
        let mut pointee_mutbl = Mutability::Immutable;

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
                    let mutbl = if cqt.qualifiers.is_const {
                        Mutability::Immutable
                    } else {
                        Mutability::Mutable
                    };

                    let rtype = self.convert_type(cqt.ctype)?;
                    let pointer_type = pointer_wrapper_type(rtype, mutbl);
                    let size = mk().lit_expr(mk().int_lit(size as u64));
                    mk().array_ty(pointer_type, size)
                } else {
                    self.convert_type(typ.ctype)?
                }
            }

            // for static pointer type (except function pointers), we wrap it in PointerMut or PointerConst
            CTypeKind::Pointer(pointee)
                if ctx.is_static
                    && matches!(
                        &self.ast_context.resolve_type(pointee.ctype).kind,
                        CTypeKind::Function(..)
                    ) == false =>
            {
                pointee_mutbl = if pointee.qualifiers.is_const {
                    Mutability::Immutable
                } else {
                    Mutability::Mutable
                };

                let kind = &self.ast_context.resolve_type(pointee.ctype).kind;
                let ty = match kind {
                    CTypeKind::Void => mk().path_ty(vec!["ffi", "c_void"]), // for void pointers, we use `c_void` type
                    _ => self.convert_type(pointee.ctype)?,
                };

                need_pointer_wrapper = true;
                pointer_wrapper_type(ty, pointee_mutbl)
            }

            _ => self.convert_type(typ.ctype)?,
        };

        let mut init = match initializer {
            Some(x) => self.convert_expr(ctx.used(), x, Some(typ)),
            None => self.implicit_default_expr(typ.ctype, ctx.is_static, ctx.inside_init_list_aop),
        };

        // wrap init expression in a PointerMut or Pointer if it is static
        if need_pointer_wrapper {
            init = init.and_then(|init| {
                let name = match pointee_mutbl {
                    Mutability::Immutable => "Pointer",
                    Mutability::Mutable => "PointerMut",
                };

                init.and_then(|init| {
                    Ok(WithStmts::new_val(
                        mk().call_expr(mk().ident_expr(name), vec![init]),
                    ))
                })
            });
        }

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
            return Ok(mk().ident_expr("None"));
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
                    let expr = self
                        .convert_expr(ctx.used(), expr_id, None)?
                        .and_then(|expr| {
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
        override_ty: Option<CQualTypeId>,
    ) -> TranslationResult<WithStmts<Box<Expr>>> {
        if let CTypeKind::VariableArray(elts, len) = self.ast_context.resolve_type(type_id).kind {
            let len = len.expect("Sizeof a VLA type with count expression omitted");

            let elts = self.compute_size_of_type(ctx, elts, override_ty)?;
            return elts.and_then(|lhs| {
                let len = self.convert_expr(ctx.used().not_static(), len, override_ty)?;
                Ok(len.map(|len| {
                    let rhs = transform::cast_int_with_suffix(len, "usize");
                    mk().binary_expr(BinOp::Mul(Default::default()), lhs, rhs)
                }))
            });
        }
        let ty = self.convert_type(type_id)?;
        let mut result = self.mk_size_of_ty_expr(ty);
        // cast to expected ty if one is known
        if let Some(expected_ty) = override_ty {
            trace!(
                "Converting result of sizeof to {:?}",
                self.ast_context.resolve_type(expected_ty.ctype)
            );
            let result_ty = self.convert_type(expected_ty.ctype)?;
            result = result.map(|x| x.map(|x| mk().cast_expr(x, result_ty)));
        }
        result
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
                && blbl.ident == mk().label(lbl.pretty_print()).name.ident
            {
                return Some(ret_val.clone());
            }
            None
        }

        match compound_stmt_id.get_node(&self.ast_context).kind {
            CStmtKind::Compound(ref substmt_ids) if !substmt_ids.is_empty() => {
                let n = substmt_ids.len();
                let result_id = substmt_ids[n - 1];

                let name = format!("<stmt-expr_{compound_stmt_id:?}>");
                let lbl = cfg::Label::FromC(compound_stmt_id, None);

                let mut stmts = match result_id.get_node(&self.ast_context).kind {
                    CStmtKind::Expr(expr_id) => {
                        let ret = cfg::ImplicitReturnType::StmtExpr(ctx, expr_id, lbl.clone());
                        self.convert_function_body(ctx, &name, &substmt_ids[0..(n - 1)], None, ret)?
                    }

                    _ => self.convert_function_body(
                        ctx,
                        &name,
                        substmt_ids,
                        None,
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

        let name_decl_id = match type_id.get_node(&self.ast_context).kind {
            CTypeKind::Typedef(decl_id) => decl_id,
            _ => decl_id,
        };

        // Otherwise, construct the initializer
        let mut init = match decl_id.get_node(&self.ast_context).kind {
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

                let field = match field_id.get_node(&self.ast_context).kind {
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

            let outer_path = mk().ident_expr(outer_name);
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
                res = mk().not_expr(res)
            }
            res
        } else if ty.is_bool() {
            if target { val } else { mk().not_expr(val) }
        } else {
            // One simplification we can make at the cost of inspecting `val` more closely: if `val`
            // is already in the form `(x <op> y) as <ty>` where `<op>` is a Rust operator
            // that returns a boolean, we can simple output `x <op> y` or `!(x <op> y)`.
            if let Expr::Cast(ExprCast { expr: ref arg, .. }) = *transform::unparen(&val)
                && let Expr::Binary(ExprBinary { op, .. }) = *transform::unparen(arg)
                && matches!(
                    op,
                    BinOp::Or(_)
                        | BinOp::And(_)
                        | BinOp::Eq(_)
                        | BinOp::Ne(_)
                        | BinOp::Lt(_)
                        | BinOp::Le(_)
                        | BinOp::Gt(_)
                        | BinOp::Ge(_)
                )
            {
                if target {
                    // If target == true, just return the argument
                    return Box::new(transform::unparen(arg).clone());
                } else {
                    // If target == false, return !arg
                    return mk().not_expr(Box::new(transform::unparen(arg).clone()));
                }
            }

            let val = if ty.is_enum() {
                mk().cast_expr(val, mk().path_ty("u64"))
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
