use crate::rust_ast::set_span::SetSpan;
use crate::translator::{
    ConvertedVariable, MacroExpansion, PADDING_SUFFIX, TranslationError, mk_linkage,
};
use c2rust_ast_builder::mk;
use indexmap::IndexSet;
use std::ops::Index;

use log::{info, trace, warn};
use proc_macro2::Span;
use syn::BinOp;
use syn::*; // To override c_ast::{BinOp,UnOp} from glob import

use crate::diagnostics::TranslationResult;
use crate::rust_ast::{SpanExt, pos_to_span};
use crate::{
    c_ast::{CDeclKind, CTypeKind},
    generic_err,
};
use c2rust_ast_builder::properties::*;

use crate::c_ast::iterators::SomeId;
use crate::c_ast::*;
use crate::{ExternCrate, cfg};
use crate::{ReplaceMode, c_ast};

use super::{
    ExprContext, Translation, add_src_loc_attr, clean_path, foreign_item_attrs, item_attrs,
    stmts_block,
};

/// Declarations can be converted into a normal item, or into a foreign item.
/// Foreign items are called out specially because we'll combine all of them
/// into a single extern block at the end of translation.
#[derive(Debug)]
pub enum ConvertedDecl {
    /// [`ForeignItem`] is large (472 bytes), so [`Box`] it.
    ForeignItem(Box<ForeignItem>), // would be 472 bytes
    Item(Box<Item>),  // 24 bytes
    Items(Vec<Item>), // 24 bytes
    NoItem,
}

impl<'c> Translation<'c> {
    pub(crate) fn convert_decl(
        &self,
        ctx: ExprContext,
        decl_id: CDeclId,
    ) -> TranslationResult<ConvertedDecl> {
        let decl = self
            .ast_context
            .get_decl(&decl_id)
            .ok_or_else(|| generic_err!("Missing decl {:?}", decl_id))?;

        let mut span = self
            .get_span(SomeId::Decl(decl_id))
            .unwrap_or_else(Span::call_site);

        use CDeclKind::*;
        match decl.kind {
            Struct { fields: None, .. }
            | Union { fields: None, .. }
            | Enum {
                integral_type: None,
                ..
            } => {
                self.use_feature("extern_types");
                let name = self
                    .type_converter
                    .borrow()
                    .resolve_decl_name(decl_id)
                    .unwrap();

                let extern_item = mk().span(span).pub_().ty_foreign_item(name);
                Ok(ConvertedDecl::ForeignItem(extern_item))
            }

            Struct {
                fields: Some(ref fields),
                is_packed,
                manual_alignment,
                max_field_alignment,
                platform_byte_size,
                ..
            } => {
                let name = self
                    .type_converter
                    .borrow()
                    .resolve_decl_name(decl_id)
                    .unwrap();

                // Check if the last field might be a flexible array member
                if let Some(last_id) = fields.last() {
                    let field_decl = &self.ast_context[*last_id];
                    if let CDeclKind::Field { typ, .. } = field_decl.kind {
                        if self.ast_context.maybe_flexible_array(typ.ctype) {
                            self.potential_flexible_array_members
                                .borrow_mut()
                                .insert(*last_id);
                        }
                    }
                }

                // Pre-declare all the field names, checking for duplicates
                let mut has_pointers = false;
                for &x in fields {
                    if let CDeclKind::Field {
                        ref name, ref typ, ..
                    } = self.ast_context.index(x).kind
                    {
                        self.type_converter
                            .borrow_mut()
                            .declare_field_name(decl_id, x, name);

                        if self.ast_context.index(typ.ctype).kind.is_pointer() {
                            has_pointers = true;
                        }
                    }
                }
                let has_pointers = has_pointers;

                // Gather up all the field names and field types
                let (field_entries, contains_va_list) =
                    self.convert_struct_fields(decl_id, fields, platform_byte_size)?;

                let mut derives = vec![];
                if !contains_va_list {
                    derives.push("Copy");
                    derives.push("Clone");
                };
                let has_bitfields =
                    fields
                        .iter()
                        .any(|field_id| match self.ast_context.index(*field_id).kind {
                            CDeclKind::Field { bitfield_width, .. } => bitfield_width.is_some(),
                            _ => unreachable!("Found non-field in record field list"),
                        });
                if has_bitfields {
                    derives.push("BitfieldStruct");
                    self.use_crate(ExternCrate::C2RustBitfields);
                }

                let mut reprs = vec![mk().meta_path("C")];
                let max_field_alignment = if is_packed {
                    // `__attribute__((packed))` forces a max alignment of 1,
                    // overriding `#pragma pack`; this is also what clang does
                    Some(1)
                } else {
                    max_field_alignment
                };
                match max_field_alignment {
                    Some(1) => reprs.push(mk().meta_path("packed")),
                    Some(mf) if mf > 1 => reprs.push(mk().meta_list("packed", vec![mf])),
                    _ => {}
                }

                let mut items = if let Some(alignment) = manual_alignment {
                    // This is the most complicated case: we have `align(N)` which
                    // might be mixed with or included into a `packed` structure,
                    // which Rust doesn't currently support; instead, we split
                    // the structure into 2 structures like this:
                    //   #[align(N)]
                    //   pub struct Foo(pub Foo_Inner);
                    //   #[packed(M)]
                    //   pub struct Foo_Inner {
                    //     ...fields...
                    //   }
                    //
                    // TODO: right now, we always emit the pair of structures
                    // instead, we should only split when needed, but that
                    // would significantly complicate the implementation
                    assert!(self.ast_context.has_inner_struct_decl(decl_id));
                    let inner_name = self.resolve_decl_inner_name(decl_id);
                    let inner_ty = mk().path_ty(vec![inner_name.clone()]);
                    let inner_struct = mk()
                        .span(span)
                        .pub_()
                        .call_attr("derive", derives)
                        .call_attr("repr", reprs)
                        .struct_item(inner_name.clone(), field_entries, false);

                    let outer_ty = mk().path_ty(vec![name.clone()]);
                    let outer_reprs = vec![
                        mk().meta_path("C"),
                        mk().meta_list("align", vec![alignment]),
                        // TODO: copy others from `reprs` above
                    ];

                    let outer_field = mk().pub_().enum_field(mk().ident_ty(inner_name));
                    let outer_struct = mk()
                        .span(span)
                        .pub_()
                        .call_attr("derive", vec!["Copy", "Clone"])
                        .call_attr("repr", outer_reprs)
                        .struct_item(name.clone(), vec![outer_field], true);

                    // Emit `const X_PADDING: usize = size_of(Outer) - size_of(Inner);`
                    let padding_name = self
                        .type_converter
                        .borrow_mut()
                        .resolve_decl_suffix_name(decl_id, PADDING_SUFFIX)
                        .to_owned();
                    let padding_ty = mk().path_ty(vec!["usize"]);
                    let outer_size = self.mk_size_of_ty_expr(outer_ty)?.to_expr();
                    let inner_size = self.mk_size_of_ty_expr(inner_ty)?.to_expr();
                    let padding_value =
                        mk().binary_expr(BinOp::Sub(Default::default()), outer_size, inner_size);
                    let padding_const = mk()
                        .span(span)
                        .call_attr("allow", vec!["dead_code", "non_upper_case_globals"])
                        .const_item(padding_name, padding_ty, padding_value);

                    let structs = vec![*outer_struct, *inner_struct, *padding_const];
                    structs
                } else {
                    assert!(!self.ast_context.has_inner_struct_decl(decl_id));
                    let mut mk_ = mk()
                        .span(span)
                        .pub_()
                        .call_attr("derive", derives)
                        .call_attr("repr", reprs);

                    if contains_va_list {
                        mk_ = mk_.generic_over(mk().lt_param(mk().ident("a")))
                    }

                    vec![*mk_.struct_item(name.clone(), field_entries, false)]
                };

                // add unsafe implement for `Sync` traits if the struct contains pointers
                if has_pointers {
                    let sync_impl_item = mk().unsafe_().impl_trait_item(
                        mk().ident_ty(name.clone()),
                        mk().path("Sync"),
                        vec![],
                    );
                    items.push(*sync_impl_item);
                }

                let converted_decl = if items.len() == 1 {
                    ConvertedDecl::Item(Box::new(items.pop().unwrap()))
                } else {
                    ConvertedDecl::Items(items)
                };

                Ok(converted_decl)
            }

            Union {
                fields: Some(ref fields),
                is_packed,
                ..
            } => {
                let name = self
                    .type_converter
                    .borrow()
                    .resolve_decl_name(decl_id)
                    .unwrap();

                let mut field_syns = vec![];
                for &x in fields {
                    let field_decl = self.ast_context.index(x);
                    match field_decl.kind {
                        CDeclKind::Field { ref name, typ, .. } => {
                            let name = self
                                .type_converter
                                .borrow_mut()
                                .declare_field_name(decl_id, x, name);
                            let typ = self.convert_type(typ.ctype)?;
                            field_syns.push(mk().pub_().struct_field(name, typ))
                        }
                        _ => {
                            return Err(generic_err!("Found non-field in record field list",));
                        }
                    }
                }

                let mut repr = vec!["C"];
                if is_packed {
                    repr.push("packed");
                }

                Ok(if field_syns.is_empty() {
                    // Empty unions are a GNU extension, but Rust doesn't allow empty unions.
                    ConvertedDecl::Item(
                        mk().span(span)
                            .pub_()
                            .call_attr("derive", vec!["Copy", "Clone"])
                            .call_attr("repr", repr)
                            .struct_item(name, vec![], false),
                    )
                } else {
                    ConvertedDecl::Item(
                        mk().span(span)
                            .pub_()
                            .call_attr("derive", vec!["Copy", "Clone"])
                            .call_attr("repr", repr)
                            .union_item(name, field_syns),
                    )
                })
            }

            Field { .. } => Err(generic_err!(
                "Field declarations should be handled inside structs/unions",
            )),

            Enum {
                integral_type: Some(integral_type),
                ..
            } => {
                let enum_name = &self
                    .type_converter
                    .borrow()
                    .resolve_decl_name(decl_id)
                    .expect("Enums should already be renamed");
                let ty = self.convert_type(integral_type.ctype)?;
                Ok(ConvertedDecl::Item(
                    mk().span(span).pub_().type_item(enum_name, ty),
                ))
            }

            EnumConstant { value, .. } => {
                let name = self
                    .renamer
                    .borrow_mut()
                    .get(&decl_id)
                    .expect("Enum constant not named");
                let enum_id = self.ast_context.parents[&decl_id];
                let enum_name = self
                    .type_converter
                    .borrow()
                    .resolve_decl_name(enum_id)
                    .expect("Enums should already be renamed");
                if let Some(cur_file) = *self.cur_file.borrow() {
                    self.add_import(cur_file, enum_id, &enum_name);
                }
                let ty = mk().path_ty(mk().path(vec![enum_name]));
                let val = match value {
                    ConstIntExpr::I(value) => mk().lit_expr(mk().int_lit(value)),
                    ConstIntExpr::U(value) => mk().lit_expr(mk().int_lit(value)),
                };

                Ok(ConvertedDecl::Item(
                    mk().span(span).pub_().const_item(name, ty, val),
                ))
            }

            // We can allow non top level function declarations (i.e. extern
            // declarations) without any problem. Clang doesn't support nested
            // functions, so we will never see nested function definitions.
            Function {
                is_global,
                is_inline,
                is_extern,
                typ,
                ref name,
                ref parameters,
                body,
                ref attrs,
                ..
            } => {
                let new_name = &self
                    .renamer
                    .borrow()
                    .get(&decl_id)
                    .expect("Functions should already be renamed");

                if self.import_simd_function(new_name)? {
                    return Ok(ConvertedDecl::NoItem);
                }

                let (ret, is_variadic): (Option<CQualTypeId>, bool) =
                    match self.ast_context.resolve_type(typ).kind {
                        CTypeKind::Function(ret, _, is_var, is_noreturn, _) => {
                            (if is_noreturn { None } else { Some(ret) }, is_var)
                        }
                        ref k => {
                            return Err(generic_err!(
                                "Type of function {:?} was not a function type, got {:?}",
                                decl_id,
                                k
                            ));
                        }
                    };

                let mut args: Vec<(CDeclId, String, CQualTypeId)> = vec![];
                for param_id in parameters {
                    if let CDeclKind::Variable { ref ident, typ, .. } =
                        self.ast_context.index(*param_id).kind
                    {
                        args.push((*param_id, ident.clone(), typ))
                    } else {
                        return Err(generic_err!("Parameter is not variable declaration",));
                    }
                }

                let is_main = self.ast_context.c_main == Some(decl_id);

                let converted_function = self.convert_function(
                    ctx,
                    span,
                    is_global,
                    is_inline,
                    is_main,
                    is_variadic,
                    is_extern,
                    new_name,
                    name,
                    &args,
                    ret,
                    body,
                    attrs,
                );

                converted_function.or_else(|e| match self.tcfg.replace_unsupported_decls {
                    ReplaceMode::Extern if body.is_none() => self.convert_function(
                        ctx,
                        span,
                        is_global,
                        false,
                        is_main,
                        is_variadic,
                        is_extern,
                        new_name,
                        name,
                        &args,
                        ret,
                        None,
                        attrs,
                    ),
                    _ => Err(e),
                })
            }

            Typedef { ref typ, .. } => {
                let new_name = &self
                    .type_converter
                    .borrow()
                    .resolve_decl_name(decl_id)
                    .unwrap();

                if self.import_simd_typedef(new_name)? {
                    return Ok(ConvertedDecl::NoItem);
                }

                // We can't typedef to std::ffi::VaList, since the typedef won't
                // have explicit lifetime params which VaList
                // requires. Temporarily disable translation of valist to Rust
                // native VaList.
                let translate_valist = std::mem::replace(
                    &mut self.type_converter.borrow_mut().translate_valist,
                    false,
                );
                let ty = self.convert_type(typ.ctype)?;
                self.type_converter.borrow_mut().translate_valist = translate_valist;

                Ok(ConvertedDecl::Item(
                    mk().span(span).pub_().type_item(new_name, ty),
                ))
            }

            // Externally-visible variable without initializer (definition elsewhere)
            Variable {
                is_externally_visible: true,
                has_static_duration,
                has_thread_duration,
                is_defn: false,
                ref ident,
                initializer,
                typ,
                ref attrs,
                ..
            } => {
                assert!(
                    has_static_duration || has_thread_duration,
                    "An extern variable must be static or thread-local"
                );
                assert!(
                    initializer.is_none(),
                    "An extern variable that isn't a definition can't have an initializer"
                );

                if has_thread_duration {
                    self.use_feature("thread_local");
                }

                let new_name = self
                    .renamer
                    .borrow()
                    .get(&decl_id)
                    .expect("Variables should already be renamed");
                let ConvertedVariable { ty, mutbl, init: _ } =
                    self.convert_variable(ctx.static_(), None, typ)?;
                // When putting extern statics into submodules, they need to be public to be accessible
                let visibility = if self.tcfg.reorganize_definitions {
                    "pub"
                } else {
                    ""
                };
                let mut extern_item = mk_linkage(true, &new_name, ident)
                    .span(span)
                    .set_mutbl(mutbl)
                    .vis(visibility);
                if has_thread_duration {
                    extern_item = extern_item.single_attr("thread_local");
                }

                for attr in attrs {
                    extern_item = match attr {
                        c_ast::Attribute::Alias(aliasee) => {
                            extern_item.str_attr("link_name", aliasee)
                        }
                        _ => continue,
                    };
                }

                Ok(ConvertedDecl::ForeignItem(
                    extern_item.static_foreign_item(&new_name, ty),
                ))
            }

            // Static-storage or thread-local variable with initializer (definition here)
            Variable {
                has_static_duration,
                has_thread_duration,
                is_externally_visible,
                ref ident,
                initializer,
                typ,
                ref attrs,
                ..
            } if has_static_duration || has_thread_duration => {
                if has_thread_duration {
                    self.use_feature("thread_local");
                }

                let new_name = &self
                    .renamer
                    .borrow()
                    .get(&decl_id)
                    .expect("Variables should already be renamed");

                // Collect problematic static initializers and offload them to sections for the linker
                // to initialize for us
                let (ty, init, mutbl) = if self.static_initializer_is_uncompilable(initializer, typ)
                {
                    // Note: We don't pass has_static_duration through here. Extracted initializers
                    // are run outside of the static initializer.
                    let ConvertedVariable { ty, mutbl: _, init } =
                        self.convert_variable(ctx.not_static(), initializer, typ)?;

                    let mut init = init?.to_expr();

                    let comment = String::from("// Initialized in run_static_initializers");
                    let comment_pos = if span.is_dummy() {
                        None
                    } else {
                        Some(span.lo())
                    };
                    span = self
                        .comment_store
                        .borrow_mut()
                        .extend_existing_comments(
                            &[comment],
                            comment_pos,
                            //CommentStyle::Isolated,
                        )
                        .map(pos_to_span)
                        .unwrap_or(span);

                    self.add_static_initializer_to_section(new_name, typ, &mut init)?;

                    (ty, init, Mutability::Mutable)
                } else {
                    let ConvertedVariable { ty, mutbl, init } =
                        self.convert_variable(ctx.static_(), initializer, typ)?;
                    let mut init = init?;
                    // TODO: Replace this by relying entirely on
                    // WithStmts.is_unsafe() of the translated variable
                    if self.static_initializer_is_unsafe(initializer, typ) {
                        init.set_unsafe()
                    }
                    let init = init.to_unsafe_pure_expr().ok_or_else(|| {
                        generic_err!("Expected no side-effects in static initializer")
                    })?;

                    (ty, init, mutbl)
                };

                let static_def = if is_externally_visible {
                    mk_linkage(false, new_name, ident).pub_().extern_("C")
                } else if self.cur_file.borrow().is_some() {
                    mk().pub_()
                } else {
                    mk()
                };

                let mut static_def = static_def.span(span);

                if mutbl == Mutability::Mutable {
                    static_def = static_def.mutbl();
                }

                if has_thread_duration {
                    static_def = static_def.single_attr("thread_local");
                }

                // Add static attributes
                for attr in attrs {
                    static_def = match attr {
                        c_ast::Attribute::Used => static_def.single_attr("used"),
                        c_ast::Attribute::Section(name) => static_def
                            .call_attr("unsafe", vec![mk().meta_namevalue("link_section", name)]),
                        _ => continue,
                    }
                }

                Ok(ConvertedDecl::Item(
                    static_def.static_item(new_name, ty, init),
                ))
            }

            Variable { .. } => Err(generic_err!(
                "This should be handled in 'convert_decl_stmt'",
            )),

            MacroObject { .. } => {
                let name = self
                    .renamer
                    .borrow_mut()
                    .get(&decl_id)
                    .expect("Macro object not named");

                trace!(
                    "Expanding macro {:?}: {:?}",
                    decl_id, self.ast_context[decl_id]
                );

                let maybe_replacement = self.canonical_macro_replacement(
                    ctx.set_const(true).set_expanding_macro(decl_id),
                    &self.ast_context.macro_expansions[&decl_id],
                );

                match maybe_replacement {
                    Ok((replacement, ty)) => {
                        trace!("  to {replacement:?}");

                        let expansion = MacroExpansion { ty };
                        self.macro_expansions
                            .borrow_mut()
                            .insert(decl_id, Some(expansion));
                        let ty = self.convert_type(ty)?;

                        Ok(ConvertedDecl::Item(mk().span(span).pub_().const_item(
                            name,
                            ty,
                            replacement,
                        )))
                    }
                    Err(e) => {
                        self.macro_expansions.borrow_mut().insert(decl_id, None);
                        info!("Could not expand macro {name}: {e}");
                        Ok(ConvertedDecl::NoItem)
                    }
                }
            }

            // We aren't doing anything with the definitions of function-like
            // macros yet.
            MacroFunction { .. } => Ok(ConvertedDecl::NoItem),

            // Do not translate non-canonical decls. They will be translated at
            // their canonical declaration.
            NonCanonicalDecl { .. } => Ok(ConvertedDecl::NoItem),

            StaticAssert { .. } => {
                warn!("ignoring static assert during translation");
                Ok(ConvertedDecl::NoItem)
            }
        }
    }

    pub(crate) fn generate_submodule_imports(
        &self,
        decl_id: CDeclId,
        decl_file_id: Option<FileId>,
    ) {
        let decl_file_id = decl_file_id.expect("There should be a decl file path");
        let decl = self.ast_context.get_decl(&decl_id).unwrap();

        match decl.kind {
            CDeclKind::Struct { ref fields, .. } | CDeclKind::Union { ref fields, .. } => {
                let field_ids = fields.as_ref().map(|vec| vec.as_slice()).unwrap_or(&[]);

                for field_id in field_ids.iter() {
                    match self.ast_context[*field_id].kind {
                        CDeclKind::Field { typ, .. } => self.import_type(typ.ctype, decl_file_id),
                        _ => unreachable!("Found something in a struct other than a field"),
                    }
                }
            }
            CDeclKind::EnumConstant { .. } | CDeclKind::Enum { .. } => {}

            CDeclKind::Variable {
                has_static_duration: true,
                is_externally_visible: true,
                typ,
                ..
            }
            | CDeclKind::Variable {
                has_thread_duration: true,
                is_externally_visible: true,
                typ,
                ..
            }
            | CDeclKind::Typedef { typ, .. } => self.import_type(typ.ctype, decl_file_id),
            CDeclKind::Function {
                is_global: true,
                typ,
                ..
            } => self.import_type(typ, decl_file_id),

            CDeclKind::MacroObject { .. } => {
                if let Some(Some(expansion)) = self.macro_expansions.borrow().get(&decl_id) {
                    self.import_type(expansion.ty, decl_file_id)
                }
            }

            CDeclKind::Function { .. } | CDeclKind::MacroFunction { .. } => {
                // TODO: We may need to explicitly skip SIMD functions here when getting types for
                // a fn definition in a header since SIMD headers define functions but we're using imports
                // rather than translating the original definition
            }
            CDeclKind::Variable {
                has_static_duration,
                has_thread_duration,
                is_externally_visible: false,
                ..
            } if has_static_duration || has_thread_duration => {}
            ref e => unimplemented!("{:?}", e),
        }
    }

    pub(crate) fn import_type(&self, ctype: CTypeId, decl_file_id: FileId) {
        use self::CTypeKind::*;

        let type_kind = &self.ast_context[ctype].kind;
        match type_kind {
            // libc can be accessed from anywhere as of Rust 2019 by full path
            Void | Char | SChar | UChar | Short | UShort | Int | UInt | Long | ULong | LongLong
            | ULongLong | Int128 | UInt128 | Half | BFloat16 | Float | Double | LongDouble
            | Float128 => {}
            // Bool uses the bool type, so no dependency on libc
            Bool => {}
            Paren(ctype)
            | Decayed(ctype)
            | IncompleteArray(ctype)
            | ConstantArray(ctype, _)
            | Elaborated(ctype)
            | Pointer(CQualTypeId { ctype, .. })
            | Attributed(CQualTypeId { ctype, .. }, _)
            | VariableArray(ctype, _)
            | Reference(CQualTypeId { ctype, .. })
            | BlockPointer(CQualTypeId { ctype, .. })
            | TypeOf(ctype)
            | Complex(ctype) => self.import_type(*ctype, decl_file_id),
            Enum(decl_id) | Typedef(decl_id) | Union(decl_id) | Struct(decl_id) => {
                let mut decl_id = *decl_id;
                // if the `decl` has been "squashed", get the corresponding `decl_id`
                if self.ast_context.prenamed_decls.contains_key(&decl_id) {
                    decl_id = *self.ast_context.prenamed_decls.get(&decl_id).unwrap();
                }

                let ident_name = &self
                    .type_converter
                    .borrow()
                    .resolve_decl_name(decl_id)
                    .expect("Expected decl name");
                self.add_import(decl_file_id, decl_id, ident_name);
            }
            Function(CQualTypeId { ctype, .. }, params, ..) => {
                // Return Type
                let type_kind = &self.ast_context[*ctype].kind;

                // Rust doesn't use void for return type, so skip
                if *type_kind != Void {
                    self.import_type(*ctype, decl_file_id);
                }

                // Param Types
                for param_id in params {
                    self.import_type(param_id.ctype, decl_file_id);
                }
            }
            Vector(..) => {
                // Handled in `import_simd_typedef`
            }
            TypeOfExpr(_) | BuiltinFn | Atomic(..) => {}
            UnhandledSveType => {
                // TODO: handle SVE types
            }
        }
    }

    /// If we're trying to organize item definitions into submodules, add them to a module
    /// scoped "namespace" if we have a path available, otherwise add it to the global "namespace"
    pub(crate) fn insert_item(&self, mut item: Box<Item>, decl: &CDecl) {
        let decl_file_id = self.ast_context.file_id(decl);

        if self.tcfg.reorganize_definitions {
            self.use_feature("register_tool");
            let attrs = item_attrs(&mut item).expect("no attrs field on unexpected item variant");
            add_src_loc_attr(attrs, &decl.loc.as_ref().map(|x| x.begin()));
            let mut item_stores = self.items.borrow_mut();
            let items = item_stores.entry(decl_file_id.unwrap()).or_default();

            items.add_item(item);
        } else {
            self.items.borrow_mut()[&self.main_file].add_item(item)
        }
    }

    /// If we're trying to organize foreign item definitions into submodules, add them to a module
    /// scoped "namespace" if we have a path available, otherwise add it to the global "namespace"
    pub(crate) fn insert_foreign_item(&self, mut item: ForeignItem, decl: &CDecl) {
        let decl_file_id = self.ast_context.file_id(decl);

        if self.tcfg.reorganize_definitions {
            self.use_feature("register_tool");
            let attrs = foreign_item_attrs(&mut item)
                .expect("no attrs field on unexpected foreign item variant");
            add_src_loc_attr(attrs, &decl.loc.as_ref().map(|x| x.begin()));
            let mut items = self.items.borrow_mut();
            let mod_block_items = items.entry(decl_file_id.unwrap()).or_default();

            mod_block_items.add_foreign_item(item);
        } else {
            self.items.borrow_mut()[&self.main_file].add_foreign_item(item)
        }
    }

    pub(crate) fn add_import(&self, decl_file_id: FileId, decl_id: CDeclId, ident_name: &str) {
        let decl = &self.ast_context[decl_id];
        let import_file_id = self.ast_context.file_id(decl);

        // If the definition lives in the same header, there is no need to import it
        // in fact, this would be a hard rust error.
        // We should never import into the main module here, as that happens in make_submodule
        if (import_file_id == Some(decl_file_id)) || decl_file_id == self.main_file {
            return;
        }

        // TODO: get rid of this, not compatible with nested modules
        let mut module_path = vec!["super".into()];

        // If the decl does not live in the main module add the path to the sibling submodule
        if let Some(file_id) = import_file_id {
            if file_id != self.main_file {
                let file_name =
                    clean_path(&self.mod_names, self.ast_context.get_file_path(file_id));

                module_path.push(file_name);
            }
        }

        self.items
            .borrow_mut()
            .entry(decl_file_id)
            .or_default()
            .add_use(module_path, ident_name);
    }

    fn convert_function(
        &self,
        ctx: ExprContext,
        span: Span,
        is_global: bool,
        is_inline: bool,
        is_main: bool,
        is_variadic: bool,
        is_extern: bool,
        new_name: &str,
        name: &str,
        arguments: &[(CDeclId, String, CQualTypeId)],
        return_type: Option<CQualTypeId>,
        body: Option<CStmtId>,
        attrs: &IndexSet<c_ast::Attribute>,
    ) -> TranslationResult<ConvertedDecl> {
        self.function_context.borrow_mut().enter_new(name);

        self.with_scope(|| {
            let mut args: Vec<FnArg> = vec![];

            // handle regular (non-variadic) arguments
            for &(decl_id, ref var, typ) in arguments {
                let ConvertedVariable { ty, mutbl, init: _ } =
                    self.convert_variable(ctx, None, typ)?;

                let pat = if var.is_empty() {
                    mk().wild_pat()
                } else {
                    // extern function declarations don't support/require mut patterns
                    let mutbl = if body.is_none() {
                        Mutability::Immutable
                    } else {
                        mutbl
                    };

                    let new_var = self
                        .renamer
                        .borrow_mut()
                        .insert(decl_id, var.as_str())
                        .unwrap_or_else(|| {
                            panic!("Failed to insert argument '{var}' while converting '{name}'")
                        });

                    mk().set_mutbl(mutbl).ident_pat(new_var)
                };

                args.push(mk().arg(ty, pat))
            }

            let variadic = if is_variadic {
                // function definitions
                let mut builder = mk();
                let arg_va_list_name = if let Some(body_id) = body {
                    // FIXME: detect mutability requirements.
                    builder = builder.set_mutbl(Mutability::Mutable);

                    Some(self.register_va_decls(body_id))
                } else {
                    None
                };

                Some(builder.variadic_arg(arg_va_list_name))
            } else {
                None
            };

            // handle return type
            let ret = match return_type {
                Some(return_type) => self.convert_type(return_type.ctype)?,
                None => mk().never_ty(),
            };
            let is_void_ret = return_type
                .map(|qty| self.ast_context[qty.ctype].kind == CTypeKind::Void)
                .unwrap_or(false);

            // If a return type is void, we should instead omit the unit type return,
            // -> (), to be more idiomatic
            let ret = if is_void_ret {
                ReturnType::Default
            } else {
                ReturnType::Type(Default::default(), ret)
            };

            let decl = mk().fn_decl(new_name, args, variadic, ret);

            if let Some(body) = body {
                // Translating an actual function

                let ret = match return_type {
                    Some(return_type) => {
                        let ret_type_id: CTypeId =
                            self.ast_context.resolve_type_id(return_type.ctype);
                        if let CTypeKind::Void = self.ast_context.index(ret_type_id).kind {
                            cfg::ImplicitReturnType::Void
                        } else if is_main {
                            cfg::ImplicitReturnType::Main
                        } else {
                            cfg::ImplicitReturnType::NoImplicitReturnType
                        }
                    }
                    _ => cfg::ImplicitReturnType::Void,
                };

                let mut body_stmts = vec![];
                for &(_, _, typ) in arguments {
                    body_stmts.append(&mut self.compute_variable_array_sizes(ctx, typ.ctype)?);
                }

                let body_ids = match self.ast_context.index(body).kind {
                    CStmtKind::Compound(ref stmts) => stmts,
                    _ => panic!("function body expects to be a compound statement"),
                };
                body_stmts.append(&mut self.convert_function_body(ctx, name, body_ids, ret)?);
                let mut block = stmts_block(body_stmts);
                if let Some(span) = self.get_span(SomeId::Stmt(body)) {
                    block.set_span(span);
                }

                // c99 extern inline functions should be pub, but not gnu_inline attributed
                // extern inlines, which become subject to their gnu89 visibility (private)
                let is_extern_inline =
                    is_inline && is_extern && !attrs.contains(&c_ast::Attribute::GnuInline);

                // Only add linkage attributes if the function is `extern`
                let mut mk_ = if is_main {
                    mk()
                } else if (is_global && !is_inline) || is_extern_inline {
                    mk_linkage(false, new_name, name).extern_("C").pub_()
                } else if self.cur_file.borrow().is_some() {
                    mk().extern_("C").pub_()
                } else {
                    mk().extern_("C")
                };

                for attr in attrs {
                    mk_ = match attr {
                        c_ast::Attribute::AlwaysInline => mk_.call_attr("inline", vec!["always"]),
                        c_ast::Attribute::Cold => mk_.single_attr("cold"),
                        c_ast::Attribute::NoInline => mk_.call_attr("inline", vec!["never"]),
                        _ => continue,
                    };
                }

                // If this function is just a regular inline
                if is_inline && !attrs.contains(&c_ast::Attribute::AlwaysInline) {
                    mk_ = mk_.single_attr("inline");

                    // * In C99, a function defined inline will never, and a function defined extern
                    //   inline will always, emit an externally visible function.
                    // * If a non-static function is declared inline, then it must be defined in the
                    //   same translation unit. The inline definition that does not use extern is
                    //   not externally visible and does not prevent other translation units from
                    //   defining the same function. This makes the inline keyword an alternative to
                    //   static for defining functions inside header files, which may be included in
                    //   multiple translation units of the same program.
                    // * always_inline implies inline -
                    //   https://gcc.gnu.org/ml/gcc-help/2007-01/msg00051.html
                    //   even if the `inline` keyword isn't present
                    // * gnu_inline instead applies gnu89 rules. extern inline will not emit an
                    //   externally visible function.
                    if is_global && is_extern && !attrs.contains(&c_ast::Attribute::GnuInline) {
                        self.use_feature("linkage");
                        // ensures that public inlined rust function can be used in other modules
                        mk_ = mk_.str_attr("linkage", "external");
                    }
                    // NOTE: it does not seem necessary to have an else branch here that
                    // specifies internal linkage in all other cases due to name mangling by rustc.
                }

                Ok(ConvertedDecl::Item(
                    mk_.span(span).unsafe_().fn_item(decl, block),
                ))
            } else {
                // Translating an extern function declaration

                // When putting extern fns into submodules, they need to be public to be accessible
                let visibility = if self.tcfg.reorganize_definitions {
                    "pub"
                } else {
                    ""
                };

                let mut mk_ = mk_linkage(true, new_name, name).span(span).vis(visibility);

                for attr in attrs {
                    mk_ = match attr {
                        c_ast::Attribute::Alias(aliasee) => mk_.str_attr("link_name", aliasee),
                        _ => continue,
                    };
                }

                let function_decl = mk_.fn_foreign_item(decl);

                Ok(ConvertedDecl::ForeignItem(function_decl))
            }
        })
    }
}
