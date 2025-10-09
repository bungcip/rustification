use std::collections::HashMap;

use super::context::ExprContext;
use super::decls::ConvertedDecl;
use super::{Translation, translate_failure};
use crate::c_ast::get_node::GetNode;
use crate::c_ast::*;
use crate::diagnostics::TranslationResult;

pub(crate) fn convert_decl(
    t: &Translation,
    ctx: ExprContext,
    decl_id: CDeclId,
) -> TranslationResult<ConvertedDecl> {
    match t.convert_decl(ctx, decl_id) {
        Err(e) => {
            let k = &t.ast_context.get_decl(&decl_id).map(|x| &x.kind);
            let msg = format!("Skipping declaration {:?} due to error: {}", k, e);
            translate_failure(t.tcfg, &msg);
            Err(e)
        }
        Ok(converted_decl) => Ok(converted_decl),
    }
}

pub(crate) fn insert_converted_decl(t: &Translation, decl: &CDecl, converted_decl: ConvertedDecl) {
    match converted_decl {
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
    }
}

pub(crate) fn convert_declarations(t: &mut Translation, ctx: ExprContext) {
    // Export all types
    let decl_ids: Vec<CDeclId> = t.ast_context.iter_decls().map(|(id, _)| *id).collect();
    for decl_id in decl_ids {
        let (needs_export, decl) = {
            let decl = decl_id.get_node(&t.ast_context);
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
            (needs_export, decl.clone())
        };

        if needs_export {
            // convert_decl_and_insert(t, ctx, decl_id, &decl);
            let decl_file_id = t.ast_context.file_id(&decl);
            if t.tcfg.reorganize_definitions {
                t.cur_file.set(decl_file_id);
            }
            let converted_decl = convert_decl(t, ctx, decl_id).unwrap();
            insert_converted_decl(t, &decl, converted_decl);
            t.cur_file.take();

            if t.tcfg.reorganize_definitions && decl_file_id.is_some_and(|id| id != t.main_file) {
                t.generate_submodule_imports(decl_id, decl_file_id);
            }
        }
    }

    // Export top-level value declarations.
    // We do this in a conversion pass and then an insertion pass
    // so that the conversion order can differ from the order they're emitted in.
    let mut converted_decls = t
        .ast_context
        .c_decls_top
        .iter()
        .filter_map(|&top_id| {
            use CDeclKind::*;
            let needs_export = match top_id.get_node(&t.ast_context).kind {
                Function { is_implicit, .. } => !is_implicit,
                Variable { .. } => true,
                MacroObject { .. } => true, // Depends on `tcfg.translate_const_macros`, but handled in `fn convert_const_macro_expansion`.
                MacroFunction { .. } => true, // Depends on `tcfg.translate_fn_macros`, but handled in `fn convert_fn_macro_invocation`.
                _ => false,
            };
            if !needs_export {
                return None;
            }

            let decl = t.ast_context.get_decl(&top_id).unwrap();
            let decl_file_id = t.ast_context.file_id(decl);
            if t.tcfg.reorganize_definitions {
                t.cur_file.set(decl_file_id);
            }

            // TODO use `.inspect_err` once stabilized in Rust 1.76.
            let converted = match t.convert_decl(ctx, top_id) {
                Err(e) => {
                    let k = &t.ast_context.get_decl(&top_id).map(|x| &x.kind);
                    let msg = format!("Skipping declaration {:?} due to error: {}", k, e);
                    translate_failure(t.tcfg, &msg);
                    Err(e)
                }
                Ok(converted) => Ok(converted),
            }
            .ok()
            .unwrap();

            t.cur_file.take();
            Some((top_id, converted))
        })
        .collect::<HashMap<_, _>>();

    t.ast_context.sort_top_decls_for_emitting();

    for top_id in &t.ast_context.c_decls_top {
        let decl = t.ast_context.get_decl(top_id).unwrap();
        let decl_file_id = t.ast_context.file_id(decl);
        // TODO use `let else` when it stabilizes.
        let converted_decl = match converted_decls.remove(top_id) {
            Some(converted) => converted,
            None => continue,
        };

        use ConvertedDecl::*;
        match converted_decl {
            Item(item) => {
                t.insert_item(item, decl);
            }
            ForeignItem(item) => {
                t.insert_foreign_item(*item, decl);
            }
            Items(items) => {
                for item in items {
                    t.insert_item(Box::new(item), decl);
                }
            }
            NoItem => {}
        };

        if t.tcfg.reorganize_definitions && decl_file_id.is_some_and(|id| id != t.main_file) {
            t.generate_submodule_imports(*top_id, decl_file_id);
        }
    }
}
