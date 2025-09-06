use super::{Translation, translate_failure};
use crate::c_ast::*;
use crate::translator::context::ExprContext;
use crate::translator::decls::ConvertedDecl;
use std::ops::Index;

pub fn convert_declarations(t: &mut Translation, ctx: ExprContext) {
    let convert_decl_and_insert = |t: &mut Translation, decl_id: CDeclId, decl: &CDecl| {
        let decl_file_id = t.ast_context.file_id(decl);
        if t.tcfg.reorganize_definitions {
            *t.cur_file.borrow_mut() = decl_file_id;
        }
        match t.convert_decl(ctx, decl_id) {
            Err(e) => {
                let k = &t.ast_context.get_decl(&decl_id).map(|x| &x.kind);
                let msg = format!("Skipping declaration {:?} due to error: {}", k, e);
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

        if t.tcfg.reorganize_definitions && decl_file_id.is_some_and(|id| id != t.main_file) {
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
            convert_decl_and_insert(t, decl_id, decl);
        }
    }

    // Export top-level value declarations
    for top_id in &t.ast_context.c_decls_top {
        use CDeclKind::*;
        let decl = t.ast_context.index(*top_id);
        let needs_export = match decl.kind {
            Function { is_implicit, .. } => !is_implicit,
            Variable { .. } => true,
            MacroObject { .. } => true, // Depends on `tcfg.translate_const_macros`, but handled in `fn convert_const_macro_expansion`.
            MacroFunction { .. } => true, // Depends on `tcfg.translate_fn_macros`, but handled in `fn convert_fn_macro_invocation`.
            _ => false,
        };
        if needs_export {
            let decl_opt = t.ast_context.get_decl(top_id);
            let decl = decl_opt.as_ref().unwrap();
            convert_decl_and_insert(t, *top_id, decl);
        }
    }
}
