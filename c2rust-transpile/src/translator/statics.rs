use c2rust_ast_builder::mk;
use syn::{Expr, Item, ReturnType};

use crate::c_ast::TypedAstContext;
use crate::c_ast::get_node::GetNode;
use crate::c_ast::iterators::DFExpr;
use crate::c_ast::iterators::SomeId;
use crate::c_ast::{CDeclKind, CExprId, CExprKind, CQualTypeId, CTypeKind, CastKind};
use crate::diagnostics::TranslationResult;
use crate::driver::Translation;
use c2rust_ast_exporter::clang_ast::LRValue;

pub(crate) fn static_initializer_is_unsafe(
    ast_context: &TypedAstContext,
    expr_id: Option<CExprId>,
    qty: CQualTypeId,
) -> bool {
    // SIMD types are always unsafe in statics
    match ast_context.resolve_type(qty.ctype).kind {
        CTypeKind::Vector(..) => return true,
        CTypeKind::ConstantArray(ctype, ..) => {
            let kind = &ast_context.resolve_type(ctype).kind;

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
    let iter = DFExpr::new(ast_context, expr_id.into());

    for i in iter {
        let expr_id = match i {
            SomeId::Expr(expr_id) => expr_id,
            _ => unreachable!("Found static initializer type other than expr"),
        };

        use CExprKind::*;
        match ast_context[expr_id].kind {
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
pub(crate) fn static_initializer_is_uncompilable(
    ast_context: &TypedAstContext,
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
    if let CTypeKind::LongDouble = qtype.ctype.get_node(ast_context).kind {
        return true;
    }

    let iter = DFExpr::new(ast_context, expr_id.into());

    for i in iter {
        let expr_id = match i {
            SomeId::Expr(expr_id) => expr_id,
            _ => unreachable!("Found static initializer type other than expr"),
        };

        use CExprKind::*;
        match ast_context[expr_id].kind {
            // Technically we're being conservative here, but it's only the most
            // contrived array indexing initializers that would be accepted
            ArraySubscript(..) => return true,
            Member(..) => return true,

            Conditional(..) => return true,
            Unary(typ, Negate, _, _) => {
                if ast_context
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
                    let k = &ast_context.resolve_type(typ.ctype).kind;
                    if k.is_unsigned_integral_type() || k.is_pointer() {
                        return true;
                    }
                }
            }
            Unary(_, AddressOf, expr_id, _) => {
                if let Member(_, expr_id, _, _, _) = ast_context[expr_id].kind
                    && let DeclRef(..) = ast_context[expr_id].kind
                {
                    return true;
                }
            }
            InitList(qtype, _, _, _) => {
                let ty = &ast_context.resolve_type(qtype.ctype).kind;

                if let &CTypeKind::Struct(decl_id) = ty {
                    let decl = &decl_id.get_node(ast_context).kind;

                    if let CDeclKind::Struct {
                        fields: Some(fields),
                        ..
                    } = decl
                    {
                        for field_id in fields {
                            let field_decl = &field_id.get_node(ast_context).kind;

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
                if let CTypeKind::Pointer(qtype) = ast_context.resolve_type(qtype.ctype).kind
                    && let CTypeKind::Function(..) = ast_context.resolve_type(qtype.ctype).kind
                {
                    return true;
                }
            }
            _ => {}
        }
    }

    false
}

impl<'c> Translation<'c> {
    pub(crate) fn add_static_initializer_to_section(
        &self,
        name: &str,
        typ: CQualTypeId,
        init: &mut Box<Expr>,
    ) -> TranslationResult<()> {
        let mut default_init = self
            .implicit_default_expr(typ.ctype, true, false)?
            .to_expr();

        std::mem::swap(init, &mut default_init);

        let root_lhs_expr = mk().ident_expr(name);
        let assign_expr = mk().assign_expr(root_lhs_expr, default_init);
        let stmt = mk().expr_stmt(assign_expr);

        self.sectioned_static_initializers.borrow_mut().push(stmt);

        Ok(())
    }

    pub(crate) fn generate_global_static_init(&mut self) -> (Box<Item>, Box<Item>) {
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
        let static_val = mk().array_expr(vec![mk().ident_expr(fn_name)]);
        let static_item = static_attributes.static_item("INIT_ARRAY", static_ty, static_val);

        (fn_item, static_item)
    }
}
