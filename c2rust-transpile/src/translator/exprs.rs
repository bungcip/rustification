use crate::translator::TranslationError;
use c2rust_ast_builder::mk;
use c2rust_ast_builder::properties::Mutability;
use std::ops::Index;

use log::trace;
use proc_macro2::{Punct, Spacing::*, TokenTree};
use syn::*;
use syn::{BinOp, UnOp}; // To override c_ast::{BinOp,UnOp} from glob import

use crate::diagnostics::TranslationResult;
use crate::transform;
use crate::translator::named_references::NamedReference;
use crate::translator::{DecayRef, pointer_offset, unwrap_function_pointer};
use crate::{
    c_ast::{CDeclKind, CExprKind, CTypeKind, UnTypeOp},
    generic_err, generic_loc_err,
    translator::transmute_expr,
    with_stmts::WithStmts,
};

use crate::ExternCrate;
use crate::c_ast;
use crate::c_ast::*;

use super::{ExprContext, Translation, vec_expr};

impl<'c> Translation<'c> {
    #[allow(clippy::vec_box/*, reason = "not worth a substantial refactor"*/)]
    pub(crate) fn convert_exprs(
        &self,
        ctx: ExprContext,
        exprs: &[CExprId],
    ) -> TranslationResult<WithStmts<Vec<Box<Expr>>>> {
        exprs
            .iter()
            .map(|arg| self.convert_expr(ctx, *arg))
            .collect()
    }

    /// Translate a C expression into a Rust one, possibly collecting side-effecting statements
    /// to run before the expression.
    ///
    /// The `use_` argument informs us how the C expression we are translating is used in the C
    /// program. See `ExprUse` for more information.
    ///
    /// In the case that `use_` is unused, all side-effecting components will be in the
    /// `stmts` field of the output and it is expected that the `val` field of the output will be
    /// ignored.
    pub fn convert_expr(
        &self,
        mut ctx: ExprContext,
        expr_id: CExprId,
    ) -> TranslationResult<WithStmts<Box<Expr>>> {
        let Located {
            loc: src_loc,
            kind: expr_kind,
        } = &self.ast_context[expr_id];

        trace!(
            "Converting expr {:?}: {:?}",
            expr_id, self.ast_context[expr_id]
        );

        if self.tcfg.translate_const_macros {
            if let Some(converted) = self.convert_macro_expansion(ctx, expr_id)? {
                return Ok(converted);
            }
        }

        if self.tcfg.translate_fn_macros {
            let text = self.ast_context.macro_expansion_text.get(&expr_id);
            if let Some(converted) = text.and_then(|text| self.convert_macro_invocation(ctx, text))
            {
                return Ok(converted);
            }
        }

        use CExprKind::*;
        match *expr_kind {
            DesignatedInitExpr(..) => Err(generic_err!("Unexpected designated init expr")),
            BadExpr => Err(generic_err!("convert_expr: expression kind not supported")),
            ShuffleVector(_, ref child_expr_ids) => self
                .convert_shuffle_vector(ctx, child_expr_ids)
                .map_err(|e| {
                    generic_loc_err!(self.ast_context.display_loc(src_loc), "{}", e.message)
                }),
            ConvertVector(..) => Err(generic_err!("convert vector not supported")),

            UnaryType(_ty, kind, opt_expr, arg_ty) => {
                let result = match kind {
                    UnTypeOp::SizeOf => match opt_expr {
                        None => self.compute_size_of_type(ctx, arg_ty.ctype)?,
                        Some(_) => {
                            let inner = self.variable_array_base_type(arg_ty.ctype);
                            let inner_size = self.compute_size_of_type(ctx, inner)?;

                            if let Some(sz) = self.compute_size_of_expr(arg_ty.ctype) {
                                inner_size.map(|x| {
                                    mk().binary_expr(BinOp::Mul(Default::default()), sz, x)
                                })
                            } else {
                                // Otherwise, use the pointer and make a deref of a pointer offset expression
                                inner_size
                            }
                        }
                    },
                    UnTypeOp::AlignOf => self.compute_align_of_type(arg_ty.ctype, false)?,
                    UnTypeOp::PreferredAlignOf => self.compute_align_of_type(arg_ty.ctype, true)?,
                };

                Ok(result.map(|x| mk().cast_expr(x, mk().path_ty(vec!["ffi", "c_ulong"]))))
            }

            ConstantExpr(_ty, child, value) => {
                if let Some(constant) = value {
                    self.convert_constant(constant).map(WithStmts::new_val)
                } else {
                    self.convert_expr(ctx, child)
                }
            }

            DeclRef(qual_ty, decl_id, lrvalue) => {
                let decl = &self
                    .ast_context
                    .get_decl(&decl_id)
                    .ok_or_else(|| generic_err!("Missing declref {:?}", decl_id))?
                    .kind;
                if ctx.is_const {
                    if let CDeclKind::Variable {
                        has_static_duration: true,
                        ..
                    } = decl
                    {
                        return Err(generic_loc_err!(
                            self.ast_context.display_loc(src_loc),
                            "Cannot refer to static duration variable in a const expression",
                        ));
                    }
                }

                let varname = decl.get_name().expect("expected variable name").to_owned();
                let rustname = self
                    .renamer
                    .borrow_mut()
                    .get(&decl_id)
                    .ok_or_else(|| generic_err!("name not declared: '{}'", varname))?;

                // Import the referenced global decl into our submodule
                if self.tcfg.reorganize_definitions {
                    if let Some(cur_file) = self.cur_file.borrow().as_ref() {
                        self.add_import(*cur_file, decl_id, &rustname);
                        // match decl {
                        //     CDeclKind::Variable { is_defn: false, .. } => {}
                        //     _ => self.add_import(cur_file, decl_id, &rustname),
                        // }
                    }
                }

                let mut val = mk().path_expr(vec![rustname]);

                // If the variable is volatile and used as something that isn't an LValue, this
                // constitutes a volatile read.
                if lrvalue.is_rvalue() && qual_ty.qualifiers.is_volatile {
                    val = self.volatile_read(val, qual_ty)?;
                }

                // If the variable is actually an `EnumConstant`, we need to add a cast to the
                // expected integral type. When modifying this, look at `Translation::enum_cast` -
                // this function assumes `DeclRef`'s to `EnumConstants`'s will translate to casts.
                if let &CDeclKind::EnumConstant { .. } = decl {
                    let ty = self.convert_type(qual_ty.ctype)?;
                    val = mk().cast_expr(val, ty);
                }

                // Most references to the va_list should refer to the VaList
                // type, not VaListImpl
                if !ctx.expecting_valistimpl && self.ast_context.is_va_list(qual_ty.ctype) {
                    val = mk().method_call_expr(val, "as_va_list", Vec::new());
                }

                // If we are referring to a function and need its address, we
                // need to cast it to fn() to ensure that it has a real address.
                let mut set_unsafe = false;
                if ctx.needs_address() {
                    if let CDeclKind::Function { parameters, .. } = decl {
                        let ty = self.convert_type(qual_ty.ctype)?;
                        let actual_ty = self
                            .type_converter
                            .borrow_mut()
                            .knr_function_type_with_parameters(
                                &self.ast_context,
                                qual_ty.ctype,
                                parameters,
                            )?;
                        if let Some(actual_ty) = actual_ty {
                            // If we're casting a concrete function to
                            // a K&R function pointer type, use transmute
                            if let Some(cur_file) = *self.cur_file.borrow() {
                                self.import_type(qual_ty.ctype, cur_file);
                            }
                            val = transmute_expr(actual_ty, ty, val);
                            set_unsafe = true;
                        } else {
                            val = mk().cast_expr(val, ty);
                        }
                    }
                }

                if let CTypeKind::VariableArray(..) =
                    self.ast_context.resolve_type(qual_ty.ctype).kind
                {
                    val = mk().method_call_expr(val, "as_mut_ptr", vec![]);
                }

                let mut res = WithStmts::new_val(val);
                res.merge_unsafe(set_unsafe);
                Ok(res)
            }

            OffsetOf(ty, ref kind) => match kind {
                OffsetOfKind::Constant(val) => Ok(WithStmts::new_val(self.mk_int_lit(
                    ty,
                    *val,
                    IntBase::Dec,
                )?)),
                OffsetOfKind::Variable(qty, field_id, expr_id) => {
                    self.use_crate(ExternCrate::Memoffset);

                    // Struct Type
                    let decl_id = {
                        let kind = match self.ast_context[qty.ctype].kind {
                            CTypeKind::Elaborated(ty_id) => &self.ast_context[ty_id].kind,
                            ref kind => kind,
                        };

                        kind.as_decl_or_typedef()
                            .expect("Did not find decl_id for offsetof struct")
                    };
                    let name = self.resolve_decl_inner_name(decl_id);
                    let ty_ident = mk().ident(name);

                    // Field name
                    let field_name = self
                        .type_converter
                        .borrow()
                        .resolve_field_name(None, *field_id)
                        .expect("Did not find name for offsetof struct field");
                    let field_ident = mk().ident(field_name);

                    // Index Expr
                    let expr = self
                        .convert_expr(ctx, *expr_id)?
                        .to_pure_expr()
                        .ok_or_else(|| {
                            generic_err!("Expected Variable offsetof to be a side-effect free")
                        })?;
                    let expr = mk().cast_expr(expr, mk().ident_ty("usize"));
                    use syn::__private::ToTokens;
                    let index_expr = expr.to_token_stream();

                    // offset_of!(Struct, field[expr as usize]) as ty
                    let macro_body = vec![
                        TokenTree::Ident(ty_ident),
                        TokenTree::Punct(Punct::new(',', Alone)),
                        TokenTree::Ident(field_ident),
                        TokenTree::Group(proc_macro2::Group::new(
                            proc_macro2::Delimiter::Bracket,
                            index_expr,
                        )),
                    ];
                    let path = mk().path("offset_of");
                    let mac = mk().mac_expr(mk().mac(
                        path,
                        macro_body,
                        MacroDelimiter::Paren(Default::default()),
                    ));

                    // Cast type
                    let cast_ty = self.convert_type(ty.ctype)?;
                    let cast_expr = mk().cast_expr(mac, cast_ty);

                    Ok(WithStmts::new_val(cast_expr))
                }
            },

            Literal(ty, ref kind) => self.convert_literal(ctx, ty, kind),

            ImplicitCast(ty, expr, kind, opt_field_id, _)
            | ExplicitCast(ty, expr, kind, opt_field_id, _) => {
                let is_explicit = matches!(expr_kind, CExprKind::ExplicitCast(..));
                // A reference must be decayed if a bitcast is required. Const casts in
                // LLVM 8 are now NoOp casts, so we need to include it as well.
                match kind {
                    CastKind::BitCast | CastKind::PointerToIntegral | CastKind::NoOp => {
                        ctx.decay_ref = DecayRef::Yes
                    }
                    CastKind::FunctionToPointerDecay | CastKind::BuiltinFnToFnPtr => {
                        ctx.needs_address = true;
                    }
                    _ => {}
                }

                let source_ty = self.ast_context[expr]
                    .kind
                    .get_qual_type()
                    .ok_or_else(|| generic_err!("bad source type"))?;

                let val = if is_explicit {
                    let stmts = self.compute_variable_array_sizes(ctx, ty.ctype)?;
                    let mut val = self.convert_expr(ctx, expr)?;
                    val.prepend_stmts(stmts);
                    val
                } else {
                    self.convert_expr(ctx, expr)?
                };
                // Shuffle Vector "function" builtins will add a cast to the output of the
                // builtin call which is unnecessary for translation purposes
                if self.casting_simd_builtin_call(expr, is_explicit, kind) {
                    return Ok(val);
                }
                self.convert_cast(
                    ctx,
                    source_ty,
                    ty,
                    val,
                    Some(expr),
                    Some(kind),
                    opt_field_id,
                )
            }

            Unary(type_id, op, arg, lrvalue) => {
                self.convert_unary_operator(ctx, op, type_id, arg, lrvalue)
            }

            Conditional(_, cond, lhs, rhs) => {
                if ctx.is_const {
                    return Err(generic_loc_err!(
                        self.ast_context.display_loc(src_loc),
                        "Constants cannot contain ternary expressions in Rust",
                    ));
                }
                let cond = self.convert_condition(ctx, true, cond)?;

                let lhs = self.convert_expr(ctx, lhs)?;
                let rhs = self.convert_expr(ctx, rhs)?;

                if ctx.is_unused() {
                    let is_unsafe = lhs.is_unsafe() || rhs.is_unsafe();
                    let then = mk().block(lhs.into_stmts());
                    let else_ = mk().block_expr(mk().block(rhs.into_stmts()));

                    let mut res = cond.and_then(|c| -> TranslationResult<_> {
                        Ok(WithStmts::new(
                            vec![mk().semi_stmt(mk().ifte_expr(c, then, Some(else_)))],
                            self.panic_or_err("Conditional expression is not supposed to be used"),
                        ))
                    })?;
                    res.merge_unsafe(is_unsafe);
                    Ok(res)
                } else {
                    let then = lhs.to_block();
                    let else_ = rhs.to_expr();

                    Ok(cond.map(|c| {
                        let ifte_expr = mk().ifte_expr(c, then, Some(else_));

                        if ctx.ternary_needs_parens {
                            mk().paren_expr(ifte_expr)
                        } else {
                            ifte_expr
                        }
                    }))
                }
            }

            BinaryConditional(ty, lhs, rhs) => {
                if ctx.is_unused() {
                    let mut lhs = self.convert_condition(ctx, false, lhs)?;
                    let rhs = self.convert_expr(ctx, rhs)?;
                    lhs.merge_unsafe(rhs.is_unsafe());

                    lhs.and_then(|val| {
                        Ok(WithStmts::new(
                            vec![mk().semi_stmt(mk().ifte_expr(
                                val,
                                mk().block(rhs.into_stmts()),
                                None,
                            ))],
                            self.panic_or_err(
                                "Binary conditional expression is not supposed to be used",
                            ),
                        ))
                    })
                } else {
                    self.name_reference_write_read(ctx, lhs)?.result_map(
                        |NamedReference {
                             rvalue: lhs_val, ..
                         }| {
                            let cond = self.match_bool(true, ty.ctype, lhs_val.clone());
                            let ite = mk().ifte_expr(
                                cond,
                                mk().block(vec![mk().expr_stmt(lhs_val)]),
                                Some(self.convert_expr(ctx, rhs)?.to_expr()),
                            );
                            Ok(ite)
                        },
                    )
                }
            }

            Binary(type_id, op, lhs, rhs, opt_lhs_type_id, opt_res_type_id) => self
                .convert_binary_expr(ctx, type_id, op, lhs, rhs, opt_lhs_type_id, opt_res_type_id)
                .map_err(|e| Box::new(e.add_loc(self.ast_context.display_loc(src_loc)))),

            ArraySubscript(_, ref lhs, ref rhs, _) => {
                let lhs_node = &self.ast_context.index(*lhs).kind;
                let rhs_node = &self.ast_context.index(*rhs).kind;

                let lhs_node_type = lhs_node
                    .get_type()
                    .ok_or_else(|| generic_err!("lhs node bad type"))?;
                let lhs_node_kind = &self.ast_context.resolve_type(lhs_node_type).kind;
                let lhs_is_indexable = lhs_node_kind.is_pointer() || lhs_node_kind.is_vector();

                // From here on in, the LHS is the pointer/array and the RHS the index
                let (lhs, rhs, lhs_node) = if lhs_is_indexable {
                    (lhs, rhs, lhs_node)
                } else {
                    (rhs, lhs, rhs_node)
                };

                let lhs_node_type = lhs_node
                    .get_type()
                    .ok_or_else(|| generic_err!("lhs node bad type"))?;
                if self
                    .ast_context
                    .resolve_type(lhs_node_type)
                    .kind
                    .is_vector()
                {
                    return Err(generic_loc_err!(
                        self.ast_context.display_loc(src_loc),
                        "Attempting to index a vector type"
                    ));
                }

                let rhs = self.convert_expr(ctx.used(), *rhs)?;
                rhs.and_then(|rhs| {
                    let simple_index_array = if ctx.needs_address() {
                        // We can't necessarily index into an array if we're using
                        // that element to compute an address.
                        None
                    } else {
                        match lhs_node {
                            &CExprKind::ImplicitCast(
                                _,
                                arr,
                                CastKind::ArrayToPointerDecay,
                                _,
                                _,
                            ) => {
                                match self.ast_context[arr].kind {
                                    CExprKind::Member(_, _, field_decl, _, _)
                                        if self
                                            .potential_flexible_array_members
                                            .borrow()
                                            .contains(&field_decl) =>
                                    {
                                        None
                                    }
                                    ref kind => {
                                        let arr_type = kind
                                            .get_type()
                                            .ok_or_else(|| generic_err!("bad arr type"))?;
                                        match self.ast_context.resolve_type(arr_type).kind {
                                            // These get translated to 0-element arrays, this avoids the bounds check
                                            // that using an array subscript in Rust would cause
                                            CTypeKind::IncompleteArray(_) => None,
                                            _ => Some(arr),
                                        }
                                    }
                                }
                            }
                            _ => None,
                        }
                    };

                    if let Some(arr) = simple_index_array {
                        // If the LHS just underwent an implicit cast from array to pointer, bypass that
                        // to make an actual Rust indexing operation

                        let t = self.ast_context[arr]
                            .kind
                            .get_type()
                            .ok_or_else(|| generic_err!("bad arr type"))?;
                        let var_elt_type_id = match self.ast_context.resolve_type(t).kind {
                            CTypeKind::ConstantArray(..) => None,
                            CTypeKind::IncompleteArray(..) => None,
                            CTypeKind::VariableArray(elt, _) => Some(elt),
                            ref other => panic!("Unexpected array type {:?}", other),
                        };

                        let is_array_of_pointer = self.check_type_is_constant_aop(t);
                        let is_static_variable = self.ast_context.is_static_variable(arr);

                        let lhs = self.convert_expr(ctx.used(), arr)?;
                        Ok(lhs.map(|lhs| {
                            // Don't dereference the offset if we're still within the variable portion
                            if let Some(elt_type_id) = var_elt_type_id {
                                let mul = self.compute_size_of_expr(elt_type_id);
                                pointer_offset(lhs, rhs, mul, false, true)
                            } else {
                                let mut expr =
                                    mk().index_expr(lhs, transform::cast_int(rhs, "usize", false));

                                if is_array_of_pointer.is_some() && is_static_variable {
                                    // if the array is pointer in static then just unwrap it
                                    // i.e: array[0].0
                                    expr = mk().anon_field_expr(expr, 0);
                                }
                                expr
                            }
                        }))
                    } else {
                        // LHS must be ref decayed for the offset method call's self param
                        let lhs = self.convert_expr(ctx.used().decay_ref(), *lhs)?;
                        lhs.result_map(|lhs| {
                            // stmts.extend(lhs.stmts_mut());
                            // is_unsafe = is_unsafe || lhs.is_unsafe();

                            let lhs_type_id = lhs_node
                                .get_type()
                                .ok_or_else(|| generic_err!("bad lhs type"))?;

                            // Determine the type of element being indexed
                            let pointee_type_id =
                                match self.ast_context.resolve_type(lhs_type_id).kind {
                                    CTypeKind::Pointer(pointee_id) => pointee_id,
                                    _ => {
                                        return Err(generic_err!(
                                            "Subscript applied to non-pointer: {:?}",
                                            lhs
                                        ));
                                    }
                                };

                            let mul = self.compute_size_of_expr(pointee_type_id.ctype);
                            Ok(pointer_offset(lhs, rhs, mul, false, true))
                        })
                    }
                })
            }

            Call(call_expr_ty, func, ref args) => {
                let fn_ty =
                    self.ast_context
                        .get_pointee_qual_type(
                            self.ast_context[func].kind.get_type().ok_or_else(|| {
                                generic_err!("Invalid callee expression {:?}", func)
                            })?,
                        )
                        .map(|ty| &self.ast_context.resolve_type(ty.ctype).kind);
                let is_variadic = match fn_ty {
                    Some(CTypeKind::Function(_, _, is_variadic, _, _)) => *is_variadic,
                    _ => false,
                };
                let func = match self.ast_context[func].kind {
                    // Direct function call
                    CExprKind::ImplicitCast(_, fexp, CastKind::FunctionToPointerDecay, _, _)
                    // Only a direct function call with pointer decay if the
                    // callee is a declref
                    if matches!(self.ast_context[fexp].kind, CExprKind::DeclRef(..)) =>
                        {
                            self.convert_expr(ctx.used(), fexp)?
                        }

                    // Builtin function call
                    CExprKind::ImplicitCast(_, fexp, CastKind::BuiltinFnToFnPtr, _, _) => {
                        return self.convert_builtin(ctx, fexp, args);
                    }

                    // Function pointer call
                    _ => {
                        let callee = self.convert_expr(ctx.used(), func)?;
                        let make_fn_ty = |ret_ty: Box<Type>| {
                            let ret_ty = match *ret_ty {
                                Type::Tuple(TypeTuple { elems: ref v, .. }) if v.is_empty() => ReturnType::Default,
                                _ => ReturnType::Type(Default::default(), ret_ty),
                            };
                            let bare_ty = (
                                vec![mk().bare_arg(mk().infer_ty(), None::<Box<Ident>>); args.len()],
                                None::<BareVariadic>,
                                ret_ty
                            );
                            mk().barefn_ty(bare_ty)
                        };
                        match fn_ty {
                            Some(CTypeKind::Function(ret_ty, _, _, _, false)) => {
                                // K&R function pointer without arguments
                                let ret_ty = self.convert_type(ret_ty.ctype)?;
                                let target_ty = make_fn_ty(ret_ty);
                                callee.map(|fn_ptr| {
                                    let fn_ptr = unwrap_function_pointer(fn_ptr);
                                    transmute_expr(mk().infer_ty(), target_ty, fn_ptr)
                                })
                            }
                            None => {
                                // We have to infer the return type from our expression type
                                let ret_ty = self.convert_type(call_expr_ty.ctype)?;
                                let target_ty = make_fn_ty(ret_ty);
                                callee.map(|fn_ptr| {
                                    transmute_expr(mk().infer_ty(), target_ty, fn_ptr)
                                })
                            }
                            Some(_) => {
                                // Normal function pointer
                                callee.map(unwrap_function_pointer)
                            }
                        }
                    }
                };

                let call = func.and_then(|func| {
                    // We want to decay refs only when function is variadic
                    ctx.decay_ref = DecayRef::from(is_variadic);

                    let args = self.convert_exprs(ctx.used(), args)?;

                    let res: TranslationResult<_> = Ok(args.map(|args| mk().call_expr(func, args)));
                    res
                })?;

                self.convert_side_effects_expr(
                    ctx,
                    call,
                    "Function call expression is not supposed to be used",
                )
            }

            Member(qual_ty, expr, decl, kind, _) => {
                if ctx.is_unused() {
                    self.convert_expr(ctx, expr)
                } else {
                    let mut val = match kind {
                        MemberKind::Dot => self.convert_expr(ctx, expr)?,
                        MemberKind::Arrow => {
                            if let CExprKind::Unary(_, c_ast::UnOp::AddressOf, subexpr_id, _) =
                                self.ast_context[expr].kind
                            {
                                // Special-case the `(&x)->field` pattern
                                // Convert it directly into `x.field`
                                self.convert_expr(ctx, subexpr_id)?
                            } else {
                                let val = self.convert_expr(ctx, expr)?;
                                val.map(|v| mk().unary_expr(UnOp::Deref(Default::default()), v))
                            }
                        }
                    };

                    let record_id = self.ast_context.parents[&decl];
                    if self.ast_context.has_inner_struct_decl(record_id) {
                        // The structure is split into an outer and an inner,
                        // so we need to go through the outer structure to the inner one
                        val = val.map(|v| mk().anon_field_expr(v, 0));
                    };

                    let field_name = self
                        .type_converter
                        .borrow()
                        .resolve_field_name(None, decl)
                        .unwrap();
                    let is_bitfield = match &self.ast_context[decl].kind {
                        CDeclKind::Field { bitfield_width, .. } => bitfield_width.is_some(),
                        _ => unreachable!("Found a member which is not a field"),
                    };
                    if is_bitfield {
                        // Convert a bitfield member one of four ways:
                        // A) bf.a()
                        // B) (*bf).a()
                        // C) bf
                        // D) (*bf)
                        //
                        // The first two are when we know this bitfield member is going to be read
                        // from (default), possibly requiring a dereference first. The latter two
                        // are generated when we are expecting to require a write, which will need
                        // to make a method call with some input which we do not yet have access
                        // to and will have to be handled elsewhere, IE `bf.set_a(1)`
                        if !ctx.is_bitfield_write {
                            // Cases A and B above
                            val = val.map(|v| mk().method_call_expr(v, field_name, vec![]));
                        }
                    } else {
                        val = val.map(|v| mk().field_expr(v, field_name));
                    };

                    // Most references to the va_list should refer to the VaList
                    // type, not VaListImpl
                    if !ctx.expecting_valistimpl && self.ast_context.is_va_list(qual_ty.ctype) {
                        val = val.map(|v| {
                            mk().method_call_expr(v, "as_va_list", Vec::<Box<Expr>>::new())
                        });
                    }

                    Ok(val)
                }
            }

            Paren(_, val) => self.convert_expr(ctx, val),

            CompoundLiteral(_, val) => self.convert_expr(ctx, val),

            InitList(ty, ref ids, opt_union_field_id, _) => {
                self.convert_init_list(ctx, ty, ids, opt_union_field_id)
            }

            ImplicitValueInit(ty) => {
                self.implicit_default_expr(ty.ctype, ctx.is_static, ctx.inside_init_list_aop)
            }

            Predefined(_, val_id) => self.convert_expr(ctx, val_id),

            Statements(_, compound_stmt_id) => {
                self.convert_statement_expression(ctx, compound_stmt_id)
            }

            VAArg(ty, val_id) => self.convert_vaarg(ctx, ty, val_id),

            Choose(_, _cond, lhs, rhs, is_cond_true) => {
                let chosen_expr = if is_cond_true {
                    self.convert_expr(ctx, lhs)?
                } else {
                    self.convert_expr(ctx, rhs)?
                };

                // TODO: Support compile-time choice between lhs and rhs based on cond.

                // From Clang Expr.h
                // ChooseExpr - GNU builtin-in function __builtin_choose_expr.
                // This AST node is similar to the conditional operator (?:) in C, with
                // the following exceptions:
                // - the test expression must be a integer constant expression.
                // - the expression returned acts like the chosen subexpression in every
                //   visible way: the type is the same as that of the chosen subexpression,
                //   and all predicates (whether it's an l-value, whether it's an integer
                //   constant expression, etc.) return the same result as for the chosen
                //   sub-expression.

                Ok(chosen_expr)
            }

            Atomic {
                ref name,
                ptr,
                order,
                val1,
                order_fail,
                val2,
                weak,
                ..
            } => self.convert_atomic(ctx, name, ptr, order, val1, order_fail, val2, weak),
        }
    }

    pub fn implicit_default_expr(
        &self,
        ty_id: CTypeId,
        is_static: bool,
        inside_init_list_aop: bool,
    ) -> TranslationResult<WithStmts<Box<Expr>>> {
        let resolved_ty_id = self.ast_context.resolve_type_id(ty_id);
        let resolved_ty = &self.ast_context.index(resolved_ty_id).kind;

        if self.ast_context.is_va_list(resolved_ty_id) {
            // generate MaybeUninit::uninit().assume_init()
            let path = vec!["core", "mem", "MaybeUninit", "uninit"];
            let call = mk().call_expr(mk().abs_path_expr(path), vec![]);
            let call = mk().method_call_expr(call, "assume_init", vec![]);
            return Ok(WithStmts::new_val(call));
        }

        if resolved_ty.is_bool() {
            Ok(WithStmts::new_val(mk().lit_expr(mk().bool_lit(false))))
        } else if resolved_ty.is_integral_type() {
            Ok(WithStmts::new_val(
                mk().lit_expr(mk().int_unsuffixed_lit(0)),
            ))
        } else if resolved_ty.is_floating_type() {
            match self.ast_context[ty_id].kind {
                CTypeKind::LongDouble => Ok(WithStmts::new_val(
                    mk().path_expr(vec!["f128", "f128", "ZERO"]),
                )),
                _ => Ok(WithStmts::new_val(
                    mk().lit_expr(mk().float_unsuffixed_lit("0.")),
                )),
            }
        } else if let &CTypeKind::Pointer(_) = resolved_ty {
            self.null_ptr(resolved_ty_id, is_static, inside_init_list_aop)
                .map(WithStmts::new_val)
        } else if let &CTypeKind::ConstantArray(elt, sz) = resolved_ty {
            let sz = mk().lit_expr(mk().int_unsuffixed_lit(sz as u128));
            Ok(self
                .implicit_default_expr(elt, is_static, inside_init_list_aop)?
                .map(|elt| mk().repeat_expr(elt, sz)))
        } else if let &CTypeKind::IncompleteArray(_) = resolved_ty {
            // Incomplete arrays are translated to zero length arrays
            Ok(WithStmts::new_val(mk().array_expr(vec![])))
        } else if let Some(decl_id) = resolved_ty.as_underlying_decl() {
            self.zero_initializer(decl_id, ty_id, is_static)
        } else if let &CTypeKind::VariableArray(elt, _) = resolved_ty {
            // Variable length arrays unnested and implemented as a flat array of the underlying
            // element type.

            // Find base element type of potentially nested arrays
            let inner = self.variable_array_base_type(elt);
            let count = self.compute_size_of_expr(ty_id).unwrap();
            Ok(self
                .implicit_default_expr(inner, is_static, inside_init_list_aop)?
                .map(|val| vec_expr(val, count)))
        } else if let &CTypeKind::Vector(CQualTypeId { ctype, .. }, len) = resolved_ty {
            self.implicit_vector_default(ctype, len, is_static)
        } else {
            Err(generic_err!(
                "Unsupported default initializer: {:?}",
                resolved_ty
            ))
        }
    }

    pub fn convert_binary_expr(
        &self,
        mut ctx: ExprContext,
        type_id: CQualTypeId,
        op: c_ast::BinOp,
        lhs: CExprId,
        rhs: CExprId,
        opt_lhs_type_id: Option<CQualTypeId>,
        opt_res_type_id: Option<CQualTypeId>,
    ) -> TranslationResult<WithStmts<Box<Expr>>> {
        // If we're not making an assignment, a binop will require parens
        // applied to ternary conditionals
        if !op.is_assignment() {
            ctx.ternary_needs_parens = true;
        }

        let lhs_loc = &self.ast_context[lhs].loc;
        let rhs_loc = &self.ast_context[rhs].loc;
        use c_ast::BinOp::*;
        match op {
            Comma => {
                // The value of the LHS of a comma expression is always discarded
                self.convert_expr(ctx.unused(), lhs)?
                    .and_then(|_| self.convert_expr(ctx, rhs))
            }

            And | Or => {
                let lhs = self.convert_condition(ctx, true, lhs)?;
                let rhs = self.convert_condition(ctx, true, rhs)?;
                lhs.map(|x| {
                    transform::bool_to_int(mk().binary_expr(BinOp::from(op), x, rhs.to_expr()))
                })
                .and_then(|out| {
                    if ctx.is_unused() {
                        Ok(WithStmts::new(
                            vec![mk().semi_stmt(out)],
                            self.panic_or_err("Binary expression is not supposed to be used"),
                        ))
                    } else {
                        Ok(WithStmts::new_val(out))
                    }
                })
            }

            // No sequence-point cases
            AssignAdd | AssignSubtract | AssignMultiply | AssignDivide | AssignModulus
            | AssignBitXor | AssignShiftLeft | AssignShiftRight | AssignBitOr | AssignBitAnd
            | Assign => self.convert_assignment_operator(
                ctx,
                op,
                type_id,
                lhs,
                rhs,
                opt_lhs_type_id,
                opt_res_type_id,
            ),

            _ => {
                // Comparing references to pointers isn't consistently supported by rust
                // and so we need to decay references to pointers to do so. See
                // https://github.com/rust-lang/rust/issues/53772. This might be removable
                // once the above issue is resolved.
                if op == c_ast::BinOp::EqualEqual || op == c_ast::BinOp::NotEqual {
                    ctx = ctx.decay_ref();
                }

                let ty = self.convert_type(type_id.ctype)?;

                let lhs_type_id = self
                    .ast_context
                    .index(lhs)
                    .kind
                    .get_qual_type()
                    .ok_or_else(|| {
                        generic_loc_err!(
                            self.ast_context.display_loc(lhs_loc),
                            "bad lhs type for assignment"
                        )
                    })?;
                let rhs_kind = &self.ast_context.index(rhs).kind;
                let rhs_type_id = rhs_kind.get_qual_type().ok_or_else(|| {
                    generic_loc_err!(
                        self.ast_context.display_loc(rhs_loc),
                        "bad rhs type for assignment"
                    )
                })?;

                if ctx.is_unused() {
                    Ok(self
                        .convert_expr(ctx, lhs)?
                        .and_then(|_| self.convert_expr(ctx, rhs))?
                        .map(|_| self.panic_or_err("Binary expression is not supposed to be used")))
                } else {
                    let rhs_ctx = ctx;

                    // When we use methods on pointers (ie wrapping_offset_from or offset)
                    // we must ensure we have an explicit raw ptr for the self param, as
                    // self references do not decay
                    if op == c_ast::BinOp::Subtract || op == c_ast::BinOp::Add {
                        let ty_kind = &self.ast_context.resolve_type(lhs_type_id.ctype).kind;

                        if let CTypeKind::Pointer(_) = ty_kind {
                            ctx = ctx.decay_ref();
                        }
                    }

                    self.convert_expr(ctx, lhs)?.and_then(|lhs_val| {
                        self.convert_expr(rhs_ctx, rhs)?.result_map(|rhs_val| {
                            let expr_ids = Some((lhs, rhs));
                            self.convert_binary_operator(
                                op,
                                ty,
                                type_id.ctype,
                                lhs_type_id,
                                rhs_type_id,
                                lhs_val,
                                rhs_val,
                                expr_ids,
                            )
                        })
                    })
                }
            }
        }
    }

    fn addr_lhs(
        &self,
        lhs: Box<Expr>,
        lhs_type: CQualTypeId,
        write: bool,
    ) -> TranslationResult<Box<Expr>> {
        let mutbl = if write {
            Mutability::Mutable
        } else {
            Mutability::Immutable
        };
        let addr_lhs = match *lhs {
            Expr::Unary(ExprUnary {
                op: UnOp::Deref(_),
                expr: e,
                ..
            }) => {
                if write == lhs_type.qualifiers.is_const {
                    let lhs_type = self.convert_type(lhs_type.ctype)?;
                    let ty = mk().set_mutbl(mutbl).ptr_ty(lhs_type);

                    mk().cast_expr(e, ty)
                } else {
                    e
                }
            }
            _ => {
                // let addr_lhs = mk().set_mutbl(mutbl).addr_of_expr(lhs);
                let addr_lhs = mk().set_mutbl(mutbl).raw_addr_expr(lhs);

                let lhs_type = self.convert_type(lhs_type.ctype)?;
                let ty = mk().set_mutbl(mutbl).ptr_ty(lhs_type);

                mk().cast_expr(addr_lhs, ty)
            }
        };
        Ok(addr_lhs)
    }

    /// Convert a C expression to a rust boolean expression
    pub fn convert_condition(
        &self,
        ctx: ExprContext,
        target: bool,
        cond_id: CExprId,
    ) -> TranslationResult<WithStmts<Box<Expr>>> {
        let ty_id = self.ast_context[cond_id]
            .kind
            .get_type()
            .ok_or_else(|| generic_err!("bad condition type"))?;

        let null_pointer_case =
            |negated: bool, ptr: CExprId| -> TranslationResult<WithStmts<Box<Expr>>> {
                let val = self.convert_expr(ctx.used().decay_ref(), ptr)?;
                let ptr_type = self.ast_context[ptr]
                    .kind
                    .get_type()
                    .ok_or_else(|| generic_err!("bad pointer type for condition"))?;
                Ok(val.map(|e| {
                    if self.ast_context.is_function_pointer(ptr_type) {
                        if negated {
                            mk().method_call_expr(e, "is_some", vec![])
                        } else {
                            mk().method_call_expr(e, "is_none", vec![])
                        }
                    } else {
                        let is_null = mk().method_call_expr(e, "is_null", vec![]);
                        if negated {
                            mk().unary_expr(UnOp::Not(Default::default()), is_null)
                        } else {
                            is_null
                        }
                    }
                }))
            };

        match self.ast_context[cond_id].kind {
            CExprKind::Binary(_, c_ast::BinOp::EqualEqual, null_expr, ptr, _, _)
                if self.ast_context.is_null_expr(null_expr) =>
            {
                null_pointer_case(!target, ptr)
            }

            CExprKind::Binary(_, c_ast::BinOp::EqualEqual, ptr, null_expr, _, _)
                if self.ast_context.is_null_expr(null_expr) =>
            {
                null_pointer_case(!target, ptr)
            }

            CExprKind::Binary(_, c_ast::BinOp::NotEqual, null_expr, ptr, _, _)
                if self.ast_context.is_null_expr(null_expr) =>
            {
                null_pointer_case(target, ptr)
            }

            CExprKind::Binary(_, c_ast::BinOp::NotEqual, ptr, null_expr, _, _)
                if self.ast_context.is_null_expr(null_expr) =>
            {
                null_pointer_case(target, ptr)
            }

            CExprKind::Unary(_, c_ast::UnOp::Not, subexpr_id, _) => {
                self.convert_condition(ctx, !target, subexpr_id)
            }

            _ => {
                // DecayRef could (and probably should) be Default instead of Yes here; however, as noted
                // in https://github.com/rust-lang/rust/issues/53772, you cant compare a reference (lhs) to
                // a ptr (rhs) (even though the reverse works!). We could also be smarter here and just
                // specify Yes for that particular case, given enough analysis.
                let val = self.convert_expr(ctx.used().decay_ref(), cond_id)?;
                Ok(val.map(|e| self.match_bool(target, ty_id, e)))
            }
        }
    }

    /// Write to a `lhs` that is volatile
    pub fn volatile_write(
        &self,
        lhs: Box<Expr>,
        lhs_type: CQualTypeId,
        rhs: Box<Expr>,
    ) -> TranslationResult<Box<Expr>> {
        let addr_lhs = self.addr_lhs(lhs, lhs_type, true)?;

        Ok(mk().call_expr(
            mk().abs_path_expr(vec!["core", "ptr", "write_volatile"]),
            vec![addr_lhs, rhs],
        ))
    }

    /// Read from a `lhs` that is volatile
    pub fn volatile_read(
        &self,
        lhs: Box<Expr>,
        lhs_type: CQualTypeId,
    ) -> TranslationResult<Box<Expr>> {
        let addr_lhs = self.addr_lhs(lhs, lhs_type, false)?;

        // We explicitly annotate the type of pointer we're reading from
        // in order to avoid omitted bit-casts to const from causing the
        // wrong type to be inferred via the result of the pointer.
        let mut path_parts: Vec<PathSegment> = vec![];
        for elt in ["core", "ptr"] {
            path_parts.push(mk().path_segment(elt))
        }
        let elt_ty = self.convert_type(lhs_type.ctype)?;
        let ty_params = mk().angle_bracketed_args(vec![elt_ty]);
        let elt = mk().path_segment_with_args("read_volatile", ty_params);
        path_parts.push(elt);

        let read_volatile_expr = mk().abs_path_expr(path_parts);
        Ok(mk().call_expr(read_volatile_expr, vec![addr_lhs]))
    }

    // Compute the offset multiplier for variable length array indexing
    // Rust type: usize
    pub fn compute_size_of_expr(&self, type_id: CTypeId) -> Option<Box<Expr>> {
        match self.ast_context.resolve_type(type_id).kind {
            CTypeKind::VariableArray(elts, Some(counts)) => {
                let opt_esize = self.compute_size_of_expr(elts);
                let csize_name = self
                    .renamer
                    .borrow()
                    .get(&CDeclId(counts.0))
                    .expect("Failed to lookup VLA expression");
                let csize = mk().path_expr(vec![csize_name]);

                let val = match opt_esize {
                    None => csize,
                    Some(esize) => mk().binary_expr(BinOp::Mul(Default::default()), csize, esize),
                };
                Some(val)
            }
            _ => None,
        }
    }
}
