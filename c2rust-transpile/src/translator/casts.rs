use crate::translator::TranslationError;
use crate::with_stmts::WithStmts;
use c2rust_ast_builder::mk;
use std::ffi::CString;
use std::ops::Index;

use log::warn;
use syn::*; // To override c_ast::{BinOp,UnOp} from glob import

use crate::diagnostics::TranslationResult;
use crate::{
    c_ast::{CDeclKind, CTypeKind},
    generic_err,
};
use c2rust_ast_builder::properties::*;

use crate::ExternCrate;
use crate::c_ast;
use crate::c_ast::*;

use super::{ExprContext, Translation, transmute_expr};
use crate::transform;

impl<'c> Translation<'c> {
    pub(crate) fn convert_cast(
        &self,
        ctx: ExprContext,
        source_ty: CQualTypeId,
        ty: CQualTypeId,
        val: WithStmts<Box<Expr>>,
        expr: Option<CExprId>,
        kind: Option<CastKind>,
        opt_field_id: Option<CFieldId>,
    ) -> TranslationResult<WithStmts<Box<Expr>>> {
        let source_ty_kind = &self.ast_context.resolve_type(source_ty.ctype).kind;
        let target_ty_kind = &self.ast_context.resolve_type(ty.ctype).kind;

        if source_ty_kind == target_ty_kind {
            return Ok(val);
        }

        let kind = kind.unwrap_or_else(|| {
            match (source_ty_kind, target_ty_kind) {
                (CTypeKind::VariableArray(..), CTypeKind::Pointer(..))
                | (CTypeKind::ConstantArray(..), CTypeKind::Pointer(..))
                | (CTypeKind::IncompleteArray(..), CTypeKind::Pointer(..)) => {
                    CastKind::ArrayToPointerDecay
                }

                (CTypeKind::Function(..), CTypeKind::Pointer(..)) => {
                    CastKind::FunctionToPointerDecay
                }

                (_, CTypeKind::Pointer(..)) if source_ty_kind.is_integral_type() => {
                    CastKind::IntegralToPointer
                }

                (CTypeKind::Pointer(..), CTypeKind::Bool) => CastKind::PointerToBoolean,

                (CTypeKind::Pointer(..), _) if target_ty_kind.is_integral_type() => {
                    CastKind::PointerToIntegral
                }

                (_, CTypeKind::Bool) if source_ty_kind.is_integral_type() => {
                    CastKind::IntegralToBoolean
                }

                (CTypeKind::Bool, _) if target_ty_kind.is_signed_integral_type() => {
                    CastKind::BooleanToSignedIntegral
                }

                (_, _)
                    if source_ty_kind.is_integral_type() && target_ty_kind.is_integral_type() =>
                {
                    CastKind::IntegralCast
                }

                (_, _)
                    if source_ty_kind.is_integral_type() && target_ty_kind.is_floating_type() =>
                {
                    CastKind::IntegralToFloating
                }

                (_, CTypeKind::Bool) if source_ty_kind.is_floating_type() => {
                    CastKind::FloatingToBoolean
                }

                (_, _)
                    if source_ty_kind.is_floating_type() && target_ty_kind.is_integral_type() =>
                {
                    CastKind::FloatingToIntegral
                }

                (_, _)
                    if source_ty_kind.is_floating_type() && target_ty_kind.is_floating_type() =>
                {
                    CastKind::FloatingCast
                }

                (CTypeKind::Pointer(..), CTypeKind::Pointer(..)) => CastKind::BitCast,

                // Ignoring Complex casts for now
                _ => {
                    warn!(
                        "Unknown CastKind for {source_ty_kind:?} to {target_ty_kind:?} cast. Defaulting to BitCast",
                    );

                    CastKind::BitCast
                }
            }
        });

        match kind {
            CastKind::BitCast | CastKind::NoOp => {
                val.and_then(|x| {
                    if self.ast_context.is_function_pointer(ty.ctype)
                        || self.ast_context.is_function_pointer(source_ty.ctype)
                    {
                        let source_ty = self.convert_type(source_ty.ctype)?;
                        let target_ty = self.convert_type(ty.ctype)?;
                        Ok(WithStmts::new_unsafe_val(transmute_expr(
                            source_ty, target_ty, x,
                        )))
                    } else if ctx.is_inside_init_list_aop() {
                        // for array-of pointer and static we wrap it inside PointerMut
                        let target_ty = self.convert_type(ty.ctype)?;
                        let x = transform::access_to_wrapped_pointer(x);
                        let cast_expr = mk().cast_expr(x, target_ty);
                        let wrapper = match ty.qualifiers.is_const {
                            true => "Pointer",
                            false => "PointerMut",
                        };
                        let call = mk().call_expr(mk().ident_expr(wrapper), vec![cast_expr]);

                        Ok(WithStmts::new_val(call))
                    } else {
                        // Normal case
                        let target_ty = self.convert_type(ty.ctype)?;
                        Ok(WithStmts::new_val(mk().cast_expr(x, target_ty)))
                    }
                })
            }

            CastKind::IntegralToPointer if self.ast_context.is_function_pointer(ty.ctype) => {
                let target_ty = self.convert_type(ty.ctype)?;
                val.and_then(|x| {
                    // core::ffi don't have a intptr_t type, so we use isize
                    let intptr_t = mk().path_ty(vec!["isize"]);
                    let intptr = mk().cast_expr(x, intptr_t.clone());
                    Ok(WithStmts::new_unsafe_val(transmute_expr(
                        intptr_t, target_ty, intptr,
                    )))
                })
            }

            CastKind::IntegralToPointer
            | CastKind::PointerToIntegral
            | CastKind::IntegralCast
            | CastKind::FloatingCast
            | CastKind::FloatingToIntegral
            | CastKind::IntegralToFloating => {
                let target_ty = self.convert_type(ty.ctype)?;
                let target_ty_ctype = &self.ast_context.resolve_type(ty.ctype).kind;

                let source_ty_ctype_id = source_ty.ctype;

                let source_ty = self.convert_type(source_ty_ctype_id)?;
                if let CTypeKind::LongDouble = target_ty_ctype {
                    if ctx.is_const {
                        return Err(generic_err!(
                            "f128 cannot be used in constants because `f128::f128::new` is not `const`"
                        ));
                    }

                    self.use_crate(ExternCrate::F128);

                    let fn_path = mk().path_expr(vec!["f128", "f128", "new"]);
                    Ok(val.map(|val| mk().call_expr(fn_path, vec![val])))
                } else if let CTypeKind::LongDouble = self.ast_context[source_ty_ctype_id].kind {
                    self.f128_cast_to(val, target_ty_ctype)
                } else if let &CTypeKind::Enum(enum_decl_id) = target_ty_ctype {
                    // Casts targeting `enum` types...
                    let expr =
                        expr.ok_or_else(|| generic_err!("Casts to enums require a C ExprId"))?;
                    Ok(self.enum_cast(ty.ctype, enum_decl_id, expr, val, source_ty, target_ty))
                } else if target_ty_ctype.is_floating_type() && source_ty_kind.is_bool() {
                    val.and_then(|x| {
                        Ok(WithStmts::new_val(mk().cast_expr(
                            mk().cast_expr(x, mk().path_ty(vec!["u8"])),
                            target_ty,
                        )))
                    })
                } else if target_ty_ctype.is_pointer() && source_ty_kind.is_bool() {
                    val.and_then(|x| {
                        // core:ffi don't have size_t so we cast it to usize
                        Ok(WithStmts::new_val(mk().cast_expr(
                            mk().cast_expr(x, mk().path_ty(vec!["usize"])),
                            target_ty,
                        )))
                    })
                } else {
                    // Other numeric casts translate to Rust `as` casts,
                    // unless the cast is to a function pointer then use `transmute`.
                    val.and_then(|x| {
                        if self.ast_context.is_function_pointer(source_ty_ctype_id) {
                            Ok(WithStmts::new_unsafe_val(transmute_expr(
                                source_ty, target_ty, x,
                            )))
                        } else {
                            Ok(WithStmts::new_val(mk().cast_expr(x, target_ty)))
                        }
                    })
                }
            }

            CastKind::LValueToRValue | CastKind::ToVoid | CastKind::ConstCast => Ok(val),

            CastKind::FunctionToPointerDecay | CastKind::BuiltinFnToFnPtr => {
                Ok(val.map(|x| mk().call_expr(mk().ident_expr("Some"), vec![x])))
            }

            CastKind::ArrayToPointerDecay => {
                // Because va_list is sometimes defined as a single-element
                // array in order for it to allocate memory as a local variable
                // and to be a pointer as a function argument we would get
                // spurious casts when trying to treat it like a VaList which
                // has reference semantics.
                if self.ast_context.is_va_list(ty.ctype) {
                    return Ok(val);
                }

                let pointee = match self.ast_context.resolve_type(ty.ctype).kind {
                    CTypeKind::Pointer(pointee) => pointee,
                    _ => panic!("Dereferencing a non-pointer"),
                };

                let is_const = pointee.qualifiers.is_const;

                let expr_kind = expr.map(|e| &self.ast_context.index(e).kind);
                match expr_kind {
                    Some(&CExprKind::Literal(_, CLiteral::String(ref bytes, _))) if is_const => {
                        // discard val and use the string literal as CStr literal
                        // ex: c"hello".as_ptr()
                        let bytes = bytes.to_owned();
                        let cstr = match CString::new(bytes) {
                            Ok(cstr) => cstr,
                            Err(e) => {
                                // we have interio NUL here, so we need to use byte literal
                                // then cast it to pointer
                                // ex: b"hello\0world\0".as_ptr()

                                let mut bytes = e.into_vec();
                                bytes.push(0);

                                let source_ty = mk().ptr_ty(mk().path_ty("u8"));
                                let target_ty = mk().ptr_ty(mk().path_ty(vec!["ffi", "c_char"]));

                                let byte_literal = mk().lit_expr(bytes);
                                let call = mk().method_call_expr(byte_literal, "as_ptr", vec![]);
                                let pointer = transmute_expr(source_ty, target_ty, call);

                                return Ok(WithStmts::new_val(pointer));
                            }
                        };

                        let cstr_literal = mk().lit_expr(cstr);
                        let expr = mk().method_call_expr(cstr_literal, "as_ptr", vec![]);

                        if ctx.is_inside_init_list_aop() && ctx.is_static {
                            let call = mk().call_expr(mk().ident_expr("Pointer"), vec![expr]);
                            return Ok(WithStmts::new_val(call));
                        }

                        Ok(WithStmts::new_val(expr))
                    }
                    _ => {
                        // Variable length arrays are already represented as pointers.
                        if let CTypeKind::VariableArray(..) =
                            self.ast_context.resolve_type(source_ty.ctype).kind
                        {
                            Ok(val)
                        } else {
                            let method = if is_const || ctx.is_static {
                                Mutability::Immutable
                            } else {
                                Mutability::Mutable
                            };

                            let call = val.map(|x| mk().set_mutbl(method).raw_addr_expr(x));
                            let target_ty = self.convert_type(pointee.ctype)?;
                            let call = call.map(|x| {
                                mk().method_call_expr(
                                    x,
                                    mk().path_segment_with_args(
                                        "cast",
                                        mk().angle_bracketed_args(vec![target_ty]),
                                    ),
                                    vec![],
                                )
                            });

                            // Static arrays can now use as_ptr. Can also cast that const ptr to a
                            // mutable pointer as we do here:
                            if ctx.is_static && !is_const {
                                return Ok(call.map(|val| {
                                    let inferred_type = mk().infer_ty();
                                    let ptr_type = mk().mutbl().ptr_ty(inferred_type);
                                    mk().cast_expr(val, ptr_type)
                                }));
                            }

                            Ok(call)
                        }
                    }
                }
            }

            CastKind::NullToPointer => {
                assert!(val.stmts().is_empty());
                Ok(WithStmts::new_val(self.null_ptr(
                    ty.ctype,
                    ctx.is_static,
                    ctx.inside_init_list_aop,
                )?))
            }

            CastKind::ToUnion => {
                let field_id = opt_field_id.expect("Missing field ID in union cast");
                let union_id = self.ast_context.parents[&field_id];

                let union_name = self
                    .type_converter
                    .borrow()
                    .resolve_decl_name(union_id)
                    .expect("required union name");
                let field_name = self
                    .type_converter
                    .borrow()
                    .resolve_field_name(Some(union_id), field_id)
                    .expect("field name required");

                Ok(val.map(|x| {
                    mk().struct_expr(mk().path(vec![union_name]), vec![mk().field(field_name, x)])
                }))
            }

            CastKind::IntegralToBoolean
            | CastKind::FloatingToBoolean
            | CastKind::PointerToBoolean => {
                if let Some(expr) = expr {
                    self.convert_condition(ctx, true, expr)
                } else {
                    Ok(val.map(|e| self.match_bool(true, source_ty.ctype, e)))
                }
            }

            // I don't know how to actually cause clang to generate this
            CastKind::BooleanToSignedIntegral => Err(generic_err!(
                "TODO boolean to signed integral not supported",
            )),

            CastKind::FloatingRealToComplex
            | CastKind::FloatingComplexToIntegralComplex
            | CastKind::FloatingComplexCast
            | CastKind::FloatingComplexToReal
            | CastKind::IntegralComplexToReal
            | CastKind::IntegralRealToComplex
            | CastKind::IntegralComplexCast
            | CastKind::IntegralComplexToFloatingComplex
            | CastKind::IntegralComplexToBoolean => Err(generic_err!(
                "TODO casts with complex numbers not supported",
            )),

            CastKind::VectorSplat => Err(generic_err!("TODO vector splat casts not supported",)),
            CastKind::AtomicToNonAtomic | CastKind::NonAtomicToAtomic => Ok(val),
        }
    }

    /// Cast a f128 to some other int or float type
    pub(crate) fn f128_cast_to(
        &self,
        val: WithStmts<Box<Expr>>,
        target_ty_ctype: &CTypeKind,
    ) -> TranslationResult<WithStmts<Box<Expr>>> {
        self.use_crate(ExternCrate::NumTraits);

        self.with_cur_file_item_store(|item_store| {
            item_store.add_use(vec!["num_traits".into()], "ToPrimitive");
        });
        let to_method_name = match target_ty_ctype {
            CTypeKind::Float => "to_f32",
            CTypeKind::Double => "to_f64",
            CTypeKind::Char => "to_i8",
            CTypeKind::UChar => "to_u8",
            CTypeKind::Short => "to_i16",
            CTypeKind::UShort => "to_u16",
            CTypeKind::Int => "to_i32",
            CTypeKind::UInt => "to_u32",
            CTypeKind::Long => "to_i64",
            CTypeKind::ULong => "to_u64",
            CTypeKind::LongLong => "to_i64",
            CTypeKind::ULongLong => "to_u64",
            CTypeKind::Int128 => "to_i128",
            CTypeKind::UInt128 => "to_u128",
            _ => {
                return Err(generic_err!(
                    "Tried casting long double to unsupported type: {:?}",
                    target_ty_ctype
                ));
            }
        };

        Ok(val.map(|val| {
            let to_call = mk().method_call_expr(val, to_method_name, Vec::new());

            mk().method_call_expr(to_call, "unwrap", Vec::new())
        }))
    }

    /// This handles translating casts when the target type in an `enum` type.
    ///
    /// When translating variable references to `EnumConstant`'s, we always insert casts to the
    /// expected type. In C, `EnumConstants` have some integral type, _not_ the enum type. However,
    /// if we then immediately have a cast to convert this variable back into an enum type, we would
    /// like to produce Rust with _no_ casts. This function handles this simplification.
    fn enum_cast(
        &self,
        enum_type: CTypeId,
        enum_decl: CEnumId, // ID of the enum declaration corresponding to the target type
        expr: CExprId,      // ID of initial C argument to cast
        val: WithStmts<Box<Expr>>, // translated Rust argument to cast
        _source_ty: Box<Type>, // source type of cast
        target_ty: Box<Type>, // target type of cast
    ) -> WithStmts<Box<Expr>> {
        // Extract the IDs of the `EnumConstant` decls underlying the enum.
        let variants = match self.ast_context.index(enum_decl).kind {
            CDeclKind::Enum { ref variants, .. } => variants,
            _ => panic!("{enum_decl:?} does not point to an `enum` declaration"),
        };

        match self.ast_context.index(expr).kind {
            // This is the case of finding a variable which is an `EnumConstant` of the same enum
            // we are casting to. Here, we can just remove the extraneous cast instead of generating
            // a new one.
            CExprKind::DeclRef(_, decl_id, _) if variants.contains(&decl_id) => {
                return val.map(|x| match *transform::unparen(&x) {
                    Expr::Cast(ExprCast { ref expr, .. }) => expr.clone(),
                    _ => panic!("DeclRef {expr:?} of enum {enum_decl:?} is not cast"),
                });
            }

            CExprKind::Literal(_, CLiteral::Integer(i, _)) => {
                return val.map(|_| self.enum_for_i64(enum_type, i as i64));
            }

            CExprKind::Unary(_, c_ast::UnOp::Negate, subexpr_id, _) => {
                if let &CExprKind::Literal(_, CLiteral::Integer(i, _)) =
                    &self.ast_context[subexpr_id].kind
                {
                    return val.map(|_| self.enum_for_i64(enum_type, -(i as i64)));
                }
            }

            // In all other cases, a cast to an enum requires a `transmute` - Rust enums cannot be
            // converted into integral types as easily as C ones.
            _ => {}
        }

        val.map(|x| mk().cast_expr(x, target_ty))
    }
}
