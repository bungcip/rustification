/// Transform contains helpers functions
/// for transforming/refactoring Rust AST to Another Rust AST
///
use c2rust_ast_builder::mk;
use syn::{Expr, ExprCall, ExprParen, Lit};

/// TODO: refactor parameter need_lit_suffix = true, only used by one function
pub(crate) fn cast_int(val: Box<Expr>, name: &str, need_lit_suffix: bool) -> Box<Expr> {
    let opt_literal_val = match &*val {
        Expr::Lit(l) => match &l.lit {
            Lit::Int(i) => Some(i.base10_digits().parse::<u128>().unwrap()),
            _ => None,
        },
        _ => None,
    };
    match opt_literal_val {
        Some(i) if need_lit_suffix == false => mk().lit_expr(mk().int_lit(i)),
        Some(i) => mk().lit_expr(mk().int_lit_with_suffix(i, name)),
        None => mk().cast_expr(val, mk().path_ty(vec![name])),
    }
}

/// Convert a boolean expression to a c_int
pub(crate) fn bool_to_int(val: Box<Expr>) -> Box<Expr> {
    mk().cast_expr(val, mk().path_ty(vec!["ffi", "c_int"]))
}

/// helper that transform an expression that access a wrapped pointer to ".0"
/// eg: let x = PointerMut(c" ".as_ptr()); x.0
pub(crate) fn access_to_wrapped_pointer(expr: Box<Expr>) -> Box<Expr> {
    let expr2 = expr.clone(); // TODO: don't clone this, use a reference instead
    if let Expr::Call(ExprCall { func, args, .. }) = *expr {
        if args.len() != 1 {
            return expr2;
        }

        if let Expr::Path(p) = *func {
            let ident = p.path.segments[0].ident.to_string();
            if ident == "PointerMut" || ident == "Pointer" {
                // If the function is PointerMut or PointerConst, we access the wrapped pointer
                // by using ".0" to get the inner value.
                return mk().anon_field_expr(expr2, 0);
            }
        }
    };
    expr2
}

/// Unwrap a layer of parenthesization from an Expr, if present
pub(crate) fn unparen(expr: &Expr) -> &Expr {
    match *expr {
        Expr::Paren(ExprParen { ref expr, .. }) => expr,
        _ => expr,
    }
}
