/// Transform contains helpers functions
/// for transforming/refactoring Rust AST to Another Rust AST
///
use c2rust_ast_builder::mk;
use syn::{Expr, ExprCall, ExprParen, ExprPath, ExprUnary, Lit};

/// extract_int_value extracts the integer value from an expression if it's a literal,
fn extract_int_value(val: &Expr) -> Option<u64> {
    match val {
        Expr::Lit(l) => match &l.lit {
            Lit::Int(i) => Some(i.base10_digits().parse::<u64>().unwrap()),
            _ => None,
        },
        _ => None,
    }
}

pub(crate) fn cast_int(val: Box<Expr>, name: &str) -> Box<Expr> {
    let value = extract_int_value(&val);
    match value {
        Some(i) => mk().lit_expr(mk().int_lit(i)),
        None => mk().cast_expr(val, mk().path_ty(vec![name])),
    }
}

pub(crate) fn cast_int_with_suffix(val: Box<Expr>, name: &str) -> Box<Expr> {
    let value = extract_int_value(&val);
    match value {
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
    if let Expr::Call(ExprCall {
        ref func, ref args, ..
    }) = *expr
        && args.len() == 1
        && let Expr::Path(ExprPath { ref path, .. }) = **func
        && let ident = path.segments[0].ident.to_string()
        && (ident == "PointerMut" || ident == "Pointer")
    {
        // If the function is PointerMut or PointerConst, we access the wrapped pointer
        // by using ".0" to get the inner value.
        return mk().anon_field_expr(expr, 0);
    };
    expr
}

/// Unwrap a layer of parenthesization from an Expr, if present
pub(crate) fn unparen(expr: &Expr) -> &Expr {
    match *expr {
        Expr::Paren(ExprParen { ref expr, .. }) => expr,
        _ => expr,
    }
}

/// Take the logical negation of an expression.
///
///   * Negating something of the form `!<expr>` produces `<expr>`
///
pub(crate) fn not(bool_expr: &Expr) -> Box<Expr> {
    match *bool_expr {
        Expr::Unary(ExprUnary {
            op: syn::UnOp::Not(_),
            ref expr,
            ..
        }) => Box::new(unparen(expr).clone()),
        _ => mk().not_expr(Box::new(bool_expr.clone())),
    }
}
