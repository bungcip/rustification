use std::cell::RefCell;
use std::path::{self, PathBuf};

use c2rust_ast_builder::mk;
use indexmap::IndexMap;
use syn::{BinOp, Block, Expr, ExprBlock, Stmt, Type};

use crate::c_ast::CDeclKind;
use crate::c_ast::SrcLoc;
use crate::driver::Translation;
use crate::transform;
use proc_macro2::TokenStream;
use syn::{
    AttrStyle, ForeignItem, ForeignItemFn, ForeignItemMacro, ForeignItemStatic, ForeignItemType,
    Item, ItemConst, ItemEnum, ItemExternCrate, ItemFn, ItemForeignMod, ItemImpl, ItemMacro,
    ItemMod, ItemStatic, ItemStruct, ItemTrait, ItemTraitAlias, ItemType, ItemUnion, ItemUse,
};

/// Pointer offset that casts its argument to isize.
///
/// This function generates a call to the `offset` method on a pointer,
/// which is equivalent to pointer arithmetic in C.
///
/// `ptr` is the base pointer.
/// `offset` is the number of elements to offset the pointer by.
/// `multiply_by` is an optional expression to multiply the offset by,
/// which is used for array indexing.
/// `neg` indicates whether the offset should be negative.
/// `deref` indicates whether the resulting pointer should be dereferenced.
pub fn pointer_offset(
    ptr: Box<Expr>,
    offset: Box<Expr>,
    multiply_by: Option<Box<Expr>>,
    neg: bool,
    mut deref: bool,
) -> Box<Expr> {
    let mut offset = transform::cast_int(offset, "isize");

    if let Some(mul) = multiply_by {
        let mul = transform::cast_int(mul, "isize");
        offset = mk().binary_expr(BinOp::Mul(Default::default()), offset, mul);
        deref = false;
    }

    if neg {
        offset = mk().neg_expr(offset);
    }

    let res = mk().method_call_expr(ptr, "offset", vec![offset]);
    if deref { mk().deref_expr(res) } else { res }
}

/// Given an expression with type `Option<fn(...)->...>`, unwrap the `Option`
/// and return the function pointer. This is used when a C function pointer
/// is translated to an `Option` in Rust, and we need to call it.
/// The `expect` method will panic if the `Option` is `None`.
pub fn unwrap_function_pointer(ptr: Box<Expr>) -> Box<Expr> {
    let err_msg = mk().lit_expr("non-null function pointer");
    mk().method_call_expr(ptr, "expect", vec![err_msg])
}

/// Generate a `core::mem::transmute` expression.
///
/// `source_ty` and `target_ty` are the source and target types of the transmute.
/// `expr` is the expression to be transmuted.
///
/// If the source and target types are both `Type::Infer`, then no type
/// arguments are generated for the `transmute` call, and the compiler is
/// expected to infer them.
pub fn transmute_expr(source_ty: Box<Type>, target_ty: Box<Type>, expr: Box<Expr>) -> Box<Expr> {
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

pub fn vec_expr(val: Box<Expr>, count: Box<Expr>) -> Box<Expr> {
    let from_elem = mk().abs_path_expr(vec!["std", "vec", "from_elem"]);
    mk().call_expr(from_elem, vec![val, count])
}

/// Create a `Block` from a `Vec<Stmt>`.
///
/// This function is a convenience wrapper around `mk().block(stmts)`. It
/// has a special case to handle a common pattern where the last statement is
/// an expression that is itself a block. In this case, it will unwrap the
/// block to avoid unnecessary nesting.
/// Add a src_loc = "line:col" attribute to an item/foreign_item
pub(crate) fn add_src_loc_attr(attrs: &mut Vec<syn::Attribute>, src_loc: &Option<SrcLoc>) {
    if let Some(src_loc) = src_loc.as_ref() {
        let loc_str = format!("{}:{}", src_loc.line, src_loc.column);
        let meta = mk().meta_namevalue(vec!["c2rust", "src_loc"], loc_str);
        // let prepared = mk().prepare_meta(meta);
        let attr = mk().attribute(AttrStyle::Outer, meta);
        attrs.push(attr);
    }
}

/// Get a mutable reference to the attributes of a ForeignItem
pub(crate) fn foreign_item_attrs(item: &mut ForeignItem) -> Option<&mut Vec<syn::Attribute>> {
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
pub(crate) fn item_attrs(item: &mut Item) -> Option<&mut Vec<syn::Attribute>> {
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

// This should only be used for tests
pub fn prefix_names(translation: &mut Translation, prefix: &str) {
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

/// This function is meant to create module names for modules being created
/// with the `--reorganize-modules` flag.
///
/// It sanitizes the path name by replacing `.` and `-` with `_`.
///
/// To avoid name collisions, it checks a map of module names to paths. If a
/// collision is detected (i.e., the same module name is used for different
/// paths), it prepends the parent directory name to the module name to
/// disambiguate.
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
