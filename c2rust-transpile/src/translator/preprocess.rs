use crate::driver::Translation;
use crate::translator::utils::prefix_names;
use crate::c_ast::*;
use indexmap::IndexMap;

pub fn preprocess_ast(t: &mut Translation) {
    // Sort the top-level declarations by file and source location so that we
    // preserve the ordering of all declarations in each file.
    t.ast_context.sort_top_decls();

    t.locate_comments();

    // Headers often pull in declarations that are unused;
    // we simplify the translator output by omitting those.
    t.ast_context
        .prune_unwanted_decls(t.tcfg.preserve_unused_functions);

    // Normalize AST types between Clang < 16 and later versions. Ensures that
    // binary and unary operators' expr types agree with their argument types
    // in the presence of typedefs.
    t.ast_context.bubble_expr_types();

    enum Name<'a> {
        Var(&'a str),
        Type(&'a str),
        Anonymous,
        None,
    }

    fn some_type_name(s: Option<&str>) -> Name<'_> {
        match s {
            None => Name::Anonymous,
            Some(r) => Name::Type(r),
        }
    }

    // Used for testing; so that we don't overlap with C function names
    if let Some(ref prefix) = t.tcfg.prefix_function_names {
        prefix_names(t, prefix);
    }

    // Identify typedefs that name unnamed types and collapse the two declarations
    // into a single name and declaration, eliminating the typedef altogether.
    let mut prenamed_decls: IndexMap<CDeclId, CDeclId> = IndexMap::new();
    for (&decl_id, decl) in t.ast_context.iter_decls() {
        if let CDeclKind::Typedef { ref name, typ, .. } = decl.kind
            && let Some(subdecl_id) = t
                .ast_context
                .resolve_type(typ.ctype)
                .kind
                .as_underlying_decl()
        {
            use CDeclKind::*;
            let is_unnamed = match t.ast_context[subdecl_id].kind {
                Struct { name: None, .. } | Union { name: None, .. } | Enum { name: None, .. } => {
                    true
                }

                // Detect case where typedef and struct share the same name.
                // In this case the purpose of the typedef was simply to eliminate
                // the need for the 'struct' tag when referring to the type name.
                Struct {
                    name: Some(ref target_name),
                    ..
                }
                | Union {
                    name: Some(ref target_name),
                    ..
                }
                | Enum {
                    name: Some(ref target_name),
                    ..
                } => name == target_name,

                _ => false,
            };

            if is_unnamed
                && !prenamed_decls
                    .values()
                    .any(|decl_id| *decl_id == subdecl_id)
            {
                prenamed_decls.insert(decl_id, subdecl_id);

                t.type_converter
                    .borrow_mut()
                    .declare_decl_name(decl_id, name);
                t.type_converter
                    .borrow_mut()
                    .alias_decl_name(subdecl_id, decl_id);
            }
        }
    }

    t.ast_context.prenamed_decls = prenamed_decls;

    // Helper function that returns true if there is either a matching typedef or its
    // corresponding struct/union/enum
    fn contains(prenamed_decls: &IndexMap<CDeclId, CDeclId>, decl_id: &CDeclId) -> bool {
        prenamed_decls.contains_key(decl_id) || prenamed_decls.values().any(|id| *id == *decl_id)
    }

    // Populate renamer with top-level names
    for (&decl_id, decl) in t.ast_context.iter_decls() {
        use CDeclKind::*;
        let decl_name = match decl.kind {
            _ if contains(&t.ast_context.prenamed_decls, &decl_id) => Name::None,
            Struct { ref name, .. } => some_type_name(name.as_ref().map(String::as_str)),
            Enum { ref name, .. } => some_type_name(name.as_ref().map(String::as_str)),
            Union { ref name, .. } => some_type_name(name.as_ref().map(String::as_str)),
            Typedef { ref name, .. } => Name::Type(name),
            Function { ref name, .. } => Name::Var(name),
            EnumConstant { ref name, .. } => Name::Var(name),
            Variable { ref ident, .. } if t.ast_context.c_decls_top.contains(&decl_id) => {
                Name::Var(ident)
            }
            MacroObject { ref name, .. } => Name::Var(name),
            _ => Name::None,
        };
        match decl_name {
            Name::None => (),
            Name::Anonymous => {
                t.type_converter
                    .borrow_mut()
                    .declare_decl_name(decl_id, "C2RustUnnamed");
            }
            Name::Type(name) => {
                t.type_converter
                    .borrow_mut()
                    .declare_decl_name(decl_id, name);
            }
            Name::Var(name) => {
                t.renamer.borrow_mut().insert(decl_id, name);
            }
        }
    }
}
