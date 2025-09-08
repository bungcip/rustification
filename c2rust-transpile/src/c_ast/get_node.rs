use crate::c_ast::*;

pub trait GetNode {
    type Node;
    fn get_node<'a>(&self, context: &'a TypedAstContext) -> &'a Self::Node;
}

impl GetNode for CExprId {
    type Node = Located<CExprKind>;
    fn get_node<'a>(&self, context: &'a TypedAstContext) -> &'a Self::Node {
        context
            .c_exprs
            .get(self)
            .unwrap_or_else(|| panic!("Could not find expression with ID {:?}", self))
    }
}

impl GetNode for CStmtId {
    type Node = Located<CStmtKind>;
    fn get_node<'a>(&self, context: &'a TypedAstContext) -> &'a Self::Node {
        context
            .c_stmts
            .get(self)
            .unwrap_or_else(|| panic!("Could not find statement with ID {:?}", self))
    }
}

impl GetNode for CDeclId {
    type Node = Located<CDeclKind>;
    fn get_node<'a>(&self, context: &'a TypedAstContext) -> &'a Self::Node {
        context
            .c_decls
            .get(self)
            .unwrap_or_else(|| panic!("Could not find declaration with ID {:?}", self))
    }
}

impl GetNode for CTypeId {
    type Node = Located<CTypeKind>;
    fn get_node<'a>(&self, context: &'a TypedAstContext) -> &'a Self::Node {
        context
            .c_types
            .get(self)
            .unwrap_or_else(|| panic!("Could not find type with ID {:?}", self))
    }
}
