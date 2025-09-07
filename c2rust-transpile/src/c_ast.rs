use c2rust_ast_exporter::clang_ast::LRValue;
use indexmap::{IndexMap, IndexSet};
use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::fmt::{self, Debug, Display};
use std::mem;
use std::ops::Index;
use std::path::{Path, PathBuf};
use std::rc::Rc;

pub use c2rust_ast_exporter::clang_ast::{BuiltinVaListKind, SrcFile, SrcLoc, SrcSpan};

/// A C type ID.
#[derive(Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Copy, Clone)]
pub struct CTypeId(pub u64);

/// A C expression ID.
#[derive(Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Copy, Clone)]
pub struct CExprId(pub u64);

/// A C declaration ID.
#[derive(Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Copy, Clone)]
pub struct CDeclId(pub u64);

/// A C statement ID.
#[derive(Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Copy, Clone)]
pub struct CStmtId(pub u64);

// These are references into particular variants of AST nodes
pub type CLabelId = CStmtId; // Labels point into the 'StmtKind::Label' that declared the label
pub type CFieldId = CDeclId; // Records always contain 'DeclKind::Field's
pub type CParamId = CDeclId; // Parameters always contain 'DeclKind::Variable's
pub type CFuncTypeId = CTypeId; // Function declarations always have types which are 'TypeKind::Function'
pub type CRecordId = CDeclId; // Record types need to point to 'DeclKind::Record'
pub type CTypedefId = CDeclId; // Typedef types need to point to 'DeclKind::Typedef'
pub type CEnumId = CDeclId; // Enum types need to point to 'DeclKind::Enum'
pub type CEnumConstantId = CDeclId; // Enum's need to point to child 'DeclKind::EnumConstant's

pub use self::conversion::*;
pub use self::print::Printer;

mod conversion;
pub mod iterators;
mod print;

use iterators::{DFNodes, SomeId};

/// AST context containing all of the nodes in the Clang AST.
#[derive(Debug, Clone)]
pub struct TypedAstContext {
    /// The C types in the AST.
    c_types: HashMap<CTypeId, CType>,
    /// The C expressions in the AST.
    c_exprs: HashMap<CExprId, CExpr>,
    /// The C statements in the AST.
    c_stmts: HashMap<CStmtId, CStmt>,

    /// The C declarations in the AST.
    ///
    /// Decls require a stable iteration order as this map will be
    /// iterated over export all defined types during translation.
    c_decls: IndexMap<CDeclId, CDecl>,

    /// The top-level C declarations in the AST.
    pub c_decls_top: Vec<CDeclId>,
    /// The `main` function, if any.
    pub c_main: Option<CDeclId>,
    /// The parent of each declaration.
    pub parents: HashMap<CDeclId, CDeclId>, // record fields and enum constants

    /// The source files in the AST.
    ///
    /// Mapping from FileId to SrcFile. Deduplicated by file path.
    files: Vec<SrcFile>,
    /// Mapping from clang file id to translator FileId.
    file_map: Vec<FileId>,

    /// Vector of include paths, indexed by FileId. Each include path is the
    /// sequence of #include statement locations and the file being included at
    /// that location.
    include_map: Vec<Vec<SrcLoc>>,

    /// The names of the labels defined in the C source code.
    pub label_names: IndexMap<CLabelId, Rc<str>>,

    /// A map from expressions to the stack of macros they were expanded from.
    pub macro_invocations: IndexMap<CExprId, Vec<CDeclId>>,

    /// A map from macro declarations to the expressions they expand to.
    pub macro_expansions: IndexMap<CDeclId, Vec<CExprId>>,

    /// A map from expressions to the text of the macro invocation they expanded
    /// from, if any.
    pub macro_expansion_text: IndexMap<CExprId, String>,

    /// The comments in the AST.
    pub comments: Vec<Located<String>>,

    /// The key is the typedef decl being squashed away,
    /// and the value is the decl id to the corresponding structure.
    pub prenamed_decls: IndexMap<CDeclId, CDeclId>,

    /// The kind of `va_list` used in the C code.
    pub va_list_kind: BuiltinVaListKind,
    /// The target triple.
    pub target: String,
}

/// Comments associated with a typed AST context.
#[derive(Debug, Clone)]
pub struct CommentContext {
    comments_by_file: HashMap<FileId, RefCell<Vec<Located<String>>>>,
}

/// A source span that can be displayed.
#[derive(Debug, Clone)]
pub struct DisplaySrcSpan {
    /// The file path, if available.
    file: Option<PathBuf>,
    /// The source span.
    loc: SrcSpan,
}

impl Display for DisplaySrcSpan {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some(ref file) = self.file {
            write!(
                f,
                "{}:{}:{}",
                file.display(),
                self.loc.begin_line,
                self.loc.begin_column
            )
        } else {
            Debug::fmt(self, f)
        }
    }
}

/// A file ID.
pub type FileId = usize;

/// Represents some AST node possibly with source location information bundled with it.
#[derive(Debug, Clone)]
pub struct Located<T> {
    /// The source location of the node.
    pub loc: Option<SrcSpan>,
    /// The node itself.
    pub kind: T,
}

impl<T> Located<T> {
    pub fn begin_loc(&self) -> Option<SrcLoc> {
        self.loc.map(|loc| loc.begin())
    }
    pub fn end_loc(&self) -> Option<SrcLoc> {
        self.loc.map(|loc| loc.end())
    }
}

impl TypedAstContext {
    /// Creates a new `TypedAstContext`.
    ///
    /// TODO: build the TypedAstContext during initialization, rather than
    /// building an empty one and filling it later.
    pub fn new(clang_files: &[SrcFile]) -> TypedAstContext {
        let mut files: Vec<SrcFile> = vec![];
        let mut file_map: Vec<FileId> = vec![];
        for file in clang_files {
            if let Some(existing) = files.iter().position(|f| f.path == file.path) {
                file_map.push(existing);
            } else {
                file_map.push(files.len());
                files.push(file.clone());
            }
        }

        let mut include_map = vec![];
        for (fileid, mut cur) in files.iter().enumerate() {
            let mut include_path = vec![];
            while let Some(include_loc) = &cur.include_loc {
                include_path.push(SrcLoc {
                    fileid: fileid as u64,
                    line: include_loc.line,
                    column: include_loc.column,
                });
                cur = &clang_files[include_loc.fileid as usize];
            }
            include_path.reverse();
            include_map.push(include_path);
        }

        TypedAstContext {
            c_types: HashMap::new(),
            c_exprs: HashMap::new(),
            c_decls: IndexMap::new(),
            c_stmts: HashMap::new(),

            c_decls_top: Vec::new(),
            c_main: None,
            files,
            file_map,
            include_map,
            parents: HashMap::new(),
            macro_invocations: Default::default(),
            macro_expansions: Default::default(),
            macro_expansion_text: Default::default(),
            label_names: Default::default(),

            comments: Vec::new(),
            prenamed_decls: IndexMap::new(),
            va_list_kind: BuiltinVaListKind::CharPtrBuiltinVaList,
            target: String::new(),
        }
    }

    /// Returns a `DisplaySrcSpan` for a given `SrcSpan`.
    pub fn display_loc(&self, loc: &Option<SrcSpan>) -> Option<DisplaySrcSpan> {
        loc.as_ref().map(|loc| DisplaySrcSpan {
            file: self.files[self.file_map[loc.fileid as usize]].path.clone(),
            loc: *loc,
        })
    }

    /// Gets the source path for a given node.
    pub fn get_source_path<'a, T>(&'a self, node: &Located<T>) -> Option<&'a Path> {
        self.file_id(node)
            .and_then(|fileid| self.get_file_path(fileid))
    }

    /// Gets the file path for a given file ID.
    pub fn get_file_path(&self, id: FileId) -> Option<&Path> {
        self.files[id].path.as_deref()
    }

    /// Compare two [`SrcLoc`]s based on their import path.
    pub fn compare_src_locs(&self, a: &SrcLoc, b: &SrcLoc) -> Ordering {
        /// Compare without regard to `fileid`.
        fn cmp_pos(a: &SrcLoc, b: &SrcLoc) -> Ordering {
            (a.line, a.column).cmp(&(b.line, b.column))
        }

        use Ordering::*;
        let path_a = &self.include_map[self.file_map[a.fileid as usize]][..];
        let path_b = &self.include_map[self.file_map[b.fileid as usize]][..];

        // Find the first include that does not match between the two
        let common_len = path_a.len().min(path_b.len());
        let order = path_a[..common_len].cmp(&path_b[..common_len]);
        if order != Equal {
            return order;
        }

        // Either all parent includes are the same, or the include paths are of different lengths
        // because .zip() stops when one of the iterators is empty.
        match path_a.len().cmp(&path_b.len()) {
            Less => {
                // a has the shorter path, which means b was included in a's file
                // so extract that include and compare the position to a
                let b = &path_b[path_a.len()];
                cmp_pos(a, b)
            }
            Equal => a.cmp(b), // a and b have the same include path and are thus in the same file
            Greater => {
                // b has the shorter path, which means a was included in b's file
                // so extract that include and compare the position to b
                let a = &path_a[path_b.len()];
                cmp_pos(a, b)
            }
        }
    }

    /// Gets the line number of the include directive for a given file.
    pub fn get_file_include_line_number(&self, file: FileId) -> Option<u64> {
        self.include_map[file].first().map(|loc| loc.line)
    }

    /// Finds the file ID for a given path.
    pub fn find_file_id(&self, path: &Path) -> Option<FileId> {
        self.files
            .iter()
            .position(|f| f.path.as_ref().is_some_and(|p| p == path))
    }

    /// Gets the file ID for a given located node.
    pub fn file_id<T>(&self, located: &Located<T>) -> Option<FileId> {
        located
            .loc
            .as_ref()
            .and_then(|loc| self.file_map.get(loc.fileid as usize).copied())
    }

    /// Gets the source location for a given ID.
    pub fn get_src_loc(&self, id: SomeId) -> Option<SrcSpan> {
        use SomeId::*;
        match id {
            Stmt(id) => self.index(id).loc,
            Expr(id) => self.index(id).loc,
            Decl(id) => self.index(id).loc,
            Type(id) => self.index(id).loc,
        }
    }

    /// Returns an iterator over the declarations in the AST.
    pub fn iter_decls(&self) -> indexmap::map::Iter<'_, CDeclId, CDecl> {
        self.c_decls.iter()
    }

    /// Returns a mutable iterator over the declarations in the AST.
    pub fn iter_mut_decls(&mut self) -> indexmap::map::IterMut<'_, CDeclId, CDecl> {
        self.c_decls.iter_mut()
    }

    /// Gets a declaration by its ID.
    pub fn get_decl(&self, key: &CDeclId) -> Option<&CDecl> {
        self.c_decls.get(key)
    }

    /// Returns `true` if the given expression is a null pointer.
    pub fn is_null_expr(&self, expr_id: CExprId) -> bool {
        use CExprKind::*;
        match self[expr_id].kind {
            ExplicitCast(_, _, CastKind::NullToPointer, _, _)
            | ImplicitCast(_, _, CastKind::NullToPointer, _, _) => true,

            ExplicitCast(ty, e, CastKind::BitCast, _, _)
            | ImplicitCast(ty, e, CastKind::BitCast, _, _) => {
                self.resolve_type(ty.ctype).kind.is_pointer() && self.is_null_expr(e)
            }

            _ => false,
        }
    }

    /// Predicate for struct, union, and enum declarations without
    /// bodies. These forward declarations are suitable for use as
    /// the targets of pointers.
    pub fn is_forward_declared_type(&self, typ: CTypeId) -> bool {
        use CDeclKind::*;
        || -> Option<()> {
            let decl_id = self.resolve_type(typ).kind.as_underlying_decl()?;
            matches!(
                self[decl_id].kind,
                Struct { fields: None, .. }
                    | Union { fields: None, .. }
                    | Enum {
                        integral_type: None,
                        ..
                    }
            )
            .then(|| ())
        }()
        .is_some()
    }

    /// Follow a chain of typedefs and return true iff the last typedef is named
    /// `__builtin_va_list` thus naming the type clang uses to represent `va_list`s.
    pub fn is_builtin_va_list(&self, typ: CTypeId) -> bool {
        match self.index(typ).kind {
            CTypeKind::Typedef(decl) => match &self.index(decl).kind {
                CDeclKind::Typedef {
                    name: name_,
                    typ: ty,
                    ..
                } => {
                    if name_ == "__builtin_va_list" {
                        true
                    } else {
                        self.is_builtin_va_list(ty.ctype)
                    }
                }
                _ => panic!("Typedef decl did not point to a typedef"),
            },
            _ => false,
        }
    }

    /// Predicate for types that are used to implement C's `va_list`.
    /// FIXME: can we get rid of this method and use `is_builtin_va_list` instead?
    pub fn is_va_list_struct(&self, typ: CTypeId) -> bool {
        // detect `va_list`s based on typedef (should work across implementations)
        //        if self.is_builtin_va_list(typ) {
        //            return true;
        //        }

        // detect `va_list`s based on type (assumes struct-based implementation)
        let resolved_ctype = self.resolve_type(typ);
        use CTypeKind::*;
        match resolved_ctype.kind {
            Struct(record_id) => {
                if let CDeclKind::Struct {
                    name: Some(nam), ..
                } = &self[record_id].kind
                {
                    nam == "__va_list_tag" || nam == "__va_list"
                } else {
                    false
                }
            }
            // va_list is a 1 element array; return true iff element type is struct __va_list_tag
            ConstantArray(typ, 1) => self.is_va_list(typ),
            _ => false,
        }
    }

    /// Predicate for pointers to types that are used to implement C's `va_list`.
    pub fn is_va_list(&self, typ: CTypeId) -> bool {
        use BuiltinVaListKind::*;
        match self.va_list_kind {
            CharPtrBuiltinVaList | VoidPtrBuiltinVaList | X86_64ABIBuiltinVaList => {
                match self.resolve_type(typ).kind {
                    CTypeKind::Pointer(CQualTypeId { ctype, .. })
                    | CTypeKind::ConstantArray(ctype, _) => self.is_va_list_struct(ctype),
                    _ => false,
                }
            }

            AArch64ABIBuiltinVaList => self.is_va_list_struct(typ),

            AAPCSABIBuiltinVaList => {
                // The mechanism applies: va_list is a `struct __va_list { ... }` as per
                // https://documentation-service.arm.com/static/5f201281bb903e39c84d7eae
                // ("Procedure Call Standard for the Arm Architecture Release 2020Q2, Document
                // number IHI 0042J") Section 8.1.4 "Additional Types"
                self.is_va_list_struct(typ)
            }

            kind => unimplemented!("va_list type {:?} not yet implemented", kind),
        }
    }

    /// Predicate for function pointers.
    pub fn is_function_pointer(&self, typ: CTypeId) -> bool {
        let resolved_ctype = self.resolve_type(typ);
        use CTypeKind::*;
        if let Pointer(p) = resolved_ctype.kind {
            matches!(self.resolve_type(p.ctype).kind, Function { .. })
        } else {
            false
        }
    }

    /// Can the given field decl be a flexible array member?
    pub fn maybe_flexible_array(&self, typ: CTypeId) -> bool {
        let field_ty = self.resolve_type(typ);
        use CTypeKind::*;
        matches!(field_ty.kind, IncompleteArray(_) | ConstantArray(_, 0 | 1))
    }

    /// Gets the pointee of a pointer type.
    pub fn get_pointee_qual_type(&self, typ: CTypeId) -> Option<CQualTypeId> {
        let resolved_ctype = self.resolve_type(typ);
        if let CTypeKind::Pointer(p) = resolved_ctype.kind {
            Some(p)
        } else {
            None
        }
    }

    /// Resolve expression value, ignoring any casts.
    pub fn resolve_expr(&self, expr_id: CExprId) -> (CExprId, &CExprKind) {
        let expr = &self.index(expr_id).kind;
        use CExprKind::*;
        match expr {
            ImplicitCast(_, subexpr, _, _, _)
            | ExplicitCast(_, subexpr, _, _, _)
            | Paren(_, subexpr) => self.resolve_expr(*subexpr),
            _ => (expr_id, expr),
        }
    }

    /// Resolve true expression type, iterating through any casts and variable
    /// references.
    pub fn resolve_expr_type_id(&self, expr_id: CExprId) -> Option<(CExprId, CTypeId)> {
        let expr = &self.index(expr_id).kind;
        let mut ty = expr.get_type();
        use CExprKind::*;
        match expr {
            ImplicitCast(_, subexpr, _, _, _)
            | ExplicitCast(_, subexpr, _, _, _)
            | Paren(_, subexpr) => {
                return self.resolve_expr_type_id(*subexpr);
            }
            DeclRef(_, decl_id, _) => {
                let decl = self.index(*decl_id);
                use CDeclKind::*;
                match decl.kind {
                    Function { typ, .. } => {
                        ty = Some(self.resolve_type_id(typ));
                    }
                    Variable { typ, .. } | Typedef { typ, .. } => {
                        ty = Some(self.resolve_type_id(typ.ctype));
                    }
                    _ => {}
                }
            }
            _ => {}
        }
        ty.map(|ty| (expr_id, ty))
    }

    /// Gets the type ID for a given type kind.
    pub fn type_for_kind(&self, kind: &CTypeKind) -> Option<CTypeId> {
        self.c_types
            .iter()
            .find_map(|(id, k)| if kind == &k.kind { Some(*id) } else { None })
    }

    /// Resolves a type ID, iterating through any typedefs.
    pub fn resolve_type_id(&self, typ: CTypeId) -> CTypeId {
        use CTypeKind::*;
        let ty = match self.index(typ).kind {
            Attributed(ty, _) => ty.ctype,
            Elaborated(ty) => ty,
            Decayed(ty) => ty,
            TypeOf(ty) => ty,
            Paren(ty) => ty,
            Typedef(decl) => match self.index(decl).kind {
                CDeclKind::Typedef { typ: ty, .. } => ty.ctype,
                _ => panic!("Typedef decl did not point to a typedef"),
            },
            _ => return typ,
        };
        self.resolve_type_id(ty)
    }

    /// Resolves a type, iterating through any typedefs.
    pub fn resolve_type(&self, typ: CTypeId) -> &CType {
        let resolved_typ_id = self.resolve_type_id(typ);
        self.index(resolved_typ_id)
    }

    /// Checks if a variable has static storage.
    pub fn is_static_variable(&self, expr: CExprId) -> bool {
        match self.index(expr).kind {
            CExprKind::DeclRef(_, decl_id, _) => {
                if let CDeclKind::Variable {
                    has_static_duration,
                    ..
                } = &self.index(decl_id).kind
                {
                    *has_static_duration
                } else {
                    false
                }
            }
            _ => false,
        }
    }

    /// Checks if an expression is a string literal.
    pub fn is_expr_string_literal(&self, expr: CExprId) -> bool {
        match &self.index(expr).kind {
            CExprKind::Literal(_, CLiteral::String(..)) => true,
            _ => {
                // check why false
                false
            }
        }
    }

    /// Extract decl of referenced function.
    /// Looks for ImplicitCast(FunctionToPointerDecay, DeclRef(function_decl)).
    pub fn fn_declref_decl(&self, func_expr: CExprId) -> Option<&CDeclKind> {
        use CastKind::FunctionToPointerDecay;
        if let CExprKind::ImplicitCast(_, fexp, FunctionToPointerDecay, _, _) = self[func_expr].kind
            && let CExprKind::DeclRef(_ty, decl_id, _rv) = &self[fexp].kind
        {
            let decl = &self.index(*decl_id).kind;
            assert!(matches!(decl, CDeclKind::Function { .. }));
            return Some(decl);
        }
        None
    }

    /// Return the list of types for a list of declared function parameters.
    ///
    /// Returns `None` if one of the parameters is not a `CDeclKind::Variable`, e.g. if it was not a
    /// function parameter but actually some other kind of declaration.
    pub fn tys_of_params(&self, parameters: &[CDeclId]) -> Option<Vec<CQualTypeId>> {
        parameters
            .iter()
            .map(|p| match self.index(*p).kind {
                CDeclKind::Variable { typ, .. } => Some(CQualTypeId::new(typ.ctype)),
                _ => None,
            })
            .collect()
    }

    /// Return the most precise possible CTypeKind for the given function declaration.
    /// Specifically, ensures that arguments' types are not resolved to underlying types if they were
    /// declared as typedefs, but returned as those typedefs.
    ///
    /// The passed CDeclId must refer to a function declaration.
    pub fn fn_decl_ty_with_declared_args(&self, func_decl: &CDeclKind) -> CTypeKind {
        if let CDeclKind::Function {
            typ, parameters, ..
        } = func_decl
        {
            let typ = self.resolve_type_id(*typ);
            let decl_arg_tys = self.tys_of_params(parameters).unwrap();
            let typ_kind = &self[typ].kind;
            if let &CTypeKind::Function(ret, ref _arg_tys, a, b, c) = typ_kind {
                return CTypeKind::Function(ret, decl_arg_tys, a, b, c);
            }
            panic!("expected {typ:?} to be CTypeKind::Function, but it was {typ_kind:?}")
        }
        panic!("expected a CDeclKind::Function, but passed {func_decl:?}")
    }

    /// Return the id of the most precise possible type for the function referenced by the given
    /// expression, if any.
    pub fn fn_declref_ty_with_declared_args(&self, func_expr: CExprId) -> Option<CQualTypeId> {
        if let Some(func_decl @ CDeclKind::Function { .. }) = self.fn_declref_decl(func_expr) {
            let kind_with_declared_args = self.fn_decl_ty_with_declared_args(func_decl);
            let specific_typ = self
                .type_for_kind(&kind_with_declared_args)
                .unwrap_or_else(|| panic!("no type for kind {kind_with_declared_args:?}"));
            return Some(CQualTypeId::new(specific_typ));
        }
        None
    }

    /// Pessimistically try to check if an expression has side effects. If it
    /// does, or we can't tell that it doesn't, return `false`.
    pub fn is_expr_pure(&self, expr: CExprId) -> bool {
        use CExprKind::*;
        let pure = |expr| self.is_expr_pure(expr);
        match self.index(expr).kind {
            BadExpr
            | ShuffleVector(..)
            | ConvertVector(..)
            | Call(..)
            | Unary(_, UnOp::PreIncrement, _, _)
            | Unary(_, UnOp::PostIncrement, _, _)
            | Unary(_, UnOp::PreDecrement, _, _)
            | Unary(_, UnOp::PostDecrement, _, _)
            | Binary(_, BinOp::Assign, _, _, _, _)
            | InitList { .. }
            | ImplicitValueInit { .. }
            | Predefined(..)
            | Statements(..) // TODO: more precision
            | VAArg(..)
            | Atomic { .. } => false,

            Literal(_, _)
            | DeclRef(_, _, _)
            | UnaryType(_, _, _, _)
            | OffsetOf(..)
            | ConstantExpr(..) => true,

            DesignatedInitExpr(_, _, e)
            | ImplicitCast(_, e, _, _, _)
            | ExplicitCast(_, e, _, _, _)
            | Member(_, e, _, _, _)
            | Paren(_, e)
            | CompoundLiteral(_, e)
            | Unary(_, _, e, _) => pure(e),

            Binary(_, op, _, _, _, _) if op.underlying_assignment().is_some() => false,
            Binary(_, _, lhs, rhs, _, _) => pure(lhs) && pure(rhs),

            ArraySubscript(_, lhs, rhs, _) => pure(lhs) && pure(rhs),
            Conditional(_, c, lhs, rhs) => pure(c) && pure(lhs) && pure(rhs),
            BinaryConditional(_, c, rhs) => pure(c) && pure(rhs),
            Choose(_, c, lhs, rhs, _) => pure(c) && pure(lhs) && pure(rhs),
        }
    }

    /// Pessimistically try to check if an expression doesn't return.
    /// If it does, or we can't tell that it doesn't, return `false`.
    pub fn expr_diverges(&self, expr_id: CExprId) -> bool {
        let func_id = match self.index(expr_id).kind {
            CExprKind::Call(_, func_id, _) => func_id,
            _ => return false,
        };

        let type_id = match self[func_id].kind.get_type() {
            None => return false,
            Some(t) => t,
        };
        let pointed_id = match self.index(type_id).kind {
            CTypeKind::Pointer(pointer_qualtype) => pointer_qualtype.ctype,
            _ => return false,
        };

        match self.index(pointed_id).kind {
            CTypeKind::Function(_, _, _, no_return, _) => no_return,
            _ => false,
        }
    }

    /// Pessimistically try to check if an expression is `const`.
    /// If it's not, or we can't tell if it is, return `false`.
    ///
    /// This should be a top-down, pessimistic/conservative analysis.
    pub fn is_const_expr(&self, expr: CExprId) -> bool {
        let is_const = |expr| self.is_const_expr(expr);

        use CExprKind::*;
        match self[expr].kind {
            // A literal is always `const`.
            Literal(_, _) => true,
            // Unary ops should be `const`.
            // TODO handle `f128` or use the primitive type.
            Unary(_, _, expr, _) => is_const(expr),
            UnaryType(_, _, _, _) => false, // TODO disabled for now as tests are broken
            // Not sure what a `None` `CExprId` means here
            // or how to detect a `sizeof` of a VLA, which is non-`const`,
            // although it seems we don't handle `sizeof(VLAs)`
            // correctly in macros elsewhere already.
            #[allow(unreachable_patterns)]
            UnaryType(_, _, expr, _) => expr.is_none_or(is_const),
            // Not sure what a `OffsetOfKind::Variable` means.
            OffsetOf(_, _) => true,
            // `ptr::offset` (ptr `BinOp::Add`) was `const` stabilized in `1.61.0`.
            // `ptr::offset_from` (ptr `BinOp::Subtract`) was `const` stabilized in `1.65.0`.
            // TODO `f128` is not yet handled, as we should eventually
            // switch to the (currently unstable) `f128` primitive type (#1262).
            Binary(_, _, lhs, rhs, _, _) => is_const(lhs) && is_const(rhs),
            ImplicitCast(_, _, CastKind::ArrayToPointerDecay, _, _) => false, // TODO disabled for now as tests are broken
            // `as` casts are always `const`.
            ImplicitCast(_, expr, _, _, _) => is_const(expr),
            // `as` casts are always `const`.
            // TODO This is `const`, although there's a bug #853.
            ExplicitCast(_, expr, _, _, _) => is_const(expr),
            // This is used in `const` locations like `match` patterns and array lengths, so it must be `const`.
            ConstantExpr(_, _, _) => true,
            // A reference in an already otherwise `const` context should be `const` itself.
            DeclRef(_, _, _) => true,
            Call(_, fn_expr, ref args) => {
                let is_const_fn = false; // TODO detect which `fn`s are `const`.
                is_const(fn_expr) && args.iter().copied().all(is_const) && is_const_fn
            }
            Member(_, expr, _, _, _) => is_const(expr),
            ArraySubscript(_, array, index, _) => is_const(array) && is_const(index),
            Conditional(_, cond, if_true, if_false) => {
                is_const(cond) && is_const(if_true) && is_const(if_false)
            }
            BinaryConditional(_, cond, if_false) => is_const(cond) && is_const(if_false),
            InitList(_, ref inits, _, _) => inits.iter().copied().all(is_const),
            ImplicitValueInit(_) => true,
            Paren(_, expr) => is_const(expr),
            CompoundLiteral(_, expr) => is_const(expr),
            Predefined(_, expr) => is_const(expr),
            Statements(_, stmt) => self.is_const_stmt(stmt),
            VAArg(_, expr) => is_const(expr),
            // SIMD is not yet `const` in Rust.
            ShuffleVector(_, _) | ConvertVector(_, _) => false,
            DesignatedInitExpr(_, _, expr) => is_const(expr),
            Choose(_, cond, if_true, if_false, _) => {
                is_const(cond) && is_const(if_true) && is_const(if_false)
            }
            // Atomics are not yet `const` in Rust.
            Atomic { .. } => false,
            BadExpr => false,
        }
    }

    /// Pessimistically try to check if a statement is `const`.
    pub fn is_const_stmt(&self, _stmt: CStmtId) -> bool {
        // TODO
        false
    }

    /// Prune unwanted declarations from the AST.
    pub fn prune_unwanted_decls(&mut self, want_unused_functions: bool) {
        // Starting from a set of root declarations, walk each one to find declarations it
        // depends on. Then walk each of those, recursively.

        // Declarations we still need to walk.  Everything in here is also in `wanted`.
        let mut to_walk: Vec<CDeclId> = Vec::new();
        // Declarations accessible from a root.
        let mut wanted: HashSet<CDeclId> = HashSet::new();

        // Mark all the roots as wanted.  Roots are all top-level functions and variables that might
        // be visible from another compilation unit.
        //
        // In addition, mark any other (unused) function wanted if configured.
        for &decl_id in &self.c_decls_top {
            let decl = self.index(decl_id);
            use CDeclKind::*;
            let is_wanted = match decl.kind {
                Function {
                    body: Some(_),
                    is_global: true,
                    is_inline,
                    is_inline_externally_visible,
                    ..
                    // Depending on the C specification and dialect, an inlined function
                    // may be externally visible. We rely on clang to determine visibility.
                } if !is_inline || is_inline_externally_visible => true,
                Function {
                    body: Some(_),
                    ..
                } if want_unused_functions => true,
                Variable {
                    is_defn: true,
                    is_externally_visible: true,
                    ..
                } => true,
                Variable { ref attrs, .. } | Function { ref attrs, .. }
                    if attrs.contains(&Attribute::Used) => true,
                _ => false,
            };

            if is_wanted {
                to_walk.push(decl_id);
                wanted.insert(decl_id);
            }
        }

        // Add all referenced macros to the set of wanted decls
        // wanted.extend(self.macro_expansions.values().flatten());

        while let Some(enclosing_decl_id) = to_walk.pop() {
            for some_id in DFNodes::new(self, SomeId::Decl(enclosing_decl_id)) {
                use SomeId::*;
                match some_id {
                    Type(type_id) => {
                        if let CTypeKind::Elaborated(decl_type_id) = self.c_types[&type_id].kind {
                            // This is a reference to a previously declared type.  If we look
                            // through it we should(?) get something that looks like a declaration,
                            // which we can mark as wanted.
                            let decl_id = self.c_types[&decl_type_id]
                                .kind
                                .as_decl_or_typedef()
                                .expect("target of CTypeKind::Elaborated isn't a decl?");
                            if wanted.insert(decl_id) {
                                to_walk.push(decl_id);
                            }
                        } else {
                            // For everything else (including `Struct` etc.), DFNodes will walk the
                            // corresponding declaration.
                        }
                    }

                    Expr(expr_id) => {
                        let expr = self.index(expr_id);
                        if let Some(macs) = self.macro_invocations.get(&expr_id) {
                            for mac_id in macs {
                                if wanted.insert(*mac_id) {
                                    to_walk.push(*mac_id);
                                }
                            }
                        }
                        if let CExprKind::DeclRef(_, decl_id, _) = &expr.kind
                            && wanted.insert(*decl_id)
                        {
                            to_walk.push(*decl_id);
                        }
                    }

                    Decl(decl_id) => {
                        if wanted.insert(decl_id) {
                            to_walk.push(decl_id);
                        }

                        if let CDeclKind::EnumConstant { .. } = self.c_decls[&decl_id].kind {
                            // Special case for enums.  The enum constant is used, so the whole
                            // enum is also used.
                            let parent_id = self.parents[&decl_id];
                            if wanted.insert(parent_id) {
                                to_walk.push(parent_id);
                            }
                        }
                    }

                    // Stmts can include decls, but we'll see the DeclId itself in a later
                    // iteration.
                    Stmt(_) => {}
                }
            }
        }

        // Unset c_main if we are not retaining its declaration
        if let Some(main_id) = self.c_main
            && !wanted.contains(&main_id)
        {
            self.c_main = None;
        }

        // Prune any declaration that isn't considered live
        self.c_decls
            .retain(|&decl_id, _decl| wanted.contains(&decl_id));

        // Prune top declarations that are not considered live
        self.c_decls_top.retain(|x| wanted.contains(x));
    }

    /// Bubble types of unary and binary operators up from their args into the expression type.
    ///
    /// In Clang 15 and below, the Clang AST resolves typedefs in the expression type of unary and
    /// binary expressions. For example, a BinaryExpr node adding two `size_t` expressions will be
    /// given an `unsigned long` type rather than the `size_t` typedef type. This behavior changed
    /// in Clang 16. This method adjusts AST node types to match those produced by Clang 16 and
    /// newer; on these later Clang versions, it should have no effect.
    ///
    /// This pass is necessary because we reify some typedef types (such as `size_t`) into their own
    /// distinct Rust types. As such, we need to make sure we know the exact type to generate when
    /// we translate an expr, not just its resolved type (looking through typedefs).
    pub fn bubble_expr_types(&mut self) {
        struct BubbleExprTypes<'a> {
            ast_context: &'a mut TypedAstContext,
        }

        use iterators::{NodeVisitor, immediate_children_all_types};
        impl<'a> NodeVisitor for BubbleExprTypes<'a> {
            fn children(&mut self, id: SomeId) -> Vec<SomeId> {
                immediate_children_all_types(self.ast_context, id)
            }
            fn post(&mut self, id: SomeId) {
                if let SomeId::Expr(e) = id {
                    let new_ty = match self.ast_context.c_exprs[&e].kind {
                        CExprKind::Conditional(_ty, _cond, lhs, rhs) => {
                            let lhs_type_id =
                                self.ast_context.c_exprs[&lhs].kind.get_qual_type().unwrap();
                            let rhs_type_id =
                                self.ast_context.c_exprs[&rhs].kind.get_qual_type().unwrap();

                            let lhs_resolved_ty = self.ast_context.resolve_type(lhs_type_id.ctype);
                            let rhs_resolved_ty = self.ast_context.resolve_type(rhs_type_id.ctype);

                            if CTypeKind::PULLBACK_KINDS.contains(&lhs_resolved_ty.kind) {
                                Some(lhs_type_id)
                            } else if CTypeKind::PULLBACK_KINDS.contains(&rhs_resolved_ty.kind) {
                                Some(rhs_type_id)
                            } else {
                                None
                            }
                        }
                        CExprKind::Binary(_ty, op, lhs, rhs, _, _) => {
                            let rhs_type_id =
                                self.ast_context.c_exprs[&rhs].kind.get_qual_type().unwrap();
                            let lhs_kind = &self.ast_context.c_exprs[&lhs].kind;
                            let lhs_type_id = lhs_kind.get_qual_type().unwrap();

                            let lhs_resolved_ty = self.ast_context.resolve_type(lhs_type_id.ctype);
                            let rhs_resolved_ty = self.ast_context.resolve_type(rhs_type_id.ctype);

                            let neither_ptr = !lhs_resolved_ty.kind.is_pointer()
                                && !rhs_resolved_ty.kind.is_pointer();

                            if op.all_types_same() && neither_ptr {
                                if CTypeKind::PULLBACK_KINDS.contains(&lhs_resolved_ty.kind) {
                                    Some(lhs_type_id)
                                } else {
                                    Some(rhs_type_id)
                                }
                            } else if op == BinOp::ShiftLeft || op == BinOp::ShiftRight {
                                Some(lhs_type_id)
                            } else {
                                return;
                            }
                        }
                        CExprKind::Unary(_ty, op, e, _idk) => op.expected_result_type(
                            self.ast_context,
                            self.ast_context.c_exprs[&e].kind.get_qual_type().unwrap(),
                        ),
                        CExprKind::Paren(_ty, e) => {
                            self.ast_context.c_exprs[&e].kind.get_qual_type()
                        }
                        _ => return,
                    };
                    if let (Some(ty), Some(new_ty)) = (
                        self.ast_context
                            .c_exprs
                            .get_mut(&e)
                            .and_then(|e| e.kind.get_qual_type_mut()),
                        new_ty,
                    ) {
                        *ty = new_ty;
                    };
                }
            }
        }
        for decl in self.c_decls_top.clone() {
            BubbleExprTypes { ast_context: self }.visit_tree(SomeId::Decl(decl));
        }
    }

    /// Sort the top-level declarations in the AST.
    pub fn sort_top_decls(&mut self) {
        // Group and sort declarations by file and by position
        let mut decls_top = mem::take(&mut self.c_decls_top);
        decls_top.sort_unstable_by(|a, b| {
            let a = self.index(*a);
            let b = self.index(*b);
            use Ordering::*;
            match (&a.loc, &b.loc) {
                (None, None) => Equal,
                (None, _) => Less,
                (_, None) => Greater,
                (Some(a), Some(b)) => self.compare_src_locs(&a.begin(), &b.begin()),
            }
        });
        self.c_decls_top = decls_top;
    }

    /// Checks if a struct declaration has a manual alignment attribute.
    pub fn has_inner_struct_decl(&self, decl_id: CDeclId) -> bool {
        matches!(
            self.index(decl_id).kind,
            CDeclKind::Struct {
                manual_alignment: Some(_),
                ..
            }
        )
    }

    /// Checks if a struct declaration is packed.
    pub fn is_packed_struct_decl(&self, decl_id: CDeclId) -> bool {
        use CDeclKind::*;
        matches!(
            self.index(decl_id).kind,
            Struct {
                is_packed: true,
                ..
            } | Struct {
                max_field_alignment: Some(_),
                ..
            }
        )
    }

    /// Checks if a struct type is aligned.
    pub fn is_aligned_struct_type(&self, typ: CTypeId) -> bool {
        if let Some(decl_id) = self.resolve_type(typ).kind.as_underlying_decl()
            && let CDeclKind::Struct {
                manual_alignment: Some(_),
                ..
            } = self.index(decl_id).kind
        {
            return true;
        }
        false
    }
}

impl CommentContext {
    /// Creates an empty `CommentContext`.
    pub fn empty() -> CommentContext {
        CommentContext {
            comments_by_file: HashMap::new(),
        }
    }

    /// Build a CommentContext from the comments in this `ast_context`.
    pub fn new(ast_context: &mut TypedAstContext) -> CommentContext {
        let mut comments_by_file: HashMap<FileId, Vec<Located<String>>> = HashMap::new();

        // Group comments by their file
        for comment in &ast_context.comments {
            // Comments without a valid FileId are probably clang
            // compiler-internal definitions
            if let Some(file_id) = ast_context.file_id(comment) {
                comments_by_file
                    .entry(file_id)
                    .or_default()
                    .push(comment.clone());
            }
        }

        // Sort in REVERSE! Last element is the first in file source
        // ordering. This makes it easy to pop the next comment off.
        for comments in comments_by_file.values_mut() {
            comments.sort_by(|a, b| {
                ast_context.compare_src_locs(&b.loc.unwrap().begin(), &a.loc.unwrap().begin())
            });
        }

        let comments_by_file = comments_by_file
            .into_iter()
            .map(|(k, v)| (k, RefCell::new(v)))
            .collect();

        CommentContext { comments_by_file }
    }

    /// Gets the comments before a given source location.
    pub fn get_comments_before(&self, loc: SrcLoc, ctx: &TypedAstContext) -> Vec<String> {
        let file_id = ctx.file_map[loc.fileid as usize];
        let mut extracted_comments = vec![];
        let mut comments = match self.comments_by_file.get(&file_id) {
            None => return extracted_comments,
            Some(comments) => comments.borrow_mut(),
        };
        while !comments.is_empty() {
            let next_comment_loc = comments
                .last()
                .unwrap()
                .begin_loc()
                .expect("All comments must have a source location");
            if ctx.compare_src_locs(&next_comment_loc, &loc) != Ordering::Less {
                break;
            }

            extracted_comments.push(comments.pop().unwrap().kind);
        }
        extracted_comments
    }

    /// Gets the comments before a given located node.
    pub fn get_comments_before_located<T>(
        &self,
        located: &Located<T>,
        ctx: &TypedAstContext,
    ) -> Vec<String> {
        match located.begin_loc() {
            None => vec![],
            Some(loc) => self.get_comments_before(loc, ctx),
        }
    }

    /// Peeks at the next comment on the same line as the given source location.
    pub fn peek_next_comment_on_line(
        &self,
        loc: SrcLoc,
        ctx: &TypedAstContext,
    ) -> Option<Located<String>> {
        let file_id = ctx.file_map[loc.fileid as usize];
        let comments = self.comments_by_file.get(&file_id)?.borrow();
        comments.last().and_then(|comment| {
            let next_comment_loc = comment
                .begin_loc()
                .expect("All comments must have a source location");
            if next_comment_loc.line != loc.line {
                None
            } else {
                Some(comment.clone())
            }
        })
    }

    /// Advance over the current comment in `file`.
    pub fn advance_comment(&self, file: FileId) {
        if let Some(comments) = self.comments_by_file.get(&file) {
            let _ = comments.borrow_mut().pop();
        }
    }

    /// Gets the remaining comments in a file.
    pub fn get_remaining_comments(&mut self, file_id: FileId) -> Vec<String> {
        match self.comments_by_file.remove(&file_id) {
            Some(comments) => comments.into_inner().into_iter().map(|c| c.kind).collect(),
            None => vec![],
        }
    }
}

impl Index<CTypeId> for TypedAstContext {
    type Output = CType;

    fn index(&self, index: CTypeId) -> &CType {
        match self.c_types.get(&index) {
            None => panic!("Could not find {index:?} in TypedAstContext"),
            Some(ty) => ty,
        }
    }
}

impl Index<CExprId> for TypedAstContext {
    type Output = CExpr;
    fn index(&self, index: CExprId) -> &CExpr {
        static BADEXPR: CExpr = Located {
            loc: None,
            kind: CExprKind::BadExpr,
        };
        match self.c_exprs.get(&index) {
            None => &BADEXPR, // panic!("Could not find {:?} in TypedAstContext", index),
            Some(e) => {
                // Transparently index through Paren expressions
                if let CExprKind::Paren(_, subexpr) = e.kind {
                    self.index(subexpr)
                } else {
                    e
                }
            }
        }
    }
}

impl Index<CDeclId> for TypedAstContext {
    type Output = CDecl;

    fn index(&self, index: CDeclId) -> &CDecl {
        match self.c_decls.get(&index) {
            None => panic!("Could not find {index:?} in TypedAstContext"),
            Some(ty) => ty,
        }
    }
}

impl Index<CStmtId> for TypedAstContext {
    type Output = CStmt;

    fn index(&self, index: CStmtId) -> &CStmt {
        match self.c_stmts.get(&index) {
            None => panic!("Could not find {index:?} in TypedAstContext"),
            Some(ty) => ty,
        }
    }
}

/// All of our AST types should have location information bundled with them
pub type CDecl = Located<CDeclKind>;
pub type CStmt = Located<CStmtKind>;
pub type CExpr = Located<CExprKind>;
pub type CType = Located<CTypeKind>;

/// The kind of a C declaration.
#[derive(Debug, Clone)]
pub enum CDeclKind {
    /// A function declaration.
    /// http://clang.llvm.org/doxygen/classclang_1_1FunctionDecl.html
    Function {
        /// Whether the function is global.
        is_global: bool,
        /// Whether the function is inline.
        is_inline: bool,
        /// Whether the function is implicit.
        is_implicit: bool,
        /// Whether the function is extern.
        is_extern: bool,
        /// Whether the function is inline and externally visible.
        is_inline_externally_visible: bool,
        /// The type of the function.
        typ: CFuncTypeId,
        /// The name of the function.
        name: String,
        /// The parameters of the function.
        parameters: Vec<CParamId>,
        /// The body of the function.
        body: Option<CStmtId>,
        /// The attributes of the function.
        attrs: IndexSet<Attribute>,
    },

    /// A variable declaration.
    /// http://clang.llvm.org/doxygen/classclang_1_1VarDecl.html
    Variable {
        /// Whether the variable has static duration.
        has_static_duration: bool,
        /// Whether the variable has thread-local storage duration.
        has_thread_duration: bool,
        /// Whether the variable is externally visible.
        is_externally_visible: bool,
        /// Whether this is a definition.
        is_defn: bool,
        /// The name of the variable.
        ident: String,
        /// The initializer of the variable.
        initializer: Option<CExprId>,
        /// The type of the variable.
        typ: CQualTypeId,
        /// The attributes of the variable.
        attrs: IndexSet<Attribute>,
    },

    /// An enum declaration.
    /// http://clang.llvm.org/doxygen/classclang_1_1EnumDecl.html
    Enum {
        /// The name of the enum.
        name: Option<String>,
        /// The variants of the enum.
        variants: Vec<CEnumConstantId>,
        /// The integral type of the enum.
        integral_type: Option<CQualTypeId>,
    },

    /// An enum constant declaration.
    EnumConstant {
        /// The name of the enum constant.
        name: String,
        /// The value of the enum constant.
        value: ConstIntExpr,
    },

    /// A typedef declaration.
    Typedef {
        /// The name of the typedef.
        name: String,
        /// The type of the typedef.
        typ: CQualTypeId,
        /// Whether the typedef is implicit.
        is_implicit: bool,
        /// The target-dependent macro that this typedef is a part of, if any.
        target_dependent_macro: Option<String>,
    },

    /// A struct declaration.
    Struct {
        /// The name of the struct.
        name: Option<String>,
        /// The fields of the struct.
        fields: Option<Vec<CFieldId>>,
        /// Whether the struct is packed.
        is_packed: bool,
        /// The manual alignment of the struct, if any.
        manual_alignment: Option<u64>,
        /// The maximum field alignment of the struct, if any.
        max_field_alignment: Option<u64>,
        /// The size of the struct in bytes on the target platform.
        platform_byte_size: u64,
        /// The alignment of the struct in bytes on the target platform.
        platform_alignment: u64,
    },

    /// A union declaration.
    Union {
        /// The name of the union.
        name: Option<String>,
        /// The fields of the union.
        fields: Option<Vec<CFieldId>>,
        /// Whether the union is packed.
        is_packed: bool,
    },

    /// A field declaration.
    Field {
        /// The name of the field.
        name: String,
        /// The type of the field.
        typ: CQualTypeId,
        /// The width of the bitfield, if any.
        bitfield_width: Option<u64>,
        /// The bit offset of the field on the target platform.
        platform_bit_offset: u64,
        /// The bit width of the type of the field on the target platform.
        platform_type_bitwidth: u64,
    },

    /// An object-like macro declaration.
    MacroObject {
        /// The name of the macro.
        name: String,
        // replacements: Vec<CExprId>,
    },

    /// A function-like macro declaration.
    MacroFunction {
        /// The name of the macro.
        name: String,
        // replacements: Vec<CExprId>,
    },

    /// A non-canonical declaration.
    NonCanonicalDecl {
        /// The canonical declaration.
        canonical_decl: CDeclId,
    },

    /// A static assert declaration.
    StaticAssert {
        /// The expression to assert.
        assert_expr: CExprId,
        /// The message to display if the assertion fails.
        message: Option<String>,
    },
}

impl CDeclKind {
    /// Gets the name of the declaration, if it has one.
    pub fn get_name(&self) -> Option<&String> {
        use CDeclKind::*;
        Some(match self {
            Function { name: i, .. } => i,
            Variable { ident: i, .. } => i,
            Typedef { name: i, .. } => i,
            EnumConstant { name: i, .. } => i,
            Enum { name: Some(i), .. } => i,
            Struct { name: Some(i), .. } => i,
            Union { name: Some(i), .. } => i,
            Field { name: i, .. } => i,
            MacroObject { name, .. } => name,
            _ => return None,
        })
    }
}

/// An OffsetOf Expr may or may not be a constant
#[derive(Debug, Clone)]
pub enum OffsetOfKind {
    /// An Integer Constant Expr
    Constant(u64),
    /// Contains more information to generate
    /// an offset_of! macro invocation
    /// Struct Type, Field Decl Id, Index Expr
    Variable(CQualTypeId, CDeclId, CExprId),
}

/// Represents an expression in C (6.5 Expressions).
///
/// This is modeled on Clang's APIs, so where documentation
/// is lacking here, look at Clang.
///
/// We've kept a qualified type on every node since Clang has this information
/// available, and since the semantics of translations of certain constructs
/// often depend on the type of the things they are given.
///
/// As per the C standard, qualifiers on types make sense only on lvalues.
#[derive(Debug, Clone)]
pub enum CExprKind {
    /// A literal value.
    Literal(CQualTypeId, CLiteral),

    /// A unary operator.
    Unary(CQualTypeId, UnOp, CExprId, LRValue),

    /// A unary type operator.
    UnaryType(CQualTypeId, UnTypeOp, Option<CExprId>, CQualTypeId),

    /// An `offsetof` expression.
    OffsetOf(CQualTypeId, OffsetOfKind),

    /// A binary operator.
    Binary(
        CQualTypeId,
        BinOp,
        CExprId,
        CExprId,
        Option<CQualTypeId>,
        Option<CQualTypeId>,
    ),

    /// An implicit cast.
    ImplicitCast(CQualTypeId, CExprId, CastKind, Option<CFieldId>, LRValue),

    /// An explicit cast.
    ExplicitCast(CQualTypeId, CExprId, CastKind, Option<CFieldId>, LRValue),

    /// A constant expression.
    ConstantExpr(CQualTypeId, CExprId, Option<ConstIntExpr>),

    /// A reference to a declaration (a variable, for instance).
    // TODO: consider enforcing what types of declarations are allowed here
    DeclRef(CQualTypeId, CDeclId, LRValue),

    /// A function call.
    Call(CQualTypeId, CExprId, Vec<CExprId>),

    /// A member access.
    Member(CQualTypeId, CExprId, CDeclId, MemberKind, LRValue),

    /// An array subscript access.
    ArraySubscript(CQualTypeId, CExprId, CExprId, LRValue),

    /// A ternary conditional operator.
    Conditional(CQualTypeId, CExprId, CExprId, CExprId),

    /// A binary conditional operator `?:` (a GNU extension).
    BinaryConditional(CQualTypeId, CExprId, CExprId),

    /// An initializer list.
    ///
    /// * type
    /// * initializers
    /// * union field
    /// * syntactic form
    InitList(CQualTypeId, Vec<CExprId>, Option<CFieldId>, Option<CExprId>),

    /// An implicit value initialization.
    ImplicitValueInit(CQualTypeId),

    /// A parenthesized expression.
    ///
    /// Ignored, but needed so we have a corresponding node.
    Paren(CQualTypeId, CExprId),

    /// A compound literal.
    CompoundLiteral(CQualTypeId, CExprId),

    /// A predefined expression.
    Predefined(CQualTypeId, CExprId),

    /// A statement expression.
    Statements(CQualTypeId, CStmtId),

    /// A `va_arg` expression.
    VAArg(CQualTypeId, CExprId),

    /// An unsupported vector operation.
    ShuffleVector(CQualTypeId, Vec<CExprId>),

    /// An unsupported convert vector operation.
    ConvertVector(CQualTypeId, Vec<CExprId>),

    /// A designated initializer expression.
    DesignatedInitExpr(CQualTypeId, Vec<Designator>, CExprId),

    /// A GNU `__builtin_choose_expr`.
    ///
    /// * condition
    /// * true expr
    /// * false expr
    /// * was condition true?
    Choose(CQualTypeId, CExprId, CExprId, CExprId, bool),

    /// A GNU/C11 atomic expression.
    Atomic {
        /// The type of the expression.
        typ: CQualTypeId,
        /// The name of the atomic operation.
        name: String,
        /// A pointer to the atomic object.
        ptr: CExprId,
        /// The memory ordering of the operation.
        order: CExprId,
        /// The first value operand.
        val1: Option<CExprId>,
        /// The memory ordering of the operation on failure.
        order_fail: Option<CExprId>,
        /// The second value operand.
        val2: Option<CExprId>,
        /// Whether the operation is weak.
        weak: Option<CExprId>,
    },

    /// An expression that could not be parsed.
    BadExpr,
}

/// The kind of a member access.
#[derive(Copy, Debug, Clone)]
pub enum MemberKind {
    /// `->`
    Arrow,
    /// `.`
    Dot,
}

impl CExprKind {
    pub fn lrvalue(&self) -> LRValue {
        match *self {
            CExprKind::Unary(_, _, _, lrvalue)
            | CExprKind::DeclRef(_, _, lrvalue)
            | CExprKind::ImplicitCast(_, _, _, _, lrvalue)
            | CExprKind::ExplicitCast(_, _, _, _, lrvalue)
            | CExprKind::Member(_, _, _, _, lrvalue)
            | CExprKind::ArraySubscript(_, _, _, lrvalue) => lrvalue,
            _ => LRValue::RValue,
        }
    }

    pub fn get_qual_type(&self) -> Option<CQualTypeId> {
        self.clone().get_qual_type_mut().copied()
    }

    pub fn get_qual_type_mut(&mut self) -> Option<&mut CQualTypeId> {
        match self {
            CExprKind::BadExpr => None,
            CExprKind::Literal(ty, _)
            | CExprKind::OffsetOf(ty, _)
            | CExprKind::Unary(ty, _, _, _)
            | CExprKind::UnaryType(ty, _, _, _)
            | CExprKind::Binary(ty, _, _, _, _, _)
            | CExprKind::ImplicitCast(ty, _, _, _, _)
            | CExprKind::ExplicitCast(ty, _, _, _, _)
            | CExprKind::DeclRef(ty, _, _)
            | CExprKind::Call(ty, _, _)
            | CExprKind::Member(ty, _, _, _, _)
            | CExprKind::ArraySubscript(ty, _, _, _)
            | CExprKind::Conditional(ty, _, _, _)
            | CExprKind::BinaryConditional(ty, _, _)
            | CExprKind::InitList(ty, _, _, _)
            | CExprKind::ImplicitValueInit(ty)
            | CExprKind::Paren(ty, _)
            | CExprKind::CompoundLiteral(ty, _)
            | CExprKind::Predefined(ty, _)
            | CExprKind::Statements(ty, _)
            | CExprKind::VAArg(ty, _)
            | CExprKind::ShuffleVector(ty, _)
            | CExprKind::ConvertVector(ty, _)
            | CExprKind::DesignatedInitExpr(ty, _, _)
            | CExprKind::ConstantExpr(ty, _, _) => Some(ty),
            CExprKind::Choose(ty, _, _, _, _) | CExprKind::Atomic { typ: ty, .. } => Some(ty),
        }
    }

    pub fn get_type(&self) -> Option<CTypeId> {
        self.get_qual_type().map(|x| x.ctype)
    }

    /// Try to determine the truthiness or falsiness of the expression. Return `None` if we can't
    /// say anything.
    pub fn get_bool(&self) -> Option<bool> {
        match *self {
            CExprKind::Literal(_, ref lit) => Some(lit.get_bool()),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CastKind {
    BitCast,
    LValueToRValue,
    NoOp,
    ToUnion,
    ArrayToPointerDecay,
    FunctionToPointerDecay,
    NullToPointer,
    IntegralToPointer,
    PointerToIntegral,
    ToVoid,
    IntegralCast,
    IntegralToBoolean,
    IntegralToFloating,
    FloatingToIntegral,
    FloatingToBoolean,
    BooleanToSignedIntegral,
    PointerToBoolean,
    FloatingCast,
    FloatingRealToComplex,
    FloatingComplexToReal,
    FloatingComplexCast,
    FloatingComplexToIntegralComplex,
    IntegralRealToComplex,
    IntegralComplexToReal,
    IntegralComplexToBoolean,
    IntegralComplexCast,
    IntegralComplexToFloatingComplex,
    BuiltinFnToFnPtr,
    ConstCast,
    VectorSplat,
    AtomicToNonAtomic,
    NonAtomicToAtomic,
}

/// Represents a unary operator in C (6.5.3 Unary operators) and GNU C extensions
#[derive(Debug, Clone, Copy)]
pub enum UnOp {
    AddressOf,     // &x
    Deref,         // *x
    Plus,          // +x
    PostIncrement, // x++
    PreIncrement,  // ++x
    Negate,        // -x
    PostDecrement, // x--
    PreDecrement,  // --x
    Complement,    // ~x
    Not,           // !x
    Real,          // [GNU C] __real x
    Imag,          // [GNU C] __imag x
    Extension,     // [GNU C] __extension__ x
    Coawait,       // [C++ Coroutines] co_await x
}

impl UnOp {
    pub fn as_str(&self) -> &'static str {
        use UnOp::*;
        match self {
            AddressOf => "&",
            Deref => "*",
            Plus => "+",
            PreIncrement => "++",
            PostIncrement => "++",
            Negate => "-",
            PreDecrement => "--",
            PostDecrement => "--",
            Complement => "~",
            Not => "!",
            Real => "__real",
            Imag => "__imag",
            Extension => "__extension__",
            Coawait => "co_await",
        }
    }

    /// Obtain the expected type of a unary expression based on the operator and its argument type
    pub fn expected_result_type(
        &self,
        ast_context: &TypedAstContext,
        arg_type: CQualTypeId,
    ) -> Option<CQualTypeId> {
        use UnOp::*;
        let resolved_ty = ast_context.resolve_type(arg_type.ctype);
        Some(match self {
            // We could construct CTypeKind::Pointer here, but it is not guaranteed to have a
            // corresponding `CTypeId` in the `TypedAstContext`, so bail out instead
            AddressOf => return None,
            Deref => {
                if let CTypeKind::Pointer(inner) = resolved_ty.kind {
                    inner
                } else {
                    panic!("dereferencing non-pointer type!")
                }
            }
            Not => {
                return ast_context
                    .type_for_kind(&CTypeKind::Int)
                    .map(CQualTypeId::new);
            }
            Real | Imag => {
                if let CTypeKind::Complex(inner) = resolved_ty.kind {
                    CQualTypeId::new(inner)
                } else {
                    panic!("__real or __imag applied to non-complex type!")
                }
            }
            Coawait => panic!("trying to propagate co_await type"),
            _ => CQualTypeId::new(arg_type.ctype),
        })
    }
}

impl Display for UnOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

/// Represents a unary type operator in C
#[derive(Debug, Clone, Copy)]
pub enum UnTypeOp {
    SizeOf,
    AlignOf,
    PreferredAlignOf,
}

impl UnTypeOp {
    pub fn as_str(&self) -> &'static str {
        use UnTypeOp::*;
        match self {
            SizeOf => "sizeof",
            AlignOf => "alignof",
            PreferredAlignOf => "__alignof",
        }
    }
}

impl Display for UnTypeOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl UnOp {
    /// Check is the operator is rendered before or after is operand.
    pub fn is_prefix(&self) -> bool {
        !matches!(*self, UnOp::PostIncrement | UnOp::PostDecrement)
    }
}

/// Represents a binary operator in C (6.5.5 Multiplicative operators - 6.5.14 Logical OR operator)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Multiply,     // *
    Divide,       // /
    Modulus,      // %
    Add,          // +
    Subtract,     // -
    ShiftLeft,    // <<
    ShiftRight,   // >>
    Less,         // <
    Greater,      // >
    LessEqual,    // <=
    GreaterEqual, // >=
    EqualEqual,   // ==
    NotEqual,     // !=
    BitAnd,       // &
    BitXor,       // ^
    BitOr,        // |
    And,          // &&
    Or,           // ||

    AssignAdd,        // +=
    AssignSubtract,   // -=
    AssignMultiply,   // *=
    AssignDivide,     // /=
    AssignModulus,    // %=
    AssignBitXor,     // ^=
    AssignShiftLeft,  // <<=
    AssignShiftRight, // >>=
    AssignBitOr,      // |=
    AssignBitAnd,     // &=

    Assign, // =
    Comma,  // ,
}

impl BinOp {
    pub fn as_str(&self) -> &'static str {
        use BinOp::*;
        match self {
            Multiply => "*",
            Divide => "/",
            Modulus => "%",
            Add => "+",
            Subtract => "-",
            ShiftLeft => "<<",
            ShiftRight => ">>",
            Less => "<",
            Greater => ">",
            LessEqual => "<=",
            GreaterEqual => ">=",
            EqualEqual => "==",
            NotEqual => "!=",
            BitAnd => "&",
            BitXor => "^",
            BitOr => "|",
            And => "&&",
            Or => "||",

            AssignAdd => "+=",
            AssignSubtract => "-=",
            AssignMultiply => "*=",
            AssignDivide => "/=",
            AssignModulus => "%=",
            AssignBitXor => "^=",
            AssignShiftLeft => "<<=",
            AssignShiftRight => ">>=",
            AssignBitOr => "|=",
            AssignBitAnd => "&=",

            Assign => "=",
            Comma => ", ",
        }
    }

    /// Does the rust equivalent of this operator have type (T, T) -> U?
    pub fn input_types_same(&self) -> bool {
        use BinOp::*;
        self.all_types_same()
            || matches!(
                self,
                Less | Greater
                    | LessEqual
                    | GreaterEqual
                    | EqualEqual
                    | NotEqual
                    | And
                    | Or
                    | AssignAdd
                    | AssignSubtract
                    | AssignMultiply
                    | AssignDivide
                    | AssignModulus
                    | AssignBitXor
                    | AssignShiftLeft
                    | AssignShiftRight
                    | AssignBitOr
                    | AssignBitAnd
                    | Assign
            )
    }

    /// Does the rust equivalent of this operator have type (T, T) -> T?
    /// This ignores cases where one argument is a pointer and we translate to `.offset()`.
    pub fn all_types_same(&self) -> bool {
        use BinOp::*;
        matches!(
            self,
            Multiply | Divide | Modulus | Add | Subtract | BitAnd | BitXor | BitOr
        )
    }
}

impl Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl BinOp {
    /// Maps compound assignment operators to operator underlying them, and returns `None` for all
    /// other operators.
    ///
    /// For example, `AssignAdd` maps to `Some(Add)` but `Add` maps to `None`.
    pub fn underlying_assignment(&self) -> Option<BinOp> {
        use BinOp::*;
        Some(match *self {
            AssignAdd => Add,
            AssignSubtract => Subtract,
            AssignMultiply => Multiply,
            AssignDivide => Divide,
            AssignModulus => Modulus,
            AssignBitXor => BitXor,
            AssignShiftLeft => ShiftLeft,
            AssignShiftRight => ShiftRight,
            AssignBitOr => BitOr,
            AssignBitAnd => BitAnd,
            _ => return None,
        })
    }

    /// Determines whether or not this is an assignment op
    pub fn is_assignment(&self) -> bool {
        matches!(self, Self::Assign) || self.underlying_assignment().is_some()
    }
}

/// The base of an integer literal.
#[derive(Eq, PartialEq, Debug, Copy, Clone)]
pub enum IntBase {
    /// Decimal.
    Dec,
    /// Hexadecimal.
    Hex,
    /// Octal.
    Oct,
}

/// A C literal.
#[derive(Debug, Clone)]
pub enum CLiteral {
    /// An integer literal.
    Integer(u64, IntBase), // value and base
    /// A character literal.
    Character(u64),
    /// A floating-point literal.
    Floating(f64, String),
    /// A string literal.
    String(Vec<u8>, u8), // Literal bytes and unit byte width
}

impl CLiteral {
    /// Determine the truthiness or falsiness of the literal.
    pub fn get_bool(&self) -> bool {
        use CLiteral::*;
        match *self {
            Integer(x, _) => x != 0u64,
            Character(x) => x != 0u64,
            Floating(x, _) => x != 0f64,
            _ => true,
        }
    }
}

/// Represents a constant integer expression as used in a case expression.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum ConstIntExpr {
    /// An unsigned integer.
    U(u64),
    /// A signed integer.
    I(i64),
}

/// Represents a statement in C (6.8 Statements).
///
/// Reflects the types in <http://clang.llvm.org/doxygen/classclang_1_1Stmt.html>
#[derive(Debug, Clone)]
pub enum CStmtKind {
    /// A labeled statement (6.8.1).
    ///
    /// All of these have a `CStmtId` to represent the substatement that comes
    /// after them.
    Label(CStmtId),
    /// A `case` statement.
    Case(CExprId, CStmtId, ConstIntExpr),
    /// A `default` statement.
    Default(CStmtId),

    /// A compound statement (6.8.2).
    Compound(Vec<CStmtId>),

    /// An expression statement (6.8.3).
    Expr(CExprId),
    /// A null statement (6.e.3).
    Empty,

    /// A selection statement (6.8.4).
    If {
        /// The scrutinee of the `if` statement.
        scrutinee: CExprId,
        /// The `then` branch of the `if` statement.
        true_variant: CStmtId,
        /// The `else` branch of the `if` statement.
        false_variant: Option<CStmtId>,
    },
    /// A `switch` statement.
    Switch {
        /// The scrutinee of the `switch` statement.
        scrutinee: CExprId,
        /// The body of the `switch` statement.
        body: CStmtId,
    },

    /// An iteration statement (6.8.5).
    While {
        /// The condition of the `while` loop.
        condition: CExprId,
        /// The body of the `while` loop.
        body: CStmtId,
    },
    /// A `do-while` loop.
    DoWhile {
        /// The body of the `do-while` loop.
        body: CStmtId,
        /// The condition of the `do-while` loop.
        condition: CExprId,
    },
    /// A `for` loop.
    ForLoop {
        /// The initializer of the `for` loop.
        init: Option<CStmtId>,
        /// The condition of the `for` loop.
        condition: Option<CExprId>,
        /// The increment of the `for` loop.
        increment: Option<CExprId>,
        /// The body of the `for` loop.
        body: CStmtId,
    },

    /// A jump statement (6.8.6).
    Goto(CLabelId),
    /// A `break` statement.
    Break,
    /// A `continue` statement.
    Continue,
    /// A `return` statement.
    Return(Option<CExprId>),

    /// A declaration statement.
    Decls(Vec<CDeclId>),

    /// A GCC-style inline assembly statement.
    Asm {
        /// The assembly code.
        asm: String,
        /// The input operands.
        inputs: Vec<AsmOperand>,
        /// The output operands.
        outputs: Vec<AsmOperand>,
        /// The clobbered registers.
        clobbers: Vec<String>,
        /// Whether the assembly is volatile.
        is_volatile: bool,
    },

    /// A statement with attributes.
    ///
    /// The substatement can be a NULL statement in case of
    /// `__attribute__((__fallthrough__))` at the end of a case statement.
    Attributed {
        /// The attributes.
        attributes: Vec<Attribute>,
        /// The substatement.
        substatement: CStmtId,
    },
}

/// An operand for an inline assembly statement.
#[derive(Clone, Debug)]
pub struct AsmOperand {
    /// The constraints on the operand.
    pub constraints: String,
    /// The expression for the operand.
    pub expression: CExprId,
}

/// Type qualifiers (6.7.3).
#[derive(Debug, Copy, Clone, Default, PartialEq, Eq)]
pub struct Qualifiers {
    /// The `const` qualifier, which marks lvalues as non-assignable.
    ///
    /// We make use of `const` in only two places:
    ///   * Variable and function bindings (which matches up to Rust's `mut` or not bindings)
    ///   * The pointed type in pointers (which matches up to Rust's `*const`/`*mut`)
    pub is_const: bool,

    /// The `restrict` qualifier.
    pub is_restrict: bool,

    /// The `volatile` qualifier, which prevents the compiler from reordering
    /// accesses through such qualified lvalues past other observable side
    /// effects (other accesses, or sequence points).
    ///
    /// The part here about not reordering (or changing in any way) access to
    /// something volatile can be replicated in Rust via `std::ptr::read_volatile`
    /// and `std::ptr::write_volatile`. Since Rust's execution model is still
    /// unclear, I am unsure that we get all of the guarantees `volatile` needs,
    /// especially regarding reordering of other side-effects.
    ///
    /// To see where we use `volatile`, check the call-sites of
    /// `Translation::volatile_write` and `Translation::volatile_read`.
    pub is_volatile: bool,
}

impl Qualifiers {
    /// Aggregate qualifier information from two sources.
    pub fn and(self, other: Qualifiers) -> Qualifiers {
        Qualifiers {
            is_const: self.is_const || other.is_const,
            is_restrict: self.is_restrict || other.is_restrict,
            is_volatile: self.is_volatile || other.is_volatile,
        }
    }
}

/// A qualified C type ID.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct CQualTypeId {
    /// The qualifiers of the type.
    pub qualifiers: Qualifiers,
    /// The ID of the type.
    pub ctype: CTypeId,
}

impl CQualTypeId {
    pub fn new(ctype: CTypeId) -> Self {
        Self {
            qualifiers: Qualifiers::default(),
            ctype,
        }
    }
}

// TODO: these may be interesting, but I'm not sure if they fit here:
//
//  * UnaryTransformType <http://clang.llvm.org/doxygen/classclang_1_1UnaryTransformType.html>
//  * AdjustedType <http://clang.llvm.org/doxygen/classclang_1_1AdjustedType.html>

/// Represents a type in C (6.2.5 Types).
///
/// Reflects the types in <http://clang.llvm.org/doxygen/classclang_1_1Type.html>
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CTypeKind {
    /// The `void` type.
    Void,

    /// The boolean type (6.2.5.2).
    Bool,

    /// The character type (6.2.5.3).
    Char,

    /// The signed integer types (6.2.5.4).
    SChar,
    /// The signed integer types (6.2.5.4).
    Short,
    /// The signed integer types (6.2.5.4).
    Int,
    /// The signed integer types (6.2.5.4).
    Long,
    /// The signed integer types (6.2.5.4).
    LongLong,

    /// The unsigned integer types (6.2.5.6).
    UChar,
    /// The unsigned integer types (6.2.5.6).
    UShort,
    /// The unsigned integer types (6.2.5.6).
    UInt,
    /// The unsigned integer types (6.2.5.6).
    ULong,
    /// The unsigned integer types (6.2.5.6).
    ULongLong,

    /// The real floating types (6.2.5.10). Ex: `double`.
    Float,
    /// The real floating types (6.2.5.10). Ex: `double`.
    Double,
    /// The real floating types (6.2.5.10). Ex: `double`.
    LongDouble,

    /// Clang-specific 128-bit integer types.
    Int128,
    /// Clang-specific 128-bit integer types.
    UInt128,

    /// A complex number type.
    Complex(CTypeId),

    /// A pointer type (6.7.5.1).
    Pointer(CQualTypeId),

    /// A C++ reference type.
    Reference(CQualTypeId),

    /// An array type (6.7.5.2).
    ///
    /// A qualifier on an array type means the same thing as a qualifier on its
    /// element type. Since Clang tracks the qualifiers in both places, we
    /// choose to discard qualifiers on the element type.
    ///
    /// The size expression on a variable-length array is optional, it might be
    /// replaced with `*`.
    ConstantArray(CTypeId, usize),
    /// An incomplete array type.
    IncompleteArray(CTypeId),
    /// A variable-length array type.
    VariableArray(CTypeId, Option<CExprId>),

    /// A `typeof` type (a GCC extension).
    TypeOf(CTypeId),
    /// A `typeof` expression (a GCC extension).
    TypeOfExpr(CExprId),

    /// A function type (6.7.5.3).
    ///
    /// Note a function taking no arguments should have one `void` argument.
    /// Functions without any arguments are in K&R format.
    ///
    /// Flags: is_variable_argument, is_noreturn, has prototype
    Function(CQualTypeId, Vec<CQualTypeId>, bool, bool, bool),

    /// A typedef type (6.7.7).
    Typedef(CTypedefId),

    /// A decayed pointer type.
    Decayed(CTypeId),
    /// An elaborated type.
    Elaborated(CTypeId),

    /// A type wrapped in parentheses.
    Paren(CTypeId),

    /// A struct type.
    Struct(CRecordId),

    /// A union type.
    Union(CRecordId),

    /// An enum type.
    Enum(CEnumId),

    /// A built-in function type.
    BuiltinFn,

    /// An attributed type.
    Attributed(CQualTypeId, Option<Attribute>),
    /// A `counted_by` or `sized_by` attributed type.
    CountAttributed(CQualTypeId, CountAttribute, CExprId),

    /// A block pointer type.
    BlockPointer(CQualTypeId),

    /// A vector type.
    Vector(CQualTypeId, usize),

    /// A 16-bit floating-point type.
    Half,
    /// A 16-bit floating-point type.
    BFloat16,

    /// An ARM Scalable Vector Extension type.
    // TODO: represent all the individual types in AArch64SVEACLETypes.def
    UnhandledSveType,

    /// A 128-bit floating-point type.
    Float128,
    /// An atomic type (6.7.2.4).
    Atomic(CQualTypeId),

    // Rust sized types, pullback'd into C so that we can treat uint16_t, etc. as real types.
    /// `int8_t`
    Int8,
    /// `int16_t`
    Int16,
    /// `int32_t`
    Int32,
    /// `int64_t`
    Int64,
    /// `intptr_t`
    IntPtr,
    /// `uint8_t`
    UInt8,
    /// `uint16_t`
    UInt16,
    /// `uint32_t`
    UInt32,
    /// `uint64_t`
    UInt64,
    /// `uintptr_t`
    UIntPtr,
    /// `intmax_t`
    IntMax,
    /// `uintmax_t`
    UIntMax,
    /// `size_t`
    Size,
    /// `ssize_t`
    SSize,
    /// `ptrdiff_t`
    PtrDiff,
    /// `wchar_t`
    WChar,
}

impl CTypeKind {
    pub const PULLBACK_KINDS: [CTypeKind; 16] = {
        use CTypeKind::*;
        [
            Int8, Int16, Int32, Int64, IntPtr, UInt8, UInt16, UInt32, UInt64, UIntPtr, IntMax,
            UIntMax, Size, SSize, PtrDiff, WChar,
        ]
    };

    pub fn as_str(&self) -> &'static str {
        use CTypeKind::*;
        match self {
            Void => "void",
            Bool => "_Bool",
            Char => "char",
            SChar => "signed char",
            Short => "signed short",
            Int => "int",
            Long => "long",
            LongLong => "long long",
            UChar => "unsigned char",
            UShort => "unsigned short",
            UInt => "unsigned int",
            ULong => "unsigned long",
            ULongLong => "unsigned long long",
            Float => "float",
            Double => "double",
            LongDouble => "long double",
            Int128 => "__int128",
            UInt128 => "unsigned __int128",
            Half => "half",
            BFloat16 => "bfloat16",
            Float128 => "__float128",

            Int8 => "int8_t",
            Int16 => "int16_t",
            Int32 => "int32_t",
            Int64 => "int64_t",
            IntPtr => "intptr_t",
            UInt8 => "uint8_t",
            UInt16 => "uint16_t",
            UInt32 => "uint32_t",
            UInt64 => "uint64_t",
            UIntPtr => "uintptr_t",
            IntMax => "intmax_t",
            UIntMax => "uintmax_t",
            Size => "size_t",
            SSize => "ssize_t",
            PtrDiff => "ptrdiff_t",
            WChar => "wchar_t",

            _ => unimplemented!("Printer::print_type({:?})", self),
        }
    }
}

impl Display for CTypeKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

/// A C designator.
#[derive(Copy, Clone, Debug)]
pub enum Designator {
    /// An array index designator.
    Index(u64),
    /// A range designator.
    Range(u64, u64),
    /// A field designator.
    Field(CFieldId),
}

/// An enumeration of supported attributes for declarations.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum Attribute {
    /// `__attribute__((alias("foo")))`
    Alias(String),
    /// `__attribute__((always_inline))`
    AlwaysInline,
    /// `__attribute__((cold))`
    Cold,
    /// `__attribute__((gnu_inline))`
    GnuInline,
    /// `__attribute__((no_inline))`
    NoInline,
    /// `__attribute__((noreturn))`
    NoReturn,
    /// `__attribute__((nonnull))`
    NotNull,
    /// `__attribute__((nullable))`
    Nullable,
    /// `__attribute__((section("foo")))`
    Section(String),
    /// `__attribute__((used))`
    Used,
    /// `__attribute__((visibility("hidden")))`
    Visibility(String),
    /// `__attribute__((fallthrough))`
    Fallthrough,
}

/// An enumeration of supported `counted_by` and `sized_by` attributes.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub enum CountAttribute {
    /// `__attribute__((counted_by(field)))`
    CountedBy,
    /// `__attribute__((sized_by(field)))`
    SizedBy,
    /// `__attribute__((counted_by_or_null(field)))`
    CountedByOrNull,
    /// `__attribute__((sized_by_or_null(field)))`
    SizedByOrNull,
}

impl CTypeKind {
    pub fn is_pointer(&self) -> bool {
        matches!(*self, Self::Pointer { .. })
    }

    pub fn is_bool(&self) -> bool {
        matches!(*self, Self::Bool)
    }

    pub fn is_enum(&self) -> bool {
        matches!(*self, Self::Enum { .. })
    }

    pub fn is_integral_type(&self) -> bool {
        self.is_unsigned_integral_type() || self.is_signed_integral_type()
    }

    pub fn is_unsigned_integral_type(&self) -> bool {
        use CTypeKind::*;
        matches!(
            self,
            Bool | UChar
                | UInt
                | UShort
                | ULong
                | ULongLong
                | UInt128
                | UInt8
                | UInt16
                | UInt32
                | UInt64
                | UIntPtr
                | UIntMax
                | Size
                | WChar
        )
    }

    pub fn is_signed_integral_type(&self) -> bool {
        use CTypeKind::*;
        // `Char` is true on the platforms we handle
        matches!(
            self,
            Char | SChar
                | Int
                | Short
                | Long
                | LongLong
                | Int128
                | Int8
                | Int16
                | Int32
                | Int64
                | IntPtr
                | IntMax
                | SSize
                | PtrDiff
        )
    }

    pub fn is_floating_type(&self) -> bool {
        use CTypeKind::*;
        matches!(self, Float | Double | LongDouble)
    }

    pub fn as_underlying_decl(&self) -> Option<CDeclId> {
        use CTypeKind::*;
        match *self {
            Struct(decl_id) | Union(decl_id) | Enum(decl_id) => Some(decl_id),
            _ => None,
        }
    }

    pub fn as_decl_or_typedef(&self) -> Option<CDeclId> {
        use CTypeKind::*;
        match *self {
            Typedef(decl_id) | Struct(decl_id) | Union(decl_id) | Enum(decl_id) => Some(decl_id),
            _ => None,
        }
    }

    pub fn is_vector(&self) -> bool {
        matches!(self, Self::Vector { .. })
    }

    /// Choose the smaller, simpler of the two types if they are cast-compatible.
    pub fn smaller_compatible_type(ty1: CTypeKind, ty2: CTypeKind) -> Option<CTypeKind> {
        let int = Self::is_integral_type;
        let float = Self::is_floating_type;

        use CTypeKind::*;
        let ty = match (&ty1, &ty2) {
            (ty, ty2) if ty == ty2 => ty1,
            (Void, _) => ty2,
            (Bool, ty) | (ty, Bool) if int(ty) => Bool,

            (Char, ty) | (ty, Char) if int(ty) => Char,
            (SChar, ty) | (ty, SChar) if int(ty) => SChar,
            (UChar, ty) | (ty, UChar) if int(ty) => UChar,

            (Short, ty) | (ty, Short) if int(ty) => Short,
            (UShort, ty) | (ty, UShort) if int(ty) => UShort,

            (Int, ty) | (ty, Int) if int(ty) => Int,
            (UInt, ty) | (ty, UInt) if int(ty) => UInt,

            (Float, ty) | (ty, Float) if float(ty) || int(ty) => Float,

            (Long, ty) | (ty, Long) if int(ty) => Long,
            (ULong, ty) | (ty, ULong) if int(ty) => ULong,

            (Double, ty) | (ty, Double) if float(ty) || int(ty) => Double,

            (LongLong, ty) | (ty, LongLong) if int(ty) => LongLong,
            (ULongLong, ty) | (ty, ULongLong) if int(ty) => ULongLong,

            (LongDouble, ty) | (ty, LongDouble) if float(ty) || int(ty) => LongDouble,

            (Int128, ty) | (ty, Int128) if int(ty) => Int128,
            (UInt128, ty) | (ty, UInt128) if int(ty) => UInt128,

            // Integer to pointer conversion. We want to keep the integer and
            // cast to a pointer at use.
            (Pointer(_), ty) if int(ty) => ty2,
            (ty, Pointer(_)) if int(ty) => ty1,

            // Array to pointer decay. We want to use the array and push the
            // decay to the use of the value.
            (Pointer(ptr_ty), ConstantArray(arr_ty, _))
            | (Pointer(ptr_ty), IncompleteArray(arr_ty))
            | (Pointer(ptr_ty), VariableArray(arr_ty, _))
                if ptr_ty.ctype == *arr_ty =>
            {
                ty2
            }
            (ConstantArray(arr_ty, _), Pointer(ptr_ty))
            | (IncompleteArray(arr_ty), Pointer(ptr_ty))
            | (VariableArray(arr_ty, _), Pointer(ptr_ty))
                if ptr_ty.ctype == *arr_ty =>
            {
                ty1
            }

            _ => return None,
        };
        Some(ty)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_compare_src_locs_ord() {
        let ctx = TypedAstContext {
            c_types: Default::default(),
            c_exprs: Default::default(),
            c_stmts: Default::default(),
            c_decls: Default::default(),
            c_decls_top: vec![],
            c_main: None,
            parents: Default::default(),
            files: vec![],
            file_map: vec![0, 1, 2, 3, 4, 5, 4, 5],
            include_map: vec![
                vec![],
                vec![],
                vec![SrcLoc {
                    fileid: 2,
                    line: 6,
                    column: 10,
                }],
                vec![],
                vec![],
                vec![SrcLoc {
                    fileid: 5,
                    line: 6,
                    column: 10,
                }],
            ],
            label_names: Default::default(),
            macro_invocations: Default::default(),
            macro_expansions: Default::default(),
            macro_expansion_text: Default::default(),
            comments: vec![],
            prenamed_decls: Default::default(),
            va_list_kind: BuiltinVaListKind::CharPtrBuiltinVaList,
            target: "".to_string(),
        };
        let locs = &mut [
            SrcLoc {
                fileid: 5,
                line: 5,
                column: 1,
            },
            SrcLoc {
                fileid: 5,
                line: 5,
                column: 1,
            },
            SrcLoc {
                fileid: 1,
                line: 5,
                column: 1,
            },
            SrcLoc {
                fileid: 1,
                line: 5,
                column: 1,
            },
            SrcLoc {
                fileid: 1,
                line: 10,
                column: 1,
            },
            SrcLoc {
                fileid: 1,
                line: 5,
                column: 1,
            },
            SrcLoc {
                fileid: 2,
                line: 4,
                column: 1,
            },
            SrcLoc {
                fileid: 5,
                line: 3,
                column: 7,
            },
            SrcLoc {
                fileid: 5,
                line: 3,
                column: 1,
            },
            SrcLoc {
                fileid: 5,
                line: 3,
                column: 1,
            },
            SrcLoc {
                fileid: 5,
                line: 5,
                column: 7,
            },
            SrcLoc {
                fileid: 5,
                line: 5,
                column: 1,
            },
            SrcLoc {
                fileid: 5,
                line: 5,
                column: 1,
            },
            SrcLoc {
                fileid: 5,
                line: 5,
                column: 7,
            },
            SrcLoc {
                fileid: 5,
                line: 7,
                column: 7,
            },
            SrcLoc {
                fileid: 5,
                line: 7,
                column: 1,
            },
            SrcLoc {
                fileid: 5,
                line: 7,
                column: 1,
            },
            SrcLoc {
                fileid: 5,
                line: 9,
                column: 7,
            },
            SrcLoc {
                fileid: 5,
                line: 9,
                column: 1,
            },
            SrcLoc {
                fileid: 5,
                line: 9,
                column: 1,
            },
            SrcLoc {
                fileid: 5,
                line: 5,
                column: 7,
            },
            SrcLoc {
                fileid: 5,
                line: 5,
                column: 1,
            },
            SrcLoc {
                fileid: 5,
                line: 5,
                column: 1,
            },
            SrcLoc {
                fileid: 5,
                line: 8,
                column: 3,
            },
            SrcLoc {
                fileid: 5,
                line: 8,
                column: 1,
            },
            SrcLoc {
                fileid: 5,
                line: 7,
                column: 1,
            },
            SrcLoc {
                fileid: 5,
                line: 0,
                column: 4,
            },
            SrcLoc {
                fileid: 5,
                line: 0,
                column: 1,
            },
            SrcLoc {
                fileid: 5,
                line: 2,
                column: 1,
            },
            SrcLoc {
                fileid: 5,
                line: 98,
                column: 3,
            },
            SrcLoc {
                fileid: 5,
                line: 98,
                column: 1,
            },
            SrcLoc {
                fileid: 5,
                line: 202,
                column: 1,
            },
            SrcLoc {
                fileid: 5,
                line: 202,
                column: 1,
            },
            SrcLoc {
                fileid: 7,
                line: 1,
                column: 1,
            },
            SrcLoc {
                fileid: 7,
                line: 3,
                column: 1,
            },
        ];

        let n = locs.len();
        for i in 0..n {
            let a = locs[i];
            for j in 0..n {
                let b = locs[j];
                for k in 0..n {
                    let c = locs[k];
                    let ab = ctx.compare_src_locs(&a, &b);
                    let bc = ctx.compare_src_locs(&b, &c);
                    let ac = ctx.compare_src_locs(&a, &c);
                    if ab == bc {
                        let [ab, bc, ac] = [ab, bc, ac].map(|ord| match ord {
                            Ordering::Less => "<",
                            Ordering::Equal => "==",
                            Ordering::Greater => ">",
                        });
                        assert_eq!(
                            ab, ac,
                            "Total order (transitivity) has been violated: {a} {ab} {b} and {b} {bc} {c}, but {a} {ac} {c}"
                        );
                    }
                }
            }
        }

        // This should not panic
        locs.sort_unstable_by(|a, b| ctx.compare_src_locs(a, b));
    }
}
