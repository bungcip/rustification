use serde_bytes::ByteBuf;
use serde_cbor::error;
use std::collections::{HashMap, VecDeque};
use std::convert::TryInto;
use std::fmt::{Display, Formatter};
use std::path::{Path, PathBuf};
use std::{self, fmt};

pub use serde_cbor::value::{Value, from_value};

include!(concat!(env!("OUT_DIR"), "/bindings.rs"));

/// Represents whether an expression is an lvalue or an rvalue.
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum LRValue {
    /// The expression is an lvalue.
    LValue,
    /// The expression is an rvalue.
    RValue,
}

impl LRValue {
    /// Returns `true` if the value is an lvalue.
    pub fn is_lvalue(&self) -> bool {
        *self == LRValue::LValue
    }
    /// Returns `true` if the value is an rvalue.
    pub fn is_rvalue(&self) -> bool {
        *self == LRValue::RValue
    }
}

/// Represents a source location.
#[derive(Copy, Debug, Clone, PartialOrd, PartialEq, Ord, Eq)]
pub struct SrcLoc {
    /// The ID of the file.
    pub fileid: u64,
    /// The line number.
    pub line: u64,
    /// The column number.
    pub column: u64,
}

impl Display for SrcLoc {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let Self {
            fileid,
            line,
            column,
        } = *self;
        write!(f, "file_{fileid}:{line}:{column}")
    }
}

/// Represents a source span.
#[derive(Copy, Debug, Clone, PartialOrd, PartialEq, Ord, Eq)]
pub struct SrcSpan {
    /// The ID of the file.
    pub fileid: u64,
    /// The beginning line number.
    pub begin_line: u64,
    /// The beginning column number.
    pub begin_column: u64,
    /// The ending line number.
    pub end_line: u64,
    /// The ending column number.
    pub end_column: u64,
}

impl Display for SrcSpan {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let Self {
            fileid,
            begin_line,
            begin_column,
            end_line,
            end_column,
        } = *self;
        write!(
            f,
            "file_{fileid}:{begin_line}:{begin_column}-{end_line}:{end_column}"
        )
    }
}

impl From<SrcLoc> for SrcSpan {
    fn from(loc: SrcLoc) -> Self {
        Self {
            fileid: loc.fileid,
            begin_line: loc.line,
            begin_column: loc.column,
            end_line: loc.line,
            end_column: loc.column,
        }
    }
}

impl SrcSpan {
    pub fn begin(&self) -> SrcLoc {
        SrcLoc {
            fileid: self.fileid,
            line: self.begin_line,
            column: self.begin_column,
        }
    }
    pub fn end(&self) -> SrcLoc {
        SrcLoc {
            fileid: self.fileid,
            line: self.end_line,
            column: self.end_column,
        }
    }
}

/// Represents a node in the Clang AST.
#[derive(Debug, Clone)]
pub struct AstNode {
    /// The tag of the AST node.
    pub tag: ASTEntryTag,
    /// The children of the AST node.
    pub children: Vec<Option<u64>>,
    /// The source location of the AST node.
    pub loc: SrcSpan,
    /// The type ID of the AST node.
    pub type_id: Option<u64>,
    /// Whether the expression is an lvalue or an rvalue.
    pub rvalue: LRValue,

    /// Stack of macros this node was expanded from, beginning with the initial
    /// macro call and ending with the leaf. This needs to be a stack for nested
    /// macro definitions.
    pub macro_expansions: Vec<u64>,
    /// The text of the macro expansion.
    pub macro_expansion_text: Option<String>,
    /// Extra data associated with the AST node.
    pub extras: Vec<Value>,
}

/// Represents a type in the Clang AST.
#[derive(Debug, Clone)]
pub struct TypeNode {
    /// The tag of the type.
    pub tag: TypeTag,
    /// Extra data associated with the type.
    pub extras: Vec<Value>,
}

/// Represents a comment in the source code.
#[derive(Debug, Clone)]
pub struct CommentNode {
    /// The source location of the comment.
    pub loc: SrcLoc,
    /// The text of the comment.
    pub string: String,
}

/// Represents a source file.
#[derive(Debug, Clone)]
pub struct SrcFile {
    /// The path to the source file.
    pub path: Option<PathBuf>,
    /// The location where the file was included, if any.
    pub include_loc: Option<SrcLoc>,
}

impl TypeNode {
    // Masks used to decode the IDs given to type nodes
    pub const ID_MASK: u64 = !0b111;
    pub const CONST_MASK: u64 = 0b001;
    pub const RESTRICT_MASK: u64 = 0b010;
    pub const VOLATILE_MASK: u64 = 0b100;
}

/// Represents the context of a Clang AST.
#[derive(Debug, Clone)]
pub struct AstContext {
    /// The AST nodes in the context.
    pub ast_nodes: HashMap<u64, AstNode>,
    /// The type nodes in the context.
    pub type_nodes: HashMap<u64, TypeNode>,
    /// The top-level AST nodes in the context.
    pub top_nodes: Vec<u64>,
    /// The comments in the source code.
    pub comments: Vec<CommentNode>,
    /// The source files in the context.
    pub files: Vec<SrcFile>,
    /// The kind of `va_list` used in the source code.
    pub va_list_kind: BuiltinVaListKind,
    /// The target triple.
    pub target: String,
}

/// A helper function that expects an optional string.
pub fn expect_opt_str(val: &Value) -> Option<Option<&str>> {
    match *val {
        Value::Null => Some(None),
        Value::Text(ref s) => Some(Some(s)),
        _ => None,
    }
}

/// A helper function that expects an optional u64.
pub fn expect_opt_u64(val: &Value) -> Option<Option<u64>> {
    match *val {
        Value::Null => Some(None),
        Value::Integer(n) => Some(Some(n.try_into().unwrap())),
        _ => None,
    }
}

/// A helper function that converts a u64 to an `ASTEntryTag`.
fn import_ast_tag(tag: u64) -> ASTEntryTag {
    unsafe { std::mem::transmute::<u32, ASTEntryTag>(tag as u32) }
}

/// A helper function that converts a u64 to a `TypeTag`.
fn import_type_tag(tag: u64) -> TypeTag {
    unsafe { std::mem::transmute::<u32, TypeTag>(tag as u32) }
}

/// A helper function that converts a u64 to a `BuiltinVaListKind`.
fn import_va_list_kind(tag: u64) -> BuiltinVaListKind {
    unsafe { std::mem::transmute::<u32, BuiltinVaListKind>(tag as u32) }
}

/// Process the CBOR representation of the Clang AST into an `AstContext`.
pub fn process(items: Value) -> error::Result<AstContext> {
    let mut asts: HashMap<u64, AstNode> = HashMap::new();
    let mut types: HashMap<u64, TypeNode> = HashMap::new();
    let mut comments: Vec<CommentNode> = vec![];

    type AllNode = VecDeque<Value>;
    type TopNode = u64;
    type File = (String, Option<(u64, u64, u64)>);
    type RawComment = (u64, u64, u64, ByteBuf);
    type VaListKind = u64;
    type Target = String;
    let (all_nodes, top_nodes, files, raw_comments, va_list_kind, target): (
        Vec<AllNode>,
        Vec<TopNode>,
        Vec<File>,
        Vec<RawComment>,
        VaListKind,
        Target,
    ) = from_value(items)?;

    let va_list_kind = import_va_list_kind(va_list_kind);

    for (fileid, line, column, bytes) in raw_comments {
        comments.push(CommentNode {
            loc: SrcLoc {
                fileid,
                line,
                column,
            },
            string: String::from_utf8_lossy(&bytes).to_string(),
        })
    }

    let files = files
        .into_iter()
        .map(|(path, loc)| {
            let path = match path.as_str() {
                "" => None,
                "?" => None,
                path => Some(Path::new(path).to_path_buf()),
            };
            SrcFile {
                path,
                include_loc: loc.map(|(fileid, line, column)| SrcLoc {
                    fileid,
                    line,
                    column,
                }),
            }
        })
        .collect::<Vec<_>>();

    for mut entry in all_nodes.into_iter() {
        let entry_id: u64 = from_value(entry.pop_front().unwrap()).unwrap();
        let tag = from_value(entry.pop_front().unwrap()).unwrap();

        // Tags before the first type tag indicate AST nodes, after indicate type nodes.
        if tag < TypeTag::TagTypeUnknown as _ {
            let children = from_value::<Vec<Value>>(entry.pop_front().unwrap())
                .unwrap()
                .iter()
                .map(|x| expect_opt_u64(x).unwrap())
                .collect::<Vec<Option<u64>>>();

            // entry[3]
            let fileid = from_value(entry.pop_front().unwrap()).unwrap();
            let begin_line = from_value(entry.pop_front().unwrap()).unwrap();
            let begin_column = from_value(entry.pop_front().unwrap()).unwrap();
            let end_line = from_value(entry.pop_front().unwrap()).unwrap();
            let end_column = from_value(entry.pop_front().unwrap()).unwrap();

            // entry[8]
            let type_id: Option<u64> = expect_opt_u64(&entry.pop_front().unwrap()).unwrap();

            // entry[9]
            let rvalue = if from_value(entry.pop_front().unwrap()).unwrap() {
                LRValue::RValue
            } else {
                LRValue::LValue
            };

            // entry[10]
            let macro_expansions = from_value::<Vec<u64>>(entry.pop_front().unwrap()).unwrap();

            let macro_expansion_text = expect_opt_str(&entry.pop_front().unwrap())
                .unwrap()
                .map(|s| s.to_string());

            let node = AstNode {
                tag: import_ast_tag(tag),
                children,
                loc: SrcSpan {
                    fileid,
                    begin_line,
                    begin_column,
                    end_line,
                    end_column,
                },
                type_id,
                rvalue,
                macro_expansions,
                macro_expansion_text,
                extras: entry.into_iter().collect(),
            };

            asts.insert(entry_id, node);
        } else {
            let node = TypeNode {
                tag: import_type_tag(tag),
                extras: entry.into_iter().collect(),
            };

            types.insert(entry_id, node);
        }
    }
    Ok(AstContext {
        top_nodes,
        ast_nodes: asts,
        type_nodes: types,
        comments,
        files,
        va_list_kind,
        target,
    })
}
