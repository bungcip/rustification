use crate::attr::Attribute;
#[cfg(feature = "full")]
use crate::generics::BoundLifetimes;
use crate::ident::Ident;
#[cfg(feature = "full")]
use crate::lifetime::Lifetime;
use crate::lit::Lit;
use crate::mac::Macro;
use crate::op::{BinOp, UnOp};
#[cfg(feature = "full")]
use crate::pat::Pat;
use crate::path::{AngleBracketedGenericArguments, Path, QSelf};
use crate::punctuated::Punctuated;
#[cfg(feature = "full")]
use crate::stmt::Block;
use crate::token;
#[cfg(feature = "full")]
use crate::ty::ReturnType;
use crate::ty::Type;
use proc_macro2::{Span, TokenStream};
#[cfg(feature = "printing")]
use quote::IdentFragment;
#[cfg(feature = "printing")]
use std::fmt::{self, Display};
use std::hash::{Hash, Hasher};

ast_enum_of_structs! {
    /// A Rust expression.
    ///
    /// *This type is available only if Syn is built with the `"derive"` or `"full"`
    /// feature, but most of the variants are not available unless "full" is enabled.*
    ///
    /// # Syntax tree enums
    ///
    /// This type is a syntax tree enum. In Syn this and other syntax tree enums
    /// are designed to be traversed using the following rebinding idiom.
    ///
    /// ```
    /// # use rast::Expr;
    /// #
    /// # fn example(expr: Expr) {
    /// # const IGNORE: &str = stringify! {
    /// let expr: Expr = /* ... */;
    /// # };
    /// match expr {
    ///     Expr::MethodCall(expr) => {
    ///         /* ... */
    ///     }
    ///     Expr::Cast(expr) => {
    ///         /* ... */
    ///     }
    ///     Expr::If(expr) => {
    ///         /* ... */
    ///     }
    ///
    ///     /* ... */
    ///     # _ => {}
    /// # }
    /// # }
    /// ```
    ///
    /// We begin with a variable `expr` of type `Expr` that has no fields
    /// (because it is an enum), and by matching on it and rebinding a variable
    /// with the same name `expr` we effectively imbue our variable with all of
    /// the data fields provided by the variant that it turned out to be. So for
    /// example above if we ended up in the `MethodCall` case then we get to use
    /// `expr.receiver`, `expr.args` etc; if we ended up in the `If` case we get
    /// to use `expr.cond`, `expr.then_branch`, `expr.else_branch`.
    ///
    /// This approach avoids repeating the variant names twice on every line.
    ///
    /// ```
    /// # use rast::{Expr, ExprMethodCall};
    /// #
    /// # fn example(expr: Expr) {
    /// // Repetitive; recommend not doing this.
    /// match expr {
    ///     Expr::MethodCall(ExprMethodCall { method, args, .. }) => {
    /// # }
    /// # _ => {}
    /// # }
    /// # }
    /// ```
    ///
    /// In general, the name to which a syntax tree enum variant is bound should
    /// be a suitable name for the complete syntax tree enum type.
    ///
    /// ```
    /// # use rast::{Expr, ExprField};
    /// #
    /// # fn example(discriminant: ExprField) {
    /// // Binding is called `base` which is the name I would use if I were
    /// // assigning `*discriminant.base` without an `if let`.
    /// if let Expr::Tuple(base) = *discriminant.base {
    /// # }
    /// # }
    /// ```
    ///
    /// A sign that you may not be choosing the right variable names is if you
    /// see names getting repeated in your code, like accessing
    /// `receiver.receiver` or `pat.pat` or `cond.cond`.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    #[non_exhaustive]
    pub enum Expr {
        /// A slice literal expression: `[a, b, c, d]`.
        Array(ExprArray),

        /// An assignment expression: `a = compute()`.
        Assign(ExprAssign),

        /// An async block: `async { ... }`.
        Async(ExprAsync),

        /// An await expression: `fut.await`.
        Await(ExprAwait),

        /// A binary operation: `a + b`, `a += b`.
        Binary(ExprBinary),

        /// A blocked scope: `{ ... }`.
        Block(ExprBlock),

        /// A `break`, with an optional label to break and an optional
        /// expression.
        Break(ExprBreak),

        /// A function call expression: `invoke(a, b)`.
        Call(ExprCall),

        /// A cast expression: `foo as f64`.
        Cast(ExprCast),

        /// A closure expression: `|a, b| a + b`.
        Closure(ExprClosure),

        /// A const block: `const { ... }`.
        Const(ExprConst),

        /// A `continue`, with an optional label.
        Continue(ExprContinue),

        /// Access of a named struct field (`obj.k`) or unnamed tuple struct
        /// field (`obj.0`).
        Field(ExprField),

        /// A for loop: `for pat in expr { ... }`.
        ForLoop(ExprForLoop),

        /// An expression contained within invisible delimiters.
        ///
        /// This variant is important for faithfully representing the precedence
        /// of expressions and is related to `None`-delimited spans in a
        /// `TokenStream`.
        Group(ExprGroup),

        /// An `if` expression with an optional `else` block: `if expr { ... }
        /// else { ... }`.
        ///
        /// The `else` branch expression may only be an `If` or `Block`
        /// expression, not any of the other types of expression.
        If(ExprIf),

        /// A square bracketed indexing expression: `vector[2]`.
        Index(ExprIndex),

        /// The inferred value of a const generic argument, denoted `_`.
        Infer(ExprInfer),

        /// A `let` guard: `let Some(x) = opt`.
        Let(ExprLet),

        /// A literal in place of an expression: `1`, `"foo"`.
        Lit(ExprLit),

        /// Conditionless loop: `loop { ... }`.
        Loop(ExprLoop),

        /// A macro invocation expression: `format!("{}", q)`.
        Macro(ExprMacro),

        /// A `match` expression: `match n { Some(n) => {}, None => {} }`.
        Match(ExprMatch),

        /// A method call expression: `x.foo::<T>(a, b)`.
        MethodCall(ExprMethodCall),

        /// A parenthesized expression: `(a + b)`.
        Paren(ExprParen),

        /// A path like `std::mem::replace` possibly containing generic
        /// parameters and a qualified self-type.
        ///
        /// A plain identifier like `x` is a path of length 1.
        Path(ExprPath),

        /// A range expression: `1..2`, `1..`, `..2`, `1..=2`, `..=2`.
        Range(ExprRange),

        /// A referencing operation: `&a` or `&mut a`.
        Reference(ExprReference),

        /// An array literal constructed from one repeated element: `[0u8; N]`.
        Repeat(ExprRepeat),

        /// A `return`, with an optional value to be returned.
        Return(ExprReturn),

        /// A struct literal expression: `Point { x: 1, y: 1 }`.
        ///
        /// The `rest` provides the value of the remaining fields as in `S { a:
        /// 1, b: 1, ..rest }`.
        Struct(ExprStruct),

        /// A try-expression: `expr?`.
        Try(ExprTry),

        /// A try block: `try { ... }`.
        TryBlock(ExprTryBlock),

        /// A tuple expression: `(a, b, c, d)`.
        Tuple(ExprTuple),

        /// A unary operation: `!x`, `*x`.
        Unary(ExprUnary),

        /// An unsafe block: `unsafe { ... }`.
        Unsafe(ExprUnsafe),

        /// Tokens in expression position not interpreted by Syn.
        Verbatim(TokenStream),

        /// A while loop: `while expr { ... }`.
        While(ExprWhile),

        /// A yield expression: `yield expr`.
        Yield(ExprYield),

        // For testing exhaustiveness in downstream code, use the following idiom:
        //
        //     match expr {
        //         #![cfg_attr(test, deny(non_exhaustive_omitted_patterns))]
        //
        //         Expr::Array(expr) => {...}
        //         Expr::Assign(expr) => {...}
        //         ...
        //         Expr::Yield(expr) => {...}
        //
        //         _ => { /* some sane fallback */ }
        //     }
        //
        // This way we fail your tests but don't break your library when adding
        // a variant. You will be notified by a test failure when a variant is
        // added, so that you can add code to handle it, but your library will
        // continue to compile and work for downstream users in the interim.
    }
}

ast_struct! {
    /// A slice literal expression: `[a, b, c, d]`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct ExprArray #full {
        pub attrs: Vec<Attribute>,
        pub bracket_token: token::Bracket,
        pub elems: Punctuated<Expr, Token![,]>,
    }
}

ast_struct! {
    /// An assignment expression: `a = compute()`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct ExprAssign #full {
        pub attrs: Vec<Attribute>,
        pub left: Box<Expr>,
        pub eq_token: Token![=],
        pub right: Box<Expr>,
    }
}

ast_struct! {
    /// An async block: `async { ... }`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct ExprAsync #full {
        pub attrs: Vec<Attribute>,
        pub async_token: Token![async],
        pub capture: Option<Token![move]>,
        pub block: Block,
    }
}

ast_struct! {
    /// An await expression: `fut.await`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct ExprAwait #full {
        pub attrs: Vec<Attribute>,
        pub base: Box<Expr>,
        pub dot_token: Token![.],
        pub await_token: Token![await],
    }
}

ast_struct! {
    /// A binary operation: `a + b`, `a += b`.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct ExprBinary {
        pub attrs: Vec<Attribute>,
        pub left: Box<Expr>,
        pub op: BinOp,
        pub right: Box<Expr>,
    }
}

ast_struct! {
    /// A blocked scope: `{ ... }`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct ExprBlock #full {
        pub attrs: Vec<Attribute>,
        pub label: Option<Label>,
        pub block: Block,
    }
}

ast_struct! {
    /// A `break`, with an optional label to break and an optional
    /// expression.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct ExprBreak #full {
        pub attrs: Vec<Attribute>,
        pub break_token: Token![break],
        pub label: Option<Lifetime>,
        pub expr: Option<Box<Expr>>,
    }
}

ast_struct! {
    /// A function call expression: `invoke(a, b)`.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct ExprCall {
        pub attrs: Vec<Attribute>,
        pub func: Box<Expr>,
        pub paren_token: token::Paren,
        pub args: Punctuated<Expr, Token![,]>,
    }
}

ast_struct! {
    /// A cast expression: `foo as f64`.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct ExprCast {
        pub attrs: Vec<Attribute>,
        pub expr: Box<Expr>,
        pub as_token: Token![as],
        pub ty: Box<Type>,
    }
}

ast_struct! {
    /// A closure expression: `|a, b| a + b`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct ExprClosure #full {
        pub attrs: Vec<Attribute>,
        pub lifetimes: Option<BoundLifetimes>,
        pub constness: Option<Token![const]>,
        pub movability: Option<Token![static]>,
        pub asyncness: Option<Token![async]>,
        pub capture: Option<Token![move]>,
        pub or1_token: Token![|],
        pub inputs: Punctuated<Pat, Token![,]>,
        pub or2_token: Token![|],
        pub output: ReturnType,
        pub body: Box<Expr>,
    }
}

ast_struct! {
    /// A const block: `const { ... }`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct ExprConst #full {
        pub attrs: Vec<Attribute>,
        pub const_token: Token![const],
        pub block: Block,
    }
}

ast_struct! {
    /// A `continue`, with an optional label.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct ExprContinue #full {
        pub attrs: Vec<Attribute>,
        pub continue_token: Token![continue],
        pub label: Option<Lifetime>,
    }
}

ast_struct! {
    /// Access of a named struct field (`obj.k`) or unnamed tuple struct
    /// field (`obj.0`).
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct ExprField {
        pub attrs: Vec<Attribute>,
        pub base: Box<Expr>,
        pub dot_token: Token![.],
        pub member: Member,
    }
}

ast_struct! {
    /// A for loop: `for pat in expr { ... }`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct ExprForLoop #full {
        pub attrs: Vec<Attribute>,
        pub label: Option<Label>,
        pub for_token: Token![for],
        pub pat: Box<Pat>,
        pub in_token: Token![in],
        pub expr: Box<Expr>,
        pub body: Block,
    }
}

ast_struct! {
    /// An expression contained within invisible delimiters.
    ///
    /// This variant is important for faithfully representing the precedence
    /// of expressions and is related to `None`-delimited spans in a
    /// `TokenStream`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct ExprGroup {
        pub attrs: Vec<Attribute>,
        pub group_token: token::Group,
        pub expr: Box<Expr>,
    }
}

ast_struct! {
    /// An `if` expression with an optional `else` block: `if expr { ... }
    /// else { ... }`.
    ///
    /// The `else` branch expression may only be an `If` or `Block`
    /// expression, not any of the other types of expression.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct ExprIf #full {
        pub attrs: Vec<Attribute>,
        pub if_token: Token![if],
        pub cond: Box<Expr>,
        pub then_branch: Block,
        pub else_branch: Option<(Token![else], Box<Expr>)>,
    }
}

ast_struct! {
    /// A square bracketed indexing expression: `vector[2]`.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct ExprIndex {
        pub attrs: Vec<Attribute>,
        pub expr: Box<Expr>,
        pub bracket_token: token::Bracket,
        pub index: Box<Expr>,
    }
}

ast_struct! {
    /// The inferred value of a const generic argument, denoted `_`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct ExprInfer #full {
        pub attrs: Vec<Attribute>,
        pub underscore_token: Token![_],
    }
}

ast_struct! {
    /// A `let` guard: `let Some(x) = opt`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct ExprLet #full {
        pub attrs: Vec<Attribute>,
        pub let_token: Token![let],
        pub pat: Box<Pat>,
        pub eq_token: Token![=],
        pub expr: Box<Expr>,
    }
}

ast_struct! {
    /// A literal in place of an expression: `1`, `"foo"`.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct ExprLit {
        pub attrs: Vec<Attribute>,
        pub lit: Lit,
    }
}

ast_struct! {
    /// Conditionless loop: `loop { ... }`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct ExprLoop #full {
        pub attrs: Vec<Attribute>,
        pub label: Option<Label>,
        pub loop_token: Token![loop],
        pub body: Block,
    }
}

ast_struct! {
    /// A macro invocation expression: `format!("{}", q)`.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct ExprMacro {
        pub attrs: Vec<Attribute>,
        pub mac: Macro,
    }
}

ast_struct! {
    /// A `match` expression: `match n { Some(n) => {}, None => {} }`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct ExprMatch #full {
        pub attrs: Vec<Attribute>,
        pub match_token: Token![match],
        pub expr: Box<Expr>,
        pub brace_token: token::Brace,
        pub arms: Vec<Arm>,
    }
}

ast_struct! {
    /// A method call expression: `x.foo::<T>(a, b)`.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct ExprMethodCall {
        pub attrs: Vec<Attribute>,
        pub receiver: Box<Expr>,
        pub dot_token: Token![.],
        pub method: Ident,
        pub turbofish: Option<AngleBracketedGenericArguments>,
        pub paren_token: token::Paren,
        pub args: Punctuated<Expr, Token![,]>,
    }
}

ast_struct! {
    /// A parenthesized expression: `(a + b)`.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct ExprParen {
        pub attrs: Vec<Attribute>,
        pub paren_token: token::Paren,
        pub expr: Box<Expr>,
    }
}

ast_struct! {
    /// A path like `std::mem::replace` possibly containing generic
    /// parameters and a qualified self-type.
    ///
    /// A plain identifier like `x` is a path of length 1.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct ExprPath {
        pub attrs: Vec<Attribute>,
        pub qself: Option<QSelf>,
        pub path: Path,
    }
}

ast_struct! {
    /// A range expression: `1..2`, `1..`, `..2`, `1..=2`, `..=2`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct ExprRange #full {
        pub attrs: Vec<Attribute>,
        pub start: Option<Box<Expr>>,
        pub limits: RangeLimits,
        pub end: Option<Box<Expr>>,
    }
}

ast_struct! {
    /// A referencing operation: `&a` or `&mut a`.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct ExprReference {
        pub attrs: Vec<Attribute>,
        pub and_token: Token![&],
        pub mutability: Option<Token![mut]>,
        pub expr: Box<Expr>,
    }
}

ast_struct! {
    /// An array literal constructed from one repeated element: `[0u8; N]`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct ExprRepeat #full {
        pub attrs: Vec<Attribute>,
        pub bracket_token: token::Bracket,
        pub expr: Box<Expr>,
        pub semi_token: Token![;],
        pub len: Box<Expr>,
    }
}

ast_struct! {
    /// A `return`, with an optional value to be returned.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct ExprReturn #full {
        pub attrs: Vec<Attribute>,
        pub return_token: Token![return],
        pub expr: Option<Box<Expr>>,
    }
}

ast_struct! {
    /// A struct literal expression: `Point { x: 1, y: 1 }`.
    ///
    /// The `rest` provides the value of the remaining fields as in `S { a:
    /// 1, b: 1, ..rest }`.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct ExprStruct {
        pub attrs: Vec<Attribute>,
        pub qself: Option<QSelf>,
        pub path: Path,
        pub brace_token: token::Brace,
        pub fields: Punctuated<FieldValue, Token![,]>,
        pub dot2_token: Option<Token![..]>,
        pub rest: Option<Box<Expr>>,
    }
}

ast_struct! {
    /// A try-expression: `expr?`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct ExprTry #full {
        pub attrs: Vec<Attribute>,
        pub expr: Box<Expr>,
        pub question_token: Token![?],
    }
}

ast_struct! {
    /// A try block: `try { ... }`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct ExprTryBlock #full {
        pub attrs: Vec<Attribute>,
        pub try_token: Token![try],
        pub block: Block,
    }
}

ast_struct! {
    /// A tuple expression: `(a, b, c, d)`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct ExprTuple #full {
        pub attrs: Vec<Attribute>,
        pub paren_token: token::Paren,
        pub elems: Punctuated<Expr, Token![,]>,
    }
}

ast_struct! {
    /// A unary operation: `!x`, `*x`.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct ExprUnary {
        pub attrs: Vec<Attribute>,
        pub op: UnOp,
        pub expr: Box<Expr>,
    }
}

ast_struct! {
    /// An unsafe block: `unsafe { ... }`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct ExprUnsafe #full {
        pub attrs: Vec<Attribute>,
        pub unsafe_token: Token![unsafe],
        pub block: Block,
    }
}

ast_struct! {
    /// A while loop: `while expr { ... }`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct ExprWhile #full {
        pub attrs: Vec<Attribute>,
        pub label: Option<Label>,
        pub while_token: Token![while],
        pub cond: Box<Expr>,
        pub body: Block,
    }
}

ast_struct! {
    /// A yield expression: `yield expr`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct ExprYield #full {
        pub attrs: Vec<Attribute>,
        pub yield_token: Token![yield],
        pub expr: Option<Box<Expr>>,
    }
}

impl Expr {
    /// An unspecified invalid expression.
    ///
    /// ```
    /// use quote::ToTokens;
    /// use std::mem;
    /// use rast::{parse_quote, Expr};
    ///
    /// fn unparenthesize(e: &mut Expr) {
    ///     while let Expr::Paren(paren) = e {
    ///         *e = mem::replace(&mut *paren.expr, Expr::PLACEHOLDER);
    ///     }
    /// }
    ///
    /// fn main() {
    ///     let mut e: Expr = parse_quote! { ((1 + 1)) };
    ///     unparenthesize(&mut e);
    ///     assert_eq!("1 + 1", e.to_token_stream().to_string());
    /// }
    /// ```
    pub const PLACEHOLDER: Self = Expr::Path(ExprPath {
        attrs: Vec::new(),
        qself: None,
        path: Path {
            leading_colon: None,
            segments: Punctuated::new(),
        },
    });
}

ast_enum! {
    /// A struct or tuple struct field accessed in a struct literal or field
    /// expression.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub enum Member {
        /// A named field like `self.x`.
        Named(Ident),
        /// An unnamed field like `self.0`.
        Unnamed(Index),
    }
}

impl From<Ident> for Member {
    fn from(ident: Ident) -> Member {
        Member::Named(ident)
    }
}

impl From<Index> for Member {
    fn from(index: Index) -> Member {
        Member::Unnamed(index)
    }
}

impl From<usize> for Member {
    fn from(index: usize) -> Member {
        Member::Unnamed(Index::from(index))
    }
}

impl Eq for Member {}

impl PartialEq for Member {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Member::Named(this), Member::Named(other)) => this == other,
            (Member::Unnamed(this), Member::Unnamed(other)) => this == other,
            _ => false,
        }
    }
}

impl Hash for Member {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Member::Named(m) => m.hash(state),
            Member::Unnamed(m) => m.hash(state),
        }
    }
}

#[cfg(feature = "printing")]
impl IdentFragment for Member {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Member::Named(m) => Display::fmt(m, formatter),
            Member::Unnamed(m) => Display::fmt(&m.index, formatter),
        }
    }

    fn span(&self) -> Option<Span> {
        match self {
            Member::Named(m) => Some(m.span()),
            Member::Unnamed(m) => Some(m.span),
        }
    }
}

ast_struct! {
    /// The index of an unnamed tuple struct field.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct Index {
        pub index: u32,
        pub span: Span,
    }
}

impl From<usize> for Index {
    fn from(index: usize) -> Index {
        assert!(index < u32::MAX as usize);
        Index {
            index: index as u32,
            span: Span::call_site(),
        }
    }
}

impl Eq for Index {}

impl PartialEq for Index {
    fn eq(&self, other: &Self) -> bool {
        self.index == other.index
    }
}

impl Hash for Index {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.index.hash(state);
    }
}

#[cfg(feature = "printing")]
impl IdentFragment for Index {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        Display::fmt(&self.index, formatter)
    }

    fn span(&self) -> Option<Span> {
        Some(self.span)
    }
}

ast_struct! {
    /// A field-value pair in a struct literal.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct FieldValue {
        pub attrs: Vec<Attribute>,
        pub member: Member,

        /// The colon in `Struct { x: x }`. If written in shorthand like
        /// `Struct { x }`, there is no colon.
        pub colon_token: Option<Token![:]>,

        pub expr: Expr,
    }
}

#[cfg(feature = "full")]
ast_struct! {
    /// A lifetime labeling a `for`, `while`, or `loop`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct Label {
        pub name: Lifetime,
        pub colon_token: Token![:],
    }
}

#[cfg(feature = "full")]
ast_struct! {
    /// One arm of a `match` expression: `0..=10 => { return true; }`.
    ///
    /// As in:
    ///
    /// ```
    /// # fn f() -> bool {
    /// #     let n = 0;
    /// match n {
    ///     0..=10 => {
    ///         return true;
    ///     }
    ///     // ...
    ///     # _ => {}
    /// }
    /// #   false
    /// # }
    /// ```
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct Arm {
        pub attrs: Vec<Attribute>,
        pub pat: Pat,
        pub guard: Option<(Token![if], Box<Expr>)>,
        pub fat_arrow_token: Token![=>],
        pub body: Box<Expr>,
        pub comma: Option<Token![,]>,
    }
}

#[cfg(feature = "full")]
ast_enum! {
    /// Limit types of a range, inclusive or exclusive.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub enum RangeLimits {
        /// Inclusive at the beginning, exclusive at the end.
        HalfOpen(Token![..]),
        /// Inclusive at the beginning and end.
        Closed(Token![..=]),
    }
}

#[cfg(feature = "printing")]
pub(crate) mod printing {
    use crate::attr::Attribute;
    #[cfg(feature = "full")]
    use crate::attr::FilterAttrs;
    use crate::classify;
    #[cfg(feature = "full")]
    use crate::expr::{
        Arm, ExprArray, ExprAssign, ExprAsync, ExprAwait, ExprBlock, ExprBreak, ExprClosure,
        ExprConst, ExprContinue, ExprForLoop, ExprIf, ExprInfer, ExprLet, ExprLoop, ExprMatch,
        ExprRange, ExprRepeat, ExprReturn, ExprTry, ExprTryBlock, ExprTuple, ExprUnsafe, ExprWhile,
        ExprYield, Label, RangeLimits,
    };
    use crate::expr::{
        Expr, ExprBinary, ExprCall, ExprCast, ExprField, ExprGroup, ExprIndex, ExprLit, ExprMacro,
        ExprMethodCall, ExprParen, ExprPath, ExprReference, ExprStruct, ExprUnary, FieldValue,
        Index, Member,
    };
    #[cfg(feature = "full")]
    use crate::fixup::FixupContext;
    use crate::op::BinOp;
    use crate::path;
    use crate::precedence::Precedence;
    use crate::token;
    #[cfg(feature = "full")]
    use crate::ty::ReturnType;
    use proc_macro2::{Literal, Span, TokenStream};
    use quote::{ToTokens, TokenStreamExt};

    #[cfg(feature = "full")]
    pub(crate) fn outer_attrs_to_tokens(attrs: &[Attribute], tokens: &mut TokenStream) {
        tokens.append_all(attrs.outer());
    }

    #[cfg(feature = "full")]
    fn inner_attrs_to_tokens(attrs: &[Attribute], tokens: &mut TokenStream) {
        tokens.append_all(attrs.inner());
    }

    #[cfg(not(feature = "full"))]
    pub(crate) fn outer_attrs_to_tokens(_attrs: &[Attribute], _tokens: &mut TokenStream) {}

    #[cfg(feature = "full")]
    fn print_condition(expr: &Expr, tokens: &mut TokenStream) {
        print_subexpression(
            expr,
            classify::confusable_with_adjacent_block(expr),
            tokens,
            FixupContext::new_condition(),
        );
    }

    fn print_subexpression(
        expr: &Expr,
        needs_group: bool,
        tokens: &mut TokenStream,
        #[cfg(feature = "full")] mut fixup: FixupContext,
    ) {
        #[cfg(not(feature = "full"))]
        let do_print_expr = |tokens: &mut TokenStream| expr.to_tokens(tokens);

        #[cfg(feature = "full")]
        let do_print_expr = {
            // If we are surrounding the whole cond in parentheses, such as:
            //
            //     if (return Struct {}) {}
            //
            // then there is no need for parenthesizing the individual struct
            // expressions within. On the other hand if the whole cond is not
            // parenthesized, then print_expr must parenthesize exterior struct
            // literals.
            //
            //     if x == (Struct {}) {}
            //
            if needs_group {
                fixup = FixupContext::NONE;
            }
            |tokens: &mut TokenStream| print_expr(expr, tokens, fixup)
        };

        if needs_group {
            token::Paren::default().surround(tokens, do_print_expr);
        } else {
            do_print_expr(tokens);
        }
    }

    #[cfg(feature = "full")]
    pub(crate) fn print_expr(expr: &Expr, tokens: &mut TokenStream, mut fixup: FixupContext) {
        let needs_group = fixup.would_cause_statement_boundary(expr);
        if needs_group {
            fixup = FixupContext::NONE;
        }

        let do_print_expr = |tokens: &mut TokenStream| match expr {
            Expr::Array(e) => e.to_tokens(tokens),
            Expr::Assign(e) => print_expr_assign(e, tokens, fixup),
            Expr::Async(e) => e.to_tokens(tokens),
            Expr::Await(e) => print_expr_await(e, tokens, fixup),
            Expr::Binary(e) => print_expr_binary(e, tokens, fixup),
            Expr::Block(e) => e.to_tokens(tokens),
            Expr::Break(e) => print_expr_break(e, tokens, fixup),
            Expr::Call(e) => print_expr_call(e, tokens, fixup),
            Expr::Cast(e) => print_expr_cast(e, tokens, fixup),
            Expr::Closure(e) => e.to_tokens(tokens),
            Expr::Const(e) => e.to_tokens(tokens),
            Expr::Continue(e) => e.to_tokens(tokens),
            Expr::Field(e) => print_expr_field(e, tokens, fixup),
            Expr::ForLoop(e) => e.to_tokens(tokens),
            Expr::Group(e) => e.to_tokens(tokens),
            Expr::If(e) => e.to_tokens(tokens),
            Expr::Index(e) => print_expr_index(e, tokens, fixup),
            Expr::Infer(e) => e.to_tokens(tokens),
            Expr::Let(e) => print_expr_let(e, tokens, fixup),
            Expr::Lit(e) => e.to_tokens(tokens),
            Expr::Loop(e) => e.to_tokens(tokens),
            Expr::Macro(e) => e.to_tokens(tokens),
            Expr::Match(e) => e.to_tokens(tokens),
            Expr::MethodCall(e) => print_expr_method_call(e, tokens, fixup),
            Expr::Paren(e) => e.to_tokens(tokens),
            Expr::Path(e) => e.to_tokens(tokens),
            Expr::Range(e) => print_expr_range(e, tokens, fixup),
            Expr::Reference(e) => print_expr_reference(e, tokens, fixup),
            Expr::Repeat(e) => e.to_tokens(tokens),
            Expr::Return(e) => print_expr_return(e, tokens, fixup),
            Expr::Struct(e) => e.to_tokens(tokens),
            Expr::Try(e) => print_expr_try(e, tokens, fixup),
            Expr::TryBlock(e) => e.to_tokens(tokens),
            Expr::Tuple(e) => e.to_tokens(tokens),
            Expr::Unary(e) => print_expr_unary(e, tokens, fixup),
            Expr::Unsafe(e) => e.to_tokens(tokens),
            Expr::Verbatim(e) => e.to_tokens(tokens),
            Expr::While(e) => e.to_tokens(tokens),
            Expr::Yield(e) => print_expr_yield(e, tokens, fixup),
        };

        if needs_group {
            token::Paren::default().surround(tokens, do_print_expr);
        } else {
            do_print_expr(tokens);
        }
    }

    #[cfg(feature = "full")]
    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ExprArray {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            outer_attrs_to_tokens(&self.attrs, tokens);
            self.bracket_token.surround(tokens, |tokens| {
                self.elems.to_tokens(tokens);
            });
        }
    }

    #[cfg(feature = "full")]
    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ExprAssign {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            print_expr_assign(self, tokens, FixupContext::NONE);
        }
    }

    #[cfg(feature = "full")]
    fn print_expr_assign(e: &ExprAssign, tokens: &mut TokenStream, fixup: FixupContext) {
        outer_attrs_to_tokens(&e.attrs, tokens);
        print_subexpression(
            &e.left,
            Precedence::of(&e.left) <= Precedence::Assign,
            tokens,
            fixup.leftmost_subexpression(),
        );
        e.eq_token.to_tokens(tokens);
        print_subexpression(
            &e.right,
            Precedence::of_rhs(&e.right) < Precedence::Assign,
            tokens,
            fixup.subsequent_subexpression(),
        );
    }

    #[cfg(feature = "full")]
    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ExprAsync {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            outer_attrs_to_tokens(&self.attrs, tokens);
            self.async_token.to_tokens(tokens);
            self.capture.to_tokens(tokens);
            self.block.to_tokens(tokens);
        }
    }

    #[cfg(feature = "full")]
    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ExprAwait {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            print_expr_await(self, tokens, FixupContext::NONE);
        }
    }

    #[cfg(feature = "full")]
    fn print_expr_await(e: &ExprAwait, tokens: &mut TokenStream, fixup: FixupContext) {
        outer_attrs_to_tokens(&e.attrs, tokens);
        print_subexpression(
            &e.base,
            Precedence::of(&e.base) < Precedence::Unambiguous,
            tokens,
            fixup.leftmost_subexpression_with_dot(),
        );
        e.dot_token.to_tokens(tokens);
        e.await_token.to_tokens(tokens);
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ExprBinary {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            print_expr_binary(
                self,
                tokens,
                #[cfg(feature = "full")]
                FixupContext::NONE,
            );
        }
    }

    fn print_expr_binary(
        e: &ExprBinary,
        tokens: &mut TokenStream,
        #[cfg(feature = "full")] fixup: FixupContext,
    ) {
        outer_attrs_to_tokens(&e.attrs, tokens);

        let binop_prec = Precedence::of_binop(&e.op);
        let left_prec = Precedence::of(&e.left);
        let right_prec = Precedence::of_rhs(&e.right);
        let (mut left_needs_group, right_needs_group) = if let Precedence::Assign = binop_prec {
            (left_prec <= binop_prec, right_prec < binop_prec)
        } else {
            (left_prec < binop_prec, right_prec <= binop_prec)
        };

        // These cases require parenthesization independently of precedence.
        match (&*e.left, &e.op) {
            // `x as i32 < y` has the parser thinking that `i32 < y` is the
            // beginning of a path type. It starts trying to parse `x as (i32 <
            // y ...` instead of `(x as i32) < ...`. We need to convince it
            // _not_ to do that.
            (_, BinOp::Lt(_) | BinOp::Shl(_)) if classify::confusable_with_adjacent_lt(&e.left) => {
                left_needs_group = true;
            }

            // We are given `(let _ = a) OP b`.
            //
            // - When `OP <= LAnd` we should print `let _ = a OP b` to avoid
            //   redundant parens as the parser will interpret this as `(let _ =
            //   a) OP b`.
            //
            // - Otherwise, e.g. when we have `(let a = b) < c` in AST, parens
            //   are required since the parser would interpret `let a = b < c`
            //   as `let a = (b < c)`. To achieve this, we force parens.
            #[cfg(feature = "full")]
            (Expr::Let(_), _) if binop_prec > Precedence::And => {
                left_needs_group = true;
            }

            _ => {}
        }

        print_subexpression(
            &e.left,
            left_needs_group,
            tokens,
            #[cfg(feature = "full")]
            fixup.leftmost_subexpression(),
        );
        e.op.to_tokens(tokens);
        print_subexpression(
            &e.right,
            right_needs_group,
            tokens,
            #[cfg(feature = "full")]
            fixup.subsequent_subexpression(),
        );
    }

    #[cfg(feature = "full")]
    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ExprBlock {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            outer_attrs_to_tokens(&self.attrs, tokens);
            self.label.to_tokens(tokens);
            self.block.brace_token.surround(tokens, |tokens| {
                inner_attrs_to_tokens(&self.attrs, tokens);
                tokens.append_all(&self.block.stmts);
            });
        }
    }

    #[cfg(feature = "full")]
    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ExprBreak {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            print_expr_break(self, tokens, FixupContext::NONE);
        }
    }

    #[cfg(feature = "full")]
    fn print_expr_break(e: &ExprBreak, tokens: &mut TokenStream, fixup: FixupContext) {
        outer_attrs_to_tokens(&e.attrs, tokens);
        e.break_token.to_tokens(tokens);
        e.label.to_tokens(tokens);
        if let Some(value) = &e.expr {
            print_subexpression(
                value,
                // Parenthesize `break 'inner: loop { break 'inner 1 } + 1`
                //                     ^---------------------------------^
                e.label.is_none() && classify::expr_leading_label(value),
                tokens,
                fixup.subsequent_subexpression(),
            );
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ExprCall {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            print_expr_call(
                self,
                tokens,
                #[cfg(feature = "full")]
                FixupContext::NONE,
            );
        }
    }

    fn print_expr_call(
        e: &ExprCall,
        tokens: &mut TokenStream,
        #[cfg(feature = "full")] fixup: FixupContext,
    ) {
        outer_attrs_to_tokens(&e.attrs, tokens);

        let precedence = if let Expr::Field(_) = &*e.func {
            Precedence::Any
        } else {
            Precedence::Unambiguous
        };
        print_subexpression(
            &e.func,
            Precedence::of(&e.func) < precedence,
            tokens,
            #[cfg(feature = "full")]
            fixup.leftmost_subexpression(),
        );

        e.paren_token.surround(tokens, |tokens| {
            e.args.to_tokens(tokens);
        });
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ExprCast {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            print_expr_cast(
                self,
                tokens,
                #[cfg(feature = "full")]
                FixupContext::NONE,
            );
        }
    }

    fn print_expr_cast(
        e: &ExprCast,
        tokens: &mut TokenStream,
        #[cfg(feature = "full")] fixup: FixupContext,
    ) {
        outer_attrs_to_tokens(&e.attrs, tokens);
        print_subexpression(
            &e.expr,
            Precedence::of(&e.expr) < Precedence::Cast,
            tokens,
            #[cfg(feature = "full")]
            fixup.leftmost_subexpression(),
        );
        e.as_token.to_tokens(tokens);
        e.ty.to_tokens(tokens);
    }

    #[cfg(feature = "full")]
    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ExprClosure {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            outer_attrs_to_tokens(&self.attrs, tokens);
            self.lifetimes.to_tokens(tokens);
            self.constness.to_tokens(tokens);
            self.movability.to_tokens(tokens);
            self.asyncness.to_tokens(tokens);
            self.capture.to_tokens(tokens);
            self.or1_token.to_tokens(tokens);
            self.inputs.to_tokens(tokens);
            self.or2_token.to_tokens(tokens);
            self.output.to_tokens(tokens);
            if matches!(self.output, ReturnType::Default) || matches!(*self.body, Expr::Block(_)) {
                self.body.to_tokens(tokens);
            } else {
                token::Brace::default().surround(tokens, |tokens| {
                    print_expr(&self.body, tokens, FixupContext::new_stmt());
                });
            }
        }
    }

    #[cfg(feature = "full")]
    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ExprConst {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            outer_attrs_to_tokens(&self.attrs, tokens);
            self.const_token.to_tokens(tokens);
            self.block.brace_token.surround(tokens, |tokens| {
                inner_attrs_to_tokens(&self.attrs, tokens);
                tokens.append_all(&self.block.stmts);
            });
        }
    }

    #[cfg(feature = "full")]
    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ExprContinue {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            outer_attrs_to_tokens(&self.attrs, tokens);
            self.continue_token.to_tokens(tokens);
            self.label.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ExprField {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            print_expr_field(
                self,
                tokens,
                #[cfg(feature = "full")]
                FixupContext::NONE,
            );
        }
    }

    fn print_expr_field(
        e: &ExprField,
        tokens: &mut TokenStream,
        #[cfg(feature = "full")] fixup: FixupContext,
    ) {
        outer_attrs_to_tokens(&e.attrs, tokens);
        print_subexpression(
            &e.base,
            Precedence::of(&e.base) < Precedence::Unambiguous,
            tokens,
            #[cfg(feature = "full")]
            fixup.leftmost_subexpression_with_dot(),
        );
        e.dot_token.to_tokens(tokens);
        e.member.to_tokens(tokens);
    }

    #[cfg(feature = "full")]
    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ExprForLoop {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            outer_attrs_to_tokens(&self.attrs, tokens);
            self.label.to_tokens(tokens);
            self.for_token.to_tokens(tokens);
            self.pat.to_tokens(tokens);
            self.in_token.to_tokens(tokens);
            print_condition(&self.expr, tokens);
            self.body.brace_token.surround(tokens, |tokens| {
                inner_attrs_to_tokens(&self.attrs, tokens);
                tokens.append_all(&self.body.stmts);
            });
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ExprGroup {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            outer_attrs_to_tokens(&self.attrs, tokens);
            self.group_token.surround(tokens, |tokens| {
                self.expr.to_tokens(tokens);
            });
        }
    }

    #[cfg(feature = "full")]
    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ExprIf {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            outer_attrs_to_tokens(&self.attrs, tokens);

            let mut expr = self;
            loop {
                expr.if_token.to_tokens(tokens);
                print_condition(&expr.cond, tokens);
                expr.then_branch.to_tokens(tokens);

                let (else_token, else_) = match &expr.else_branch {
                    Some(else_branch) => else_branch,
                    None => break,
                };

                else_token.to_tokens(tokens);
                match &**else_ {
                    Expr::If(next) => {
                        expr = next;
                    }
                    Expr::Block(last) => {
                        last.to_tokens(tokens);
                        break;
                    }
                    // If this is not one of the valid expressions to exist in
                    // an else clause, wrap it in a block.
                    other => {
                        token::Brace::default().surround(tokens, |tokens| {
                            print_expr(other, tokens, FixupContext::new_stmt());
                        });
                        break;
                    }
                }
            }
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ExprIndex {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            print_expr_index(
                self,
                tokens,
                #[cfg(feature = "full")]
                FixupContext::NONE,
            );
        }
    }

    fn print_expr_index(
        e: &ExprIndex,
        tokens: &mut TokenStream,
        #[cfg(feature = "full")] fixup: FixupContext,
    ) {
        outer_attrs_to_tokens(&e.attrs, tokens);
        print_subexpression(
            &e.expr,
            Precedence::of(&e.expr) < Precedence::Unambiguous,
            tokens,
            #[cfg(feature = "full")]
            fixup.leftmost_subexpression(),
        );
        e.bracket_token.surround(tokens, |tokens| {
            e.index.to_tokens(tokens);
        });
    }

    #[cfg(feature = "full")]
    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ExprInfer {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            outer_attrs_to_tokens(&self.attrs, tokens);
            self.underscore_token.to_tokens(tokens);
        }
    }

    #[cfg(feature = "full")]
    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ExprLet {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            print_expr_let(self, tokens, FixupContext::NONE);
        }
    }

    #[cfg(feature = "full")]
    fn print_expr_let(e: &ExprLet, tokens: &mut TokenStream, fixup: FixupContext) {
        outer_attrs_to_tokens(&e.attrs, tokens);
        e.let_token.to_tokens(tokens);
        e.pat.to_tokens(tokens);
        e.eq_token.to_tokens(tokens);
        print_subexpression(
            &e.expr,
            fixup.needs_group_as_let_scrutinee(&e.expr),
            tokens,
            FixupContext::NONE,
        );
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ExprLit {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            outer_attrs_to_tokens(&self.attrs, tokens);
            self.lit.to_tokens(tokens);
        }
    }

    #[cfg(feature = "full")]
    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ExprLoop {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            outer_attrs_to_tokens(&self.attrs, tokens);
            self.label.to_tokens(tokens);
            self.loop_token.to_tokens(tokens);
            self.body.brace_token.surround(tokens, |tokens| {
                inner_attrs_to_tokens(&self.attrs, tokens);
                tokens.append_all(&self.body.stmts);
            });
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ExprMacro {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            outer_attrs_to_tokens(&self.attrs, tokens);
            self.mac.to_tokens(tokens);
        }
    }

    #[cfg(feature = "full")]
    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ExprMatch {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            outer_attrs_to_tokens(&self.attrs, tokens);
            self.match_token.to_tokens(tokens);
            print_condition(&self.expr, tokens);
            self.brace_token.surround(tokens, |tokens| {
                inner_attrs_to_tokens(&self.attrs, tokens);
                for (i, arm) in self.arms.iter().enumerate() {
                    arm.to_tokens(tokens);
                    // Ensure that we have a comma after a non-block arm, except
                    // for the last one.
                    let is_last = i == self.arms.len() - 1;
                    if !is_last
                        && classify::requires_comma_to_be_match_arm(&arm.body)
                        && arm.comma.is_none()
                    {
                        <Token![,]>::default().to_tokens(tokens);
                    }
                }
            });
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ExprMethodCall {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            print_expr_method_call(
                self,
                tokens,
                #[cfg(feature = "full")]
                FixupContext::NONE,
            );
        }
    }

    fn print_expr_method_call(
        e: &ExprMethodCall,
        tokens: &mut TokenStream,
        #[cfg(feature = "full")] fixup: FixupContext,
    ) {
        outer_attrs_to_tokens(&e.attrs, tokens);
        print_subexpression(
            &e.receiver,
            Precedence::of(&e.receiver) < Precedence::Unambiguous,
            tokens,
            #[cfg(feature = "full")]
            fixup.leftmost_subexpression_with_dot(),
        );
        e.dot_token.to_tokens(tokens);
        e.method.to_tokens(tokens);
        e.turbofish.to_tokens(tokens);
        e.paren_token.surround(tokens, |tokens| {
            e.args.to_tokens(tokens);
        });
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ExprParen {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            outer_attrs_to_tokens(&self.attrs, tokens);
            self.paren_token.surround(tokens, |tokens| {
                self.expr.to_tokens(tokens);
            });
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ExprPath {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            outer_attrs_to_tokens(&self.attrs, tokens);
            path::printing::print_path(tokens, &self.qself, &self.path);
        }
    }

    #[cfg(feature = "full")]
    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ExprRange {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            print_expr_range(self, tokens, FixupContext::NONE);
        }
    }

    #[cfg(feature = "full")]
    fn print_expr_range(e: &ExprRange, tokens: &mut TokenStream, fixup: FixupContext) {
        outer_attrs_to_tokens(&e.attrs, tokens);
        if let Some(start) = &e.start {
            print_subexpression(
                start,
                Precedence::of(start) <= Precedence::Range,
                tokens,
                fixup.leftmost_subexpression(),
            );
        }
        e.limits.to_tokens(tokens);
        if let Some(end) = &e.end {
            print_subexpression(
                end,
                Precedence::of_rhs(end) <= Precedence::Range,
                tokens,
                fixup.subsequent_subexpression(),
            );
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ExprReference {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            print_expr_reference(
                self,
                tokens,
                #[cfg(feature = "full")]
                FixupContext::NONE,
            );
        }
    }

    fn print_expr_reference(
        e: &ExprReference,
        tokens: &mut TokenStream,
        #[cfg(feature = "full")] fixup: FixupContext,
    ) {
        outer_attrs_to_tokens(&e.attrs, tokens);
        e.and_token.to_tokens(tokens);
        e.mutability.to_tokens(tokens);
        print_subexpression(
            &e.expr,
            Precedence::of_rhs(&e.expr) < Precedence::Prefix,
            tokens,
            #[cfg(feature = "full")]
            fixup.subsequent_subexpression(),
        );
    }

    #[cfg(feature = "full")]
    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ExprRepeat {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            outer_attrs_to_tokens(&self.attrs, tokens);
            self.bracket_token.surround(tokens, |tokens| {
                self.expr.to_tokens(tokens);
                self.semi_token.to_tokens(tokens);
                self.len.to_tokens(tokens);
            });
        }
    }

    #[cfg(feature = "full")]
    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ExprReturn {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            print_expr_return(self, tokens, FixupContext::NONE);
        }
    }

    #[cfg(feature = "full")]
    fn print_expr_return(e: &ExprReturn, tokens: &mut TokenStream, fixup: FixupContext) {
        outer_attrs_to_tokens(&e.attrs, tokens);
        e.return_token.to_tokens(tokens);
        if let Some(expr) = &e.expr {
            print_expr(expr, tokens, fixup.subsequent_subexpression());
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ExprStruct {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            outer_attrs_to_tokens(&self.attrs, tokens);
            path::printing::print_path(tokens, &self.qself, &self.path);
            self.brace_token.surround(tokens, |tokens| {
                self.fields.to_tokens(tokens);
                if let Some(dot2_token) = &self.dot2_token {
                    dot2_token.to_tokens(tokens);
                } else if self.rest.is_some() {
                    Token![..](Span::call_site()).to_tokens(tokens);
                }
                self.rest.to_tokens(tokens);
            });
        }
    }

    #[cfg(feature = "full")]
    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ExprTry {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            print_expr_try(self, tokens, FixupContext::NONE);
        }
    }

    #[cfg(feature = "full")]
    fn print_expr_try(e: &ExprTry, tokens: &mut TokenStream, fixup: FixupContext) {
        outer_attrs_to_tokens(&e.attrs, tokens);
        print_subexpression(
            &e.expr,
            Precedence::of(&e.expr) < Precedence::Unambiguous,
            tokens,
            fixup.leftmost_subexpression_with_dot(),
        );
        e.question_token.to_tokens(tokens);
    }

    #[cfg(feature = "full")]
    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ExprTryBlock {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            outer_attrs_to_tokens(&self.attrs, tokens);
            self.try_token.to_tokens(tokens);
            self.block.to_tokens(tokens);
        }
    }

    #[cfg(feature = "full")]
    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ExprTuple {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            outer_attrs_to_tokens(&self.attrs, tokens);
            self.paren_token.surround(tokens, |tokens| {
                self.elems.to_tokens(tokens);
                // If we only have one argument, we need a trailing comma to
                // distinguish ExprTuple from ExprParen.
                if self.elems.len() == 1 && !self.elems.trailing_punct() {
                    <Token![,]>::default().to_tokens(tokens);
                }
            });
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ExprUnary {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            print_expr_unary(
                self,
                tokens,
                #[cfg(feature = "full")]
                FixupContext::NONE,
            );
        }
    }

    fn print_expr_unary(
        e: &ExprUnary,
        tokens: &mut TokenStream,
        #[cfg(feature = "full")] fixup: FixupContext,
    ) {
        outer_attrs_to_tokens(&e.attrs, tokens);
        e.op.to_tokens(tokens);
        print_subexpression(
            &e.expr,
            Precedence::of_rhs(&e.expr) < Precedence::Prefix,
            tokens,
            #[cfg(feature = "full")]
            fixup.subsequent_subexpression(),
        );
    }

    #[cfg(feature = "full")]
    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ExprUnsafe {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            outer_attrs_to_tokens(&self.attrs, tokens);
            self.unsafe_token.to_tokens(tokens);
            self.block.brace_token.surround(tokens, |tokens| {
                inner_attrs_to_tokens(&self.attrs, tokens);
                tokens.append_all(&self.block.stmts);
            });
        }
    }

    #[cfg(feature = "full")]
    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ExprWhile {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            outer_attrs_to_tokens(&self.attrs, tokens);
            self.label.to_tokens(tokens);
            self.while_token.to_tokens(tokens);
            print_condition(&self.cond, tokens);
            self.body.brace_token.surround(tokens, |tokens| {
                inner_attrs_to_tokens(&self.attrs, tokens);
                tokens.append_all(&self.body.stmts);
            });
        }
    }

    #[cfg(feature = "full")]
    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ExprYield {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            print_expr_yield(self, tokens, FixupContext::NONE);
        }
    }

    #[cfg(feature = "full")]
    fn print_expr_yield(e: &ExprYield, tokens: &mut TokenStream, fixup: FixupContext) {
        outer_attrs_to_tokens(&e.attrs, tokens);
        e.yield_token.to_tokens(tokens);
        if let Some(expr) = &e.expr {
            print_expr(expr, tokens, fixup.subsequent_subexpression());
        }
    }

    #[cfg(feature = "full")]
    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for Arm {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.append_all(&self.attrs);
            self.pat.to_tokens(tokens);
            if let Some((if_token, guard)) = &self.guard {
                if_token.to_tokens(tokens);
                guard.to_tokens(tokens);
            }
            self.fat_arrow_token.to_tokens(tokens);
            print_expr(&self.body, tokens, FixupContext::new_match_arm());
            self.comma.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for FieldValue {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            outer_attrs_to_tokens(&self.attrs, tokens);
            self.member.to_tokens(tokens);
            if let Some(colon_token) = &self.colon_token {
                colon_token.to_tokens(tokens);
                self.expr.to_tokens(tokens);
            }
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for Index {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            let mut lit = Literal::i64_unsuffixed(i64::from(self.index));
            lit.set_span(self.span);
            tokens.append(lit);
        }
    }

    #[cfg(feature = "full")]
    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for Label {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.name.to_tokens(tokens);
            self.colon_token.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for Member {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            match self {
                Member::Named(ident) => ident.to_tokens(tokens),
                Member::Unnamed(index) => index.to_tokens(tokens),
            }
        }
    }

    #[cfg(feature = "full")]
    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for RangeLimits {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            match self {
                RangeLimits::HalfOpen(t) => t.to_tokens(tokens),
                RangeLimits::Closed(t) => t.to_tokens(tokens),
            }
        }
    }
}
