//! [![github]](https://github.com/dtolnay/syn)&ensp;[![crates-io]](https://crates.io/crates/syn)&ensp;[![docs-rs]](crate)
//!
//! [github]: https://img.shields.io/badge/github-8da0cb?style=for-the-badge&labelColor=555555&logo=github
//! [crates-io]: https://img.shields.io/badge/crates.io-fc8d62?style=for-the-badge&labelColor=555555&logo=rust
//! [docs-rs]: https://img.shields.io/badge/docs.rs-66c2a5?style=for-the-badge&labelColor=555555&logo=docs.rs
//!
//! <br>
//!
//! Syn is a parsing library for parsing a stream of Rust tokens into a syntax
//! tree of Rust source code.
//!
//! Currently this library is geared toward use in Rust procedural macros, but
//! contains some APIs that may be useful more generally.
//!
//! - **Data structures** — Syn provides a complete syntax tree that can
//!   represent any valid Rust source code. The syntax tree is rooted at
//!   [`rast::File`] which represents a full source file, but there are other
//!   entry points that may be useful to procedural macros including
//!   [`rast::Item`], [`rast::Expr`] and [`rast::Type`].
//!
//! - **Derives** — Of particular interest to derive macros is
//!   [`rast::DeriveInput`] which is any of the three legal input items to a
//!   derive macro. An example below shows using this type in a library that can
//!   derive implementations of a user-defined trait.
//!
//! - **Parsing** — Parsing in Syn is built around [parser functions] with the
//!   signature `fn(ParseStream) -> Result<T>`. Every syntax tree node defined
//!   by Syn is individually parsable and may be used as a building block for
//!   custom syntaxes, or you may dream up your own brand new syntax without
//!   involving any of our syntax tree types.
//!
//! - **Location information** — Every token parsed by Syn is associated with a
//!   `Span` that tracks line and column information back to the source of that
//!   token. These spans allow a procedural macro to display detailed error
//!   messages pointing to all the right places in the user's code. There is an
//!   example of this below.
//!
//! - **Feature flags** — Functionality is aggressively feature gated so your
//!   procedural macros enable only what they need, and do not pay in compile
//!   time for all the rest.
//!
//! [`rast::File`]: File
//! [`rast::Item`]: Item
//! [`rast::Expr`]: Expr
//! [`rast::Type`]: Type
//! [`rast::DeriveInput`]: DeriveInput
//! [parser functions]: mod@parse
//!
//! <br>
//!
//! # Example of a derive macro
//!
//! The canonical derive macro using Syn looks like this. We write an ordinary
//! Rust function tagged with a `proc_macro_derive` attribute and the name of
//! the trait we are deriving. Any time that derive appears in the user's code,
//! the Rust compiler passes their data structure as tokens into our macro. We
//! get to execute arbitrary Rust code to figure out what to do with those
//! tokens, then hand some tokens back to the compiler to compile into the
//! user's crate.
//!
//! [`TokenStream`]: proc_macro::TokenStream
//!
//! ```toml
//! [dependencies]
//! syn = "2.0"
//! quote = "1.0"
//!
//! [lib]
//! proc-macro = true
//! ```
//!
//! ```
//! # extern crate proc_macro;
//! #
//! use proc_macro::TokenStream;
//! use quote::quote;
//! use rast::{parse_macro_input, DeriveInput};
//!
//! # const IGNORE_TOKENS: &str = stringify! {
//! #[proc_macro_derive(MyMacro)]
//! # };
//! pub fn my_macro(input: TokenStream) -> TokenStream {
//!     // Parse the input tokens into a syntax tree
//!     let input = parse_macro_input!(input as DeriveInput);
//!
//!     // Build the output, possibly using quasi-quotation
//!     let expanded = quote! {
//!         // ...
//!     };
//!
//!     // Hand the output tokens back to the compiler
//!     TokenStream::from(expanded)
//! }
//! ```
//!
//! The [`heapsize`] example directory shows a complete working implementation
//! of a derive macro. The example derives a `HeapSize` trait which computes an
//! estimate of the amount of heap memory owned by a value.
//!
//! [`heapsize`]: https://github.com/dtolnay/syn/tree/master/examples/heapsize
//!
//! ```
//! pub trait HeapSize {
//!     /// Total number of bytes of heap memory owned by `self`.
//!     fn heap_size_of_children(&self) -> usize;
//! }
//! ```
//!
//! The derive macro allows users to write `#[derive(HeapSize)]` on data
//! structures in their program.
//!
//! ```
//! # const IGNORE_TOKENS: &str = stringify! {
//! #[derive(HeapSize)]
//! # };
//! struct Demo<'a, T: ?Sized> {
//!     a: Box<T>,
//!     b: u8,
//!     c: &'a str,
//!     d: String,
//! }
//! ```
//!
//! <p><br></p>
//!
//! # Spans and error reporting
//!
//! The token-based procedural macro API provides great control over where the
//! compiler's error messages are displayed in user code. Consider the error the
//! user sees if one of their field types does not implement `HeapSize`.
//!
//! ```
//! # const IGNORE_TOKENS: &str = stringify! {
//! #[derive(HeapSize)]
//! # };
//! struct Broken {
//!     ok: String,
//!     bad: std::thread::Thread,
//! }
//! ```
//!
//! By tracking span information all the way through the expansion of a
//! procedural macro as shown in the `heapsize` example, token-based macros in
//! Syn are able to trigger errors that directly pinpoint the source of the
//! problem.
//!
//! ```text
//! error[E0277]: the trait bound `std::thread::Thread: HeapSize` is not satisfied
//!  --> src/main.rs:7:5
//!   |
//! 7 |     bad: std::thread::Thread,
//!   |     ^^^^^^^^^^^^^^^^^^^^^^^^ the trait `HeapSize` is not implemented for `Thread`
//! ```
//!
//! <br>
//!
//! # Parsing a custom syntax
//!
//! The [`lazy-static`] example directory shows the implementation of a
//! `functionlike!(...)` procedural macro in which the input tokens are parsed
//! using Syn's parsing API.
//!
//! [`lazy-static`]: https://github.com/dtolnay/syn/tree/master/examples/lazy-static
//!
//! The example reimplements the popular `lazy_static` crate from crates.io as a
//! procedural macro.
//!
//! ```
//! # macro_rules! lazy_static {
//! #     ($($tt:tt)*) => {}
//! # }
//! #
//! lazy_static! {
//!     static ref USERNAME: Regex = Regex::new("^[a-z0-9_-]{3,16}$").unwrap();
//! }
//! ```
//!
//! The implementation shows how to trigger custom warnings and error messages
//! on the macro input.
//!
//! ```text
//! warning: come on, pick a more creative name
//!   --> src/main.rs:10:16
//!    |
//! 10 |     static ref FOO: String = "lazy_static".to_owned();
//!    |                ^^^
//! ```
//!
//! <br>
//!
//! # Testing
//!
//! When testing macros, we often care not just that the macro can be used
//! successfully but also that when the macro is provided with invalid input it
//! produces maximally helpful error messages. Consider using the [`trybuild`]
//! crate to write tests for errors that are emitted by your macro or errors
//! detected by the Rust compiler in the expanded code following misuse of the
//! macro. Such tests help avoid regressions from later refactors that
//! mistakenly make an error no longer trigger or be less helpful than it used
//! to be.
//!
//! [`trybuild`]: https://github.com/dtolnay/trybuild
//!
//! <br>
//!
//! # Debugging
//!
//! When developing a procedural macro it can be helpful to look at what the
//! generated code looks like. Use `cargo rustc -- -Zunstable-options
//! --pretty=expanded` or the [`cargo expand`] subcommand.
//!
//! [`cargo expand`]: https://github.com/dtolnay/cargo-expand
//!
//! To show the expanded code for some crate that uses your procedural macro,
//! run `cargo expand` from that crate. To show the expanded code for one of
//! your own test cases, run `cargo expand --test the_test_case` where the last
//! argument is the name of the test file without the `.rs` extension.
//!
//! This write-up by Brandon W Maister discusses debugging in more detail:
//! [Debugging Rust's new Custom Derive system][debugging].
//!
//! [debugging]: https://quodlibetor.github.io/posts/debugging-rusts-new-custom-derive-system/
//!
//! <br>
//!
//! # Optional features
//!
//! Syn puts a lot of functionality behind optional features in order to
//! optimize compile time for the most common use cases. The following features
//! are available.
//!
//! - **`derive`** *(enabled by default)* — Data structures for representing the
//!   possible input to a derive macro, including structs and enums and types.
//! - **`full`** — Data structures for representing the syntax tree of all valid
//!   Rust source code, including items and expressions.
//! - **`parsing`** *(enabled by default)* — Ability to parse input tokens into
//!   a syntax tree node of a chosen type.
//! - **`printing`** *(enabled by default)* — Ability to print a syntax tree
//!   node as tokens of Rust source code.
//! - **`visit`** — Trait for traversing a syntax tree.
//! - **`visit-mut`** — Trait for traversing and mutating in place a syntax
//!   tree.
//! - **`fold`** — Trait for transforming an owned syntax tree.
//! - **`clone-impls`** *(enabled by default)* — Clone impls for all syntax tree
//!   types.
//! - **`extra-traits`** — Debug, Eq, PartialEq, Hash impls for all syntax tree
//!   types.
//! - **`proc-macro`** *(enabled by default)* — Runtime dependency on the
//!   dynamic library libproc_macro from rustc toolchain.

// Syn types in rustdoc of other crates get linked to here.
#![doc(html_root_url = "https://docs.rs/syn/2.0.68")]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![deny(unsafe_op_in_unsafe_fn)]
#![allow(non_camel_case_types)]
#![cfg_attr(not(check_cfg), allow(unexpected_cfgs))]
#![allow(
    clippy::bool_to_int_with_if,
    clippy::cast_lossless,
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    clippy::cast_ptr_alignment,
    clippy::default_trait_access,
    clippy::derivable_impls,
    clippy::diverging_sub_expression,
    clippy::doc_markdown,
    clippy::expl_impl_clone_on_copy,
    clippy::explicit_auto_deref,
    clippy::if_not_else,
    clippy::inherent_to_string,
    clippy::into_iter_without_iter,
    clippy::items_after_statements,
    clippy::large_enum_variant,
    clippy::let_underscore_untyped, // https://github.com/rust-lang/rust-clippy/issues/10410
    clippy::manual_assert,
    clippy::manual_let_else,
    clippy::manual_map,
    clippy::match_like_matches_macro,
    clippy::match_on_vec_items,
    clippy::match_same_arms,
    clippy::match_wildcard_for_single_variants, // clippy bug: https://github.com/rust-lang/rust-clippy/issues/6984
    clippy::missing_errors_doc,
    clippy::missing_panics_doc,
    clippy::module_name_repetitions,
    clippy::must_use_candidate,
    clippy::needless_doctest_main,
    clippy::needless_pass_by_value,
    clippy::never_loop,
    clippy::range_plus_one,
    clippy::redundant_else,
    clippy::return_self_not_must_use,
    clippy::similar_names,
    clippy::single_match_else,
    clippy::struct_excessive_bools,
    clippy::too_many_arguments,
    clippy::too_many_lines,
    clippy::trivially_copy_pass_by_ref,
    clippy::unconditional_recursion, // https://github.com/rust-lang/rust-clippy/issues/12133
    clippy::uninhabited_references,
    clippy::uninlined_format_args,
    clippy::unnecessary_box_returns,
    clippy::unnecessary_unwrap,
    clippy::used_underscore_binding,
    clippy::wildcard_imports,
)]

#[cfg(feature = "proc-macro")]
extern crate proc_macro;

#[macro_use]
mod macros;

#[macro_use]
pub mod token;

#[cfg(any(feature = "full", feature = "derive"))]
mod attr;
#[cfg(any(feature = "full", feature = "derive"))]
#[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
pub use crate::attr::{AttrStyle, Attribute, Meta, MetaList, MetaNameValue};

mod bigint;
mod classify;
mod custom_keyword;


#[cfg(any(feature = "full", feature = "derive"))]
mod data;
#[cfg(any(feature = "full", feature = "derive"))]
#[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
pub use crate::data::{Field, Fields, FieldsNamed, FieldsUnnamed, Variant};

#[cfg(any(feature = "full", feature = "derive"))]
mod derive;
#[cfg(feature = "derive")]
#[cfg_attr(docsrs, doc(cfg(feature = "derive")))]
pub use crate::derive::{Data, DataEnum, DataStruct, DataUnion, DeriveInput};

mod drops;

mod error;
pub use crate::error::{Error, Result};

#[cfg(any(feature = "full", feature = "derive"))]
mod expr;
#[cfg(feature = "full")]
#[cfg_attr(docsrs, doc(cfg(feature = "full")))]
pub use crate::expr::{Arm, Label, RangeLimits};
#[cfg(any(feature = "full", feature = "derive"))]
#[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
pub use crate::expr::{
    Expr, ExprBinary, ExprCall, ExprCast, ExprField, ExprIndex, ExprLit, ExprMacro, ExprMethodCall,
    ExprParen, ExprPath, ExprReference, ExprStruct, ExprUnary, FieldValue, Index, Member,
};
#[cfg(any(feature = "full", feature = "derive"))]
#[cfg_attr(docsrs, doc(cfg(feature = "full")))]
pub use crate::expr::{
    ExprArray, ExprAssign, ExprAsync, ExprAwait, ExprBlock, ExprBreak, ExprClosure, ExprConst,
    ExprContinue, ExprForLoop, ExprGroup, ExprIf, ExprInfer, ExprLet, ExprLoop, ExprMatch,
    ExprRange, ExprRepeat, ExprReturn, ExprTry, ExprTryBlock, ExprTuple, ExprUnsafe, ExprWhile,
    ExprYield,
};


#[cfg(feature = "full")]
mod file;
#[cfg(feature = "full")]
#[cfg_attr(docsrs, doc(cfg(feature = "full")))]
pub use crate::file::File;

#[cfg(all(feature = "full", feature = "printing"))]
mod fixup;

#[cfg(any(feature = "full", feature = "derive"))]
mod generics;
#[cfg(any(feature = "full", feature = "derive"))]
#[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
pub use crate::generics::{
    BoundLifetimes, ConstParam, GenericParam, Generics, LifetimeParam, PredicateLifetime,
    PredicateType, TraitBound, TraitBoundModifier, TypeParam, TypeParamBound, WhereClause,
    WherePredicate,
};
#[cfg(all(any(feature = "full", feature = "derive"), feature = "printing"))]
#[cfg_attr(
    docsrs,
    doc(cfg(all(any(feature = "full", feature = "derive"), feature = "printing")))
)]
pub use crate::generics::{ImplGenerics, Turbofish, TypeGenerics};

mod ident;
#[doc(inline)]
pub use crate::ident::Ident;

#[cfg(feature = "full")]
mod item;
#[cfg(feature = "full")]
#[cfg_attr(docsrs, doc(cfg(feature = "full")))]
pub use crate::item::{
    FnArg, ForeignItem, ForeignItemFn, ForeignItemMacro, ForeignItemStatic, ForeignItemType,
    ImplItem, ImplItemConst, ImplItemFn, ImplItemMacro, ImplItemType, ImplRestriction, Item,
    ItemConst, ItemEnum, ItemExternCrate, ItemFn, ItemForeignMod, ItemImpl, ItemMacro, ItemMod,
    ItemStatic, ItemStruct, ItemTrait, ItemTraitAlias, ItemType, ItemUnion, ItemUse, Receiver,
    Signature, StaticMutability, TraitItem, TraitItemConst, TraitItemFn, TraitItemMacro,
    TraitItemType, UseGlob, UseGroup, UseName, UsePath, UseRename, UseTree, Variadic,
};

mod lifetime;
#[doc(inline)]
pub use crate::lifetime::Lifetime;

mod lit;
#[doc(hidden)] // https://github.com/dtolnay/syn/issues/1566
pub use crate::lit::StrStyle;
#[doc(inline)]
pub use crate::lit::{
    Lit, LitBool, LitByte, LitByteStr, LitCStr, LitChar, LitFloat, LitInt, LitStr,
};

#[cfg(any(feature = "full", feature = "derive"))]
mod mac;
#[cfg(any(feature = "full", feature = "derive"))]
#[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
pub use crate::mac::{Macro, MacroDelimiter};


#[cfg(any(feature = "full", feature = "derive"))]
mod op;
#[cfg(any(feature = "full", feature = "derive"))]
#[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
pub use crate::op::{BinOp, UnOp};


#[cfg(feature = "full")]
mod pat;
#[cfg(feature = "full")]
#[cfg_attr(docsrs, doc(cfg(feature = "full")))]
pub use crate::pat::{
    FieldPat, Pat, PatConst, PatIdent, PatLit, PatMacro, PatOr, PatParen, PatPath, PatRange,
    PatReference, PatRest, PatSlice, PatStruct, PatTuple, PatTupleStruct, PatType, PatWild,
};

#[cfg(any(feature = "full", feature = "derive"))]
mod path;
#[cfg(any(feature = "full", feature = "derive"))]
#[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
pub use crate::path::{
    AngleBracketedGenericArguments, AssocConst, AssocType, Constraint, GenericArgument,
    ParenthesizedGenericArguments, Path, PathArguments, PathSegment, QSelf,
};

#[cfg(all(
    any(feature = "full", feature = "derive"),
    any(feature = "parsing", feature = "printing")
))]
mod precedence;

#[cfg(all(any(feature = "full", feature = "derive"), feature = "printing"))]
mod print;

pub mod punctuated;

#[cfg(any(feature = "full", feature = "derive"))]
mod restriction;
#[cfg(any(feature = "full", feature = "derive"))]
#[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
pub use crate::restriction::{FieldMutability, VisRestricted, Visibility};

mod span;

#[cfg(all(feature = "parsing", feature = "printing"))]
#[cfg_attr(docsrs, doc(cfg(all(feature = "parsing", feature = "printing"))))]
pub mod spanned;

#[cfg(feature = "full")]
mod stmt;
#[cfg(feature = "full")]
#[cfg_attr(docsrs, doc(cfg(feature = "full")))]
pub use crate::stmt::{Block, Local, LocalInit, Stmt, StmtMacro};

mod thread;

#[cfg(all(any(feature = "full", feature = "derive"), feature = "extra-traits"))]
mod tt;

#[cfg(any(feature = "full", feature = "derive"))]
mod ty;
#[cfg(any(feature = "full", feature = "derive"))]
#[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
pub use crate::ty::{
    Abi, BareFnArg, BareVariadic, ReturnType, Type, TypeArray, TypeBareFn, TypeGroup,
    TypeImplTrait, TypeInfer, TypeMacro, TypeNever, TypeParen, TypePath, TypePtr, TypeReference,
    TypeSlice, TypeTraitObject, TypeTuple,
};


#[rustfmt::skip] // https://github.com/rust-lang/rustfmt/issues/6176
mod gen {
    #[cfg(feature = "clone-impls")]
    #[rustfmt::skip]
    mod clone;

    #[cfg(feature = "extra-traits")]
    #[rustfmt::skip]
    mod debug;

    #[cfg(feature = "extra-traits")]
    #[rustfmt::skip]
    mod eq;

    #[cfg(feature = "extra-traits")]
    #[rustfmt::skip]
    mod hash;
}


// Not public API.
#[path = "export.rs"]
pub mod __private;

