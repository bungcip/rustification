// #[cfg(feature = "parsing")]
// use crate::error::Error;
// #[cfg(feature = "parsing")]
// use crate::error::Result;
use crate::expr::Expr;
use crate::mac::MacroDelimiter;
use crate::path::Path;
use crate::token;
use proc_macro2::TokenStream;
#[cfg(feature = "printing")]
use std::iter;
#[cfg(feature = "printing")]
use std::slice;

ast_struct! {
    /// An attribute, like `#[repr(transparent)]`.
    ///
    /// <br>
    ///
    /// # Syntax
    ///
    /// Rust has six types of attributes.
    ///
    /// - Outer attributes like `#[repr(transparent)]`. These appear outside or
    ///   in front of the item they describe.
    ///
    /// - Inner attributes like `#![feature(proc_macro)]`. These appear inside
    ///   of the item they describe, usually a module.
    ///
    /// - Outer one-line doc comments like `/// Example`.
    ///
    /// - Inner one-line doc comments like `//! Please file an issue`.
    ///
    /// - Outer documentation blocks `/** Example */`.
    ///
    /// - Inner documentation blocks `/*! Please file an issue */`.
    ///
    /// The `style` field of type `AttrStyle` distinguishes whether an attribute
    /// is outer or inner.
    ///
    /// Every attribute has a `path` that indicates the intended interpretation
    /// of the rest of the attribute's contents. The path and the optional
    /// additional contents are represented together in the `meta` field of the
    /// attribute in three possible varieties:
    ///
    /// - Meta::Path &mdash; attributes whose information content conveys just a
    ///   path, for example the `#[test]` attribute.
    ///
    /// - Meta::List &mdash; attributes that carry arbitrary tokens after the
    ///   path, surrounded by a delimiter (parenthesis, bracket, or brace). For
    ///   example `#[derive(Copy)]` or `#[precondition(x < 5)]`.
    ///
    /// - Meta::NameValue &mdash; attributes with an `=` sign after the path,
    ///   followed by a Rust expression. For example `#[path =
    ///   "sys/windows.rs"]`.
    ///
    /// All doc comments are represented in the NameValue style with a path of
    /// "doc", as this is how they are processed by the compiler and by
    /// `macro_rules!` macros.
    ///
    /// ```text
    /// #[derive(Copy, Clone)]
    ///   ~~~~~~Path
    ///   ^^^^^^^^^^^^^^^^^^^Meta::List
    ///
    /// #[path = "sys/windows.rs"]
    ///   ~~~~Path
    ///   ^^^^^^^^^^^^^^^^^^^^^^^Meta::NameValue
    ///
    /// #[test]
    ///   ^^^^Meta::Path
    /// ```
    ///
    /// <br>
    ///
    /// # Parsing from tokens to Attribute
    ///
    /// This type does not implement the [`Parse`] trait and thus cannot be
    /// parsed directly by [`ParseStream::parse`]. Instead use
    /// [`ParseStream::call`] with one of the two parser functions
    /// [`Attribute::parse_outer`] or [`Attribute::parse_inner`] depending on
    /// which you intend to parse.
    ///
    /// [`Parse`]: crate::parse::Parse
    /// [`ParseStream::parse`]: crate::parse::ParseBuffer::parse
    /// [`ParseStream::call`]: crate::parse::ParseBuffer::call
    ///
    /// ```
    /// use rast::{Attribute, Ident, Result, Token};
    /// use rast::parse::{Parse, ParseStream};
    ///
    /// // Parses a unit struct with attributes.
    /// //
    /// //     #[path = "s.tmpl"]
    /// //     struct S;
    /// struct UnitStruct {
    ///     attrs: Vec<Attribute>,
    ///     struct_token: Token![struct],
    ///     name: Ident,
    ///     semi_token: Token![;],
    /// }
    ///
    /// impl Parse for UnitStruct {
    ///     fn parse(input: ParseStream) -> Result<Self> {
    ///         Ok(UnitStruct {
    ///             attrs: input.call(Attribute::parse_outer)?,
    ///             struct_token: input.parse()?,
    ///             name: input.parse()?,
    ///             semi_token: input.parse()?,
    ///         })
    ///     }
    /// }
    /// ```
    ///
    /// <p><br></p>
    ///
    /// # Parsing from Attribute to structured arguments
    ///
    /// The grammar of attributes in Rust is very flexible, which makes the
    /// syntax tree not that useful on its own. In particular, arguments of the
    /// `Meta::List` variety of attribute are held in an arbitrary `tokens:
    /// TokenStream`. Macros are expected to check the `path` of the attribute,
    /// decide whether they recognize it, and then parse the remaining tokens
    /// according to whatever grammar they wish to require for that kind of
    /// attribute. Use [`parse_args()`] to parse those tokens into the expected
    /// data structure.
    ///
    /// [`parse_args()`]: Attribute::parse_args
    ///
    /// <p><br></p>
    ///
    /// # Doc comments
    ///
    /// The compiler transforms doc comments, such as `/// comment` and `/*!
    /// comment */`, into attributes before macros are expanded. Each comment is
    /// expanded into an attribute of the form `#[doc = r"comment"]`.
    ///
    /// As an example, the following `mod` items are expanded identically:
    ///
    /// ```
    /// # use rast::{ItemMod, parse_quote};
    /// let doc: ItemMod = parse_quote! {
    ///     /// Single line doc comments
    ///     /// We write so many!
    ///     /**
    ///      * Multi-line comments...
    ///      * May span many lines
    ///      */
    ///     mod example {
    ///         //! Of course, they can be inner too
    ///         /*! And fit in a single line */
    ///     }
    /// };
    /// let attr: ItemMod = parse_quote! {
    ///     #[doc = r" Single line doc comments"]
    ///     #[doc = r" We write so many!"]
    ///     #[doc = r"
    ///      * Multi-line comments...
    ///      * May span many lines
    ///      "]
    ///     mod example {
    ///         #![doc = r" Of course, they can be inner too"]
    ///         #![doc = r" And fit in a single line "]
    ///     }
    /// };
    /// assert_eq!(doc, attr);
    /// ```
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct Attribute {
        pub pound_token: Token![#],
        pub style: AttrStyle,
        pub bracket_token: token::Bracket,
        pub meta: Meta,
    }
}

impl Attribute {
    /// Returns the path that identifies the interpretation of this attribute.
    ///
    /// For example this would return the `test` in `#[test]`, the `derive` in
    /// `#[derive(Copy)]`, and the `path` in `#[path = "sys/windows.rs"]`.
    pub fn path(&self) -> &Path {
        self.meta.path()
    }


 

}

ast_enum! {
    /// Distinguishes between attributes that decorate an item and attributes
    /// that are contained within an item.
    ///
    /// # Outer attributes
    ///
    /// - `#[repr(transparent)]`
    /// - `/// # Example`
    /// - `/** Please file an issue */`
    ///
    /// # Inner attributes
    ///
    /// - `#![feature(proc_macro)]`
    /// - `//! # Example`
    /// - `/*! Please file an issue */`
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub enum AttrStyle {
        Outer,
        Inner(Token![!]),
    }
}

ast_enum_of_structs! {
    /// Content of a compile-time structured attribute.
    ///
    /// ## Path
    ///
    /// A meta path is like the `test` in `#[test]`.
    ///
    /// ## List
    ///
    /// A meta list is like the `derive(Copy)` in `#[derive(Copy)]`.
    ///
    /// ## NameValue
    ///
    /// A name-value meta is like the `path = "..."` in `#[path =
    /// "sys/windows.rs"]`.
    ///
    /// # Syntax tree enum
    ///
    /// This type is a [syntax tree enum].
    ///
    /// [syntax tree enum]: crate::expr::Expr#syntax-tree-enums
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub enum Meta {
        Path(Path),

        /// A structured list within an attribute, like `derive(Copy, Clone)`.
        List(MetaList),

        /// A name-value pair within an attribute, like `feature = "nightly"`.
        NameValue(MetaNameValue),
    }
}

ast_struct! {
    /// A structured list within an attribute, like `derive(Copy, Clone)`.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct MetaList {
        pub path: Path,
        pub delimiter: MacroDelimiter,
        pub tokens: TokenStream,
    }
}

ast_struct! {
    /// A name-value pair within an attribute, like `feature = "nightly"`.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct MetaNameValue {
        pub path: Path,
        pub eq_token: Token![=],
        pub value: Expr,
    }
}

impl Meta {
    /// Returns the path that begins this structured meta item.
    ///
    /// For example this would return the `test` in `#[test]`, the `derive` in
    /// `#[derive(Copy)]`, and the `path` in `#[path = "sys/windows.rs"]`.
    pub fn path(&self) -> &Path {
        match self {
            Meta::Path(path) => path,
            Meta::List(meta) => &meta.path,
            Meta::NameValue(meta) => &meta.path,
        }
    }

    // /// Error if this is a `Meta::List` or `Meta::NameValue`.
    // #[cfg(feature = "parsing")]
    // #[cfg_attr(docsrs, doc(cfg(feature = "parsing")))]
    // pub fn require_path_only(&self) -> Result<&Path> {
    //     let error_span = match self {
    //         Meta::Path(path) => return Ok(path),
    //         Meta::List(meta) => meta.delimiter.span().open(),
    //         Meta::NameValue(meta) => meta.eq_token.span,
    //     };
    //     Err(Error::new(error_span, "unexpected token in attribute"))
    // }

    // #[cfg(feature = "parsing")]
    // #[cfg_attr(docsrs, doc(cfg(feature = "parsing")))]
    // pub fn require_list(&self) -> Result<&MetaList> {
    //     match self {
    //         Meta::List(meta) => Ok(meta),
    //         Meta::Path(path) => Err(crate::error::new2(
    //             path.segments.first().unwrap().ident.span(),
    //             path.segments.last().unwrap().ident.span(),
    //             format!(
    //                 "expected attribute arguments in parentheses: `{}(...)`",
    //                 parsing::DisplayPath(path),
    //             ),
    //         )),
    //         Meta::NameValue(meta) => Err(Error::new(meta.eq_token.span, "expected `(`")),
    //     }
    // }

    // #[cfg(feature = "parsing")]
    // #[cfg_attr(docsrs, doc(cfg(feature = "parsing")))]
    // pub fn require_name_value(&self) -> Result<&MetaNameValue> {
    //     match self {
    //         Meta::NameValue(meta) => Ok(meta),
    //         Meta::Path(path) => Err(crate::error::new2(
    //             path.segments.first().unwrap().ident.span(),
    //             path.segments.last().unwrap().ident.span(),
    //             format!(
    //                 "expected a value for this attribute: `{} = ...`",
    //                 parsing::DisplayPath(path),
    //             ),
    //         )),
    //         Meta::List(meta) => Err(Error::new(meta.delimiter.span().open(), "expected `=`")),
    //     }
    // }
}

impl MetaList {


}

#[cfg(feature = "printing")]
pub(crate) trait FilterAttrs<'a> {
    type Ret: Iterator<Item = &'a Attribute>;

    fn outer(self) -> Self::Ret;
    #[cfg(feature = "full")]
    fn inner(self) -> Self::Ret;
}

#[cfg(feature = "printing")]
impl<'a> FilterAttrs<'a> for &'a [Attribute] {
    type Ret = iter::Filter<slice::Iter<'a, Attribute>, fn(&&Attribute) -> bool>;

    fn outer(self) -> Self::Ret {
        fn is_outer(attr: &&Attribute) -> bool {
            match attr.style {
                AttrStyle::Outer => true,
                AttrStyle::Inner(_) => false,
            }
        }
        self.iter().filter(is_outer)
    }

    #[cfg(feature = "full")]
    fn inner(self) -> Self::Ret {
        fn is_inner(attr: &&Attribute) -> bool {
            match attr.style {
                AttrStyle::Inner(_) => true,
                AttrStyle::Outer => false,
            }
        }
        self.iter().filter(is_inner)
    }
}

#[cfg(feature = "printing")]
mod printing {
    use crate::attr::{AttrStyle, Attribute, MetaList, MetaNameValue};
    use proc_macro2::TokenStream;
    use quote::ToTokens;

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for Attribute {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.pound_token.to_tokens(tokens);
            if let AttrStyle::Inner(b) = &self.style {
                b.to_tokens(tokens);
            }
            self.bracket_token.surround(tokens, |tokens| {
                self.meta.to_tokens(tokens);
            });
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for MetaList {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.path.to_tokens(tokens);
            self.delimiter.surround(tokens, self.tokens.clone());
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for MetaNameValue {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.path.to_tokens(tokens);
            self.eq_token.to_tokens(tokens);
            self.value.to_tokens(tokens);
        }
    }
}
