use self::private::WithSpan;
use crate::span::IntoSpans;
use proc_macro2::extra::DelimSpan;
use proc_macro2::Span;
use proc_macro2::TokenStream;
use proc_macro2::{Delimiter, Ident};
use quote::{ToTokens, TokenStreamExt};
use std::cmp;
use std::fmt::{self, Debug};
use std::hash::{Hash, Hasher};
use std::ops::{Deref, DerefMut};

pub(crate) mod private {
    use proc_macro2::Span;

    /// Support writing `token.span` rather than `token.spans[0]` on tokens that
    /// hold a single span.
    #[repr(transparent)]
    #[allow(unknown_lints, repr_transparent_external_private_fields)] // False positive: https://github.com/rust-lang/rust/issues/78586#issuecomment-1722680482
    pub struct WithSpan {
        pub span: Span,
    }
}

macro_rules! impl_low_level_token {
    ($display:literal $($path:ident)::+ $get:ident) => {};
}

impl_low_level_token!("punctuation token" Punct punct);
impl_low_level_token!("literal" Literal literal);
impl_low_level_token!("token" TokenTree token_tree);
impl_low_level_token!("group token" proc_macro2::Group any_group);
impl_low_level_token!("lifetime" Lifetime lifetime);

macro_rules! define_keywords {
    ($($token:literal pub struct $name:ident)*) => {
        $(
            #[doc = concat!('`', $token, '`')]
            ///
            /// Don't try to remember the name of this type &mdash; use the
            /// [`Token!`] macro instead.
            ///
            /// [`Token!`]: crate::token
            pub struct $name {
                pub span: Span,
            }

            #[doc(hidden)]
            #[allow(non_snake_case)]
            pub fn $name<S: IntoSpans<Span>>(span: S) -> $name {
                $name {
                    span: span.into_spans(),
                }
            }

            impl std::default::Default for $name {
                fn default() -> Self {
                    $name {
                        span: Span::call_site(),
                    }
                }
            }

            #[cfg(feature = "clone-impls")]
            #[cfg_attr(docsrs, doc(cfg(feature = "clone-impls")))]
            impl Copy for $name {}

            #[cfg(feature = "clone-impls")]
            #[cfg_attr(docsrs, doc(cfg(feature = "clone-impls")))]
            impl Clone for $name {
                fn clone(&self) -> Self {
                    *self
                }
            }

            #[cfg(feature = "extra-traits")]
            #[cfg_attr(docsrs, doc(cfg(feature = "extra-traits")))]
            impl Debug for $name {
                fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                    f.write_str(stringify!($name))
                }
            }

            #[cfg(feature = "extra-traits")]
            #[cfg_attr(docsrs, doc(cfg(feature = "extra-traits")))]
            impl cmp::Eq for $name {}

            #[cfg(feature = "extra-traits")]
            #[cfg_attr(docsrs, doc(cfg(feature = "extra-traits")))]
            impl PartialEq for $name {
                fn eq(&self, _other: &$name) -> bool {
                    true
                }
            }

            #[cfg(feature = "extra-traits")]
            #[cfg_attr(docsrs, doc(cfg(feature = "extra-traits")))]
            impl Hash for $name {
                fn hash<H: Hasher>(&self, _state: &mut H) {}
            }

            #[cfg(feature = "printing")]
            #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
            impl ToTokens for $name {
                fn to_tokens(&self, tokens: &mut TokenStream) {
                    printing::keyword($token, self.span, tokens);
                }
            }

        )*
    };
}

macro_rules! impl_deref_if_len_is_1 {
    ($name:ident/1) => {
        impl Deref for $name {
            type Target = WithSpan;

            fn deref(&self) -> &Self::Target {
                unsafe { &*(self as *const Self).cast::<WithSpan>() }
            }
        }

        impl DerefMut for $name {
            fn deref_mut(&mut self) -> &mut Self::Target {
                unsafe { &mut *(self as *mut Self).cast::<WithSpan>() }
            }
        }
    };

    ($name:ident/$len:literal) => {};
}

macro_rules! define_punctuation_structs {
    ($($token:literal pub struct $name:ident/$len:tt #[doc = $usage:literal])*) => {
        $(
            #[cfg_attr(not(doc), repr(transparent))]
            #[allow(unknown_lints, repr_transparent_external_private_fields)] // False positive: https://github.com/rust-lang/rust/issues/78586#issuecomment-1722680482
            #[doc = concat!('`', $token, '`')]
            ///
            /// Usage:
            #[doc = concat!($usage, '.')]
            ///
            /// Don't try to remember the name of this type &mdash; use the
            /// [`Token!`] macro instead.
            ///
            /// [`Token!`]: crate::token
            pub struct $name {
                pub spans: [Span; $len],
            }

            #[doc(hidden)]
            #[allow(non_snake_case)]
            pub fn $name<S: IntoSpans<[Span; $len]>>(spans: S) -> $name {
                $name {
                    spans: spans.into_spans(),
                }
            }

            impl std::default::Default for $name {
                fn default() -> Self {
                    $name {
                        spans: [Span::call_site(); $len],
                    }
                }
            }

            #[cfg(feature = "clone-impls")]
            #[cfg_attr(docsrs, doc(cfg(feature = "clone-impls")))]
            impl Copy for $name {}

            #[cfg(feature = "clone-impls")]
            #[cfg_attr(docsrs, doc(cfg(feature = "clone-impls")))]
            impl Clone for $name {
                fn clone(&self) -> Self {
                    *self
                }
            }

            #[cfg(feature = "extra-traits")]
            #[cfg_attr(docsrs, doc(cfg(feature = "extra-traits")))]
            impl Debug for $name {
                fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                    f.write_str(stringify!($name))
                }
            }

            #[cfg(feature = "extra-traits")]
            #[cfg_attr(docsrs, doc(cfg(feature = "extra-traits")))]
            impl cmp::Eq for $name {}

            #[cfg(feature = "extra-traits")]
            #[cfg_attr(docsrs, doc(cfg(feature = "extra-traits")))]
            impl PartialEq for $name {
                fn eq(&self, _other: &$name) -> bool {
                    true
                }
            }

            #[cfg(feature = "extra-traits")]
            #[cfg_attr(docsrs, doc(cfg(feature = "extra-traits")))]
            impl Hash for $name {
                fn hash<H: Hasher>(&self, _state: &mut H) {}
            }

            impl_deref_if_len_is_1!($name/$len);
        )*
    };
}

macro_rules! define_punctuation {
    ($($token:literal pub struct $name:ident/$len:tt #[doc = $usage:literal])*) => {
        $(
            define_punctuation_structs! {
                $token pub struct $name/$len #[doc = $usage]
            }

            #[cfg(feature = "printing")]
            #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
            impl ToTokens for $name {
                fn to_tokens(&self, tokens: &mut TokenStream) {
                    printing::punct($token, &self.spans, tokens);
                }
            }

        )*
    };
}

macro_rules! define_delimiters {
    ($($delim:ident pub struct $name:ident #[$doc:meta])*) => {
        $(
            #[$doc]
            pub struct $name {
                pub span: DelimSpan,
            }

            #[doc(hidden)]
            #[allow(non_snake_case)]
            pub fn $name<S: IntoSpans<DelimSpan>>(span: S) -> $name {
                $name {
                    span: span.into_spans(),
                }
            }

            impl std::default::Default for $name {
                fn default() -> Self {
                    $name(Span::call_site())
                }
            }

            #[cfg(feature = "clone-impls")]
            #[cfg_attr(docsrs, doc(cfg(feature = "clone-impls")))]
            impl Copy for $name {}

            #[cfg(feature = "clone-impls")]
            #[cfg_attr(docsrs, doc(cfg(feature = "clone-impls")))]
            impl Clone for $name {
                fn clone(&self) -> Self {
                    *self
                }
            }

            #[cfg(feature = "extra-traits")]
            #[cfg_attr(docsrs, doc(cfg(feature = "extra-traits")))]
            impl Debug for $name {
                fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                    f.write_str(stringify!($name))
                }
            }

            #[cfg(feature = "extra-traits")]
            #[cfg_attr(docsrs, doc(cfg(feature = "extra-traits")))]
            impl cmp::Eq for $name {}

            #[cfg(feature = "extra-traits")]
            #[cfg_attr(docsrs, doc(cfg(feature = "extra-traits")))]
            impl PartialEq for $name {
                fn eq(&self, _other: &$name) -> bool {
                    true
                }
            }

            #[cfg(feature = "extra-traits")]
            #[cfg_attr(docsrs, doc(cfg(feature = "extra-traits")))]
            impl Hash for $name {
                fn hash<H: Hasher>(&self, _state: &mut H) {}
            }

            impl $name {
                #[cfg(feature = "printing")]
                pub fn surround<F>(&self, tokens: &mut TokenStream, f: F)
                where
                    F: FnOnce(&mut TokenStream),
                {
                    let mut inner = TokenStream::new();
                    f(&mut inner);
                    printing::delim(Delimiter::$delim, self.span.join(), tokens, inner);
                }
            }

        )*
    };
}

define_punctuation_structs! {
    "_" pub struct Underscore/1 /// wildcard patterns, inferred types, unnamed items in constants, extern crates, use declarations, and destructuring assignment
}

#[cfg(feature = "printing")]
#[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
impl ToTokens for Underscore {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        tokens.append(Ident::new("_", self.span));
    }
}

/// None-delimited group
pub struct Group {
    pub span: Span,
}

#[doc(hidden)]
#[allow(non_snake_case)]
pub fn Group<S: IntoSpans<Span>>(span: S) -> Group {
    Group {
        span: span.into_spans(),
    }
}

impl std::default::Default for Group {
    fn default() -> Self {
        Group {
            span: Span::call_site(),
        }
    }
}

#[cfg(feature = "clone-impls")]
#[cfg_attr(docsrs, doc(cfg(feature = "clone-impls")))]
impl Copy for Group {}

#[cfg(feature = "clone-impls")]
#[cfg_attr(docsrs, doc(cfg(feature = "clone-impls")))]
impl Clone for Group {
    fn clone(&self) -> Self {
        *self
    }
}

#[cfg(feature = "extra-traits")]
#[cfg_attr(docsrs, doc(cfg(feature = "extra-traits")))]
impl Debug for Group {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("Group")
    }
}

#[cfg(feature = "extra-traits")]
#[cfg_attr(docsrs, doc(cfg(feature = "extra-traits")))]
impl cmp::Eq for Group {}

#[cfg(feature = "extra-traits")]
#[cfg_attr(docsrs, doc(cfg(feature = "extra-traits")))]
impl PartialEq for Group {
    fn eq(&self, _other: &Group) -> bool {
        true
    }
}

#[cfg(feature = "extra-traits")]
#[cfg_attr(docsrs, doc(cfg(feature = "extra-traits")))]
impl Hash for Group {
    fn hash<H: Hasher>(&self, _state: &mut H) {}
}

impl Group {
    #[cfg(feature = "printing")]
    pub fn surround<F>(&self, tokens: &mut TokenStream, f: F)
    where
        F: FnOnce(&mut TokenStream),
    {
        let mut inner = TokenStream::new();
        f(&mut inner);
        printing::delim(Delimiter::None, self.span, tokens, inner);
    }
}

define_keywords! {
    "abstract"    pub struct Abstract
    "as"          pub struct As
    "async"       pub struct Async
    "auto"        pub struct Auto
    "await"       pub struct Await
    "become"      pub struct Become
    "box"         pub struct Box
    "break"       pub struct Break
    "const"       pub struct Const
    "continue"    pub struct Continue
    "crate"       pub struct Crate
    "default"     pub struct Default
    "do"          pub struct Do
    "dyn"         pub struct Dyn
    "else"        pub struct Else
    "enum"        pub struct Enum
    "extern"      pub struct Extern
    "final"       pub struct Final
    "fn"          pub struct Fn
    "for"         pub struct For
    "if"          pub struct If
    "impl"        pub struct Impl
    "in"          pub struct In
    "let"         pub struct Let
    "loop"        pub struct Loop
    "macro"       pub struct Macro
    "match"       pub struct Match
    "mod"         pub struct Mod
    "move"        pub struct Move
    "mut"         pub struct Mut
    "override"    pub struct Override
    "priv"        pub struct Priv
    "pub"         pub struct Pub
    "ref"         pub struct Ref
    "return"      pub struct Return
    "Self"        pub struct SelfType
    "self"        pub struct SelfValue
    "static"      pub struct Static
    "struct"      pub struct Struct
    "super"       pub struct Super
    "trait"       pub struct Trait
    "try"         pub struct Try
    "type"        pub struct Type
    "typeof"      pub struct Typeof
    "union"       pub struct Union
    "unsafe"      pub struct Unsafe
    "unsized"     pub struct Unsized
    "use"         pub struct Use
    "virtual"     pub struct Virtual
    "where"       pub struct Where
    "while"       pub struct While
    "yield"       pub struct Yield
}

define_punctuation! {
    "&"           pub struct And/1        /// bitwise and logical AND, borrow, references, reference patterns
    "&&"          pub struct AndAnd/2     /// lazy AND, borrow, references, reference patterns
    "&="          pub struct AndEq/2      /// bitwise AND assignment
    "@"           pub struct At/1         /// subpattern binding
    "^"           pub struct Caret/1      /// bitwise and logical XOR
    "^="          pub struct CaretEq/2    /// bitwise XOR assignment
    ":"           pub struct Colon/1      /// various separators
    ","           pub struct Comma/1      /// various separators
    "$"           pub struct Dollar/1     /// macros
    "."           pub struct Dot/1        /// field access, tuple index
    ".."          pub struct DotDot/2     /// range, struct expressions, patterns, range patterns
    "..."         pub struct DotDotDot/3  /// variadic functions, range patterns
    "..="         pub struct DotDotEq/3   /// inclusive range, range patterns
    "="           pub struct Eq/1         /// assignment, attributes, various type definitions
    "=="          pub struct EqEq/2       /// equal
    "=>"          pub struct FatArrow/2   /// match arms, macros
    ">="          pub struct Ge/2         /// greater than or equal to, generics
    ">"           pub struct Gt/1         /// greater than, generics, paths
    "<-"          pub struct LArrow/2     /// unused
    "<="          pub struct Le/2         /// less than or equal to
    "<"           pub struct Lt/1         /// less than, generics, paths
    "-"           pub struct Minus/1      /// subtraction, negation
    "-="          pub struct MinusEq/2    /// subtraction assignment
    "!="          pub struct Ne/2         /// not equal
    "!"           pub struct Not/1        /// bitwise and logical NOT, macro calls, inner attributes, never type, negative impls
    "|"           pub struct Or/1         /// bitwise and logical OR, closures, patterns in match, if let, and while let
    "|="          pub struct OrEq/2       /// bitwise OR assignment
    "||"          pub struct OrOr/2       /// lazy OR, closures
    "::"          pub struct PathSep/2    /// path separator
    "%"           pub struct Percent/1    /// remainder
    "%="          pub struct PercentEq/2  /// remainder assignment
    "+"           pub struct Plus/1       /// addition, trait bounds, macro Kleene matcher
    "+="          pub struct PlusEq/2     /// addition assignment
    "#"           pub struct Pound/1      /// attributes
    "?"           pub struct Question/1   /// question mark operator, questionably sized, macro Kleene matcher
    "->"          pub struct RArrow/2     /// function return type, closure return type, function pointer type
    ";"           pub struct Semi/1       /// terminator for various items and statements, array types
    "<<"          pub struct Shl/2        /// shift left, nested generics
    "<<="         pub struct ShlEq/3      /// shift left assignment
    ">>"          pub struct Shr/2        /// shift right, nested generics
    ">>="         pub struct ShrEq/3      /// shift right assignment, nested generics
    "/"           pub struct Slash/1      /// division
    "/="          pub struct SlashEq/2    /// division assignment
    "*"           pub struct Star/1       /// multiplication, dereference, raw pointers, macro Kleene matcher, use wildcards
    "*="          pub struct StarEq/2     /// multiplication assignment
    "~"           pub struct Tilde/1      /// unused since before Rust 1.0
}

define_delimiters! {
    Brace         pub struct Brace        /// `{`&hellip;`}`
    Bracket       pub struct Bracket      /// `[`&hellip;`]`
    Parenthesis   pub struct Paren        /// `(`&hellip;`)`
}

/// A type-macro that expands to the name of the Rust type representation of a
/// given token.
///
/// As a type, `Token!` is commonly used in the type of struct fields, the type
/// of a `let` statement, or in turbofish for a `parse` function.
///
/// ```
/// use rast::{Ident, Token};
/// use rast::parse::{Parse, ParseStream, Result};
///
/// // `struct Foo;`
/// pub struct UnitStruct {
///     struct_token: Token![struct],
///     ident: Ident,
///     semi_token: Token![;],
/// }
///
/// impl Parse for UnitStruct {
///     fn parse(input: ParseStream) -> Result<Self> {
///         let struct_token: Token![struct] = input.parse()?;
///         let ident: Ident = input.parse()?;
///         let semi_token = input.parse::<Token![;]>()?;
///         Ok(UnitStruct { struct_token, ident, semi_token })
///     }
/// }
/// ```
///
/// As an expression, `Token!` is used for peeking tokens or instantiating
/// tokens from a span.
///
/// ```
/// # use rast::{Ident, Token};
/// # use rast::parse::{Parse, ParseStream, Result};
/// #
/// # struct UnitStruct {
/// #     struct_token: Token![struct],
/// #     ident: Ident,
/// #     semi_token: Token![;],
/// # }
/// #
/// # impl Parse for UnitStruct {
/// #     fn parse(input: ParseStream) -> Result<Self> {
/// #         unimplemented!()
/// #     }
/// # }
/// #
/// fn make_unit_struct(name: Ident) -> UnitStruct {
///     let span = name.span();
///     UnitStruct {
///         struct_token: Token![struct](span),
///         ident: name,
///         semi_token: Token![;](span),
///     }
/// }
///
/// # fn parse(input: ParseStream) -> Result<()> {
/// if input.peek(Token![struct]) {
///     let unit_struct: UnitStruct = input.parse()?;
///     /* ... */
/// }
/// # Ok(())
/// # }
/// ```
///
/// See the [token module] documentation for details and examples.
///
/// [token module]: crate::token
#[macro_export]
macro_rules! Token {
    [abstract]    => { $crate::token::Abstract };
    [as]          => { $crate::token::As };
    [async]       => { $crate::token::Async };
    [auto]        => { $crate::token::Auto };
    [await]       => { $crate::token::Await };
    [become]      => { $crate::token::Become };
    [box]         => { $crate::token::Box };
    [break]       => { $crate::token::Break };
    [const]       => { $crate::token::Const };
    [continue]    => { $crate::token::Continue };
    [crate]       => { $crate::token::Crate };
    [default]     => { $crate::token::Default };
    [do]          => { $crate::token::Do };
    [dyn]         => { $crate::token::Dyn };
    [else]        => { $crate::token::Else };
    [enum]        => { $crate::token::Enum };
    [extern]      => { $crate::token::Extern };
    [final]       => { $crate::token::Final };
    [fn]          => { $crate::token::Fn };
    [for]         => { $crate::token::For };
    [if]          => { $crate::token::If };
    [impl]        => { $crate::token::Impl };
    [in]          => { $crate::token::In };
    [let]         => { $crate::token::Let };
    [loop]        => { $crate::token::Loop };
    [macro]       => { $crate::token::Macro };
    [match]       => { $crate::token::Match };
    [mod]         => { $crate::token::Mod };
    [move]        => { $crate::token::Move };
    [mut]         => { $crate::token::Mut };
    [override]    => { $crate::token::Override };
    [priv]        => { $crate::token::Priv };
    [pub]         => { $crate::token::Pub };
    [ref]         => { $crate::token::Ref };
    [return]      => { $crate::token::Return };
    [Self]        => { $crate::token::SelfType };
    [self]        => { $crate::token::SelfValue };
    [static]      => { $crate::token::Static };
    [struct]      => { $crate::token::Struct };
    [super]       => { $crate::token::Super };
    [trait]       => { $crate::token::Trait };
    [try]         => { $crate::token::Try };
    [type]        => { $crate::token::Type };
    [typeof]      => { $crate::token::Typeof };
    [union]       => { $crate::token::Union };
    [unsafe]      => { $crate::token::Unsafe };
    [unsized]     => { $crate::token::Unsized };
    [use]         => { $crate::token::Use };
    [virtual]     => { $crate::token::Virtual };
    [where]       => { $crate::token::Where };
    [while]       => { $crate::token::While };
    [yield]       => { $crate::token::Yield };
    [&]           => { $crate::token::And };
    [&&]          => { $crate::token::AndAnd };
    [&=]          => { $crate::token::AndEq };
    [@]           => { $crate::token::At };
    [^]           => { $crate::token::Caret };
    [^=]          => { $crate::token::CaretEq };
    [:]           => { $crate::token::Colon };
    [,]           => { $crate::token::Comma };
    [$]           => { $crate::token::Dollar };
    [.]           => { $crate::token::Dot };
    [..]          => { $crate::token::DotDot };
    [...]         => { $crate::token::DotDotDot };
    [..=]         => { $crate::token::DotDotEq };
    [=]           => { $crate::token::Eq };
    [==]          => { $crate::token::EqEq };
    [=>]          => { $crate::token::FatArrow };
    [>=]          => { $crate::token::Ge };
    [>]           => { $crate::token::Gt };
    [<-]          => { $crate::token::LArrow };
    [<=]          => { $crate::token::Le };
    [<]           => { $crate::token::Lt };
    [-]           => { $crate::token::Minus };
    [-=]          => { $crate::token::MinusEq };
    [!=]          => { $crate::token::Ne };
    [!]           => { $crate::token::Not };
    [|]           => { $crate::token::Or };
    [|=]          => { $crate::token::OrEq };
    [||]          => { $crate::token::OrOr };
    [::]          => { $crate::token::PathSep };
    [%]           => { $crate::token::Percent };
    [%=]          => { $crate::token::PercentEq };
    [+]           => { $crate::token::Plus };
    [+=]          => { $crate::token::PlusEq };
    [#]           => { $crate::token::Pound };
    [?]           => { $crate::token::Question };
    [->]          => { $crate::token::RArrow };
    [;]           => { $crate::token::Semi };
    [<<]          => { $crate::token::Shl };
    [<<=]         => { $crate::token::ShlEq };
    [>>]          => { $crate::token::Shr };
    [>>=]         => { $crate::token::ShrEq };
    [/]           => { $crate::token::Slash };
    [/=]          => { $crate::token::SlashEq };
    [*]           => { $crate::token::Star };
    [*=]          => { $crate::token::StarEq };
    [~]           => { $crate::token::Tilde };
    [_]           => { $crate::token::Underscore };
}

// Not public API.
#[doc(hidden)]
#[cfg(feature = "printing")]
pub(crate) mod printing {
    use proc_macro2::{Delimiter, Group, Ident, Punct, Spacing, Span, TokenStream};
    use quote::TokenStreamExt;

    #[doc(hidden)]
    pub fn punct(s: &str, spans: &[Span], tokens: &mut TokenStream) {
        assert_eq!(s.len(), spans.len());

        let mut chars = s.chars();
        let mut spans = spans.iter();
        let ch = chars.next_back().unwrap();
        let span = spans.next_back().unwrap();
        for (ch, span) in chars.zip(spans) {
            let mut op = Punct::new(ch, Spacing::Joint);
            op.set_span(*span);
            tokens.append(op);
        }

        let mut op = Punct::new(ch, Spacing::Alone);
        op.set_span(*span);
        tokens.append(op);
    }

    pub(crate) fn keyword(s: &str, span: Span, tokens: &mut TokenStream) {
        tokens.append(Ident::new(s, span));
    }

    pub(crate) fn delim(
        delim: Delimiter,
        span: Span,
        tokens: &mut TokenStream,
        inner: TokenStream,
    ) {
        let mut g = Group::new(delim, inner);
        g.set_span(span);
        tokens.append(g);
    }
}
