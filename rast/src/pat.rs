use crate::attr::Attribute;
use crate::expr::Member;
use crate::ident::Ident;
use crate::path::{Path, QSelf};
use crate::punctuated::Punctuated;
use crate::token;
use crate::ty::Type;
use proc_macro2::TokenStream;

pub use crate::expr::{
    ExprConst as PatConst, ExprLit as PatLit, ExprMacro as PatMacro, ExprPath as PatPath,
    ExprRange as PatRange,
};

ast_enum_of_structs! {
    /// A pattern in a local binding, function signature, match expression, or
    /// various other places.
    ///
    /// # Syntax tree enum
    ///
    /// This type is a [syntax tree enum].
    ///
    /// [syntax tree enum]: crate::expr::Expr#syntax-tree-enums
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    #[non_exhaustive]
    pub enum Pat {
        /// A const block: `const { ... }`.
        Const(PatConst),

        /// A pattern that binds a new variable: `ref mut binding @ SUBPATTERN`.
        Ident(PatIdent),

        /// A literal pattern: `0`.
        Lit(PatLit),

        /// A macro in pattern position.
        Macro(PatMacro),

        /// A pattern that matches any one of a set of cases.
        Or(PatOr),

        /// A parenthesized pattern: `(A | B)`.
        Paren(PatParen),

        /// A path pattern like `Color::Red`, optionally qualified with a
        /// self-type.
        ///
        /// Unqualified path patterns can legally refer to variants, structs,
        /// constants or associated constants. Qualified path patterns like
        /// `<A>::B::C` and `<A as Trait>::B::C` can only legally refer to
        /// associated constants.
        Path(PatPath),

        /// A range pattern: `1..=2`.
        Range(PatRange),

        /// A reference pattern: `&mut var`.
        Reference(PatReference),

        /// The dots in a tuple or slice pattern: `[0, 1, ..]`.
        Rest(PatRest),

        /// A dynamically sized slice pattern: `[a, b, ref i @ .., y, z]`.
        Slice(PatSlice),

        /// A struct or struct variant pattern: `Variant { x, y, .. }`.
        Struct(PatStruct),

        /// A tuple pattern: `(a, b)`.
        Tuple(PatTuple),

        /// A tuple struct or tuple variant pattern: `Variant(x, y, .., z)`.
        TupleStruct(PatTupleStruct),

        /// A type ascription pattern: `foo: f64`.
        Type(PatType),

        /// Tokens in pattern position not interpreted by Syn.
        Verbatim(TokenStream),

        /// A pattern that matches any value: `_`.
        Wild(PatWild),

        // For testing exhaustiveness in downstream code, use the following idiom:
        //
        //     match pat {
        //         #![cfg_attr(test, deny(non_exhaustive_omitted_patterns))]
        //
        //         Pat::Box(pat) => {...}
        //         Pat::Ident(pat) => {...}
        //         ...
        //         Pat::Wild(pat) => {...}
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
    /// A pattern that binds a new variable: `ref mut binding @ SUBPATTERN`.
    ///
    /// It may also be a unit struct or struct variant (e.g. `None`), or a
    /// constant; these cannot be distinguished syntactically.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct PatIdent {
        pub attrs: Vec<Attribute>,
        pub by_ref: Option<Token![ref]>,
        pub mutability: Option<Token![mut]>,
        pub ident: Ident,
        pub subpat: Option<(Token![@], Box<Pat>)>,
    }
}

ast_struct! {
    /// A pattern that matches any one of a set of cases.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct PatOr {
        pub attrs: Vec<Attribute>,
        pub leading_vert: Option<Token![|]>,
        pub cases: Punctuated<Pat, Token![|]>,
    }
}

ast_struct! {
    /// A parenthesized pattern: `(A | B)`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct PatParen {
        pub attrs: Vec<Attribute>,
        pub paren_token: token::Paren,
        pub pat: Box<Pat>,
    }
}

ast_struct! {
    /// A reference pattern: `&mut var`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct PatReference {
        pub attrs: Vec<Attribute>,
        pub and_token: Token![&],
        pub mutability: Option<Token![mut]>,
        pub pat: Box<Pat>,
    }
}

ast_struct! {
    /// The dots in a tuple or slice pattern: `[0, 1, ..]`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct PatRest {
        pub attrs: Vec<Attribute>,
        pub dot2_token: Token![..],
    }
}

ast_struct! {
    /// A dynamically sized slice pattern: `[a, b, ref i @ .., y, z]`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct PatSlice {
        pub attrs: Vec<Attribute>,
        pub bracket_token: token::Bracket,
        pub elems: Punctuated<Pat, Token![,]>,
    }
}

ast_struct! {
    /// A struct or struct variant pattern: `Variant { x, y, .. }`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct PatStruct {
        pub attrs: Vec<Attribute>,
        pub qself: Option<QSelf>,
        pub path: Path,
        pub brace_token: token::Brace,
        pub fields: Punctuated<FieldPat, Token![,]>,
        pub rest: Option<PatRest>,
    }
}

ast_struct! {
    /// A tuple pattern: `(a, b)`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct PatTuple {
        pub attrs: Vec<Attribute>,
        pub paren_token: token::Paren,
        pub elems: Punctuated<Pat, Token![,]>,
    }
}

ast_struct! {
    /// A tuple struct or tuple variant pattern: `Variant(x, y, .., z)`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct PatTupleStruct {
        pub attrs: Vec<Attribute>,
        pub qself: Option<QSelf>,
        pub path: Path,
        pub paren_token: token::Paren,
        pub elems: Punctuated<Pat, Token![,]>,
    }
}

ast_struct! {
    /// A type ascription pattern: `foo: f64`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct PatType {
        pub attrs: Vec<Attribute>,
        pub pat: Box<Pat>,
        pub colon_token: Token![:],
        pub ty: Box<Type>,
    }
}

ast_struct! {
    /// A pattern that matches any value: `_`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct PatWild {
        pub attrs: Vec<Attribute>,
        pub underscore_token: Token![_],
    }
}

ast_struct! {
    /// A single field in a struct pattern.
    ///
    /// Patterns like the fields of Foo `{ x, ref y, ref mut z }` are treated
    /// the same as `x: x, y: ref y, z: ref mut z` but there is no colon token.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct FieldPat {
        pub attrs: Vec<Attribute>,
        pub member: Member,
        pub colon_token: Option<Token![:]>,
        pub pat: Box<Pat>,
    }
}


#[cfg(feature = "printing")]
mod printing {
    use crate::attr::FilterAttrs;
    use crate::pat::{
        FieldPat, Pat, PatIdent, PatOr, PatParen, PatReference, PatRest, PatSlice, PatStruct,
        PatTuple, PatTupleStruct, PatType, PatWild,
    };
    use crate::path;
    use proc_macro2::TokenStream;
    use quote::{ToTokens, TokenStreamExt};

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for PatIdent {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.append_all(self.attrs.outer());
            self.by_ref.to_tokens(tokens);
            self.mutability.to_tokens(tokens);
            self.ident.to_tokens(tokens);
            if let Some((at_token, subpat)) = &self.subpat {
                at_token.to_tokens(tokens);
                subpat.to_tokens(tokens);
            }
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for PatOr {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.append_all(self.attrs.outer());
            self.leading_vert.to_tokens(tokens);
            self.cases.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for PatParen {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.append_all(self.attrs.outer());
            self.paren_token.surround(tokens, |tokens| {
                self.pat.to_tokens(tokens);
            });
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for PatReference {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.append_all(self.attrs.outer());
            self.and_token.to_tokens(tokens);
            self.mutability.to_tokens(tokens);
            self.pat.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for PatRest {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.append_all(self.attrs.outer());
            self.dot2_token.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for PatSlice {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.append_all(self.attrs.outer());
            self.bracket_token.surround(tokens, |tokens| {
                self.elems.to_tokens(tokens);
            });
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for PatStruct {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.append_all(self.attrs.outer());
            path::printing::print_path(tokens, &self.qself, &self.path);
            self.brace_token.surround(tokens, |tokens| {
                self.fields.to_tokens(tokens);
                // NOTE: We need a comma before the dot2 token if it is present.
                if !self.fields.empty_or_trailing() && self.rest.is_some() {
                    <Token![,]>::default().to_tokens(tokens);
                }
                self.rest.to_tokens(tokens);
            });
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for PatTuple {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.append_all(self.attrs.outer());
            self.paren_token.surround(tokens, |tokens| {
                self.elems.to_tokens(tokens);
                // If there is only one element, a trailing comma is needed to
                // distinguish PatTuple from PatParen, unless this is `(..)`
                // which is a tuple pattern even without comma.
                if self.elems.len() == 1
                    && !self.elems.trailing_punct()
                    && !matches!(self.elems[0], Pat::Rest { .. })
                {
                    <Token![,]>::default().to_tokens(tokens);
                }
            });
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for PatTupleStruct {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.append_all(self.attrs.outer());
            path::printing::print_path(tokens, &self.qself, &self.path);
            self.paren_token.surround(tokens, |tokens| {
                self.elems.to_tokens(tokens);
            });
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for PatType {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.append_all(self.attrs.outer());
            self.pat.to_tokens(tokens);
            self.colon_token.to_tokens(tokens);
            self.ty.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for PatWild {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.append_all(self.attrs.outer());
            self.underscore_token.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for FieldPat {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.append_all(self.attrs.outer());
            if let Some(colon_token) = &self.colon_token {
                self.member.to_tokens(tokens);
                colon_token.to_tokens(tokens);
            }
            self.pat.to_tokens(tokens);
        }
    }
}
