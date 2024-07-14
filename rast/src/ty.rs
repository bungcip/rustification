use crate::attr::Attribute;
use crate::expr::Expr;
use crate::generics::{BoundLifetimes, TypeParamBound};
use crate::ident::Ident;
use crate::lifetime::Lifetime;
use crate::lit::LitStr;
use crate::mac::Macro;
use crate::path::{Path, QSelf};
use crate::punctuated::Punctuated;
use crate::token;
use proc_macro2::TokenStream;

ast_enum_of_structs! {
    /// The possible types that a Rust value could have.
    ///
    /// # Syntax tree enum
    ///
    /// This type is a [syntax tree enum].
    ///
    /// [syntax tree enum]: crate::expr::Expr#syntax-tree-enums
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    #[non_exhaustive]
    pub enum Type {
        /// A fixed size array type: `[T; n]`.
        Array(TypeArray),

        /// A bare function type: `fn(usize) -> bool`.
        BareFn(TypeBareFn),

        /// A type contained within invisible delimiters.
        Group(TypeGroup),

        /// An `impl Bound1 + Bound2 + Bound3` type where `Bound` is a trait or
        /// a lifetime.
        ImplTrait(TypeImplTrait),

        /// Indication that a type should be inferred by the compiler: `_`.
        Infer(TypeInfer),

        /// A macro in the type position.
        Macro(TypeMacro),

        /// The never type: `!`.
        Never(TypeNever),

        /// A parenthesized type equivalent to the inner type.
        Paren(TypeParen),

        /// A path like `std::slice::Iter`, optionally qualified with a
        /// self-type as in `<Vec<T> as SomeTrait>::Associated`.
        Path(TypePath),

        /// A raw pointer type: `*const T` or `*mut T`.
        Ptr(TypePtr),

        /// A reference type: `&'a T` or `&'a mut T`.
        Reference(TypeReference),

        /// A dynamically sized slice type: `[T]`.
        Slice(TypeSlice),

        /// A trait object type `dyn Bound1 + Bound2 + Bound3` where `Bound` is a
        /// trait or a lifetime.
        TraitObject(TypeTraitObject),

        /// A tuple type: `(A, B, C, String)`.
        Tuple(TypeTuple),

        /// Tokens in type position not interpreted by Syn.
        Verbatim(TokenStream),

        // For testing exhaustiveness in downstream code, use the following idiom:
        //
        //     match ty {
        //         #![cfg_attr(test, deny(non_exhaustive_omitted_patterns))]
        //
        //         Type::Array(ty) => {...}
        //         Type::BareFn(ty) => {...}
        //         ...
        //         Type::Verbatim(ty) => {...}
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
    /// A fixed size array type: `[T; n]`.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct TypeArray {
        pub bracket_token: token::Bracket,
        pub elem: Box<Type>,
        pub semi_token: Token![;],
        pub len: Expr,
    }
}

ast_struct! {
    /// A bare function type: `fn(usize) -> bool`.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct TypeBareFn {
        pub lifetimes: Option<BoundLifetimes>,
        pub unsafety: Option<Token![unsafe]>,
        pub abi: Option<Abi>,
        pub fn_token: Token![fn],
        pub paren_token: token::Paren,
        pub inputs: Punctuated<BareFnArg, Token![,]>,
        pub variadic: Option<BareVariadic>,
        pub output: ReturnType,
    }
}

ast_struct! {
    /// A type contained within invisible delimiters.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct TypeGroup {
        pub group_token: token::Group,
        pub elem: Box<Type>,
    }
}

ast_struct! {
    /// An `impl Bound1 + Bound2 + Bound3` type where `Bound` is a trait or
    /// a lifetime.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct TypeImplTrait {
        pub impl_token: Token![impl],
        pub bounds: Punctuated<TypeParamBound, Token![+]>,
    }
}

ast_struct! {
    /// Indication that a type should be inferred by the compiler: `_`.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct TypeInfer {
        pub underscore_token: Token![_],
    }
}

ast_struct! {
    /// A macro in the type position.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct TypeMacro {
        pub mac: Macro,
    }
}

ast_struct! {
    /// The never type: `!`.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct TypeNever {
        pub bang_token: Token![!],
    }
}

ast_struct! {
    /// A parenthesized type equivalent to the inner type.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct TypeParen {
        pub paren_token: token::Paren,
        pub elem: Box<Type>,
    }
}

ast_struct! {
    /// A path like `std::slice::Iter`, optionally qualified with a
    /// self-type as in `<Vec<T> as SomeTrait>::Associated`.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct TypePath {
        pub qself: Option<QSelf>,
        pub path: Path,
    }
}

ast_struct! {
    /// A raw pointer type: `*const T` or `*mut T`.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct TypePtr {
        pub star_token: Token![*],
        pub const_token: Option<Token![const]>,
        pub mutability: Option<Token![mut]>,
        pub elem: Box<Type>,
    }
}

ast_struct! {
    /// A reference type: `&'a T` or `&'a mut T`.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct TypeReference {
        pub and_token: Token![&],
        pub lifetime: Option<Lifetime>,
        pub mutability: Option<Token![mut]>,
        pub elem: Box<Type>,
    }
}

ast_struct! {
    /// A dynamically sized slice type: `[T]`.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct TypeSlice {
        pub bracket_token: token::Bracket,
        pub elem: Box<Type>,
    }
}

ast_struct! {
    /// A trait object type `dyn Bound1 + Bound2 + Bound3` where `Bound` is a
    /// trait or a lifetime.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct TypeTraitObject {
        pub dyn_token: Option<Token![dyn]>,
        pub bounds: Punctuated<TypeParamBound, Token![+]>,
    }
}

ast_struct! {
    /// A tuple type: `(A, B, C, String)`.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct TypeTuple {
        pub paren_token: token::Paren,
        pub elems: Punctuated<Type, Token![,]>,
    }
}

ast_struct! {
    /// The binary interface of a function: `extern "C"`.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct Abi {
        pub extern_token: Token![extern],
        pub name: Option<LitStr>,
    }
}

ast_struct! {
    /// An argument in a function type: the `usize` in `fn(usize) -> bool`.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct BareFnArg {
        pub attrs: Vec<Attribute>,
        pub name: Option<(Ident, Token![:])>,
        pub ty: Type,
    }
}

ast_struct! {
    /// The variadic argument of a function pointer like `fn(usize, ...)`.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct BareVariadic {
        pub attrs: Vec<Attribute>,
        pub name: Option<(Ident, Token![:])>,
        pub dots: Token![...],
        pub comma: Option<Token![,]>,
    }
}

ast_enum! {
    /// Return type of a function signature.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub enum ReturnType {
        /// Return type is not specified.
        ///
        /// Functions default to `()` and closures default to type inference.
        Default,
        /// A particular type is returned.
        Type(Token![->], Box<Type>),
    }
}

#[cfg(feature = "printing")]
mod printing {
    use crate::attr::FilterAttrs;
    use crate::path;
    use crate::print::TokensOrDefault;
    use crate::ty::{
        Abi, BareFnArg, BareVariadic, ReturnType, TypeArray, TypeBareFn, TypeGroup, TypeImplTrait,
        TypeInfer, TypeMacro, TypeNever, TypeParen, TypePath, TypePtr, TypeReference, TypeSlice,
        TypeTraitObject, TypeTuple,
    };
    use proc_macro2::TokenStream;
    use quote::{ToTokens, TokenStreamExt};

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for TypeSlice {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.bracket_token.surround(tokens, |tokens| {
                self.elem.to_tokens(tokens);
            });
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for TypeArray {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.bracket_token.surround(tokens, |tokens| {
                self.elem.to_tokens(tokens);
                self.semi_token.to_tokens(tokens);
                self.len.to_tokens(tokens);
            });
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for TypePtr {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.star_token.to_tokens(tokens);
            match &self.mutability {
                Some(tok) => tok.to_tokens(tokens),
                None => {
                    TokensOrDefault(&self.const_token).to_tokens(tokens);
                }
            }
            self.elem.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for TypeReference {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.and_token.to_tokens(tokens);
            self.lifetime.to_tokens(tokens);
            self.mutability.to_tokens(tokens);
            self.elem.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for TypeBareFn {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.lifetimes.to_tokens(tokens);
            self.unsafety.to_tokens(tokens);
            self.abi.to_tokens(tokens);
            self.fn_token.to_tokens(tokens);
            self.paren_token.surround(tokens, |tokens| {
                self.inputs.to_tokens(tokens);
                if let Some(variadic) = &self.variadic {
                    if !self.inputs.empty_or_trailing() {
                        let span = variadic.dots.spans[0];
                        Token![,](span).to_tokens(tokens);
                    }
                    variadic.to_tokens(tokens);
                }
            });
            self.output.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for TypeNever {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.bang_token.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for TypeTuple {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.paren_token.surround(tokens, |tokens| {
                self.elems.to_tokens(tokens);
                // If we only have one argument, we need a trailing comma to
                // distinguish TypeTuple from TypeParen.
                if self.elems.len() == 1 && !self.elems.trailing_punct() {
                    <Token![,]>::default().to_tokens(tokens);
                }
            });
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for TypePath {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            path::printing::print_path(tokens, &self.qself, &self.path);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for TypeTraitObject {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.dyn_token.to_tokens(tokens);
            self.bounds.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for TypeImplTrait {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.impl_token.to_tokens(tokens);
            self.bounds.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for TypeGroup {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.group_token.surround(tokens, |tokens| {
                self.elem.to_tokens(tokens);
            });
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for TypeParen {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.paren_token.surround(tokens, |tokens| {
                self.elem.to_tokens(tokens);
            });
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for TypeInfer {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.underscore_token.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for TypeMacro {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.mac.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ReturnType {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            match self {
                ReturnType::Default => {}
                ReturnType::Type(arrow, ty) => {
                    arrow.to_tokens(tokens);
                    ty.to_tokens(tokens);
                }
            }
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for BareFnArg {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.append_all(self.attrs.outer());
            if let Some((name, colon)) = &self.name {
                name.to_tokens(tokens);
                colon.to_tokens(tokens);
            }
            self.ty.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for BareVariadic {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.append_all(self.attrs.outer());
            if let Some((name, colon)) = &self.name {
                name.to_tokens(tokens);
                colon.to_tokens(tokens);
            }
            self.dots.to_tokens(tokens);
            self.comma.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for Abi {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.extern_token.to_tokens(tokens);
            self.name.to_tokens(tokens);
        }
    }
}
