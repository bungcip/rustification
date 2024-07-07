use crate::expr::Expr;
use crate::generics::TypeParamBound;
use crate::ident::Ident;
use crate::lifetime::Lifetime;
use crate::punctuated::Punctuated;
use crate::token;
use crate::ty::{ReturnType, Type};

ast_struct! {
    /// A path at which a named item is exported (e.g. `std::collections::HashMap`).
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct Path {
        pub leading_colon: Option<Token![::]>,
        pub segments: Punctuated<PathSegment, Token![::]>,
    }
}

impl<T> From<T> for Path
where
    T: Into<PathSegment>,
{
    fn from(segment: T) -> Self {
        let mut path = Path {
            leading_colon: None,
            segments: Punctuated::new(),
        };
        path.segments.push_value(segment.into());
        path
    }
}

impl Path {
    /// Determines whether this is a path of length 1 equal to the given
    /// ident.
    ///
    /// For them to compare equal, it must be the case that:
    ///
    /// - the path has no leading colon,
    /// - the number of path segments is 1,
    /// - the first path segment has no angle bracketed or parenthesized
    ///   path arguments, and
    /// - the ident of the first path segment is equal to the given one.
    ///
    /// # Example
    ///
    /// ```
    /// use proc_macro2::TokenStream;
    /// use rast::{Attribute, Error, Meta, Result};
    ///
    /// fn get_serde_meta_item(attr: &Attribute) -> Result<Option<&TokenStream>> {
    ///     if attr.path().is_ident("serde") {
    ///         match &attr.meta {
    ///             Meta::List(meta) => Ok(Some(&meta.tokens)),
    ///             bad => Err(Error::new_spanned(bad, "unrecognized attribute")),
    ///         }
    ///     } else {
    ///         Ok(None)
    ///     }
    /// }
    /// ```
    pub fn is_ident<I>(&self, ident: &I) -> bool
    where
        I: ?Sized,
        Ident: PartialEq<I>,
    {
        match self.get_ident() {
            Some(id) => id == ident,
            None => false,
        }
    }

    /// If this path consists of a single ident, returns the ident.
    ///
    /// A path is considered an ident if:
    ///
    /// - the path has no leading colon,
    /// - the number of path segments is 1, and
    /// - the first path segment has no angle bracketed or parenthesized
    ///   path arguments.
    pub fn get_ident(&self) -> Option<&Ident> {
        if self.leading_colon.is_none()
            && self.segments.len() == 1
            && self.segments[0].arguments.is_none()
        {
            Some(&self.segments[0].ident)
        } else {
            None
        }
    }

}

ast_struct! {
    /// A segment of a path together with any path arguments on that segment.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct PathSegment {
        pub ident: Ident,
        pub arguments: PathArguments,
    }
}

impl<T> From<T> for PathSegment
where
    T: Into<Ident>,
{
    fn from(ident: T) -> Self {
        PathSegment {
            ident: ident.into(),
            arguments: PathArguments::None,
        }
    }
}

ast_enum! {
    /// Angle bracketed or parenthesized arguments of a path segment.
    ///
    /// ## Angle bracketed
    ///
    /// The `<'a, T>` in `std::slice::iter<'a, T>`.
    ///
    /// ## Parenthesized
    ///
    /// The `(A, B) -> C` in `Fn(A, B) -> C`.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub enum PathArguments {
        None,
        /// The `<'a, T>` in `std::slice::iter<'a, T>`.
        AngleBracketed(AngleBracketedGenericArguments),
        /// The `(A, B) -> C` in `Fn(A, B) -> C`.
        Parenthesized(ParenthesizedGenericArguments),
    }
}

impl Default for PathArguments {
    fn default() -> Self {
        PathArguments::None
    }
}

impl PathArguments {
    pub fn is_empty(&self) -> bool {
        match self {
            PathArguments::None => true,
            PathArguments::AngleBracketed(bracketed) => bracketed.args.is_empty(),
            PathArguments::Parenthesized(_) => false,
        }
    }

    pub fn is_none(&self) -> bool {
        match self {
            PathArguments::None => true,
            PathArguments::AngleBracketed(_) | PathArguments::Parenthesized(_) => false,
        }
    }
}

ast_enum! {
    /// An individual generic argument, like `'a`, `T`, or `Item = T`.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    #[non_exhaustive]
    pub enum GenericArgument {
        /// A lifetime argument.
        Lifetime(Lifetime),
        /// A type argument.
        Type(Type),
        /// A const expression. Must be inside of a block.
        ///
        /// NOTE: Identity expressions are represented as Type arguments, as
        /// they are indistinguishable syntactically.
        Const(Expr),
        /// A binding (equality constraint) on an associated type: the `Item =
        /// u8` in `Iterator<Item = u8>`.
        AssocType(AssocType),
        /// An equality constraint on an associated constant: the `PANIC =
        /// false` in `Trait<PANIC = false>`.
        AssocConst(AssocConst),
        /// An associated type bound: `Iterator<Item: Display>`.
        Constraint(Constraint),
    }
}

ast_struct! {
    /// Angle bracketed arguments of a path segment: the `<K, V>` in `HashMap<K,
    /// V>`.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct AngleBracketedGenericArguments {
        pub colon2_token: Option<Token![::]>,
        pub lt_token: Token![<],
        pub args: Punctuated<GenericArgument, Token![,]>,
        pub gt_token: Token![>],
    }
}

ast_struct! {
    /// A binding (equality constraint) on an associated type: the `Item = u8`
    /// in `Iterator<Item = u8>`.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct AssocType {
        pub ident: Ident,
        pub generics: Option<AngleBracketedGenericArguments>,
        pub eq_token: Token![=],
        pub ty: Type,
    }
}

ast_struct! {
    /// An equality constraint on an associated constant: the `PANIC = false` in
    /// `Trait<PANIC = false>`.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct AssocConst {
        pub ident: Ident,
        pub generics: Option<AngleBracketedGenericArguments>,
        pub eq_token: Token![=],
        pub value: Expr,
    }
}

ast_struct! {
    /// An associated type bound: `Iterator<Item: Display>`.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct Constraint {
        pub ident: Ident,
        pub generics: Option<AngleBracketedGenericArguments>,
        pub colon_token: Token![:],
        pub bounds: Punctuated<TypeParamBound, Token![+]>,
    }
}

ast_struct! {
    /// Arguments of a function path segment: the `(A, B) -> C` in `Fn(A,B) ->
    /// C`.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct ParenthesizedGenericArguments {
        pub paren_token: token::Paren,
        /// `(A, B)`
        pub inputs: Punctuated<Type, Token![,]>,
        /// `C`
        pub output: ReturnType,
    }
}

ast_struct! {
    /// The explicit Self type in a qualified path: the `T` in `<T as
    /// Display>::fmt`.
    ///
    /// The actual path, including the trait and the associated item, is stored
    /// separately. The `position` field represents the index of the associated
    /// item qualified with this Self type.
    ///
    /// ```text
    /// <Vec<T> as a::b::Trait>::AssociatedItem
    ///  ^~~~~~    ~~~~~~~~~~~~~~^
    ///  ty        position = 3
    ///
    /// <Vec<T>>::AssociatedItem
    ///  ^~~~~~   ^
    ///  ty       position = 0
    /// ```
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct QSelf {
        pub lt_token: Token![<],
        pub ty: Box<Type>,
        pub position: usize,
        pub as_token: Option<Token![as]>,
        pub gt_token: Token![>],
    }
}


#[cfg(feature = "printing")]
pub(crate) mod printing {
    use crate::generics;
    use crate::path::{
        AngleBracketedGenericArguments, AssocConst, AssocType, Constraint, GenericArgument,
        ParenthesizedGenericArguments, Path, PathArguments, PathSegment, QSelf,
    };
    use crate::print::TokensOrDefault;
    #[cfg(feature = "parsing")]
    use crate::spanned::Spanned;
    #[cfg(feature = "parsing")]
    use proc_macro2::Span;
    use proc_macro2::TokenStream;
    use quote::ToTokens;
    use std::cmp;

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for Path {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.leading_colon.to_tokens(tokens);
            self.segments.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for PathSegment {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.ident.to_tokens(tokens);
            self.arguments.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for PathArguments {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            match self {
                PathArguments::None => {}
                PathArguments::AngleBracketed(arguments) => {
                    arguments.to_tokens(tokens);
                }
                PathArguments::Parenthesized(arguments) => {
                    arguments.to_tokens(tokens);
                }
            }
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for GenericArgument {
        #[allow(clippy::match_same_arms)]
        fn to_tokens(&self, tokens: &mut TokenStream) {
            match self {
                GenericArgument::Lifetime(lt) => lt.to_tokens(tokens),
                GenericArgument::Type(ty) => ty.to_tokens(tokens),
                GenericArgument::Const(expr) => {
                    generics::printing::print_const_argument(expr, tokens);
                }
                GenericArgument::AssocType(assoc) => assoc.to_tokens(tokens),
                GenericArgument::AssocConst(assoc) => assoc.to_tokens(tokens),
                GenericArgument::Constraint(constraint) => constraint.to_tokens(tokens),
            }
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for AngleBracketedGenericArguments {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.colon2_token.to_tokens(tokens);
            self.lt_token.to_tokens(tokens);

            // Print lifetimes before types/consts/bindings, regardless of their
            // order in self.args.
            let mut trailing_or_empty = true;
            for param in self.args.pairs() {
                match param.value() {
                    GenericArgument::Lifetime(_) => {
                        param.to_tokens(tokens);
                        trailing_or_empty = param.punct().is_some();
                    }
                    GenericArgument::Type(_)
                    | GenericArgument::Const(_)
                    | GenericArgument::AssocType(_)
                    | GenericArgument::AssocConst(_)
                    | GenericArgument::Constraint(_) => {}
                }
            }
            for param in self.args.pairs() {
                match param.value() {
                    GenericArgument::Type(_)
                    | GenericArgument::Const(_)
                    | GenericArgument::AssocType(_)
                    | GenericArgument::AssocConst(_)
                    | GenericArgument::Constraint(_) => {
                        if !trailing_or_empty {
                            <Token![,]>::default().to_tokens(tokens);
                        }
                        param.to_tokens(tokens);
                        trailing_or_empty = param.punct().is_some();
                    }
                    GenericArgument::Lifetime(_) => {}
                }
            }

            self.gt_token.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for AssocType {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.ident.to_tokens(tokens);
            self.generics.to_tokens(tokens);
            self.eq_token.to_tokens(tokens);
            self.ty.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for AssocConst {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.ident.to_tokens(tokens);
            self.generics.to_tokens(tokens);
            self.eq_token.to_tokens(tokens);
            generics::printing::print_const_argument(&self.value, tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for Constraint {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.ident.to_tokens(tokens);
            self.generics.to_tokens(tokens);
            self.colon_token.to_tokens(tokens);
            self.bounds.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ParenthesizedGenericArguments {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.paren_token.surround(tokens, |tokens| {
                self.inputs.to_tokens(tokens);
            });
            self.output.to_tokens(tokens);
        }
    }

    pub(crate) fn print_path(tokens: &mut TokenStream, qself: &Option<QSelf>, path: &Path) {
        let qself = match qself {
            Some(qself) => qself,
            None => {
                path.to_tokens(tokens);
                return;
            }
        };
        qself.lt_token.to_tokens(tokens);
        qself.ty.to_tokens(tokens);

        let pos = cmp::min(qself.position, path.segments.len());
        let mut segments = path.segments.pairs();
        if pos > 0 {
            TokensOrDefault(&qself.as_token).to_tokens(tokens);
            path.leading_colon.to_tokens(tokens);
            for (i, segment) in segments.by_ref().take(pos).enumerate() {
                if i + 1 == pos {
                    segment.value().to_tokens(tokens);
                    qself.gt_token.to_tokens(tokens);
                    segment.punct().to_tokens(tokens);
                } else {
                    segment.to_tokens(tokens);
                }
            }
        } else {
            qself.gt_token.to_tokens(tokens);
            path.leading_colon.to_tokens(tokens);
        }
        for segment in segments {
            segment.to_tokens(tokens);
        }
    }

    #[cfg(feature = "parsing")]
    #[cfg_attr(docsrs, doc(cfg(all(feature = "parsing", feature = "printing"))))]
    impl Spanned for QSelf {
        fn span(&self) -> Span {
            struct QSelfDelimiters<'a>(&'a QSelf);

            impl<'a> ToTokens for QSelfDelimiters<'a> {
                fn to_tokens(&self, tokens: &mut TokenStream) {
                    self.0.lt_token.to_tokens(tokens);
                    self.0.gt_token.to_tokens(tokens);
                }
            }

            QSelfDelimiters(self).span()
        }
    }
}
