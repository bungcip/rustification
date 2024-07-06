use crate::attr::Attribute;
use crate::expr::Expr;
use crate::ident::Ident;
use crate::lifetime::Lifetime;
use crate::path::Path;
use crate::punctuated::{Iter, IterMut, Punctuated};
use crate::token;
use crate::ty::Type;
use proc_macro2::TokenStream;
#[cfg(all(feature = "printing", feature = "extra-traits"))]
use std::fmt::{self, Debug};
#[cfg(all(feature = "printing", feature = "extra-traits"))]
use std::hash::{Hash, Hasher};

ast_struct! {
    /// Lifetimes and type parameters attached to a declaration of a function,
    /// enum, trait, etc.
    ///
    /// This struct represents two distinct optional syntactic elements,
    /// [generic parameters] and [where clause]. In some locations of the
    /// grammar, there may be other tokens in between these two things.
    ///
    /// [generic parameters]: https://doc.rust-lang.org/stable/reference/items/generics.html#generic-parameters
    /// [where clause]: https://doc.rust-lang.org/stable/reference/items/generics.html#where-clauses
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct Generics {
        pub lt_token: Option<Token![<]>,
        pub params: Punctuated<GenericParam, Token![,]>,
        pub gt_token: Option<Token![>]>,
        pub where_clause: Option<WhereClause>,
    }
}

ast_enum_of_structs! {
    /// A generic type parameter, lifetime, or const generic: `T: Into<String>`,
    /// `'a: 'b`, `const LEN: usize`.
    ///
    /// # Syntax tree enum
    ///
    /// This type is a [syntax tree enum].
    ///
    /// [syntax tree enum]: crate::expr::Expr#syntax-tree-enums
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub enum GenericParam {
        /// A lifetime parameter: `'a: 'b + 'c + 'd`.
        Lifetime(LifetimeParam),

        /// A generic type parameter: `T: Into<String>`.
        Type(TypeParam),

        /// A const generic parameter: `const LENGTH: usize`.
        Const(ConstParam),
    }
}

ast_struct! {
    /// A lifetime definition: `'a: 'b + 'c + 'd`.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct LifetimeParam {
        pub attrs: Vec<Attribute>,
        pub lifetime: Lifetime,
        pub colon_token: Option<Token![:]>,
        pub bounds: Punctuated<Lifetime, Token![+]>,
    }
}

ast_struct! {
    /// A generic type parameter: `T: Into<String>`.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct TypeParam {
        pub attrs: Vec<Attribute>,
        pub ident: Ident,
        pub colon_token: Option<Token![:]>,
        pub bounds: Punctuated<TypeParamBound, Token![+]>,
        pub eq_token: Option<Token![=]>,
        pub default: Option<Type>,
    }
}

ast_struct! {
    /// A const generic parameter: `const LENGTH: usize`.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct ConstParam {
        pub attrs: Vec<Attribute>,
        pub const_token: Token![const],
        pub ident: Ident,
        pub colon_token: Token![:],
        pub ty: Type,
        pub eq_token: Option<Token![=]>,
        pub default: Option<Expr>,
    }
}

impl Default for Generics {
    fn default() -> Self {
        Generics {
            lt_token: None,
            params: Punctuated::new(),
            gt_token: None,
            where_clause: None,
        }
    }
}

impl Generics {
    /// Returns an
    /// <code
    ///   style="padding-right:0;">Iterator&lt;Item = &amp;</code><a
    ///   href="struct.LifetimeParam.html"><code
    ///   style="padding-left:0;padding-right:0;">LifetimeParam</code></a><code
    ///   style="padding-left:0;">&gt;</code>
    /// over the lifetime parameters in `self.params`.
    pub fn lifetimes(&self) -> Lifetimes {
        Lifetimes(self.params.iter())
    }

    /// Returns an
    /// <code
    ///   style="padding-right:0;">Iterator&lt;Item = &amp;mut </code><a
    ///   href="struct.LifetimeParam.html"><code
    ///   style="padding-left:0;padding-right:0;">LifetimeParam</code></a><code
    ///   style="padding-left:0;">&gt;</code>
    /// over the lifetime parameters in `self.params`.
    pub fn lifetimes_mut(&mut self) -> LifetimesMut {
        LifetimesMut(self.params.iter_mut())
    }

    /// Returns an
    /// <code
    ///   style="padding-right:0;">Iterator&lt;Item = &amp;</code><a
    ///   href="struct.TypeParam.html"><code
    ///   style="padding-left:0;padding-right:0;">TypeParam</code></a><code
    ///   style="padding-left:0;">&gt;</code>
    /// over the type parameters in `self.params`.
    pub fn type_params(&self) -> TypeParams {
        TypeParams(self.params.iter())
    }

    /// Returns an
    /// <code
    ///   style="padding-right:0;">Iterator&lt;Item = &amp;mut </code><a
    ///   href="struct.TypeParam.html"><code
    ///   style="padding-left:0;padding-right:0;">TypeParam</code></a><code
    ///   style="padding-left:0;">&gt;</code>
    /// over the type parameters in `self.params`.
    pub fn type_params_mut(&mut self) -> TypeParamsMut {
        TypeParamsMut(self.params.iter_mut())
    }

    /// Returns an
    /// <code
    ///   style="padding-right:0;">Iterator&lt;Item = &amp;</code><a
    ///   href="struct.ConstParam.html"><code
    ///   style="padding-left:0;padding-right:0;">ConstParam</code></a><code
    ///   style="padding-left:0;">&gt;</code>
    /// over the constant parameters in `self.params`.
    pub fn const_params(&self) -> ConstParams {
        ConstParams(self.params.iter())
    }

    /// Returns an
    /// <code
    ///   style="padding-right:0;">Iterator&lt;Item = &amp;mut </code><a
    ///   href="struct.ConstParam.html"><code
    ///   style="padding-left:0;padding-right:0;">ConstParam</code></a><code
    ///   style="padding-left:0;">&gt;</code>
    /// over the constant parameters in `self.params`.
    pub fn const_params_mut(&mut self) -> ConstParamsMut {
        ConstParamsMut(self.params.iter_mut())
    }

    /// Initializes an empty `where`-clause if there is not one present already.
    pub fn make_where_clause(&mut self) -> &mut WhereClause {
        self.where_clause.get_or_insert_with(|| WhereClause {
            where_token: <Token![where]>::default(),
            predicates: Punctuated::new(),
        })
    }
}

pub struct Lifetimes<'a>(Iter<'a, GenericParam>);

impl<'a> Iterator for Lifetimes<'a> {
    type Item = &'a LifetimeParam;

    fn next(&mut self) -> Option<Self::Item> {
        let next = match self.0.next() {
            Some(item) => item,
            None => return None,
        };
        if let GenericParam::Lifetime(lifetime) = next {
            Some(lifetime)
        } else {
            self.next()
        }
    }
}

pub struct LifetimesMut<'a>(IterMut<'a, GenericParam>);

impl<'a> Iterator for LifetimesMut<'a> {
    type Item = &'a mut LifetimeParam;

    fn next(&mut self) -> Option<Self::Item> {
        let next = match self.0.next() {
            Some(item) => item,
            None => return None,
        };
        if let GenericParam::Lifetime(lifetime) = next {
            Some(lifetime)
        } else {
            self.next()
        }
    }
}

pub struct TypeParams<'a>(Iter<'a, GenericParam>);

impl<'a> Iterator for TypeParams<'a> {
    type Item = &'a TypeParam;

    fn next(&mut self) -> Option<Self::Item> {
        let next = match self.0.next() {
            Some(item) => item,
            None => return None,
        };
        if let GenericParam::Type(type_param) = next {
            Some(type_param)
        } else {
            self.next()
        }
    }
}

pub struct TypeParamsMut<'a>(IterMut<'a, GenericParam>);

impl<'a> Iterator for TypeParamsMut<'a> {
    type Item = &'a mut TypeParam;

    fn next(&mut self) -> Option<Self::Item> {
        let next = match self.0.next() {
            Some(item) => item,
            None => return None,
        };
        if let GenericParam::Type(type_param) = next {
            Some(type_param)
        } else {
            self.next()
        }
    }
}

pub struct ConstParams<'a>(Iter<'a, GenericParam>);

impl<'a> Iterator for ConstParams<'a> {
    type Item = &'a ConstParam;

    fn next(&mut self) -> Option<Self::Item> {
        let next = match self.0.next() {
            Some(item) => item,
            None => return None,
        };
        if let GenericParam::Const(const_param) = next {
            Some(const_param)
        } else {
            self.next()
        }
    }
}

pub struct ConstParamsMut<'a>(IterMut<'a, GenericParam>);

impl<'a> Iterator for ConstParamsMut<'a> {
    type Item = &'a mut ConstParam;

    fn next(&mut self) -> Option<Self::Item> {
        let next = match self.0.next() {
            Some(item) => item,
            None => return None,
        };
        if let GenericParam::Const(const_param) = next {
            Some(const_param)
        } else {
            self.next()
        }
    }
}

/// Returned by `Generics::split_for_impl`.
#[cfg(feature = "printing")]
#[cfg_attr(
    docsrs,
    doc(cfg(all(any(feature = "full", feature = "derive"), feature = "printing")))
)]
pub struct ImplGenerics<'a>(&'a Generics);

/// Returned by `Generics::split_for_impl`.
#[cfg(feature = "printing")]
#[cfg_attr(
    docsrs,
    doc(cfg(all(any(feature = "full", feature = "derive"), feature = "printing")))
)]
pub struct TypeGenerics<'a>(&'a Generics);

/// Returned by `TypeGenerics::as_turbofish`.
#[cfg(feature = "printing")]
#[cfg_attr(
    docsrs,
    doc(cfg(all(any(feature = "full", feature = "derive"), feature = "printing")))
)]
pub struct Turbofish<'a>(&'a Generics);

#[cfg(feature = "printing")]
impl Generics {
    /// Split a type's generics into the pieces required for impl'ing a trait
    /// for that type.
    ///
    /// ```
    /// # use proc_macro2::{Span, Ident};
    /// # use quote::quote;
    /// #
    /// # let generics: rast::Generics = Default::default();
    /// # let name = Ident::new("MyType", Span::call_site());
    /// #
    /// let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();
    /// quote! {
    ///     impl #impl_generics MyTrait for #name #ty_generics #where_clause {
    ///         // ...
    ///     }
    /// }
    /// # ;
    /// ```
    #[cfg_attr(
        docsrs,
        doc(cfg(all(any(feature = "full", feature = "derive"), feature = "printing")))
    )]
    pub fn split_for_impl(&self) -> (ImplGenerics, TypeGenerics, Option<&WhereClause>) {
        (
            ImplGenerics(self),
            TypeGenerics(self),
            self.where_clause.as_ref(),
        )
    }
}

#[cfg(feature = "printing")]
macro_rules! generics_wrapper_impls {
    ($ty:ident) => {
        #[cfg(feature = "clone-impls")]
        #[cfg_attr(docsrs, doc(cfg(feature = "clone-impls")))]
        impl<'a> Clone for $ty<'a> {
            fn clone(&self) -> Self {
                $ty(self.0)
            }
        }

        #[cfg(feature = "extra-traits")]
        #[cfg_attr(docsrs, doc(cfg(feature = "extra-traits")))]
        impl<'a> Debug for $ty<'a> {
            fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter
                    .debug_tuple(stringify!($ty))
                    .field(self.0)
                    .finish()
            }
        }

        #[cfg(feature = "extra-traits")]
        #[cfg_attr(docsrs, doc(cfg(feature = "extra-traits")))]
        impl<'a> Eq for $ty<'a> {}

        #[cfg(feature = "extra-traits")]
        #[cfg_attr(docsrs, doc(cfg(feature = "extra-traits")))]
        impl<'a> PartialEq for $ty<'a> {
            fn eq(&self, other: &Self) -> bool {
                self.0 == other.0
            }
        }

        #[cfg(feature = "extra-traits")]
        #[cfg_attr(docsrs, doc(cfg(feature = "extra-traits")))]
        impl<'a> Hash for $ty<'a> {
            fn hash<H: Hasher>(&self, state: &mut H) {
                self.0.hash(state);
            }
        }
    };
}

#[cfg(feature = "printing")]
generics_wrapper_impls!(ImplGenerics);
#[cfg(feature = "printing")]
generics_wrapper_impls!(TypeGenerics);
#[cfg(feature = "printing")]
generics_wrapper_impls!(Turbofish);

#[cfg(feature = "printing")]
impl<'a> TypeGenerics<'a> {
    /// Turn a type's generics like `<X, Y>` into a turbofish like `::<X, Y>`.
    pub fn as_turbofish(&self) -> Turbofish {
        Turbofish(self.0)
    }
}

ast_struct! {
    /// A set of bound lifetimes: `for<'a, 'b, 'c>`.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct BoundLifetimes {
        pub for_token: Token![for],
        pub lt_token: Token![<],
        pub lifetimes: Punctuated<GenericParam, Token![,]>,
        pub gt_token: Token![>],
    }
}

impl Default for BoundLifetimes {
    fn default() -> Self {
        BoundLifetimes {
            for_token: Default::default(),
            lt_token: Default::default(),
            lifetimes: Punctuated::new(),
            gt_token: Default::default(),
        }
    }
}

impl LifetimeParam {
    pub fn new(lifetime: Lifetime) -> Self {
        LifetimeParam {
            attrs: Vec::new(),
            lifetime,
            colon_token: None,
            bounds: Punctuated::new(),
        }
    }
}

impl From<Ident> for TypeParam {
    fn from(ident: Ident) -> Self {
        TypeParam {
            attrs: vec![],
            ident,
            colon_token: None,
            bounds: Punctuated::new(),
            eq_token: None,
            default: None,
        }
    }
}

ast_enum_of_structs! {
    /// A trait or lifetime used as a bound on a type parameter.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    #[non_exhaustive]
    pub enum TypeParamBound {
        Trait(TraitBound),
        Lifetime(Lifetime),
        Verbatim(TokenStream),
    }
}

ast_struct! {
    /// A trait used as a bound on a type parameter.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct TraitBound {
        pub paren_token: Option<token::Paren>,
        pub modifier: TraitBoundModifier,
        /// The `for<'a>` in `for<'a> Foo<&'a T>`
        pub lifetimes: Option<BoundLifetimes>,
        /// The `Foo<&'a T>` in `for<'a> Foo<&'a T>`
        pub path: Path,
    }
}

ast_enum! {
    /// A modifier on a trait bound, currently only used for the `?` in
    /// `?Sized`.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub enum TraitBoundModifier {
        None,
        Maybe(Token![?]),
    }
}

ast_struct! {
    /// A `where` clause in a definition: `where T: Deserialize<'de>, D:
    /// 'static`.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct WhereClause {
        pub where_token: Token![where],
        pub predicates: Punctuated<WherePredicate, Token![,]>,
    }
}

ast_enum_of_structs! {
    /// A single predicate in a `where` clause: `T: Deserialize<'de>`.
    ///
    /// # Syntax tree enum
    ///
    /// This type is a [syntax tree enum].
    ///
    /// [syntax tree enum]: crate::expr::Expr#syntax-tree-enums
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    #[non_exhaustive]
    pub enum WherePredicate {
        /// A lifetime predicate in a `where` clause: `'a: 'b + 'c`.
        Lifetime(PredicateLifetime),

        /// A type predicate in a `where` clause: `for<'c> Foo<'c>: Trait<'c>`.
        Type(PredicateType),
    }
}

ast_struct! {
    /// A lifetime predicate in a `where` clause: `'a: 'b + 'c`.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct PredicateLifetime {
        pub lifetime: Lifetime,
        pub colon_token: Token![:],
        pub bounds: Punctuated<Lifetime, Token![+]>,
    }
}

ast_struct! {
    /// A type predicate in a `where` clause: `for<'c> Foo<'c>: Trait<'c>`.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct PredicateType {
        /// Any lifetimes from a `for` binding
        pub lifetimes: Option<BoundLifetimes>,
        /// The type being bounded
        pub bounded_ty: Type,
        pub colon_token: Token![:],
        /// Trait and lifetime bounds (`Clone+Send+'static`)
        pub bounds: Punctuated<TypeParamBound, Token![+]>,
    }
}


#[cfg(feature = "printing")]
pub(crate) mod printing {
    use crate::attr::FilterAttrs;
    #[cfg(feature = "full")]
    use crate::expr;
    use crate::expr::Expr;
    #[cfg(feature = "full")]
    use crate::fixup::FixupContext;
    use crate::generics::{
        BoundLifetimes, ConstParam, GenericParam, Generics, ImplGenerics, LifetimeParam,
        PredicateLifetime, PredicateType, TraitBound, TraitBoundModifier, Turbofish, TypeGenerics,
        TypeParam, WhereClause,
    };
    use crate::print::TokensOrDefault;
    use crate::token;
    use proc_macro2::TokenStream;
    use quote::{ToTokens, TokenStreamExt};

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for Generics {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            if self.params.is_empty() {
                return;
            }

            TokensOrDefault(&self.lt_token).to_tokens(tokens);

            // Print lifetimes before types and consts, regardless of their
            // order in self.params.
            let mut trailing_or_empty = true;
            for param in self.params.pairs() {
                if let GenericParam::Lifetime(_) = **param.value() {
                    param.to_tokens(tokens);
                    trailing_or_empty = param.punct().is_some();
                }
            }
            for param in self.params.pairs() {
                match param.value() {
                    GenericParam::Type(_) | GenericParam::Const(_) => {
                        if !trailing_or_empty {
                            <Token![,]>::default().to_tokens(tokens);
                            trailing_or_empty = true;
                        }
                        param.to_tokens(tokens);
                    }
                    GenericParam::Lifetime(_) => {}
                }
            }

            TokensOrDefault(&self.gt_token).to_tokens(tokens);
        }
    }

    impl<'a> ToTokens for ImplGenerics<'a> {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            if self.0.params.is_empty() {
                return;
            }

            TokensOrDefault(&self.0.lt_token).to_tokens(tokens);

            // Print lifetimes before types and consts, regardless of their
            // order in self.params.
            let mut trailing_or_empty = true;
            for param in self.0.params.pairs() {
                if let GenericParam::Lifetime(_) = **param.value() {
                    param.to_tokens(tokens);
                    trailing_or_empty = param.punct().is_some();
                }
            }
            for param in self.0.params.pairs() {
                if let GenericParam::Lifetime(_) = **param.value() {
                    continue;
                }
                if !trailing_or_empty {
                    <Token![,]>::default().to_tokens(tokens);
                    trailing_or_empty = true;
                }
                match param.value() {
                    GenericParam::Lifetime(_) => unreachable!(),
                    GenericParam::Type(param) => {
                        // Leave off the type parameter defaults
                        tokens.append_all(param.attrs.outer());
                        param.ident.to_tokens(tokens);
                        if !param.bounds.is_empty() {
                            TokensOrDefault(&param.colon_token).to_tokens(tokens);
                            param.bounds.to_tokens(tokens);
                        }
                    }
                    GenericParam::Const(param) => {
                        // Leave off the const parameter defaults
                        tokens.append_all(param.attrs.outer());
                        param.const_token.to_tokens(tokens);
                        param.ident.to_tokens(tokens);
                        param.colon_token.to_tokens(tokens);
                        param.ty.to_tokens(tokens);
                    }
                }
                param.punct().to_tokens(tokens);
            }

            TokensOrDefault(&self.0.gt_token).to_tokens(tokens);
        }
    }

    impl<'a> ToTokens for TypeGenerics<'a> {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            if self.0.params.is_empty() {
                return;
            }

            TokensOrDefault(&self.0.lt_token).to_tokens(tokens);

            // Print lifetimes before types and consts, regardless of their
            // order in self.params.
            let mut trailing_or_empty = true;
            for param in self.0.params.pairs() {
                if let GenericParam::Lifetime(def) = *param.value() {
                    // Leave off the lifetime bounds and attributes
                    def.lifetime.to_tokens(tokens);
                    param.punct().to_tokens(tokens);
                    trailing_or_empty = param.punct().is_some();
                }
            }
            for param in self.0.params.pairs() {
                if let GenericParam::Lifetime(_) = **param.value() {
                    continue;
                }
                if !trailing_or_empty {
                    <Token![,]>::default().to_tokens(tokens);
                    trailing_or_empty = true;
                }
                match param.value() {
                    GenericParam::Lifetime(_) => unreachable!(),
                    GenericParam::Type(param) => {
                        // Leave off the type parameter defaults
                        param.ident.to_tokens(tokens);
                    }
                    GenericParam::Const(param) => {
                        // Leave off the const parameter defaults
                        param.ident.to_tokens(tokens);
                    }
                }
                param.punct().to_tokens(tokens);
            }

            TokensOrDefault(&self.0.gt_token).to_tokens(tokens);
        }
    }

    impl<'a> ToTokens for Turbofish<'a> {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            if !self.0.params.is_empty() {
                <Token![::]>::default().to_tokens(tokens);
                TypeGenerics(self.0).to_tokens(tokens);
            }
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for BoundLifetimes {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.for_token.to_tokens(tokens);
            self.lt_token.to_tokens(tokens);
            self.lifetimes.to_tokens(tokens);
            self.gt_token.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for LifetimeParam {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.append_all(self.attrs.outer());
            self.lifetime.to_tokens(tokens);
            if !self.bounds.is_empty() {
                TokensOrDefault(&self.colon_token).to_tokens(tokens);
                self.bounds.to_tokens(tokens);
            }
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for TypeParam {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.append_all(self.attrs.outer());
            self.ident.to_tokens(tokens);
            if !self.bounds.is_empty() {
                TokensOrDefault(&self.colon_token).to_tokens(tokens);
                self.bounds.to_tokens(tokens);
            }
            if let Some(default) = &self.default {
                TokensOrDefault(&self.eq_token).to_tokens(tokens);
                default.to_tokens(tokens);
            }
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for TraitBound {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            let to_tokens = |tokens: &mut TokenStream| {
                self.modifier.to_tokens(tokens);
                self.lifetimes.to_tokens(tokens);
                self.path.to_tokens(tokens);
            };
            match &self.paren_token {
                Some(paren) => paren.surround(tokens, to_tokens),
                None => to_tokens(tokens),
            }
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for TraitBoundModifier {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            match self {
                TraitBoundModifier::None => {}
                TraitBoundModifier::Maybe(t) => t.to_tokens(tokens),
            }
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ConstParam {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.append_all(self.attrs.outer());
            self.const_token.to_tokens(tokens);
            self.ident.to_tokens(tokens);
            self.colon_token.to_tokens(tokens);
            self.ty.to_tokens(tokens);
            if let Some(default) = &self.default {
                TokensOrDefault(&self.eq_token).to_tokens(tokens);
                print_const_argument(default, tokens);
            }
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for WhereClause {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            if !self.predicates.is_empty() {
                self.where_token.to_tokens(tokens);
                self.predicates.to_tokens(tokens);
            }
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for PredicateLifetime {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.lifetime.to_tokens(tokens);
            self.colon_token.to_tokens(tokens);
            self.bounds.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for PredicateType {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.lifetimes.to_tokens(tokens);
            self.bounded_ty.to_tokens(tokens);
            self.colon_token.to_tokens(tokens);
            self.bounds.to_tokens(tokens);
        }
    }

    pub(crate) fn print_const_argument(expr: &Expr, tokens: &mut TokenStream) {
        match expr {
            Expr::Lit(expr) => expr.to_tokens(tokens),

            Expr::Path(expr)
                if expr.attrs.is_empty()
                    && expr.qself.is_none()
                    && expr.path.get_ident().is_some() =>
            {
                expr.to_tokens(tokens);
            }

            #[cfg(feature = "full")]
            Expr::Block(expr) => expr.to_tokens(tokens),

            #[cfg(not(feature = "full"))]
            Expr::Verbatim(expr) => expr.to_tokens(tokens),

            // ERROR CORRECTION: Add braces to make sure that the
            // generated code is valid.
            _ => token::Brace::default().surround(tokens, |tokens| {
                #[cfg(feature = "full")]
                expr::printing::print_expr(expr, tokens, FixupContext::new_stmt());

                #[cfg(not(feature = "full"))]
                expr.to_tokens(tokens);
            }),
        }
    }
}
