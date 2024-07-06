use crate::path::Path;
use crate::token;

ast_enum! {
    /// The visibility level of an item: inherited or `pub` or
    /// `pub(restricted)`.
    ///
    /// # Syntax tree enum
    ///
    /// This type is a [syntax tree enum].
    ///
    /// [syntax tree enum]: crate::expr::Expr#syntax-tree-enums
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub enum Visibility {
        /// A public visibility level: `pub`.
        Public(Token![pub]),

        /// A visibility level restricted to some path: `pub(self)` or
        /// `pub(super)` or `pub(crate)` or `pub(in some::module)`.
        Restricted(VisRestricted),

        /// An inherited visibility, which usually means private.
        Inherited,
    }
}

ast_struct! {
    /// A visibility level restricted to some path: `pub(self)` or
    /// `pub(super)` or `pub(crate)` or `pub(in some::module)`.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct VisRestricted {
        pub pub_token: Token![pub],
        pub paren_token: token::Paren,
        pub in_token: Option<Token![in]>,
        pub path: Box<Path>,
    }
}

ast_enum! {
    /// Unused, but reserved for RFC 3323 restrictions.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    #[non_exhaustive]
    pub enum FieldMutability {
        None,

        // TODO: https://rust-lang.github.io/rfcs/3323-restrictions.html
        //
        // FieldMutability::Restricted(MutRestricted)
        //
        // pub struct MutRestricted {
        //     pub mut_token: Token![mut],
        //     pub paren_token: token::Paren,
        //     pub in_token: Option<Token![in]>,
        //     pub path: Box<Path>,
        // }
    }
}

#[cfg(feature = "printing")]
mod printing {
    use crate::restriction::{VisRestricted, Visibility};
    use proc_macro2::TokenStream;
    use quote::ToTokens;

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for Visibility {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            match self {
                Visibility::Public(pub_token) => pub_token.to_tokens(tokens),
                Visibility::Restricted(vis_restricted) => vis_restricted.to_tokens(tokens),
                Visibility::Inherited => {}
            }
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for VisRestricted {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.pub_token.to_tokens(tokens);
            self.paren_token.surround(tokens, |tokens| {
                // TODO: If we have a path which is not "self" or "super" or
                // "crate", automatically add the "in" token.
                self.in_token.to_tokens(tokens);
                self.path.to_tokens(tokens);
            });
        }
    }
}
