use crate::path::Path;
use crate::token::{Brace, Bracket, Paren};
use proc_macro2::extra::DelimSpan;
use proc_macro2::TokenStream;

ast_struct! {
    /// A macro invocation: `println!("{}", mac)`.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub struct Macro {
        pub path: Path,
        pub bang_token: Token![!],
        pub delimiter: MacroDelimiter,
        pub tokens: TokenStream,
    }
}

ast_enum! {
    /// A grouping token that surrounds a macro body: `m!(...)` or `m!{...}` or `m![...]`.
    #[cfg_attr(docsrs, doc(cfg(any(feature = "full", feature = "derive"))))]
    pub enum MacroDelimiter {
        Paren(Paren),
        Brace(Brace),
        Bracket(Bracket),
    }
}

impl MacroDelimiter {
    pub fn span(&self) -> &DelimSpan {
        match self {
            MacroDelimiter::Paren(token) => &token.span,
            MacroDelimiter::Brace(token) => &token.span,
            MacroDelimiter::Bracket(token) => &token.span,
        }
    }

    pub(crate) fn is_brace(&self) -> bool {
        match self {
            MacroDelimiter::Brace(_) => true,
            MacroDelimiter::Paren(_) | MacroDelimiter::Bracket(_) => false,
        }
    }
}

impl Macro {}

#[cfg(feature = "printing")]
mod printing {
    use crate::mac::{Macro, MacroDelimiter};
    use crate::token;
    use proc_macro2::{Delimiter, TokenStream};
    use quote::ToTokens;

    impl MacroDelimiter {
        pub(crate) fn surround(&self, tokens: &mut TokenStream, inner: TokenStream) {
            let (delim, span) = match self {
                MacroDelimiter::Paren(paren) => (Delimiter::Parenthesis, paren.span),
                MacroDelimiter::Brace(brace) => (Delimiter::Brace, brace.span),
                MacroDelimiter::Bracket(bracket) => (Delimiter::Bracket, bracket.span),
            };
            token::printing::delim(delim, span.join(), tokens, inner);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for Macro {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.path.to_tokens(tokens);
            self.bang_token.to_tokens(tokens);
            self.delimiter.surround(tokens, self.tokens.clone());
        }
    }
}
