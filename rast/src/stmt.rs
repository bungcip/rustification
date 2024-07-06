use crate::attr::Attribute;
use crate::expr::Expr;
use crate::item::Item;
use crate::mac::Macro;
use crate::pat::Pat;
use crate::token;

ast_struct! {
    /// A braced block containing Rust statements.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct Block {
        pub brace_token: token::Brace,
        /// Statements in a block
        pub stmts: Vec<Stmt>,
    }
}

ast_enum! {
    /// A statement, usually ending in a semicolon.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub enum Stmt {
        /// A local (let) binding.
        Local(Local),

        /// An item definition.
        Item(Item),

        /// Expression, with or without trailing semicolon.
        Expr(Expr, Option<Token![;]>),

        /// A macro invocation in statement position.
        ///
        /// Syntactically it's ambiguous which other kind of statement this
        /// macro would expand to. It can be any of local variable (`let`),
        /// item, or expression.
        Macro(StmtMacro),
    }
}

ast_struct! {
    /// A local `let` binding: `let x: u64 = s.parse()?`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct Local {
        pub attrs: Vec<Attribute>,
        pub let_token: Token![let],
        pub pat: Pat,
        pub init: Option<LocalInit>,
        pub semi_token: Token![;],
    }
}

ast_struct! {
    /// The expression assigned in a local `let` binding, including optional
    /// diverging `else` block.
    ///
    /// `LocalInit` represents `= s.parse()?` in `let x: u64 = s.parse()?` and
    /// `= r else { return }` in `let Ok(x) = r else { return }`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct LocalInit {
        pub eq_token: Token![=],
        pub expr: Box<Expr>,
        pub diverge: Option<(Token![else], Box<Expr>)>,
    }
}

ast_struct! {
    /// A macro invocation in statement position.
    ///
    /// Syntactically it's ambiguous which other kind of statement this macro
    /// would expand to. It can be any of local variable (`let`), item, or
    /// expression.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct StmtMacro {
        pub attrs: Vec<Attribute>,
        pub mac: Macro,
        pub semi_token: Option<Token![;]>,
    }
}

#[cfg(feature = "printing")]
pub(crate) mod printing {
    use crate::classify;
    use crate::expr::{self, Expr};
    use crate::fixup::FixupContext;
    use crate::stmt::{Block, Local, Stmt, StmtMacro};
    use crate::token;
    use proc_macro2::TokenStream;
    use quote::{ToTokens, TokenStreamExt};

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for Block {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.brace_token.surround(tokens, |tokens| {
                tokens.append_all(&self.stmts);
            });
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for Stmt {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            match self {
                Stmt::Local(local) => local.to_tokens(tokens),
                Stmt::Item(item) => item.to_tokens(tokens),
                Stmt::Expr(expr, semi) => {
                    expr::printing::print_expr(expr, tokens, FixupContext::new_stmt());
                    semi.to_tokens(tokens);
                }
                Stmt::Macro(mac) => mac.to_tokens(tokens),
            }
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for Local {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            expr::printing::outer_attrs_to_tokens(&self.attrs, tokens);
            self.let_token.to_tokens(tokens);
            self.pat.to_tokens(tokens);
            if let Some(init) = &self.init {
                init.eq_token.to_tokens(tokens);
                if init.diverge.is_some() && classify::expr_trailing_brace(&init.expr) {
                    token::Paren::default().surround(tokens, |tokens| init.expr.to_tokens(tokens));
                } else {
                    init.expr.to_tokens(tokens);
                }
                if let Some((else_token, diverge)) = &init.diverge {
                    else_token.to_tokens(tokens);
                    match &**diverge {
                        Expr::Block(diverge) => diverge.to_tokens(tokens),
                        _ => token::Brace::default().surround(tokens, |tokens| {
                            expr::printing::print_expr(diverge, tokens, FixupContext::new_stmt());
                        }),
                    }
                }
            }
            self.semi_token.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for StmtMacro {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            expr::printing::outer_attrs_to_tokens(&self.attrs, tokens);
            self.mac.to_tokens(tokens);
            self.semi_token.to_tokens(tokens);
        }
    }
}
