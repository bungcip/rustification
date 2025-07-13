#![deny(missing_docs)]
//! This code is used to generate literal expressions of various kinds.
//! These include integer, floating, array, struct, union, enum literals.

use crate::generic_err;

use super::*;

impl<'c> Translation<'c> {
    pub(crate) fn convert_macro_expansion(
        &self,
        ctx: ExprContext,
        expr_id: CExprId,
    ) -> TranslationResult<Option<WithStmts<Box<Expr>>>> {
        if let Some(macs) = self.ast_context.macro_invocations.get(&expr_id) {
            // Find the first macro after the macro we're currently
            // expanding, if any.
            if let Some(macro_id) = macs
                .splitn(2, |macro_id| ctx.expanding_macro(macro_id))
                .last()
                .unwrap()
                .first()
            {
                trace!("  found macro expansion: {macro_id:?}");
                // Ensure that we've converted this macro and that it has a
                // valid definition
                let expansion = self.macro_expansions.borrow().get(macro_id).cloned();
                let macro_ty = match expansion {
                    // expansion exists
                    Some(Some(expansion)) => expansion.ty,

                    // expansion wasn't possible
                    Some(None) => return Ok(None),

                    // We haven't tried to expand it yet
                    None => {
                        self.convert_decl(ctx, *macro_id)?;
                        if let Some(Some(expansion)) = self.macro_expansions.borrow().get(macro_id)
                        {
                            expansion.ty
                        } else {
                            return Ok(None);
                        }
                    }
                };
                let rustname = self
                    .renamer
                    .borrow_mut()
                    .get(macro_id)
                    .ok_or_else(|| generic_err!("Macro name not declared"))?;

                if let Some(cur_file) = self.cur_file.borrow().as_ref() {
                    self.add_import(*cur_file, *macro_id, &rustname);
                }

                let val = WithStmts::new_val(mk().ident_expr(rustname));

                let expr_kind = &self.ast_context[expr_id].kind;
                if let Some(expr_ty) = expr_kind.get_qual_type() {
                    return self
                        .convert_cast(
                            ctx,
                            CQualTypeId::new(macro_ty),
                            expr_ty,
                            val,
                            None,
                            None,
                            None,
                        )
                        .map(Some);
                } else {
                    return Ok(Some(val));
                }

                // TODO: May need to handle volatile reads here, see
                // DeclRef below
            }
        }

        Ok(None)
    }

    pub(crate) fn convert_macro_invocation(
        &self,
        _ctx: ExprContext,
        text: &str,
    ) -> Option<WithStmts<Box<Expr>>> {
        let mut split = text.splitn(2, '(');
        let ident = split.next()?.trim();
        let args = split.next()?.trim_end_matches(')');

        let ts: TokenStream = syn::parse_str(args).ok()?;
        Some(WithStmts::new_val(mk().mac_expr(mk().mac(
            mk().path(ident),
            ts,
            MacroDelimiter::Paren(Default::default()),
        ))))
    }
}
