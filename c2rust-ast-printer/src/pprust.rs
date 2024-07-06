#[cfg(test)]
mod tests;

#[derive(PartialEq, Eq, Debug, PartialOrd, Ord, Copy, Clone)]
pub struct BytePos(pub u32);

pub mod comments {
    #[derive(Clone)]
    pub struct Comment {
        pub lines: Vec<String>,
        pub pos: super::BytePos,
    }
}

pub enum MacHeader<'a> {
    Path(&'a rast::Path),
    Keyword(&'static str),
}

pub struct Comments {
    //cm: &'a SourceMap,
    comments: Vec<comments::Comment>,
    current: usize,
}

impl Comments {
    pub fn new(
        //cm: &'a SourceMap,
        comments: Vec<comments::Comment>,
    ) -> Comments {
        Comments {
            //cm,
            comments,
            current: 0,
        }
    }

    // pub fn parse(
    //     cm: &'a SourceMap,
    //     sess: &ParseSess,
    //     filename: FileName,
    //     input: String,
    // ) -> Comments<'a> {
    //     let comments = comments::gather_comments(sess, filename, input);
    //     Comments {
    //         cm,
    //         comments,
    //         current: 0,
    //     }
    // }

    pub fn next(&self) -> Option<comments::Comment> {
        self.comments.get(self.current).cloned()
    }

    pub fn trailing_comment(
        &mut self,
        _span: proc_macro2::Span,
        _next_pos: Option<usize>,
    ) -> Option<String> {
        /*if let Some(cmnt) = self.next() {
            if cmnt.style != comments::Trailing { return None; }
            let span_line = self.cm.lookup_char_pos(span.hi());
            let comment_line = self.cm.lookup_char_pos(cmnt.pos);
            let next = next_pos.unwrap_or_else(|| cmnt.pos + BytePos(1));
            if span.hi() < cmnt.pos && cmnt.pos < next && span_line.line == comment_line.line {
                return Some(cmnt);
            }
        }*/

        None
    }
}

impl Extend<comments::Comment> for Comments {
    fn extend<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = comments::Comment>,
    {
        self.comments.extend(iter);
    }
}

fn strip_main_fn(s: &str) -> &str {
    s.trim_start()
        .trim_start_matches("fn main()")
        .trim_start()
        .trim_start_matches('{')
        .trim_start()
        .trim_end()
        .trim_end_matches('}')
        .trim_end()
}

fn minimal_file(stmt: rast::Stmt) -> rast::File {
    let item = rast::Item::Fn(main_fn(stmt));
    rast::File {
        shebang: None,
        attrs: vec![],
        items: vec![item],
    }
}

fn main_fn(stmt: rast::Stmt) -> rast::ItemFn {
    let generics = rast::Generics {
        lt_token: None,
        params: Default::default(),
        gt_token: None,
        where_clause: None,
    };
    let ident = rast::Ident::new("main", proc_macro2::Span::call_site());
    let sig = rast::Signature {
        constness: None,
        asyncness: None,
        unsafety: None,
        abi: None,
        fn_token: Default::default(),
        ident,
        generics,
        paren_token: Default::default(),
        inputs: Default::default(),
        variadic: None,
        output: rast::ReturnType::Default,
    };
    let block = Box::new(rast::Block {
        brace_token: Default::default(),
        stmts: vec![stmt],
    });
    rast::ItemFn {
        attrs: vec![],
        vis: rast::Visibility::Inherited,
        sig,
        block,
    }
}

fn ret_expr() -> rast::Expr {
    rast::Expr::Return(rast::ExprReturn {
        attrs: vec![],
        return_token: Default::default(),
        expr: None,
    })
}

pub fn expr_to_string(e: &rast::Expr) -> String {
    let s = to_string(move || minimal_file(rast::Stmt::Expr(e.clone(), None)));
    strip_main_fn(&s).trim_end_matches(';').to_owned()
}

pub fn path_to_string(p: &rast::Path) -> String {
    let e = rast::Expr::Path(rast::ExprPath {
        attrs: vec![],
        qself: None,
        path: p.clone(),
    });
    expr_to_string(&e)
}

pub fn pat_to_string(p: &rast::Pat) -> String {
    let ret_expr = Box::new(ret_expr());
    let e = rast::Expr::Let(rast::ExprLet {
        attrs: vec![],
        let_token: Default::default(),
        pat: Box::new(p.clone()),
        eq_token: Default::default(),
        expr: ret_expr,
    });
    let expr_str = expr_to_string(&e);
    expr_str
        .trim_start_matches("let")
        .trim_start()
        .trim_end()
        .trim_end_matches(';')
        .trim_end_matches("return")
        .trim_end()
        .trim_end_matches('=')
        .trim_end()
        .to_owned()
}

pub fn stmt_to_string(s: &rast::Stmt) -> String {
    let s = to_string(move || minimal_file(s.clone()));
    strip_main_fn(&s).to_owned()
}

pub fn to_string<F>(f: F) -> String
where
    F: FnOnce() -> rast::File,
{
    pp::unparse(&f())
}
