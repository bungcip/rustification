use indexmap::IndexSet;

use crate::c_ast::CDeclId;

use super::DecayRef;

#[derive(Copy, Clone, Debug)]
pub struct ExprContext {
    pub used: bool,
    pub is_static: bool,
    pub is_const: bool,
    pub decay_ref: DecayRef,
    pub is_bitfield_write: bool,

    // set this if expr is inside InitList of static variable declaration of array of pointer (AOP)
    // ex: `static unsigned char *const z[] = {(unsigned char *)"Z"};`
    pub inside_init_list_aop: bool,

    // We will be referring to the expression by address. In this context we
    // can't index arrays because they may legally go out of bounds. We also
    // need to explicitly cast function references to fn() so we get their
    // address in function pointer literals.
    pub needs_address: bool,

    /// Set to false if we should decay VaListImpl to VaList or true if we are
    /// expect a VaListImpl in this context.
    pub expecting_valistimpl: bool,

    pub ternary_needs_parens: bool,
    pub expanding_macro: Option<CDeclId>,
}

impl ExprContext {
    pub fn used(self) -> Self {
        ExprContext { used: true, ..self }
    }
    pub fn unused(self) -> Self {
        ExprContext {
            used: false,
            ..self
        }
    }
    pub fn is_used(&self) -> bool {
        self.used
    }
    pub fn is_unused(&self) -> bool {
        self.used == false
    }

    pub fn inside_init_list_aop(self) -> Self {
        ExprContext {
            inside_init_list_aop: true,
            ..self
        }
    }

    pub fn is_inside_init_list_aop(&self) -> bool {
        self.inside_init_list_aop
    }

    pub fn decay_ref(self) -> Self {
        ExprContext {
            decay_ref: DecayRef::Yes,
            ..self
        }
    }
    pub fn not_static(self) -> Self {
        ExprContext {
            is_static: false,
            ..self
        }
    }
    pub fn static_(self) -> Self {
        ExprContext {
            is_static: true,
            ..self
        }
    }
    pub fn set_static(self, is_static: bool) -> Self {
        ExprContext { is_static, ..self }
    }
    pub fn set_const(self, is_const: bool) -> Self {
        ExprContext { is_const, ..self }
    }
    pub fn is_bitfield_write(&self) -> bool {
        self.is_bitfield_write
    }
    pub fn set_bitfield_write(self, is_bitfield_write: bool) -> Self {
        ExprContext {
            is_bitfield_write,
            ..self
        }
    }
    pub fn needs_address(&self) -> bool {
        self.needs_address
    }
    pub fn set_needs_address(self, needs_address: bool) -> Self {
        ExprContext {
            needs_address,
            ..self
        }
    }

    pub fn expect_valistimpl(self) -> Self {
        ExprContext {
            expecting_valistimpl: true,
            ..self
        }
    }

    /// Are we expanding the given macro in the current context?
    pub fn expanding_macro(&self, mac: &CDeclId) -> bool {
        match self.expanding_macro {
            Some(expanding) => expanding == *mac,
            None => false,
        }
    }
    pub fn set_expanding_macro(self, mac: CDeclId) -> Self {
        ExprContext {
            expanding_macro: Some(mac),
            ..self
        }
    }
}

#[derive(Clone, Debug, Default)]
pub(crate) struct FuncContext {
    /// The name of the function we're currently translating
    pub name: Option<String>,
    /// The name we give to the Rust function argument corresponding
    /// to the ellipsis in variadic C functions.
    pub va_list_arg_name: Option<String>,
    /// The va_list decls that are either `va_start`ed or `va_copy`ed.
    pub va_list_decl_ids: Option<IndexSet<CDeclId>>,
}

impl FuncContext {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn enter_new(&mut self, fn_name: &str) {
        self.name = Some(fn_name.to_string());
        self.va_list_arg_name = None;
        self.va_list_decl_ids = None;
    }

    // pub fn get_name(&self) -> &str {
    //     self.name.as_ref().unwrap()
    // }

    pub fn get_va_list_arg_name(&self) -> &str {
        self.va_list_arg_name.as_ref().unwrap()
    }
}
