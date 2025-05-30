use c2rust_ast_builder::{mk, properties::Mutability};
use syn::Item;

use super::Translation;

impl<'c> Translation<'c> {
    /// generate struct definition of PointerMut<T> / Pointer<T>
    /// this struct serve as wrapper for *mut pointer / *const pointer in static declaration
    /// because rust forbid pointer in static, so as workaround we create this struct
    /// and implement unsafe impl Sync for it
    pub(crate) fn generate_global_pointer_wrapper_struct(
        &mut self,
        mutbl_: Mutability,
    ) -> (Box<Item>, Box<Item>) {
        let name = match mutbl_ {
            Mutability::Mutable => "PointerMut",
            Mutability::Immutable => "Pointer",
        };

        let struct_item = mk()
            .call_attr("derive", vec!["Copy", "Clone"])
            .generic_over(mk().ty_param(mk().ident("T")))
            .where_clause(vec![
                mk().where_predicate(mk().ident_ty("T"), vec!["Copy", "Clone"]),
            ])
            .pub_()
            .struct_item(
                name,
                vec![
                    mk().pub_()
                        .struct_unamed_field(mk().set_mutbl(mutbl_).ptr_ty(mk().ident_ty("T"))),
                ],
                true,
            );

        let sync_impl = mk()
            .unsafe_()
            .generic_over(mk().ty_param(mk().ident("T")))
            .where_clause(vec![
                mk().where_predicate(mk().path_ty(vec!["T"]), vec!["Copy", "Clone"]),
            ])
            .impl_trait_item(
                mk().path_ty(vec![mk().path_segment_with_args(
                    name,
                    mk().angle_bracketed_args(vec![mk().path_ty(vec!["T"])]),
                )]),
                mk().path("Sync"),
                vec![],
            );

        (struct_item, sync_impl)
    }
}
