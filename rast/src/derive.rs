use crate::attr::Attribute;
use crate::data::{Fields, FieldsNamed, Variant};
use crate::generics::Generics;
use crate::ident::Ident;
use crate::punctuated::Punctuated;
use crate::restriction::Visibility;
use crate::token;

ast_struct! {
    /// Data structure sent to a `proc_macro_derive` macro.
    #[cfg_attr(docsrs, doc(cfg(feature = "derive")))]
    pub struct DeriveInput {
        pub attrs: Vec<Attribute>,
        pub vis: Visibility,
        pub ident: Ident,
        pub generics: Generics,
        pub data: Data,
    }
}

ast_enum! {
    /// The storage of a struct, enum or union data structure.
    ///
    /// # Syntax tree enum
    ///
    /// This type is a [syntax tree enum].
    ///
    /// [syntax tree enum]: crate::expr::Expr#syntax-tree-enums
    #[cfg_attr(docsrs, doc(cfg(feature = "derive")))]
    pub enum Data {
        Struct(DataStruct),
        Enum(DataEnum),
        Union(DataUnion),
    }
}

ast_struct! {
    /// A struct input to a `proc_macro_derive` macro.
    #[cfg_attr(docsrs, doc(cfg(feature = "derive")))]
    pub struct DataStruct {
        pub struct_token: Token![struct],
        pub fields: Fields,
        pub semi_token: Option<Token![;]>,
    }
}

ast_struct! {
    /// An enum input to a `proc_macro_derive` macro.
    #[cfg_attr(docsrs, doc(cfg(feature = "derive")))]
    pub struct DataEnum {
        pub enum_token: Token![enum],
        pub brace_token: token::Brace,
        pub variants: Punctuated<Variant, Token![,]>,
    }
}

ast_struct! {
    /// An untagged union input to a `proc_macro_derive` macro.
    #[cfg_attr(docsrs, doc(cfg(feature = "derive")))]
    pub struct DataUnion {
        pub union_token: Token![union],
        pub fields: FieldsNamed,
    }
}

#[cfg(feature = "printing")]
mod printing {
    use crate::attr::FilterAttrs;
    use crate::data::Fields;
    use crate::derive::{Data, DeriveInput};
    use crate::print::TokensOrDefault;
    use proc_macro2::TokenStream;
    use quote::ToTokens;

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for DeriveInput {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            for attr in self.attrs.outer() {
                attr.to_tokens(tokens);
            }
            self.vis.to_tokens(tokens);
            match &self.data {
                Data::Struct(d) => d.struct_token.to_tokens(tokens),
                Data::Enum(d) => d.enum_token.to_tokens(tokens),
                Data::Union(d) => d.union_token.to_tokens(tokens),
            }
            self.ident.to_tokens(tokens);
            self.generics.to_tokens(tokens);
            match &self.data {
                Data::Struct(data) => match &data.fields {
                    Fields::Named(fields) => {
                        self.generics.where_clause.to_tokens(tokens);
                        fields.to_tokens(tokens);
                    }
                    Fields::Unnamed(fields) => {
                        fields.to_tokens(tokens);
                        self.generics.where_clause.to_tokens(tokens);
                        TokensOrDefault(&data.semi_token).to_tokens(tokens);
                    }
                    Fields::Unit => {
                        self.generics.where_clause.to_tokens(tokens);
                        TokensOrDefault(&data.semi_token).to_tokens(tokens);
                    }
                },
                Data::Enum(data) => {
                    self.generics.where_clause.to_tokens(tokens);
                    data.brace_token.surround(tokens, |tokens| {
                        data.variants.to_tokens(tokens);
                    });
                }
                Data::Union(data) => {
                    self.generics.where_clause.to_tokens(tokens);
                    data.fields.to_tokens(tokens);
                }
            }
        }
    }
}
