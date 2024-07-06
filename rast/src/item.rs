use crate::attr::Attribute;
use crate::data::{Fields, FieldsNamed, Variant};
use crate::derive::{Data, DataEnum, DataStruct, DataUnion, DeriveInput};
use crate::expr::Expr;
use crate::generics::{Generics, TypeParamBound};
use crate::ident::Ident;
use crate::lifetime::Lifetime;
use crate::mac::Macro;
use crate::pat::{Pat, PatType};
use crate::path::Path;
use crate::punctuated::Punctuated;
use crate::restriction::Visibility;
use crate::stmt::Block;
use crate::token;
use crate::ty::{Abi, ReturnType, Type};
use proc_macro2::TokenStream;

ast_enum_of_structs! {
    /// Things that can appear directly inside of a module or scope.
    ///
    /// # Syntax tree enum
    ///
    /// This type is a [syntax tree enum].
    ///
    /// [syntax tree enum]: crate::expr::Expr#syntax-tree-enums
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    #[non_exhaustive]
    pub enum Item {
        /// A constant item: `const MAX: u16 = 65535`.
        Const(ItemConst),

        /// An enum definition: `enum Foo<A, B> { A(A), B(B) }`.
        Enum(ItemEnum),

        /// An `extern crate` item: `extern crate serde`.
        ExternCrate(ItemExternCrate),

        /// A free-standing function: `fn process(n: usize) -> Result<()> { ...
        /// }`.
        Fn(ItemFn),

        /// A block of foreign items: `extern "C" { ... }`.
        ForeignMod(ItemForeignMod),

        /// An impl block providing trait or associated items: `impl<A> Trait
        /// for Data<A> { ... }`.
        Impl(ItemImpl),

        /// A macro invocation, which includes `macro_rules!` definitions.
        Macro(ItemMacro),

        /// A module or module declaration: `mod m` or `mod m { ... }`.
        Mod(ItemMod),

        /// A static item: `static BIKE: Shed = Shed(42)`.
        Static(ItemStatic),

        /// A struct definition: `struct Foo<A> { x: A }`.
        Struct(ItemStruct),

        /// A trait definition: `pub trait Iterator { ... }`.
        Trait(ItemTrait),

        /// A trait alias: `pub trait SharableIterator = Iterator + Sync`.
        TraitAlias(ItemTraitAlias),

        /// A type alias: `type Result<T> = std::result::Result<T, MyError>`.
        Type(ItemType),

        /// A union definition: `union Foo<A, B> { x: A, y: B }`.
        Union(ItemUnion),

        /// A use declaration: `use std::collections::HashMap`.
        Use(ItemUse),

        /// Tokens forming an item not interpreted by Syn.
        Verbatim(TokenStream),

        // For testing exhaustiveness in downstream code, use the following idiom:
        //
        //     match item {
        //         #![cfg_attr(test, deny(non_exhaustive_omitted_patterns))]
        //
        //         Item::Const(item) => {...}
        //         Item::Enum(item) => {...}
        //         ...
        //         Item::Verbatim(item) => {...}
        //
        //         _ => { /* some sane fallback */ }
        //     }
        //
        // This way we fail your tests but don't break your library when adding
        // a variant. You will be notified by a test failure when a variant is
        // added, so that you can add code to handle it, but your library will
        // continue to compile and work for downstream users in the interim.
    }
}

ast_struct! {
    /// A constant item: `const MAX: u16 = 65535`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct ItemConst {
        pub attrs: Vec<Attribute>,
        pub vis: Visibility,
        pub const_token: Token![const],
        pub ident: Ident,
        pub generics: Generics,
        pub colon_token: Token![:],
        pub ty: Box<Type>,
        pub eq_token: Token![=],
        pub expr: Box<Expr>,
        pub semi_token: Token![;],
    }
}

ast_struct! {
    /// An enum definition: `enum Foo<A, B> { A(A), B(B) }`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct ItemEnum {
        pub attrs: Vec<Attribute>,
        pub vis: Visibility,
        pub enum_token: Token![enum],
        pub ident: Ident,
        pub generics: Generics,
        pub brace_token: token::Brace,
        pub variants: Punctuated<Variant, Token![,]>,
    }
}

ast_struct! {
    /// An `extern crate` item: `extern crate serde`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct ItemExternCrate {
        pub attrs: Vec<Attribute>,
        pub vis: Visibility,
        pub extern_token: Token![extern],
        pub crate_token: Token![crate],
        pub ident: Ident,
        pub rename: Option<(Token![as], Ident)>,
        pub semi_token: Token![;],
    }
}

ast_struct! {
    /// A free-standing function: `fn process(n: usize) -> Result<()> { ... }`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct ItemFn {
        pub attrs: Vec<Attribute>,
        pub vis: Visibility,
        pub sig: Signature,
        pub block: Box<Block>,
    }
}

ast_struct! {
    /// A block of foreign items: `extern "C" { ... }`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct ItemForeignMod {
        pub attrs: Vec<Attribute>,
        pub unsafety: Option<Token![unsafe]>,
        pub abi: Abi,
        pub brace_token: token::Brace,
        pub items: Vec<ForeignItem>,
    }
}

ast_struct! {
    /// An impl block providing trait or associated items: `impl<A> Trait
    /// for Data<A> { ... }`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct ItemImpl {
        pub attrs: Vec<Attribute>,
        pub defaultness: Option<Token![default]>,
        pub unsafety: Option<Token![unsafe]>,
        pub impl_token: Token![impl],
        pub generics: Generics,
        /// Trait this impl implements.
        pub trait_: Option<(Option<Token![!]>, Path, Token![for])>,
        /// The Self type of the impl.
        pub self_ty: Box<Type>,
        pub brace_token: token::Brace,
        pub items: Vec<ImplItem>,
    }
}

ast_struct! {
    /// A macro invocation, which includes `macro_rules!` definitions.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct ItemMacro {
        pub attrs: Vec<Attribute>,
        /// The `example` in `macro_rules! example { ... }`.
        pub ident: Option<Ident>,
        pub mac: Macro,
        pub semi_token: Option<Token![;]>,
    }
}

ast_struct! {
    /// A module or module declaration: `mod m` or `mod m { ... }`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct ItemMod {
        pub attrs: Vec<Attribute>,
        pub vis: Visibility,
        pub unsafety: Option<Token![unsafe]>,
        pub mod_token: Token![mod],
        pub ident: Ident,
        pub content: Option<(token::Brace, Vec<Item>)>,
        pub semi: Option<Token![;]>,
    }
}

ast_struct! {
    /// A static item: `static BIKE: Shed = Shed(42)`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct ItemStatic {
        pub attrs: Vec<Attribute>,
        pub vis: Visibility,
        pub static_token: Token![static],
        pub mutability: StaticMutability,
        pub ident: Ident,
        pub colon_token: Token![:],
        pub ty: Box<Type>,
        pub eq_token: Token![=],
        pub expr: Box<Expr>,
        pub semi_token: Token![;],
    }
}

ast_struct! {
    /// A struct definition: `struct Foo<A> { x: A }`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct ItemStruct {
        pub attrs: Vec<Attribute>,
        pub vis: Visibility,
        pub struct_token: Token![struct],
        pub ident: Ident,
        pub generics: Generics,
        pub fields: Fields,
        pub semi_token: Option<Token![;]>,
    }
}

ast_struct! {
    /// A trait definition: `pub trait Iterator { ... }`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct ItemTrait {
        pub attrs: Vec<Attribute>,
        pub vis: Visibility,
        pub unsafety: Option<Token![unsafe]>,
        pub auto_token: Option<Token![auto]>,
        pub restriction: Option<ImplRestriction>,
        pub trait_token: Token![trait],
        pub ident: Ident,
        pub generics: Generics,
        pub colon_token: Option<Token![:]>,
        pub supertraits: Punctuated<TypeParamBound, Token![+]>,
        pub brace_token: token::Brace,
        pub items: Vec<TraitItem>,
    }
}

ast_struct! {
    /// A trait alias: `pub trait SharableIterator = Iterator + Sync`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct ItemTraitAlias {
        pub attrs: Vec<Attribute>,
        pub vis: Visibility,
        pub trait_token: Token![trait],
        pub ident: Ident,
        pub generics: Generics,
        pub eq_token: Token![=],
        pub bounds: Punctuated<TypeParamBound, Token![+]>,
        pub semi_token: Token![;],
    }
}

ast_struct! {
    /// A type alias: `type Result<T> = std::result::Result<T, MyError>`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct ItemType {
        pub attrs: Vec<Attribute>,
        pub vis: Visibility,
        pub type_token: Token![type],
        pub ident: Ident,
        pub generics: Generics,
        pub eq_token: Token![=],
        pub ty: Box<Type>,
        pub semi_token: Token![;],
    }
}

ast_struct! {
    /// A union definition: `union Foo<A, B> { x: A, y: B }`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct ItemUnion {
        pub attrs: Vec<Attribute>,
        pub vis: Visibility,
        pub union_token: Token![union],
        pub ident: Ident,
        pub generics: Generics,
        pub fields: FieldsNamed,
    }
}

ast_struct! {
    /// A use declaration: `use std::collections::HashMap`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct ItemUse {
        pub attrs: Vec<Attribute>,
        pub vis: Visibility,
        pub use_token: Token![use],
        pub leading_colon: Option<Token![::]>,
        pub tree: UseTree,
        pub semi_token: Token![;],
    }
}


impl From<DeriveInput> for Item {
    fn from(input: DeriveInput) -> Item {
        match input.data {
            Data::Struct(data) => Item::Struct(ItemStruct {
                attrs: input.attrs,
                vis: input.vis,
                struct_token: data.struct_token,
                ident: input.ident,
                generics: input.generics,
                fields: data.fields,
                semi_token: data.semi_token,
            }),
            Data::Enum(data) => Item::Enum(ItemEnum {
                attrs: input.attrs,
                vis: input.vis,
                enum_token: data.enum_token,
                ident: input.ident,
                generics: input.generics,
                brace_token: data.brace_token,
                variants: data.variants,
            }),
            Data::Union(data) => Item::Union(ItemUnion {
                attrs: input.attrs,
                vis: input.vis,
                union_token: data.union_token,
                ident: input.ident,
                generics: input.generics,
                fields: data.fields,
            }),
        }
    }
}

impl From<ItemStruct> for DeriveInput {
    fn from(input: ItemStruct) -> DeriveInput {
        DeriveInput {
            attrs: input.attrs,
            vis: input.vis,
            ident: input.ident,
            generics: input.generics,
            data: Data::Struct(DataStruct {
                struct_token: input.struct_token,
                fields: input.fields,
                semi_token: input.semi_token,
            }),
        }
    }
}

impl From<ItemEnum> for DeriveInput {
    fn from(input: ItemEnum) -> DeriveInput {
        DeriveInput {
            attrs: input.attrs,
            vis: input.vis,
            ident: input.ident,
            generics: input.generics,
            data: Data::Enum(DataEnum {
                enum_token: input.enum_token,
                brace_token: input.brace_token,
                variants: input.variants,
            }),
        }
    }
}

impl From<ItemUnion> for DeriveInput {
    fn from(input: ItemUnion) -> DeriveInput {
        DeriveInput {
            attrs: input.attrs,
            vis: input.vis,
            ident: input.ident,
            generics: input.generics,
            data: Data::Union(DataUnion {
                union_token: input.union_token,
                fields: input.fields,
            }),
        }
    }
}

ast_enum_of_structs! {
    /// A suffix of an import tree in a `use` item: `Type as Renamed` or `*`.
    ///
    /// # Syntax tree enum
    ///
    /// This type is a [syntax tree enum].
    ///
    /// [syntax tree enum]: crate::expr::Expr#syntax-tree-enums
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub enum UseTree {
        /// A path prefix of imports in a `use` item: `std::...`.
        Path(UsePath),

        /// An identifier imported by a `use` item: `HashMap`.
        Name(UseName),

        /// An renamed identifier imported by a `use` item: `HashMap as Map`.
        Rename(UseRename),

        /// A glob import in a `use` item: `*`.
        Glob(UseGlob),

        /// A braced group of imports in a `use` item: `{A, B, C}`.
        Group(UseGroup),
    }
}

ast_struct! {
    /// A path prefix of imports in a `use` item: `std::...`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct UsePath {
        pub ident: Ident,
        pub colon2_token: Token![::],
        pub tree: Box<UseTree>,
    }
}

ast_struct! {
    /// An identifier imported by a `use` item: `HashMap`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct UseName {
        pub ident: Ident,
    }
}

ast_struct! {
    /// An renamed identifier imported by a `use` item: `HashMap as Map`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct UseRename {
        pub ident: Ident,
        pub as_token: Token![as],
        pub rename: Ident,
    }
}

ast_struct! {
    /// A glob import in a `use` item: `*`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct UseGlob {
        pub star_token: Token![*],
    }
}

ast_struct! {
    /// A braced group of imports in a `use` item: `{A, B, C}`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct UseGroup {
        pub brace_token: token::Brace,
        pub items: Punctuated<UseTree, Token![,]>,
    }
}

ast_enum_of_structs! {
    /// An item within an `extern` block.
    ///
    /// # Syntax tree enum
    ///
    /// This type is a [syntax tree enum].
    ///
    /// [syntax tree enum]: crate::expr::Expr#syntax-tree-enums
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    #[non_exhaustive]
    pub enum ForeignItem {
        /// A foreign function in an `extern` block.
        Fn(ForeignItemFn),

        /// A foreign static item in an `extern` block: `static ext: u8`.
        Static(ForeignItemStatic),

        /// A foreign type in an `extern` block: `type void`.
        Type(ForeignItemType),

        /// A macro invocation within an extern block.
        Macro(ForeignItemMacro),

        /// Tokens in an `extern` block not interpreted by Syn.
        Verbatim(TokenStream),

        // For testing exhaustiveness in downstream code, use the following idiom:
        //
        //     match item {
        //         #![cfg_attr(test, deny(non_exhaustive_omitted_patterns))]
        //
        //         ForeignItem::Fn(item) => {...}
        //         ForeignItem::Static(item) => {...}
        //         ...
        //         ForeignItem::Verbatim(item) => {...}
        //
        //         _ => { /* some sane fallback */ }
        //     }
        //
        // This way we fail your tests but don't break your library when adding
        // a variant. You will be notified by a test failure when a variant is
        // added, so that you can add code to handle it, but your library will
        // continue to compile and work for downstream users in the interim.
    }
}

ast_struct! {
    /// A foreign function in an `extern` block.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct ForeignItemFn {
        pub attrs: Vec<Attribute>,
        pub vis: Visibility,
        pub sig: Signature,
        pub semi_token: Token![;],
    }
}

ast_struct! {
    /// A foreign static item in an `extern` block: `static ext: u8`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct ForeignItemStatic {
        pub attrs: Vec<Attribute>,
        pub vis: Visibility,
        pub static_token: Token![static],
        pub mutability: StaticMutability,
        pub ident: Ident,
        pub colon_token: Token![:],
        pub ty: Box<Type>,
        pub semi_token: Token![;],
    }
}

ast_struct! {
    /// A foreign type in an `extern` block: `type void`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct ForeignItemType {
        pub attrs: Vec<Attribute>,
        pub vis: Visibility,
        pub type_token: Token![type],
        pub ident: Ident,
        pub generics: Generics,
        pub semi_token: Token![;],
    }
}

ast_struct! {
    /// A macro invocation within an extern block.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct ForeignItemMacro {
        pub attrs: Vec<Attribute>,
        pub mac: Macro,
        pub semi_token: Option<Token![;]>,
    }
}

ast_enum_of_structs! {
    /// An item declaration within the definition of a trait.
    ///
    /// # Syntax tree enum
    ///
    /// This type is a [syntax tree enum].
    ///
    /// [syntax tree enum]: crate::expr::Expr#syntax-tree-enums
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    #[non_exhaustive]
    pub enum TraitItem {
        /// An associated constant within the definition of a trait.
        Const(TraitItemConst),

        /// An associated function within the definition of a trait.
        Fn(TraitItemFn),

        /// An associated type within the definition of a trait.
        Type(TraitItemType),

        /// A macro invocation within the definition of a trait.
        Macro(TraitItemMacro),

        /// Tokens within the definition of a trait not interpreted by Syn.
        Verbatim(TokenStream),

        // For testing exhaustiveness in downstream code, use the following idiom:
        //
        //     match item {
        //         #![cfg_attr(test, deny(non_exhaustive_omitted_patterns))]
        //
        //         TraitItem::Const(item) => {...}
        //         TraitItem::Fn(item) => {...}
        //         ...
        //         TraitItem::Verbatim(item) => {...}
        //
        //         _ => { /* some sane fallback */ }
        //     }
        //
        // This way we fail your tests but don't break your library when adding
        // a variant. You will be notified by a test failure when a variant is
        // added, so that you can add code to handle it, but your library will
        // continue to compile and work for downstream users in the interim.
    }
}

ast_struct! {
    /// An associated constant within the definition of a trait.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct TraitItemConst {
        pub attrs: Vec<Attribute>,
        pub const_token: Token![const],
        pub ident: Ident,
        pub generics: Generics,
        pub colon_token: Token![:],
        pub ty: Type,
        pub default: Option<(Token![=], Expr)>,
        pub semi_token: Token![;],
    }
}

ast_struct! {
    /// An associated function within the definition of a trait.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct TraitItemFn {
        pub attrs: Vec<Attribute>,
        pub sig: Signature,
        pub default: Option<Block>,
        pub semi_token: Option<Token![;]>,
    }
}

ast_struct! {
    /// An associated type within the definition of a trait.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct TraitItemType {
        pub attrs: Vec<Attribute>,
        pub type_token: Token![type],
        pub ident: Ident,
        pub generics: Generics,
        pub colon_token: Option<Token![:]>,
        pub bounds: Punctuated<TypeParamBound, Token![+]>,
        pub default: Option<(Token![=], Type)>,
        pub semi_token: Token![;],
    }
}

ast_struct! {
    /// A macro invocation within the definition of a trait.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct TraitItemMacro {
        pub attrs: Vec<Attribute>,
        pub mac: Macro,
        pub semi_token: Option<Token![;]>,
    }
}

ast_enum_of_structs! {
    /// An item within an impl block.
    ///
    /// # Syntax tree enum
    ///
    /// This type is a [syntax tree enum].
    ///
    /// [syntax tree enum]: crate::expr::Expr#syntax-tree-enums
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    #[non_exhaustive]
    pub enum ImplItem {
        /// An associated constant within an impl block.
        Const(ImplItemConst),

        /// An associated function within an impl block.
        Fn(ImplItemFn),

        /// An associated type within an impl block.
        Type(ImplItemType),

        /// A macro invocation within an impl block.
        Macro(ImplItemMacro),

        /// Tokens within an impl block not interpreted by Syn.
        Verbatim(TokenStream),

        // For testing exhaustiveness in downstream code, use the following idiom:
        //
        //     match item {
        //         #![cfg_attr(test, deny(non_exhaustive_omitted_patterns))]
        //
        //         ImplItem::Const(item) => {...}
        //         ImplItem::Fn(item) => {...}
        //         ...
        //         ImplItem::Verbatim(item) => {...}
        //
        //         _ => { /* some sane fallback */ }
        //     }
        //
        // This way we fail your tests but don't break your library when adding
        // a variant. You will be notified by a test failure when a variant is
        // added, so that you can add code to handle it, but your library will
        // continue to compile and work for downstream users in the interim.
    }
}

ast_struct! {
    /// An associated constant within an impl block.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct ImplItemConst {
        pub attrs: Vec<Attribute>,
        pub vis: Visibility,
        pub defaultness: Option<Token![default]>,
        pub const_token: Token![const],
        pub ident: Ident,
        pub generics: Generics,
        pub colon_token: Token![:],
        pub ty: Type,
        pub eq_token: Token![=],
        pub expr: Expr,
        pub semi_token: Token![;],
    }
}

ast_struct! {
    /// An associated function within an impl block.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct ImplItemFn {
        pub attrs: Vec<Attribute>,
        pub vis: Visibility,
        pub defaultness: Option<Token![default]>,
        pub sig: Signature,
        pub block: Block,
    }
}

ast_struct! {
    /// An associated type within an impl block.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct ImplItemType {
        pub attrs: Vec<Attribute>,
        pub vis: Visibility,
        pub defaultness: Option<Token![default]>,
        pub type_token: Token![type],
        pub ident: Ident,
        pub generics: Generics,
        pub eq_token: Token![=],
        pub ty: Type,
        pub semi_token: Token![;],
    }
}

ast_struct! {
    /// A macro invocation within an impl block.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct ImplItemMacro {
        pub attrs: Vec<Attribute>,
        pub mac: Macro,
        pub semi_token: Option<Token![;]>,
    }
}

ast_struct! {
    /// A function signature in a trait or implementation: `unsafe fn
    /// initialize(&self)`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct Signature {
        pub constness: Option<Token![const]>,
        pub asyncness: Option<Token![async]>,
        pub unsafety: Option<Token![unsafe]>,
        pub abi: Option<Abi>,
        pub fn_token: Token![fn],
        pub ident: Ident,
        pub generics: Generics,
        pub paren_token: token::Paren,
        pub inputs: Punctuated<FnArg, Token![,]>,
        pub variadic: Option<Variadic>,
        pub output: ReturnType,
    }
}

impl Signature {
    /// A method's `self` receiver, such as `&self` or `self: Box<Self>`.
    pub fn receiver(&self) -> Option<&Receiver> {
        let arg = self.inputs.first()?;
        match arg {
            FnArg::Receiver(receiver) => Some(receiver),
            FnArg::Typed(_) => None,
        }
    }
}

ast_enum_of_structs! {
    /// An argument in a function signature: the `n: usize` in `fn f(n: usize)`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub enum FnArg {
        /// The `self` argument of an associated method.
        Receiver(Receiver),

        /// A function argument accepted by pattern and type.
        Typed(PatType),
    }
}

ast_struct! {
    /// The `self` argument of an associated method.
    ///
    /// If `colon_token` is present, the receiver is written with an explicit
    /// type such as `self: Box<Self>`. If `colon_token` is absent, the receiver
    /// is written in shorthand such as `self` or `&self` or `&mut self`. In the
    /// shorthand case, the type in `ty` is reconstructed as one of `Self`,
    /// `&Self`, or `&mut Self`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct Receiver {
        pub attrs: Vec<Attribute>,
        pub reference: Option<(Token![&], Option<Lifetime>)>,
        pub mutability: Option<Token![mut]>,
        pub self_token: Token![self],
        pub colon_token: Option<Token![:]>,
        pub ty: Box<Type>,
    }
}

impl Receiver {
    pub fn lifetime(&self) -> Option<&Lifetime> {
        self.reference.as_ref()?.1.as_ref()
    }
}

ast_struct! {
    /// The variadic argument of a foreign function.
    ///
    /// ```rust
    /// # struct c_char;
    /// # struct c_int;
    /// #
    /// extern "C" {
    ///     fn printf(format: *const c_char, ...) -> c_int;
    ///     //                               ^^^
    /// }
    /// ```
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    pub struct Variadic {
        pub attrs: Vec<Attribute>,
        pub pat: Option<(Box<Pat>, Token![:])>,
        pub dots: Token![...],
        pub comma: Option<Token![,]>,
    }
}

ast_enum! {
    /// The mutability of an `Item::Static` or `ForeignItem::Static`.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    #[non_exhaustive]
    pub enum StaticMutability {
        Mut(Token![mut]),
        None,
    }
}

ast_enum! {
    /// Unused, but reserved for RFC 3323 restrictions.
    #[cfg_attr(docsrs, doc(cfg(feature = "full")))]
    #[non_exhaustive]
    pub enum ImplRestriction {}


    // TODO: https://rust-lang.github.io/rfcs/3323-restrictions.html
    //
    // pub struct ImplRestriction {
    //     pub impl_token: Token![impl],
    //     pub paren_token: token::Paren,
    //     pub in_token: Option<Token![in]>,
    //     pub path: Box<Path>,
    // }
}


#[cfg(feature = "printing")]
mod printing {
    use crate::attr::FilterAttrs;
    use crate::data::Fields;
    use crate::item::{
        ForeignItemFn, ForeignItemMacro, ForeignItemStatic, ForeignItemType, ImplItemConst,
        ImplItemFn, ImplItemMacro, ImplItemType, ItemConst, ItemEnum, ItemExternCrate, ItemFn,
        ItemForeignMod, ItemImpl, ItemMacro, ItemMod, ItemStatic, ItemStruct, ItemTrait,
        ItemTraitAlias, ItemType, ItemUnion, ItemUse, Receiver, Signature, StaticMutability,
        TraitItemConst, TraitItemFn, TraitItemMacro, TraitItemType, UseGlob, UseGroup, UseName,
        UsePath, UseRename, Variadic,
    };
    use crate::mac::MacroDelimiter;
    use crate::print::TokensOrDefault;
    use crate::ty::Type;
    use proc_macro2::TokenStream;
    use quote::{ToTokens, TokenStreamExt};

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ItemExternCrate {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.append_all(self.attrs.outer());
            self.vis.to_tokens(tokens);
            self.extern_token.to_tokens(tokens);
            self.crate_token.to_tokens(tokens);
            self.ident.to_tokens(tokens);
            if let Some((as_token, rename)) = &self.rename {
                as_token.to_tokens(tokens);
                rename.to_tokens(tokens);
            }
            self.semi_token.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ItemUse {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.append_all(self.attrs.outer());
            self.vis.to_tokens(tokens);
            self.use_token.to_tokens(tokens);
            self.leading_colon.to_tokens(tokens);
            self.tree.to_tokens(tokens);
            self.semi_token.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ItemStatic {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.append_all(self.attrs.outer());
            self.vis.to_tokens(tokens);
            self.static_token.to_tokens(tokens);
            self.mutability.to_tokens(tokens);
            self.ident.to_tokens(tokens);
            self.colon_token.to_tokens(tokens);
            self.ty.to_tokens(tokens);
            self.eq_token.to_tokens(tokens);
            self.expr.to_tokens(tokens);
            self.semi_token.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ItemConst {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.append_all(self.attrs.outer());
            self.vis.to_tokens(tokens);
            self.const_token.to_tokens(tokens);
            self.ident.to_tokens(tokens);
            self.colon_token.to_tokens(tokens);
            self.ty.to_tokens(tokens);
            self.eq_token.to_tokens(tokens);
            self.expr.to_tokens(tokens);
            self.semi_token.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ItemFn {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.append_all(self.attrs.outer());
            self.vis.to_tokens(tokens);
            self.sig.to_tokens(tokens);
            self.block.brace_token.surround(tokens, |tokens| {
                tokens.append_all(self.attrs.inner());
                tokens.append_all(&self.block.stmts);
            });
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ItemMod {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.append_all(self.attrs.outer());
            self.vis.to_tokens(tokens);
            self.unsafety.to_tokens(tokens);
            self.mod_token.to_tokens(tokens);
            self.ident.to_tokens(tokens);
            if let Some((brace, items)) = &self.content {
                brace.surround(tokens, |tokens| {
                    tokens.append_all(self.attrs.inner());
                    tokens.append_all(items);
                });
            } else {
                TokensOrDefault(&self.semi).to_tokens(tokens);
            }
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ItemForeignMod {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.append_all(self.attrs.outer());
            self.unsafety.to_tokens(tokens);
            self.abi.to_tokens(tokens);
            self.brace_token.surround(tokens, |tokens| {
                tokens.append_all(self.attrs.inner());
                tokens.append_all(&self.items);
            });
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ItemType {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.append_all(self.attrs.outer());
            self.vis.to_tokens(tokens);
            self.type_token.to_tokens(tokens);
            self.ident.to_tokens(tokens);
            self.generics.to_tokens(tokens);
            self.generics.where_clause.to_tokens(tokens);
            self.eq_token.to_tokens(tokens);
            self.ty.to_tokens(tokens);
            self.semi_token.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ItemEnum {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.append_all(self.attrs.outer());
            self.vis.to_tokens(tokens);
            self.enum_token.to_tokens(tokens);
            self.ident.to_tokens(tokens);
            self.generics.to_tokens(tokens);
            self.generics.where_clause.to_tokens(tokens);
            self.brace_token.surround(tokens, |tokens| {
                self.variants.to_tokens(tokens);
            });
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ItemStruct {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.append_all(self.attrs.outer());
            self.vis.to_tokens(tokens);
            self.struct_token.to_tokens(tokens);
            self.ident.to_tokens(tokens);
            self.generics.to_tokens(tokens);
            match &self.fields {
                Fields::Named(fields) => {
                    self.generics.where_clause.to_tokens(tokens);
                    fields.to_tokens(tokens);
                }
                Fields::Unnamed(fields) => {
                    fields.to_tokens(tokens);
                    self.generics.where_clause.to_tokens(tokens);
                    TokensOrDefault(&self.semi_token).to_tokens(tokens);
                }
                Fields::Unit => {
                    self.generics.where_clause.to_tokens(tokens);
                    TokensOrDefault(&self.semi_token).to_tokens(tokens);
                }
            }
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ItemUnion {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.append_all(self.attrs.outer());
            self.vis.to_tokens(tokens);
            self.union_token.to_tokens(tokens);
            self.ident.to_tokens(tokens);
            self.generics.to_tokens(tokens);
            self.generics.where_clause.to_tokens(tokens);
            self.fields.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ItemTrait {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.append_all(self.attrs.outer());
            self.vis.to_tokens(tokens);
            self.unsafety.to_tokens(tokens);
            self.auto_token.to_tokens(tokens);
            self.trait_token.to_tokens(tokens);
            self.ident.to_tokens(tokens);
            self.generics.to_tokens(tokens);
            if !self.supertraits.is_empty() {
                TokensOrDefault(&self.colon_token).to_tokens(tokens);
                self.supertraits.to_tokens(tokens);
            }
            self.generics.where_clause.to_tokens(tokens);
            self.brace_token.surround(tokens, |tokens| {
                tokens.append_all(self.attrs.inner());
                tokens.append_all(&self.items);
            });
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ItemTraitAlias {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.append_all(self.attrs.outer());
            self.vis.to_tokens(tokens);
            self.trait_token.to_tokens(tokens);
            self.ident.to_tokens(tokens);
            self.generics.to_tokens(tokens);
            self.eq_token.to_tokens(tokens);
            self.bounds.to_tokens(tokens);
            self.generics.where_clause.to_tokens(tokens);
            self.semi_token.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ItemImpl {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.append_all(self.attrs.outer());
            self.defaultness.to_tokens(tokens);
            self.unsafety.to_tokens(tokens);
            self.impl_token.to_tokens(tokens);
            self.generics.to_tokens(tokens);
            if let Some((polarity, path, for_token)) = &self.trait_ {
                polarity.to_tokens(tokens);
                path.to_tokens(tokens);
                for_token.to_tokens(tokens);
            }
            self.self_ty.to_tokens(tokens);
            self.generics.where_clause.to_tokens(tokens);
            self.brace_token.surround(tokens, |tokens| {
                tokens.append_all(self.attrs.inner());
                tokens.append_all(&self.items);
            });
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ItemMacro {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.append_all(self.attrs.outer());
            self.mac.path.to_tokens(tokens);
            self.mac.bang_token.to_tokens(tokens);
            self.ident.to_tokens(tokens);
            match &self.mac.delimiter {
                MacroDelimiter::Paren(paren) => {
                    paren.surround(tokens, |tokens| self.mac.tokens.to_tokens(tokens));
                }
                MacroDelimiter::Brace(brace) => {
                    brace.surround(tokens, |tokens| self.mac.tokens.to_tokens(tokens));
                }
                MacroDelimiter::Bracket(bracket) => {
                    bracket.surround(tokens, |tokens| self.mac.tokens.to_tokens(tokens));
                }
            }
            self.semi_token.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for UsePath {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.ident.to_tokens(tokens);
            self.colon2_token.to_tokens(tokens);
            self.tree.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for UseName {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.ident.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for UseRename {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.ident.to_tokens(tokens);
            self.as_token.to_tokens(tokens);
            self.rename.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for UseGlob {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.star_token.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for UseGroup {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.brace_token.surround(tokens, |tokens| {
                self.items.to_tokens(tokens);
            });
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for TraitItemConst {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.append_all(self.attrs.outer());
            self.const_token.to_tokens(tokens);
            self.ident.to_tokens(tokens);
            self.colon_token.to_tokens(tokens);
            self.ty.to_tokens(tokens);
            if let Some((eq_token, default)) = &self.default {
                eq_token.to_tokens(tokens);
                default.to_tokens(tokens);
            }
            self.semi_token.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for TraitItemFn {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.append_all(self.attrs.outer());
            self.sig.to_tokens(tokens);
            match &self.default {
                Some(block) => {
                    block.brace_token.surround(tokens, |tokens| {
                        tokens.append_all(self.attrs.inner());
                        tokens.append_all(&block.stmts);
                    });
                }
                None => {
                    TokensOrDefault(&self.semi_token).to_tokens(tokens);
                }
            }
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for TraitItemType {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.append_all(self.attrs.outer());
            self.type_token.to_tokens(tokens);
            self.ident.to_tokens(tokens);
            self.generics.to_tokens(tokens);
            if !self.bounds.is_empty() {
                TokensOrDefault(&self.colon_token).to_tokens(tokens);
                self.bounds.to_tokens(tokens);
            }
            if let Some((eq_token, default)) = &self.default {
                eq_token.to_tokens(tokens);
                default.to_tokens(tokens);
            }
            self.generics.where_clause.to_tokens(tokens);
            self.semi_token.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for TraitItemMacro {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.append_all(self.attrs.outer());
            self.mac.to_tokens(tokens);
            self.semi_token.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ImplItemConst {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.append_all(self.attrs.outer());
            self.vis.to_tokens(tokens);
            self.defaultness.to_tokens(tokens);
            self.const_token.to_tokens(tokens);
            self.ident.to_tokens(tokens);
            self.colon_token.to_tokens(tokens);
            self.ty.to_tokens(tokens);
            self.eq_token.to_tokens(tokens);
            self.expr.to_tokens(tokens);
            self.semi_token.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ImplItemFn {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.append_all(self.attrs.outer());
            self.vis.to_tokens(tokens);
            self.defaultness.to_tokens(tokens);
            self.sig.to_tokens(tokens);
            self.block.brace_token.surround(tokens, |tokens| {
                tokens.append_all(self.attrs.inner());
                tokens.append_all(&self.block.stmts);
            });
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ImplItemType {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.append_all(self.attrs.outer());
            self.vis.to_tokens(tokens);
            self.defaultness.to_tokens(tokens);
            self.type_token.to_tokens(tokens);
            self.ident.to_tokens(tokens);
            self.generics.to_tokens(tokens);
            self.eq_token.to_tokens(tokens);
            self.ty.to_tokens(tokens);
            self.generics.where_clause.to_tokens(tokens);
            self.semi_token.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ImplItemMacro {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.append_all(self.attrs.outer());
            self.mac.to_tokens(tokens);
            self.semi_token.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ForeignItemFn {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.append_all(self.attrs.outer());
            self.vis.to_tokens(tokens);
            self.sig.to_tokens(tokens);
            self.semi_token.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ForeignItemStatic {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.append_all(self.attrs.outer());
            self.vis.to_tokens(tokens);
            self.static_token.to_tokens(tokens);
            self.mutability.to_tokens(tokens);
            self.ident.to_tokens(tokens);
            self.colon_token.to_tokens(tokens);
            self.ty.to_tokens(tokens);
            self.semi_token.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ForeignItemType {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.append_all(self.attrs.outer());
            self.vis.to_tokens(tokens);
            self.type_token.to_tokens(tokens);
            self.ident.to_tokens(tokens);
            self.generics.to_tokens(tokens);
            self.generics.where_clause.to_tokens(tokens);
            self.semi_token.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for ForeignItemMacro {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.append_all(self.attrs.outer());
            self.mac.to_tokens(tokens);
            self.semi_token.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for Signature {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            self.constness.to_tokens(tokens);
            self.asyncness.to_tokens(tokens);
            self.unsafety.to_tokens(tokens);
            self.abi.to_tokens(tokens);
            self.fn_token.to_tokens(tokens);
            self.ident.to_tokens(tokens);
            self.generics.to_tokens(tokens);
            self.paren_token.surround(tokens, |tokens| {
                self.inputs.to_tokens(tokens);
                if let Some(variadic) = &self.variadic {
                    if !self.inputs.empty_or_trailing() {
                        <Token![,]>::default().to_tokens(tokens);
                    }
                    variadic.to_tokens(tokens);
                }
            });
            self.output.to_tokens(tokens);
            self.generics.where_clause.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for Receiver {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.append_all(self.attrs.outer());
            if let Some((ampersand, lifetime)) = &self.reference {
                ampersand.to_tokens(tokens);
                lifetime.to_tokens(tokens);
            }
            self.mutability.to_tokens(tokens);
            self.self_token.to_tokens(tokens);
            if let Some(colon_token) = &self.colon_token {
                colon_token.to_tokens(tokens);
                self.ty.to_tokens(tokens);
            } else {
                let consistent = match (&self.reference, &self.mutability, &*self.ty) {
                    (Some(_), mutability, Type::Reference(ty)) => {
                        mutability.is_some() == ty.mutability.is_some()
                            && match &*ty.elem {
                                Type::Path(ty) => ty.qself.is_none() && ty.path.is_ident("Self"),
                                _ => false,
                            }
                    }
                    (None, _, Type::Path(ty)) => ty.qself.is_none() && ty.path.is_ident("Self"),
                    _ => false,
                };
                if !consistent {
                    <Token![:]>::default().to_tokens(tokens);
                    self.ty.to_tokens(tokens);
                }
            }
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for Variadic {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            tokens.append_all(self.attrs.outer());
            if let Some((pat, colon)) = &self.pat {
                pat.to_tokens(tokens);
                colon.to_tokens(tokens);
            }
            self.dots.to_tokens(tokens);
            self.comma.to_tokens(tokens);
        }
    }

    #[cfg_attr(docsrs, doc(cfg(feature = "printing")))]
    impl ToTokens for StaticMutability {
        fn to_tokens(&self, tokens: &mut TokenStream) {
            match self {
                StaticMutability::None => {}
                StaticMutability::Mut(mut_token) => mut_token.to_tokens(tokens),
            }
        }
    }
}
