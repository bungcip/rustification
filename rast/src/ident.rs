// #[cfg(feature = "parsing")]
// use crate::lookahead;

pub use proc_macro2::Ident;

// #[cfg(feature = "parsing")]
// pub_if_not_doc! {
//     #[doc(hidden)]
//     #[allow(non_snake_case)]
//     pub fn Ident(marker: lookahead::TokenMarker) -> Ident {
//         match marker {}
//     }
// }

macro_rules! ident_from_token {
    ($token:ident) => {
        impl From<Token![$token]> for Ident {
            fn from(token: Token![$token]) -> Ident {
                Ident::new(stringify!($token), token.span)
            }
        }
    };
}

ident_from_token!(self);
ident_from_token!(Self);
ident_from_token!(super);
ident_from_token!(crate);
ident_from_token!(extern);

impl From<Token![_]> for Ident {
    fn from(token: Token![_]) -> Ident {
        Ident::new("_", token.span)
    }
}

pub(crate) fn xid_ok(symbol: &str) -> bool {
    let mut chars = symbol.chars();
    let first = chars.next().unwrap();
    if !(first == '_' || unicode_ident::is_xid_start(first)) {
        return false;
    }
    for ch in chars {
        if !unicode_ident::is_xid_continue(ch) {
            return false;
        }
    }
    true
}

