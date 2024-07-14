#[doc(hidden)]
pub use std::clone::Clone;
#[doc(hidden)]
pub use std::cmp::{Eq, PartialEq};
#[doc(hidden)]
pub use std::concat;
#[doc(hidden)]
pub use std::default::Default;
#[doc(hidden)]
pub use std::fmt::Debug;
#[doc(hidden)]
pub use std::hash::{Hash, Hasher};
#[doc(hidden)]
pub use std::marker::Copy;
#[doc(hidden)]
pub use std::option::Option::{None, Some};
#[doc(hidden)]
pub use std::result::Result::{Err, Ok};
#[doc(hidden)]
pub use std::stringify;

#[doc(hidden)]
pub type Formatter<'a> = std::fmt::Formatter<'a>;
#[doc(hidden)]
pub type FmtResult = std::fmt::Result;

#[doc(hidden)]
pub type bool = std::primitive::bool;
#[doc(hidden)]
pub type str = std::primitive::str;

#[doc(hidden)]
pub type Span = proc_macro2::Span;
#[doc(hidden)]
pub type TokenStream2 = proc_macro2::TokenStream;

#[doc(hidden)]
pub use crate::span::IntoSpans;

#[cfg(feature = "proc-macro")]
#[doc(hidden)]
pub type TokenStream = proc_macro::TokenStream;

#[cfg(feature = "printing")]
#[doc(hidden)]
pub use quote::{ToTokens, TokenStreamExt};

#[doc(hidden)]
pub struct private(pub(crate) ());
