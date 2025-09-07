//! A crate for building Rust AST nodes.
//!
//! This crate provides a `Builder` struct that can be used to create Rust AST
//! nodes in a more convenient way than by constructing them directly.

mod builder;
pub use crate::builder::{Builder, Make, mk, properties};
