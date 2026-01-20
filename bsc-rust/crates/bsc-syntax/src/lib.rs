//! Core AST types for the BSC Rust frontend.
//!
//! This crate provides:
//! - `CSyntax` - Concrete syntax AST (parser output)
//! - `ISyntax` - Internal syntax AST (type-checked, for backends)
//! - `VModInfo` - Verilog module information types
//! - Common types like identifiers and literals

pub mod csyntax;
pub mod csyntax_display;
pub mod id;
pub mod isyntax;
pub mod literal;
pub mod vmodinfo;
pub mod vmodinfo_display;

pub use csyntax::*;
pub use id::{Id, Qualifier};
pub use isyntax::*;
pub use literal::{IntLiteral, Literal};
pub use vmodinfo::*;
