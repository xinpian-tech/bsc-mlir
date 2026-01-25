//! Type checking for the BSC Rust frontend.
//!
//! This crate provides type inference and checking for BSC, mirroring the
//! Haskell implementation in `src/comp/TCheck.hs` and `src/comp/TIMonad.hs`.
//!
//! # Architecture
//!
//! The type checker uses Hindley-Milner type inference with extensions for:
//! - Type classes (similar to Haskell)
//! - Numeric types and type-level arithmetic
//! - Qualified types with predicates
//!
//! # Main Entry Points
//!
//! - [`infer_expr`] - Infer the type of an expression
//! - [`check_defn`] - Type check a top-level definition
//! - [`TypeCheckContext`] - The type checking monad/context
//!
//! # Example
//!
//! ```ignore
//! use bsc_typecheck::{TypeCheckContext, infer_expr};
//! use bsc_symtab::SymTab;
//!
//! let mut ctx = TypeCheckContext::new();
//! let env = SymTab::new();
//! let ty = infer_expr(&mut ctx, &env, &expr)?;
//! ```

pub mod context;
pub mod infer;

pub use context::TypeCheckContext;
pub use infer::{check_defn, infer_expr};

