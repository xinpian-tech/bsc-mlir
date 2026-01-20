//! Type system for the BSC Rust frontend.
//!
//! This crate provides the core type system infrastructure:
//! - `ty` - Type and Kind representations (mirrors CType.hs)
//! - `subst` - Type substitution (mirrors Subst.hs)
//! - `unify` - Unification algorithm (mirrors Unify.hs)
//!
//! # Design Principles
//!
//! - **No silent failures**: All errors are explicit with Result types
//! - **Minimal lifetime scope**: Prefers owned data over complex lifetimes
//! - **Mirrors Haskell**: Closely follows the original BSC Haskell implementation
//!
//! # Type System Overview
//!
//! The BSC type system includes:
//! - Value types (kind `*`): `Bool`, `Int#32`, etc.
//! - Numeric types (kind `#`): `32`, `64`, `Add#32#32`, etc.
//! - String types (kind `$`): `"hello"`, etc.
//! - Type constructors: `Bit`, `Vector`, etc.
//! - Type variables: `a`, `n`, etc.
//!
//! # Example
//!
//! ```rust
//! use bsc_types::{Type, TyVar, TyCon, Kind, Substitution, Types};
//! use bsc_syntax::Id;
//! use bsc_diagnostics::Position;
//!
//! // Create a type variable 'a' with kind *
//! let var_a = TyVar::new(Id::unpositioned("a"), Kind::Star);
//! let ty_a = Type::var(var_a.clone());
//!
//! // Create a numeric type literal 32
//! let ty_32 = Type::num(32, Position::unknown());
//!
//! // Create a substitution [a := Int]
//! let ty_int = Type::con(TyCon::abstract_type(
//!     Id::unpositioned("Int"),
//!     Kind::Star
//! ));
//! let subst = Substitution::singleton(var_a, ty_int.clone());
//!
//! // Apply the substitution
//! let result = ty_a.apply_subst(&subst);
//! assert_eq!(result, ty_int);
//! ```

pub mod subst;
pub mod ty;
pub mod unify;

// Re-export main types
pub use subst::{Substitution, Types};
pub use ty::{Kind, Pred, QualType, StructSubType, TyCon, TyConSort, TyVar, Type, Typeclass};
pub use unify::{match_type, match_types, unify, Unify, UnifyError, UnifyResult};
