//! Type and Kind representations for BSC.
//!
//! Mirrors `src/comp/CType.hs` from the Haskell implementation.
//!
//! This module provides the core type system representations:
//! - `Type` - The type representation (TVar, TCon, TAp, TGen, TDefMonad)
//! - `TyVar` - Type variables with name, number, and kind
//! - `TyCon` - Type constructors (named, numeric literals, string literals)
//! - `Kind` - Kinds for classifying types (* for values, # for numbers, $ for strings)
//! - `PartialKind` - Partial kind information during inference
//!
//! # Type System Constants
//!
//! - `BASE_KVAR`: Starting number for generated kind variables (1000)
//! - `NO_TYVAR_NUM`: Indicates a user-defined (non-generated) type variable (-1)
//! - `NO_TYPE`: A placeholder "no type" value
//!
//! # Integer Representation
//!
//! Haskell's `Integer` type is unbounded. To maintain 1-to-1 behavioral compatibility,
//! we use `num_bigint::BigInt` for type-level numeric literals and type synonym arities.
//! Haskell's `Int` type (at least 30 bits) is represented as `i64` in Rust for safety.

use bsc_diagnostics::Position;
use bsc_syntax::{Id, IfcPragma};
use num_bigint::BigInt;
use num_traits::{ToPrimitive, Zero};
use smol_str::SmolStr;
use std::fmt;

// ============================================================================
// Constants
// ============================================================================

/// Base value for generated kind variables.
///
/// Kind variables generated during kind inference start numbering from this value.
/// Mirrors `baseKVar = 1000` from CType.hs:532.
pub const BASE_KVAR: i64 = 1000;

/// Kind of a type - classifies types by their "type".
///
/// Mirrors Haskell's `Kind` from CType.hs:141-147:
/// ```haskell
/// data Kind = KStar | KNum | KStr | Kfun Kind Kind | KVar Int
/// ```
///
/// - KStar: kind of value types (*)
/// - KNum: kind of numeric types (#)
/// - KStr: kind of string types ($)
/// - Kfun: kind of type constructors (k1 -> k2)
/// - KVar: kind variable (used during kind inference)
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Kind {
    /// `KStar` - Kind of value types (written as * in Haskell)
    Star,
    /// `KNum` - Kind of numeric types (written as # in Haskell)
    Num,
    /// `KStr` - Kind of string types (written as $ in Haskell)
    Str,
    /// `Kfun Kind Kind` - Kind of type constructors: means k1 -> k2
    Fun(Box<Kind>, Box<Kind>),
    /// `KVar Int` - Kind variable (used during kind inference)
    /// Uses i64 to match Haskell Int semantics (at least 30 bits).
    Var(i64),
}

impl Kind {
    /// Create a function kind (k1 -> k2).
    #[must_use]
    pub fn fun(arg: Kind, result: Kind) -> Self {
        Kind::Fun(Box::new(arg), Box::new(result))
    }

    /// Check if this is a kind variable.
    #[must_use]
    pub fn is_var(&self) -> bool {
        matches!(self, Kind::Var(_))
    }

    /// Get the argument kinds of a function kind.
    ///
    /// For `k1 -> k2 -> k3`, returns `[k1, k2]`.
    #[must_use]
    pub fn arg_kinds(&self) -> Vec<&Kind> {
        let mut result = Vec::new();
        let mut k = self;
        while let Kind::Fun(arg, res) = k {
            result.push(arg.as_ref());
            k = res.as_ref();
        }
        result
    }

    /// Get the result kind of a (possibly nested) function kind.
    ///
    /// For `k1 -> k2 -> k3`, returns `k3`.
    #[must_use]
    pub fn result_kind(&self) -> &Kind {
        let mut k = self;
        while let Kind::Fun(_, res) = k {
            k = res.as_ref();
        }
        k
    }
}

impl fmt::Display for Kind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Kind::Star => write!(f, "*"),
            Kind::Num => write!(f, "#"),
            Kind::Str => write!(f, "$"),
            Kind::Fun(arg, res) => {
                // Add parens around left side if it's also a function
                match arg.as_ref() {
                    Kind::Fun(_, _) => write!(f, "({arg}) -> {res}"),
                    _ => write!(f, "{arg} -> {res}"),
                }
            }
            Kind::Var(n) => {
                // Display kind variables with letters like the Haskell version (showKVar in CType.hs:540-552)
                if *n >= BASE_KVAR {
                    let v = n - BASE_KVAR;
                    let mut chars = Vec::new();
                    let mut val = v;
                    loop {
                        let digit = (val % 26) as u32;
                        chars.push(char::from_u32(digit + 97).unwrap_or('?'));
                        val /= 26;
                        if val == 0 {
                            break;
                        }
                    }
                    chars.reverse();
                    let s: String = chars.into_iter().collect();
                    write!(f, "{s}")
                } else {
                    write!(f, "{n}")
                }
            }
        }
    }
}

// ============================================================================
// PartialKind - Partial Kind Information
// ============================================================================

/// Partial kind information used during kind inference.
///
/// Mirrors `PartialKind` from CType.hs. This represents incomplete kind information
/// that may be refined during kind inference. It's used for user-provided kind
/// annotations that may not fully specify the kind.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PartialKind {
    /// No kind information available
    NoInfo,
    /// Star kind (*)
    Star,
    /// Numeric kind (#)
    Num,
    /// String kind ($)
    Str,
    /// Function kind
    Fun(Box<PartialKind>, Box<PartialKind>),
}

impl PartialKind {
    /// Create a function partial kind.
    #[must_use]
    pub fn fun(arg: PartialKind, result: PartialKind) -> Self {
        PartialKind::Fun(Box::new(arg), Box::new(result))
    }

    /// Check if this is NoInfo (completely unknown).
    #[must_use]
    pub fn is_no_info(&self) -> bool {
        matches!(self, PartialKind::NoInfo)
    }

    /// Convert to a full Kind, if fully specified.
    ///
    /// Returns None if this PartialKind contains NoInfo anywhere.
    #[must_use]
    pub fn to_kind(&self) -> Option<Kind> {
        match self {
            PartialKind::NoInfo => None,
            PartialKind::Star => Some(Kind::Star),
            PartialKind::Num => Some(Kind::Num),
            PartialKind::Str => Some(Kind::Str),
            PartialKind::Fun(arg, res) => {
                let arg_k = arg.to_kind()?;
                let res_k = res.to_kind()?;
                Some(Kind::fun(arg_k, res_k))
            }
        }
    }

    /// Convert from a Kind to a PartialKind.
    #[must_use]
    pub fn from_kind(kind: &Kind) -> Self {
        match kind {
            Kind::Star => PartialKind::Star,
            Kind::Num => PartialKind::Num,
            Kind::Str => PartialKind::Str,
            Kind::Fun(arg, res) => {
                PartialKind::fun(Self::from_kind(arg), Self::from_kind(res))
            }
            Kind::Var(_) => PartialKind::NoInfo,
        }
    }
}

impl fmt::Display for PartialKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PartialKind::NoInfo => write!(f, "?"),
            PartialKind::Star => write!(f, "*"),
            PartialKind::Num => write!(f, "#"),
            PartialKind::Str => write!(f, "$"),
            PartialKind::Fun(arg, res) => {
                match arg.as_ref() {
                    PartialKind::Fun(_, _) => write!(f, "({arg}) -> {res}"),
                    _ => write!(f, "{arg} -> {res}"),
                }
            }
        }
    }
}

impl Default for PartialKind {
    fn default() -> Self {
        PartialKind::NoInfo
    }
}

/// The sort of a type constructor - what purpose does it serve?
///
/// Mirrors `TISort` from CType.hs:113-123:
/// ```haskell
/// data TISort
///     = TItype Integer Type           -- type synonym with arity
///     | TIdata { tidata_cons :: [Id], tidata_enum :: Bool }
///     | TIstruct StructSubType [Id]
///     | TIabstract
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TyConSort {
    /// `TItype Integer Type` - Type synonym with arity and expanded type.
    /// The Integer (arity) is unbounded in Haskell, so we use BigInt.
    TypeSyn {
        /// Number of arguments the synonym takes (Haskell Integer → BigInt)
        arity: BigInt,
        /// The expanded type
        expansion: Box<Type>,
    },
    /// `TIdata [Id] Bool` - Data type with constructors
    Data {
        /// Constructor names
        constructors: Vec<Id>,
        /// Is this an enum (all constructors have no arguments)?
        is_enum: bool,
    },
    /// `TIstruct StructSubType [Id]` - Struct type
    Struct {
        /// Sub-type classification
        sub_type: StructSubType,
        /// Field names
        fields: Vec<Id>,
    },
    /// `TIabstract` - Primitive abstract type (Integer, Bit, Module, etc.)
    Abstract,
}

/// Sub-classification for struct types.
///
/// Mirrors StructSubType from CType.hs.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum StructSubType {
    /// Plain struct
    Struct,
    /// Type class
    Class,
    /// Data constructor
    DataCon {
        /// Data constructor name
        id: Id,
        /// Whether fields are named
        named_fields: bool,
    },
    /// Interface type
    ///
    /// Mirrors `SInterface [IfcPragma]` from CType.hs:132.
    Interface(Vec<IfcPragma>),
    /// Polymorphic wrapper
    PolyWrap {
        /// Name of the type with the wrapped field
        id: Id,
        /// Name of the data constructor (if any)
        constructor: Option<Id>,
        /// Name of the wrapped field
        field: Id,
    },
}

/// A type variable.
///
/// Mirrors `TyVar` from CType.hs:90-93:
/// ```haskell
/// data TyVar = TyVar { tv_name :: Id, tv_num :: Int, tv_kind :: Kind }
/// ```
///
/// - name: identifier for the variable
/// - num: number for generated type variables (-1 for user-defined)
/// - kind: the kind of the type variable
#[derive(Debug, Clone)]
pub struct TyVar {
    /// `tv_name` - Name of the type variable
    pub name: Id,
    /// `tv_num` - Number for generated type variables (-1 for user-defined)
    /// Uses i64 to match Haskell Int semantics (at least 30 bits).
    pub num: i64,
    /// `tv_kind` - Kind of the type variable
    pub kind: Kind,
}

/// Value indicating a non-generated (user-defined) type variable.
///
/// Mirrors `noTyVarNo = -1` from CType.hs:326.
pub const NO_TYVAR_NUM: i64 = -1;

impl TyVar {
    /// Create a new type variable with a specific kind.
    #[must_use]
    pub fn new(name: Id, kind: Kind) -> Self {
        Self {
            name,
            num: NO_TYVAR_NUM,
            kind,
        }
    }

    /// Create a new generated type variable with a number.
    #[must_use]
    pub fn generated(name: Id, num: i64, kind: Kind) -> Self {
        Self { name, num, kind }
    }

    /// Check if this is a generated (compiler-created) type variable.
    #[must_use]
    pub fn is_generated(&self) -> bool {
        self.num != NO_TYVAR_NUM
    }

    /// Get the position of this type variable.
    #[must_use]
    pub fn position(&self) -> Position {
        self.name.position()
    }
}

// Equality for TyVar ignores kind (matches Haskell implementation)
impl PartialEq for TyVar {
    fn eq(&self, other: &Self) -> bool {
        self.num == other.num && self.name == other.name
    }
}

impl Eq for TyVar {}

impl std::hash::Hash for TyVar {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.num.hash(state);
        self.name.hash(state);
    }
}

impl PartialOrd for TyVar {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for TyVar {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (&self.num, &self.name).cmp(&(&other.num, &other.name))
    }
}

impl fmt::Display for TyVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

/// A type constructor.
///
/// Mirrors `TyCon` from CType.hs:98-111:
/// ```haskell
/// data TyCon = TyCon { tcon_name :: Id, tcon_kind :: Maybe Kind, tcon_sort :: TISort }
///            | TyNum { tynum_value :: Integer, tynum_pos :: Position }
///            | TyStr { tystr_value :: FString, tystr_pos :: Position }
/// ```
///
/// - Named: a named type constructor with optional kind and sort
/// - TyNum: a type-level numeric literal (uses BigInt for unbounded Integer)
/// - TyStr: a type-level string literal
#[derive(Debug, Clone)]
pub enum TyCon {
    /// `TyCon { name, kind, sort }` - A named type constructor
    Named {
        /// `tcon_name` - Name of the type constructor
        name: Id,
        /// `tcon_kind` - Kind of the type constructor (None if not yet inferred)
        kind: Option<Kind>,
        /// `tcon_sort` - Purpose/sort of the type constructor
        sort: TyConSort,
    },
    /// `TyNum { tynum_value :: Integer, tynum_pos :: Position }` - Type-level numeric literal
    /// Uses BigInt to match Haskell's unbounded Integer type.
    TyNum {
        /// `tynum_value` - The numeric value (unbounded, using BigInt)
        value: BigInt,
        /// `tynum_pos` - Position where it was introduced
        position: Position,
    },
    /// `TyStr { tystr_value :: FString, tystr_pos :: Position }` - Type-level string literal
    TyStr {
        /// `tystr_value` - The string value (interned via SmolStr)
        value: SmolStr,
        /// `tystr_pos` - Position where it was introduced
        position: Position,
    },
}

impl TyCon {
    /// Create a new named type constructor.
    #[must_use]
    pub fn named(name: Id, kind: Option<Kind>, sort: TyConSort) -> Self {
        TyCon::Named { name, kind, sort }
    }

    /// Create a new abstract type constructor with a kind.
    #[must_use]
    pub fn abstract_type(name: Id, kind: Kind) -> Self {
        TyCon::Named {
            name,
            kind: Some(kind),
            sort: TyConSort::Abstract,
        }
    }

    /// Create a new numeric type literal from a BigInt.
    #[must_use]
    pub fn num(value: BigInt, position: Position) -> Self {
        TyCon::TyNum { value, position }
    }

    /// Create a new numeric type literal from an i64.
    #[must_use]
    pub fn num_i64(value: i64, position: Position) -> Self {
        TyCon::TyNum {
            value: BigInt::from(value),
            position,
        }
    }

    /// Create a new numeric type literal from an i128 (convenience method).
    #[must_use]
    pub fn num_i128(value: i128, position: Position) -> Self {
        TyCon::TyNum {
            value: BigInt::from(value),
            position,
        }
    }

    /// Create a new string type literal.
    #[must_use]
    pub fn string(value: impl Into<SmolStr>, position: Position) -> Self {
        TyCon::TyStr {
            value: value.into(),
            position,
        }
    }

    /// Get the kind of this type constructor.
    #[must_use]
    pub fn kind(&self) -> Option<&Kind> {
        match self {
            TyCon::Named { kind, .. } => kind.as_ref(),
            TyCon::TyNum { .. } => Some(&Kind::Num),
            TyCon::TyStr { .. } => Some(&Kind::Str),
        }
    }

    /// Get the name of this type constructor, if it has one.
    #[must_use]
    pub fn name(&self) -> Option<&Id> {
        match self {
            TyCon::Named { name, .. } => Some(name),
            TyCon::TyNum { .. } | TyCon::TyStr { .. } => None,
        }
    }

    /// Get the position of this type constructor.
    #[must_use]
    pub fn position(&self) -> Position {
        match self {
            TyCon::Named { name, .. } => name.position(),
            TyCon::TyNum { position, .. } | TyCon::TyStr { position, .. } => position.clone(),
        }
    }

    /// Check if this is a numeric type literal.
    #[must_use]
    pub fn is_num(&self) -> bool {
        matches!(self, TyCon::TyNum { .. })
    }

    /// Check if this is a string type literal.
    #[must_use]
    pub fn is_str(&self) -> bool {
        matches!(self, TyCon::TyStr { .. })
    }

    /// Qualified equality for type constructors.
    ///
    /// If either type constructor is unqualified (has no module path),
    /// only the base name is compared. Otherwise, both the qualifier
    /// and name must match.
    ///
    /// Mirrors `qualEq` behavior from Haskell BSC.
    #[must_use]
    pub fn qual_eq(&self, other: &TyCon) -> bool {
        match (self, other) {
            (
                TyCon::Named { name: n1, .. },
                TyCon::Named { name: n2, .. },
            ) => n1.qual_eq(n2),
            (TyCon::TyNum { value: v1, .. }, TyCon::TyNum { value: v2, .. }) => v1 == v2,
            (TyCon::TyStr { value: v1, .. }, TyCon::TyStr { value: v2, .. }) => v1 == v2,
            _ => false,
        }
    }
}

// Custom equality: for Named, compare by name and kind; for literals, compare values
impl PartialEq for TyCon {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (
                TyCon::Named {
                    name: n1,
                    kind: k1,
                    ..
                },
                TyCon::Named {
                    name: n2,
                    kind: k2,
                    ..
                },
            ) => n1 == n2 && k1 == k2,
            (TyCon::TyNum { value: v1, .. }, TyCon::TyNum { value: v2, .. }) => v1 == v2,
            (TyCon::TyStr { value: v1, .. }, TyCon::TyStr { value: v2, .. }) => v1 == v2,
            _ => false,
        }
    }
}

impl Eq for TyCon {}

impl std::hash::Hash for TyCon {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::mem::discriminant(self).hash(state);
        match self {
            TyCon::Named { name, kind, .. } => {
                name.hash(state);
                kind.hash(state);
            }
            TyCon::TyNum { value, .. } => value.hash(state),
            TyCon::TyStr { value, .. } => value.hash(state),
        }
    }
}

impl fmt::Display for TyCon {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TyCon::Named { name, .. } => write!(f, "{name}"),
            TyCon::TyNum { value, .. } => write!(f, "{value}"),
            TyCon::TyStr { value, .. } => write!(f, "\"{value}\""),
        }
    }
}

/// A type in the BSC type system.
///
/// Mirrors `Type` from CType.hs:82-87:
/// ```haskell
/// data Type = TVar TyVar | TCon TyCon | TAp Type Type
///           | TGen Position Int | TDefMonad Position
/// ```
///
/// - TVar: type variable
/// - TCon: type constructor
/// - TAp: type application
/// - TGen: quantified type variable (in type schemes)
/// - TDefMonad: monad placeholder (used during imperative do-block parsing)
#[derive(Debug, Clone)]
pub enum Type {
    /// `TVar TyVar` - Type variable
    Var(TyVar),
    /// `TCon TyCon` - Type constructor
    Con(TyCon),
    /// `TAp Type Type` - Type application (f applied to a)
    App(Box<Type>, Box<Type>),
    /// `TGen Position Int` - Generic/quantified type variable (used in type schemes)
    /// Contains position and de Bruijn index.
    /// Uses i64 to match Haskell Int semantics.
    Gen {
        /// Position where this was introduced
        position: Position,
        /// De Bruijn index (Haskell Int → i64)
        index: i64,
    },
    /// `TDefMonad Position` - Monad placeholder.
    ///
    /// Used during parsing of imperative do-blocks.
    /// This is NOT used after CVParserImperative transforms the code.
    /// It represents the implicit monad in imperative-style code.
    DefMonad(Position),
}

impl Type {
    // ========================================================================
    // Constructors
    // ========================================================================

    /// Create a type variable.
    #[must_use]
    pub fn var(tv: TyVar) -> Self {
        Type::Var(tv)
    }

    /// Create a type constructor.
    #[must_use]
    pub fn con(tc: TyCon) -> Self {
        Type::Con(tc)
    }

    /// Create a type application.
    #[must_use]
    pub fn app(fun: Type, arg: Type) -> Self {
        Type::App(Box::new(fun), Box::new(arg))
    }

    /// Create a generic type variable.
    #[must_use]
    pub fn generic(position: Position, index: i64) -> Self {
        Type::Gen { position, index }
    }

    /// Create a default monad type.
    #[must_use]
    pub fn def_monad(position: Position) -> Self {
        Type::DefMonad(position)
    }

    /// Create a numeric type literal from BigInt.
    #[must_use]
    pub fn num(value: BigInt, position: Position) -> Self {
        Type::Con(TyCon::num(value, position))
    }

    /// Create a numeric type literal from i64.
    #[must_use]
    pub fn num_i64(value: i64, position: Position) -> Self {
        Type::Con(TyCon::num_i64(value, position))
    }

    /// Create a numeric type literal from i128 (convenience method).
    #[must_use]
    pub fn num_i128(value: i128, position: Position) -> Self {
        Type::Con(TyCon::num_i128(value, position))
    }

    /// Create a string type literal.
    #[must_use]
    pub fn string(value: impl Into<SmolStr>, position: Position) -> Self {
        Type::Con(TyCon::string(value, position))
    }

    /// Apply this type to multiple arguments.
    #[must_use]
    pub fn apply_many(self, args: impl IntoIterator<Item = Type>) -> Self {
        args.into_iter().fold(self, |acc, arg| Type::app(acc, arg))
    }

    // ========================================================================
    // Basic Type Checks
    // ========================================================================

    /// Check if this is a type variable.
    #[must_use]
    pub fn is_var(&self) -> bool {
        matches!(self, Type::Var(_))
    }

    /// Check if this is a type constructor.
    #[must_use]
    pub fn is_con(&self) -> bool {
        matches!(self, Type::Con(_))
    }

    /// Check if this is a type application.
    #[must_use]
    pub fn is_app(&self) -> bool {
        matches!(self, Type::App(_, _))
    }

    /// Check if this is a generic type variable.
    #[must_use]
    pub fn is_gen(&self) -> bool {
        matches!(self, Type::Gen { .. })
    }

    /// Check if this is a default monad placeholder.
    #[must_use]
    pub fn is_def_monad(&self) -> bool {
        matches!(self, Type::DefMonad(_))
    }

    /// Check if this is a numeric type literal.
    #[must_use]
    pub fn is_num(&self) -> bool {
        matches!(self, Type::Con(TyCon::TyNum { .. }))
    }

    /// Check if this is a string type literal.
    #[must_use]
    pub fn is_str(&self) -> bool {
        matches!(self, Type::Con(TyCon::TyStr { .. }))
    }

    // ========================================================================
    // Value Extraction
    // ========================================================================

    /// Get the type variable if this is a TVar.
    #[must_use]
    pub fn get_var(&self) -> Option<&TyVar> {
        match self {
            Type::Var(tv) => Some(tv),
            _ => None,
        }
    }

    /// Get the type constructor if this is a TCon.
    #[must_use]
    pub fn get_con(&self) -> Option<&TyCon> {
        match self {
            Type::Con(tc) => Some(tc),
            _ => None,
        }
    }

    /// Get the numeric value if this is a TyNum.
    /// Returns a reference to the BigInt value.
    #[must_use]
    pub fn get_num(&self) -> Option<&BigInt> {
        match self {
            Type::Con(TyCon::TyNum { value, .. }) => Some(value),
            _ => None,
        }
    }

    /// Get the numeric value as i64 if it fits.
    /// Returns None if not a TyNum or if the value doesn't fit in i64.
    #[must_use]
    pub fn get_num_i64(&self) -> Option<i64> {
        self.get_num().and_then(|n| n.to_i64())
    }

    /// Get the string value if this is a TyStr.
    #[must_use]
    pub fn get_str(&self) -> Option<&SmolStr> {
        match self {
            Type::Con(TyCon::TyStr { value, .. }) => Some(value),
            _ => None,
        }
    }

    /// Get the generic index if this is a TGen.
    #[must_use]
    pub fn get_gen_index(&self) -> Option<i64> {
        match self {
            Type::Gen { index, .. } => Some(*index),
            _ => None,
        }
    }

    // ========================================================================
    // Type Structure Analysis
    // ========================================================================

    /// Get the leftmost type constructor, if any.
    #[must_use]
    pub fn left_tycon(&self) -> Option<&TyCon> {
        match self {
            Type::App(f, _) => f.left_tycon(),
            Type::Con(tc) => Some(tc),
            _ => None,
        }
    }

    /// Get the leftmost type constructor's name, if any.
    #[must_use]
    pub fn left_con_name(&self) -> Option<&Id> {
        self.left_tycon().and_then(TyCon::name)
    }

    /// Split a type application into its head and arguments.
    ///
    /// For `F a b c`, returns `(F, [a, b, c])`.
    #[must_use]
    pub fn split_app(&self) -> (&Type, Vec<&Type>) {
        fn go<'a>(ty: &'a Type, args: &mut Vec<&'a Type>) -> &'a Type {
            match ty {
                Type::App(f, a) => {
                    args.push(a.as_ref());
                    go(f.as_ref(), args)
                }
                _ => ty,
            }
        }
        let mut args = Vec::new();
        let head = go(self, &mut args);
        args.reverse();
        (head, args)
    }

    /// Get the argument and result types if this is a function type.
    ///
    /// Returns `(argument_type, result_type)` if this is of form `a -> b`.
    #[must_use]
    pub fn get_arrow(&self) -> Option<(&Type, &Type)> {
        if let Type::App(f, res) = self {
            if let Type::App(f2, arg) = f.as_ref() {
                if let Type::Con(TyCon::Named { name, .. }) = f2.as_ref() {
                    if name.name_str() == "->" {
                        return Some((arg.as_ref(), res.as_ref()));
                    }
                }
            }
        }
        None
    }

    /// Get all argument types and the final result type for a function type.
    ///
    /// For `a -> b -> c -> d`, returns `([a, b, c], d)`.
    #[must_use]
    pub fn get_arrows(&self) -> (Vec<&Type>, &Type) {
        let mut args = Vec::new();
        let mut current = self;

        while let Some((arg, res)) = current.get_arrow() {
            args.push(arg);
            current = res;
        }

        (args, current)
    }

    /// Get only the result type (final return type) of a function.
    #[must_use]
    pub fn get_result(&self) -> &Type {
        self.get_arrows().1
    }

    /// Count the number of arrow applications (function arguments).
    #[must_use]
    pub fn arity(&self) -> usize {
        self.get_arrows().0.len()
    }

    // ========================================================================
    // Named Type Checks
    // ========================================================================

    /// Check if this type has a specific constructor name at the head.
    #[must_use]
    pub fn has_con_name(&self, name: &str) -> bool {
        self.left_con_name().is_some_and(|n| n.name_str() == name)
    }

    /// Check if this is the Bit type.
    #[must_use]
    pub fn is_bit(&self) -> bool {
        self.has_con_name("Bit")
    }

    /// Check if this is the Action type.
    #[must_use]
    pub fn is_action(&self) -> bool {
        self.has_con_name("Action")
    }

    /// Check if this is the ActionValue type.
    #[must_use]
    pub fn is_action_value(&self) -> bool {
        self.has_con_name("ActionValue") || self.has_con_name("ActionValue_")
    }

    /// Check if this is the Rules type.
    #[must_use]
    pub fn is_rules(&self) -> bool {
        self.has_con_name("Rules")
    }

    /// Check if this is the Module type.
    #[must_use]
    pub fn is_module(&self) -> bool {
        self.has_con_name("Module")
    }

    /// Check if this is the Integer type.
    #[must_use]
    pub fn is_integer(&self) -> bool {
        self.has_con_name("Integer")
    }

    /// Check if this is the Real type.
    #[must_use]
    pub fn is_real(&self) -> bool {
        self.has_con_name("Real")
    }

    /// Check if this is the String type.
    #[must_use]
    pub fn is_string_type(&self) -> bool {
        self.has_con_name("String")
    }

    /// Check if this is the Bool type.
    #[must_use]
    pub fn is_bool(&self) -> bool {
        self.has_con_name("Bool")
    }

    /// Check if this is a function type (->).
    #[must_use]
    pub fn is_function(&self) -> bool {
        self.get_arrow().is_some()
    }

    /// Check if this is a pair type.
    #[must_use]
    pub fn is_pair(&self) -> bool {
        self.has_con_name("PrimPair")
    }

    // ========================================================================
    // Kind and Position
    // ========================================================================

    /// Get the kind of this type, if it can be determined.
    #[must_use]
    pub fn kind(&self) -> Option<Kind> {
        match self {
            Type::Var(tv) => Some(tv.kind.clone()),
            Type::Con(tc) => tc.kind().cloned(),
            Type::App(f, _) => match f.kind()? {
                Kind::Fun(_, res) => Some((*res).clone()),
                _ => None,
            },
            Type::Gen { .. } | Type::DefMonad(_) => None,
        }
    }

    /// Get the position of this type.
    #[must_use]
    pub fn position(&self) -> Position {
        match self {
            Type::Var(tv) => tv.position(),
            Type::Con(tc) => tc.position(),
            Type::App(f, a) => {
                let fp = f.position();
                let ap = a.position();
                if fp.is_valid() {
                    fp
                } else {
                    ap
                }
            }
            Type::Gen { position, .. } | Type::DefMonad(position) => position.clone(),
        }
    }
}

/// A placeholder "no type" constant.
///
/// This represents an unknown or missing type, similar to Haskell's noType.
/// Uses TGen with index -1 which should never appear in valid type schemes.
pub fn no_type() -> Type {
    Type::Gen {
        position: Position::unknown(),
        index: -1,
    }
}

/// Check if a type is the "no type" placeholder.
#[must_use]
pub fn is_no_type(ty: &Type) -> bool {
    matches!(ty, Type::Gen { index: -1, .. })
}

// Type equality based on the Haskell cmp function
impl PartialEq for Type {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Type::Var(v1), Type::Var(v2)) => v1 == v2,
            (Type::Con(c1), Type::Con(c2)) => c1 == c2,
            (Type::App(f1, a1), Type::App(f2, a2)) => f1 == f2 && a1 == a2,
            (Type::Gen { index: i1, .. }, Type::Gen { index: i2, .. }) => i1 == i2,
            (Type::DefMonad(p1), Type::DefMonad(p2)) => p1 == p2,
            _ => false,
        }
    }
}

impl Eq for Type {}

impl std::hash::Hash for Type {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::mem::discriminant(self).hash(state);
        match self {
            Type::Var(v) => v.hash(state),
            Type::Con(c) => c.hash(state),
            Type::App(f, a) => {
                f.hash(state);
                a.hash(state);
            }
            Type::Gen { index, .. } => index.hash(state),
            Type::DefMonad(p) => {
                p.line.hash(state);
                p.column.hash(state);
            }
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Var(tv) => write!(f, "{tv}"),
            Type::Con(tc) => write!(f, "{tc}"),
            Type::App(fun, arg) => {
                // Check for special syntax (arrows, pairs)
                if let Type::App(f2, a1) = fun.as_ref() {
                    if let Type::Con(TyCon::Named { name, .. }) = f2.as_ref() {
                        let n = name.name().as_str();
                        if n == "->" {
                            return write!(f, "({a1} -> {arg})");
                        }
                        if n == "PrimPair" {
                            return write!(f, "({a1}, {arg})");
                        }
                    }
                }
                write!(f, "({fun} {arg})")
            }
            Type::Gen { index, .. } => write!(f, "(TGen {index})"),
            Type::DefMonad(_) => write!(f, "(TDefMonad)"),
        }
    }
}

/// A named typeclass.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Typeclass {
    /// The name of the typeclass
    pub name: Id,
}

impl Typeclass {
    /// Create a new typeclass.
    #[must_use]
    pub fn new(name: Id) -> Self {
        Self { name }
    }
}

impl fmt::Display for Typeclass {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

/// A predicate (constraint) in a type.
///
/// Represents typeclass constraints like `Eq a` or `Bits a n`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Pred {
    /// The typeclass being constrained
    pub class: Typeclass,
    /// The type arguments to the constraint
    pub args: Vec<Type>,
}

impl Pred {
    /// Create a new predicate.
    #[must_use]
    pub fn new(class: Typeclass, args: Vec<Type>) -> Self {
        Self { class, args }
    }
}

impl fmt::Display for Pred {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.class)?;
        for arg in &self.args {
            write!(f, " {arg}")?;
        }
        Ok(())
    }
}

/// A qualified type with predicates.
///
/// Represents types with constraints like `(Eq a, Bits a n) => a -> Bool`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct QualType {
    /// The predicates (constraints)
    pub preds: Vec<Pred>,
    /// The underlying type
    pub ty: Type,
}

impl QualType {
    /// Create a new qualified type.
    #[must_use]
    pub fn new(preds: Vec<Pred>, ty: Type) -> Self {
        Self { preds, ty }
    }

    /// Create an unqualified type (no predicates).
    #[must_use]
    pub fn unqualified(ty: Type) -> Self {
        Self {
            preds: Vec::new(),
            ty,
        }
    }
}

impl fmt::Display for QualType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.preds.is_empty() {
            write!(f, "{}", self.ty)
        } else {
            write!(f, "(")?;
            for (i, pred) in self.preds.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{pred}")?;
            }
            write!(f, ") => {}", self.ty)
        }
    }
}

