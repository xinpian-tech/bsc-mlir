//! Concrete Syntax AST (CSyntax).
//!
//! Mirrors `src/comp/CSyntax.hs` from the Haskell implementation.
//! This is the output of parsing, before type checking.
//!
//! # Major Types
//!
//! - `CPackage` - A compilation unit
//! - `CDefn` - Top-level definitions
//! - `CExpr` - Expressions (40+ variants)
//! - `CPat` - Patterns
//! - `CType` - Concrete types
//!
//! # Internal Variants
//!
//! Some CExpr variants are "internal" - they are generated during type checking
//! and elaboration, not during parsing. These are marked with the `Typed` suffix
//! or are prefixed with type information (e.g., `ConTyped`, `LitTyped`).

use crate::id::Id;
use crate::literal::Literal;
use bsc_diagnostics::Span;
use bsc_diagnostics::Position;

// ============================================================================
// IdK - Identifier with optional Kind
// ============================================================================

/// An identifier with optional kind annotation.
///
/// Mirrors `IdK` from CSyntax.hs. Used in type definitions where the
/// type parameters may have kind annotations.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum IdK {
    /// Plain identifier (kind will be inferred)
    Plain(Id),
    /// Identifier with explicit kind
    WithKind(Id, CKind),
    /// Identifier with partial kind information
    WithPartialKind(Id, CPartialKind),
}

impl IdK {
    /// Get the identifier.
    #[must_use]
    pub fn id(&self) -> &Id {
        match self {
            IdK::Plain(id) | IdK::WithKind(id, _) | IdK::WithPartialKind(id, _) => id,
        }
    }

    /// Get the kind, if explicitly specified.
    #[must_use]
    pub fn kind(&self) -> Option<&CKind> {
        match self {
            IdK::WithKind(_, k) => Some(k),
            _ => None,
        }
    }
}

// ============================================================================
// CPartialKind - Partial Kind (for user annotations)
// ============================================================================

/// Partial kind information from user annotations.
///
/// Used when the user provides incomplete kind information.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum CPartialKind {
    /// No kind information
    NoInfo,
    /// Star kind (*)
    Star,
    /// Numeric kind (#)
    Num,
    /// String kind ($)
    Str,
    /// Function kind
    Fun(Box<CPartialKind>, Box<CPartialKind>),
}

// ============================================================================
// UndefKind - Kinds of undefined values
// ============================================================================

/// The kind of undefined value.
///
/// Mirrors `UndefKind` from CSyntax.hs. Used in `_` patterns and undefined values.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum UndefKind {
    /// General undefined (from _)
    General,
    /// Don't care value (from ? in Classic syntax)
    DontCare,
    /// Uninitialized value
    Uninitialized,
    /// No match (from failed pattern matching)
    NoMatch,
    /// No implicit condition
    NoImplicitCond,
}

// ============================================================================
// Package and Exports
// ============================================================================

/// Export specification - distinguishes "export only these" from "export all but these".
///
/// Mirrors `Either [CExport] [CExport]` from CSyntax.hs:
/// - `Left exports` = export only these items → `ExportSpec::Only`
/// - `Right exports` = export everything except these → `ExportSpec::Hiding`
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ExportSpec {
    /// Export only these items (Haskell: Left [CExport])
    Only(Vec<CExport>),
    /// Export everything except these items (Haskell: Right [CExport])
    Hiding(Vec<CExport>),
}

/// An included file.
///
/// Mirrors `CInclude` newtype from CSyntax.hs.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CInclude(pub String);

/// A package (compilation unit) in concrete syntax.
///
/// Mirrors `CPackage` from CSyntax.hs:112-118.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CPackage {
    /// Package name
    pub name: Id,
    /// Export specification
    pub exports: ExportSpec,
    /// Imports
    pub imports: Vec<CImport>,
    /// Fixity declarations
    pub fixities: Vec<CFixity>,
    /// Top-level definitions
    pub definitions: Vec<CDefn>,
    /// Included files
    pub includes: Vec<CInclude>,
    /// Source span
    pub span: Span,
}

/// An export specification item.
///
/// Mirrors `CExport` from CSyntax.hs:120-123.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum CExport {
    /// Export a variable (CExpVar)
    Var(Id),
    /// Export a constructor only (CExpCon) - NOT constructors of a type
    Con(Id),
    /// Export a type with all constructors (CExpConAll)
    ConAll(Id),
    /// Export a type with specific constructors/fields
    Type(Id, Vec<Id>),
    /// Re-export a module/package (CExpPkg)
    Package(Id),
}

/// An import declaration.
///
/// Mirrors `CImport` from CSyntax.hs:125-127.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum CImport {
    /// Simple import (CImpId)
    Simple {
        /// Is this a qualified import?
        qualified: bool,
        /// Module being imported
        module: Id,
        /// Optional alias (import qualified M as N)
        alias: Option<Id>,
        /// Import specification (hiding or explicit list)
        spec: Option<CImportSpec>,
        /// Source span
        span: Span,
    },
    /// Signature import (CImpSign)
    Signature {
        /// Signature name
        name: String,
        /// Is this a qualified import?
        qualified: bool,
        /// The package signature
        signature: CPackageSignature,
        /// Source span
        span: Span,
    },
}

impl CImport {
    /// Get the span of this import.
    #[must_use]
    pub fn span(&self) -> Span {
        match self {
            CImport::Simple { span, .. } | CImport::Signature { span, .. } => *span,
        }
    }
}

/// Package signature.
///
/// Mirrors `CSignature` from CSyntax.hs:152-156.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CPackageSignature {
    /// Signature name
    pub name: Id,
    /// Required imports
    pub imports: Vec<Id>,
    /// Fixity declarations
    pub fixities: Vec<CFixity>,
    /// Signature definitions
    pub definitions: Vec<CDefn>,
}

/// Import specification.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum CImportSpec {
    /// Import specific items
    Include(Vec<CExport>),
    /// Import everything except these items
    Hiding(Vec<CExport>),
}

/// Fixity declaration.
///
/// Mirrors Haskell's `CInfix Integer Id | CInfixl Integer Id | CInfixr Integer Id`.
/// Each fixity declaration binds ONE operator. Multiple operators on the same line
/// in source become multiple CFixity entries.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum CFixity {
    /// `infix N op` - Non-associative operator
    Infix(i64, Id),
    /// `infixl N op` - Left-associative operator
    Infixl(i64, Id),
    /// `infixr N op` - Right-associative operator
    Infixr(i64, Id),
}


/// A top-level definition.
///
/// Mirrors `CDefn` from CSyntax.hs:159-213.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum CDefn {
    /// Type synonym: type T a = ... (Ctype)
    Type(CTypeDef),
    /// Data type: data T a = C1 | C2 ... (Cdata)
    Data(CDataDef),
    /// Struct type: struct T a = { ... } (Cstruct)
    Struct(CStructDef),
    /// Type class: class C a where ... (Cclass)
    Class(CClassDef),
    /// Instance: instance C T where ... (Cinstance)
    Instance(CInstanceDef),
    /// Value definition: f x = ... (CValue)
    Value(CValueDef),
    /// Value definition with type signature (CValueSign)
    ValueSign(CDef),
    /// Type signature: f :: T
    Signature(CTypeSignature),
    /// Foreign import (Cforeign)
    Foreign(CForeignDef),
    /// Primitive declaration (Cprimitive)
    Primitive(CPrimitiveDef),
    /// Primitive type declaration (CprimType)
    PrimitiveType(CPrimitiveTypeDef),
    /// Pragma (CPragma)
    Pragma(CPragma),

    // ========================================================================
    // Signature-only variants (from CSyntax.hs:188-213)
    // ========================================================================

    /// Interface instance in signature (CIinstance)
    SigInstance {
        /// Interface name
        name: Id,
        /// Instance type
        ty: CQType,
    },
    /// Abstract type in signature (CItype)
    SigType {
        /// Type name with kind
        name: IdK,
        /// Type parameters
        params: Vec<Id>,
        /// Positions (for error reporting)
        positions: Vec<Position>,
    },
    /// Class in signature (CIclass)
    SigClass {
        /// Coherence flag (Just False = coherent, Just True = incoherent, Nothing = default)
        incoherent_matches: Option<bool>,
        /// Superclass predicates
        supers: Vec<CPred>,
        /// Class name with kind
        name: IdK,
        /// Type parameters
        params: Vec<Id>,
        /// Functional dependencies
        fundeps: Vec<CFunDep>,
        /// Method names
        methods: Vec<Id>,
    },
    /// Value signature in signature (CIValueSign)
    SigValue {
        /// Value name
        name: Id,
        /// Value type
        ty: CQType,
    },
}

/// Type synonym definition.
///
/// Mirrors `Ctype` from CSyntax.hs:163-164.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CTypeDef {
    /// Type name with optional kind
    pub name: IdK,
    /// Type parameters
    pub params: Vec<Id>,
    /// Definition
    pub body: CType,
    /// Source span
    pub span: Span,
}

/// Data type definition.
///
/// Mirrors `Cdata` from CSyntax.hs:165-172.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CDataDef {
    /// Visibility flag (cd_visible)
    pub visible: bool,
    /// Type name with optional kind
    pub name: IdK,
    /// Type parameters
    pub params: Vec<Id>,
    /// Original summands (before field unpacking) - from parser
    pub original_summands: Vec<COriginalSummand>,
    /// Internal summands (after field unpacking) - after elaboration
    pub internal_summands: Vec<CInternalSummand>,
    /// Deriving clauses
    pub deriving: Vec<CTypeclass>,
    /// Source span
    pub span: Span,
}

/// Original summand (data constructor before field unpacking).
///
/// Mirrors `COriginalSummand` from CSyntax.hs:388-394.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct COriginalSummand {
    /// Constructor names (multiple for backwards compatibility)
    pub names: Vec<Id>,
    /// Argument types
    pub arg_types: Vec<CQType>,
    /// Named field names (if record syntax)
    pub field_names: Option<Vec<Id>>,
    /// Tag encoding (if specified with =)
    pub tag_encoding: Option<i64>,
}

/// Internal summand (data constructor after field unpacking).
///
/// Mirrors `CInternalSummand` from CSyntax.hs:398-403.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CInternalSummand {
    /// Constructor names
    pub names: Vec<Id>,
    /// Packed argument type (single type containing all fields)
    pub arg_type: CType,
    /// Tag encoding
    pub tag_encoding: i64,
}

/// Type class reference for deriving clauses.
///
/// Mirrors `CTypeclass` from CType.hs.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CTypeclass {
    /// Type class name
    pub name: Id,
}

/// A named field in a struct, interface, or class.
///
/// Mirrors `CField` from CSyntax.hs:318-324.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CField {
    /// Field name
    pub name: Id,
    /// Interface pragmas (for interface methods)
    pub pragmas: Option<Vec<IfcPragma>>,
    /// Field type (qualified type with constraints)
    pub ty: CQType,
    /// Default implementation (clauses for pattern matching)
    pub default: Vec<CClause>,
    /// Original type (before transformation)
    pub orig_type: Option<CType>,
    /// Source span
    pub span: Span,
}

/// Interface pragma for method attributes.
///
/// Mirrors `IfcPragma` from ISyntax.hs.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum IfcPragma {
    /// Method is always ready
    AlwaysReady,
    /// Method is always enabled
    AlwaysEnabled,
    /// Method has specified prefix
    Prefix(String),
    /// Method result is a port
    Result(String),
    /// Method has specified ready signal name
    Ready(String),
    /// Method has specified enable signal name
    Enable(String),
    /// Method argument names
    ArgNames(Vec<Id>),
    /// Clock argument
    ArgClock(String),
    /// Reset argument
    ArgReset(String),
    /// Inout argument
    ArgInout(String),
}

/// Struct/Interface subtype classification.
///
/// Mirrors `StructSubType` from CType.hs:205-211.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum StructSubType {
    /// Plain struct
    Struct,
    /// Type class (for dictionaries)
    Class,
    /// Data constructor wrapper
    DataCon {
        /// Parent data type
        type_id: Id,
        /// Whether fields are named
        named_fields: bool,
    },
    /// Interface
    Interface(Vec<IfcPragma>),
    /// Polymorphic wrapper (for PolyWrap transformation)
    PolyWrap {
        /// Original type
        original_id: Id,
        /// Constructor (if any)
        constructor: Option<Id>,
        /// Field name
        field: Id,
    },
}

/// Struct type definition.
///
/// Mirrors `Cstruct` from CSyntax.hs:175-181.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CStructDef {
    /// Visibility flag
    pub visible: bool,
    /// Struct subtype (struct, class, interface, etc.)
    pub sub_type: StructSubType,
    /// Type name with optional kind
    pub name: IdK,
    /// Type parameters
    pub params: Vec<Id>,
    /// Fields (methods for interfaces)
    pub fields: Vec<CField>,
    /// Deriving clauses
    pub deriving: Vec<CTypeclass>,
    /// Source span
    pub span: Span,
}

/// Type class definition.
///
/// Mirrors `Cclass` from CSyntax.hs:183-188.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CClassDef {
    /// Coherence flag (Just False = coherent, Just True = incoherent, Nothing = default)
    pub incoherent_matches: Option<bool>,
    /// Superclass predicates
    pub supers: Vec<CPred>,
    /// Class name with optional kind
    pub name: IdK,
    /// Type parameters (multiple allowed)
    pub params: Vec<Id>,
    /// Functional dependencies
    pub fundeps: Vec<CFunDep>,
    /// Methods (with default implementations in cf_default)
    pub methods: Vec<CField>,
    /// Source span
    pub span: Span,
}

/// Functional dependency.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CFunDep {
    /// Source type variables
    pub from: Vec<Id>,
    /// Target type variables
    pub to: Vec<Id>,
}

/// Instance definition.
///
/// Mirrors `Cinstance` from CSyntax.hs:186-187.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CInstanceDef {
    /// Instance qualified type (context => class type)
    pub ty: CQType,
    /// Method implementations (local definitions)
    pub methods: Vec<CDefl>,
    /// Source span
    pub span: Span,
}

/// Value definition without type signature.
///
/// Mirrors `CValue` from CSyntax.hs.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CValueDef {
    /// Name being defined
    pub name: Id,
    /// Clauses (pattern matching)
    pub clauses: Vec<CClause>,
    /// Source span
    pub span: Span,
}

/// Value definition with type signature.
///
/// Mirrors `CValueSign CDef` and `CDefT` from CSyntax.hs:328-330.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum CDef {
    /// Untyped definition (before type checking)
    Untyped {
        /// Name being defined
        name: Id,
        /// Type signature
        ty: CQType,
        /// Clauses
        clauses: Vec<CClause>,
        /// Source span
        span: Span,
    },
    /// Typed definition (after type checking)
    Typed {
        /// Name being defined
        name: Id,
        /// Type variables
        type_vars: Vec<CTyVar>,
        /// Type signature
        ty: CQType,
        /// Clauses
        clauses: Vec<CClause>,
        /// Source span
        span: Span,
    },
}

impl CDef {
    /// Get the name of this definition.
    #[must_use]
    pub fn name(&self) -> Id {
        match self {
            CDef::Untyped { name, .. } | CDef::Typed { name, .. } => name.clone(),
        }
    }

    /// Get the clauses of this definition.
    #[must_use]
    pub fn clauses(&self) -> &[CClause] {
        match self {
            CDef::Untyped { clauses, .. } | CDef::Typed { clauses, .. } => clauses,
        }
    }

    /// Get the span of this definition.
    #[must_use]
    pub fn span(&self) -> Span {
        match self {
            CDef::Untyped { span, .. } | CDef::Typed { span, .. } => *span,
        }
    }
}

/// Type variable (for typed definitions).
///
/// Mirrors type variable representation from CType.hs.
/// The `num` field uses i64 to match Haskell Int semantics.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CTyVar {
    /// Variable name
    pub name: Id,
    /// Variable number (unique during type checking)
    /// Uses i64 to match Haskell Int semantics.
    pub num: i64,
    /// Variable kind
    pub kind: CKind,
}

/// A clause in a definition (one line of pattern matching).
///
/// Mirrors `CClause` from CSyntax.hs:336.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CClause {
    /// Patterns for arguments
    pub patterns: Vec<CPat>,
    /// Qualifiers (guards and generators)
    pub qualifiers: Vec<CQual>,
    /// Body expression
    pub body: CExpr,
    /// Source span
    pub span: Span,
}

/// Type signature (standalone, not attached to definition).
///
/// Used for CDefn::Signature.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CTypeSignature {
    /// Name being typed
    pub name: Id,
    /// Type with context
    pub ty: CQType,
    /// Source span
    pub span: Span,
}

/// Foreign function declaration.
///
/// Mirrors `Cforeign` from CSyntax.hs:
/// ```haskell
/// Cforeign { cforg_name :: Id,
///            cforg_type :: CQType,
///            cforg_foreign_name :: Maybe String,
///            cforg_ports :: Maybe ([String], [String]) }
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CForeignDef {
    /// Bluespec name
    pub name: Id,
    /// Bluespec type
    pub ty: CQType,
    /// Foreign (C/Verilog) name
    pub foreign_name: Option<String>,
    /// Port names: (input_ports, output_ports)
    pub ports: Option<(Vec<String>, Vec<String>)>,
    /// Source span
    pub span: Span,
}

/// Primitive declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CPrimitiveDef {
    /// Name
    pub name: Id,
    /// Type
    pub ty: CQType,
    /// Source span
    pub span: Span,
}

/// Primitive type declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CPrimitiveTypeDef {
    /// Type name
    pub name: Id,
    /// Kind
    pub kind: CKind,
    /// Source span
    pub span: Span,
}

/// Pragma.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum CPragma {
    /// Properties for a definition
    Properties(Id, Vec<CPragmaProperty>),
    /// Synthesize pragma
    Synthesize(Id),
    /// No inline
    NoInline(Id),
}

/// Pragma property.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CPragmaProperty {
    pub name: String,
    pub value: Option<String>,
}

// ============================================================================
// Expressions
// ============================================================================

/// An expression in concrete syntax.
///
/// This enum has approximately 50 variants to mirror `CExpr` from CSyntax.hs.
/// Some variants are only produced during parsing, while others are produced
/// during type elaboration (marked with "Internal:" in their doc comment).
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum CExpr {
    // ========================================================================
    // Basic Expressions (from parsing)
    // ========================================================================

    /// Variable reference
    Var(Id),
    /// Constructor application with arguments
    /// Mirrors `CCon Id [CExpr]` from CSyntax.hs
    Con(Id, Vec<CExpr>, Span),
    /// Literal value - stores Position like Haskell's CLit
    Lit(Literal, Position),
    /// Lambda: \x -> e
    Lambda(Vec<CPat>, Box<CExpr>, Span),
    /// Typed lambda: \(x :: T) -> e
    LambdaTyped {
        /// Parameter (either a position for implicit or an Id)
        param: LambdaParam,
        /// Parameter type
        param_type: CQType,
        /// Body expression
        body: Box<CExpr>,
        /// Source span
        span: Span,
    },
    /// Application: f x
    Apply(Box<CExpr>, Vec<CExpr>, Span),
    /// Infix operator application (before fixity resolution)
    Infix(Box<CExpr>, Id, Box<CExpr>, Span),
    /// Operator chain (before fixity resolution)
    /// Contains alternating operands and operators
    OperChain(Vec<COperand>, Span),
    /// Operator section (left): (+ x)
    SectionL(Id, Box<CExpr>, Span),
    /// Operator section (right): (x +)
    SectionR(Box<CExpr>, Id, Span),
    /// If-then-else - stores Position like Haskell's `Cif Position CExpr CExpr CExpr`
    If(Position, Box<CExpr>, Box<CExpr>, Box<CExpr>),
    /// Case expression - `Ccase Position CExpr CCaseArms`
    Case(Position, Box<CExpr>, Vec<CCaseArm>),
    /// Let expression (sequential)
    LetSeq(Vec<CDefl>, Box<CExpr>, Span),
    /// Let expression (recursive)
    LetRec(Vec<CDefl>, Box<CExpr>, Span),
    /// Do notation
    /// The bool indicates recursive monadicDo (true = mdo/rec)
    /// Mirrors `Cdo Bool CStmts` from CSyntax.hs
    Do {
        /// Whether this is a recursive do (mdo)
        recursive: bool,
        /// Statements in the do block
        stmts: Vec<CStmt>,
        /// Source span
        span: Span,
    },

    // ========================================================================
    // Module/Interface Expressions
    // ========================================================================

    /// Module expression (matches Haskell: Cmodule Position [CMStmt])
    Module(Position, Vec<CModuleItem>),
    /// Interface expression (mirrors Haskell's Cinterface)
    /// Haskell: Cinterface Position (Maybe Id) [CDefl]
    Interface(Position, Option<Id>, Vec<CDefl>),
    /// Rules block
    Rules(Vec<CSchedulePragma>, Vec<CRule>, Span),

    // ========================================================================
    // Struct/Record Expressions
    // ========================================================================

    /// Struct literal: T { x = 1, y = 2 }
    /// The Option<bool> indicates visibility (Some(true) = visible)
    Struct(Option<bool>, Id, Vec<CFieldInit>, Span),
    /// Struct update: e { x = 1 }
    Update(Box<CExpr>, Vec<CFieldInit>, Span),
    /// Field selection: e.x
    Select(Box<CExpr>, Id, Span),

    // ========================================================================
    // Hardware-Specific Expressions
    // ========================================================================

    /// Hardware write: lhs <= rhs (for registers/wires)
    Write {
        /// Position of the write
        position: Position,
        /// Left-hand side (what to write to)
        lhs: Box<CExpr>,
        /// Right-hand side (value to write)
        rhs: Box<CExpr>,
        /// Source span
        span: Span,
    },
    /// Undefined value
    Any {
        /// Position
        position: Position,
        /// Kind of undefined
        kind: UndefKind,
        /// Source span
        span: Span,
    },
    /// Array/bit indexing: e[i]
    Index {
        pos: Position,
        /// Array/bit-vector expression
        expr: Box<CExpr>,
        /// Index expression
        index: Box<CExpr>,
        /// Source span
        span: Span,
    },
    /// Bit range selection: e[hi:lo]
    IndexRange {
        /// Bit-vector expression
        expr: Box<CExpr>,
        /// High bit index
        hi: Box<CExpr>,
        /// Low bit index
        lo: Box<CExpr>,
        /// Source span
        span: Span,
    },
    /// Bit range update: e[hi:lo] = v
    IndexUpdate {
        /// Position
        position: Position,
        /// Bit-vector expression
        expr: Box<CExpr>,
        /// Range (high, low)
        range: (Box<CExpr>, Box<CExpr>),
        /// New value
        value: Box<CExpr>,
        /// Source span
        span: Span,
    },
    /// System task application: $display(...)
    TaskApply(Box<CExpr>, Vec<CExpr>, Span),
    /// Typed system task application
    TaskApplyTyped(Box<CExpr>, CType, Vec<CExpr>, Span),

    // ========================================================================
    // Type-Related Expressions
    // ========================================================================

    /// Type ascription: e :: T
    TypeAscription(Box<CExpr>, CQType, Span),
    /// Type application: e @T
    TypeApply(Box<CExpr>, Vec<CType>, Span),
    /// valueOf(t) - type to value
    ValueOf(CType, Span),
    /// stringOf(t) - type to string
    StringOf(CType, Span),

    // ========================================================================
    // Container Literals
    // ========================================================================

    /// Parenthesized expression
    Paren(Box<CExpr>, Span),
    /// List literal: [1, 2, 3]
    List(Vec<CExpr>, Span),
    /// Tuple literal: (1, 2, 3)
    Tuple(Vec<CExpr>, Span),

    // ========================================================================
    // Verilog Integration
    // ========================================================================

    /// Verilog module instantiation (simplified)
    Verilog(CVerilog, Span),
    /// Verilog module expression (full form matching Haskell's CmoduleVerilog)
    /// Haskell: CmoduleVerilog CExpr Bool VClockInfo VResetInfo [(VArgInfo,CExpr)] [VFieldInfo] VSchedInfo VPathInfo
    ModuleVerilog {
        /// Module name expression (type String)
        name_expr: Box<CExpr>,
        /// Whether it is a user-imported module
        user_imported: bool,
        /// Clock information
        clock_info: crate::vmodinfo::VClockInfo,
        /// Reset information
        reset_info: crate::vmodinfo::VResetInfo,
        /// Input arguments (arg info, expression pairs)
        args: Vec<(crate::vmodinfo::VArgInfo, CExpr)>,
        /// Output interface fields
        fields: Vec<crate::vmodinfo::VFieldInfo>,
        /// Scheduling annotations
        sched_info: crate::vmodinfo::VSchedInfo,
        /// Path annotations
        path_info: crate::vmodinfo::VPathInfo,
    },
    /// Foreign C function
    ForeignFuncC {
        /// Function name
        name: Id,
        /// Function type
        ty: CQType,
        /// Source span
        span: Span,
    },

    // ========================================================================
    // Action Expressions
    // ========================================================================

    /// Action block
    /// Haskell: Caction Position CStmts
    Action(Position, Vec<CStmt>),
    /// ActionValue block
    ActionValue(Vec<CStmt>, Span),

    // ========================================================================
    // Attributes
    // ========================================================================

    /// Attribute: (* attr *) expr
    Attributed(Vec<CAttribute>, Box<CExpr>, Span),

    // ========================================================================
    // Internal Variants (generated during elaboration)
    // ========================================================================

    /// Internal: Typed constructor application
    ConTyped {
        /// Type constructor name
        type_name: Id,
        /// Data constructor name
        con_name: Id,
        /// Arguments
        args: Vec<CExpr>,
        /// Source span
        span: Span,
    },
    /// Internal: Typed literal
    LitTyped(CType, Literal, Span),
    /// Internal: Typed undefined
    AnyTyped {
        /// Position
        position: Position,
        /// Kind of undefined
        kind: UndefKind,
        /// Type
        ty: CType,
        /// Source span
        span: Span,
    },
    /// Internal: Typed field selection
    SelectTyped {
        /// Type constructor name
        type_name: Id,
        /// Expression
        expr: Box<CExpr>,
        /// Field name
        field: Id,
        /// Source span
        span: Span,
    },
    /// Internal: Typed struct literal
    StructTyped(CType, Vec<CFieldInit>, Span),
    /// Internal: Typed Verilog module
    VerilogTyped(CType, CVerilog, Span),
    /// Internal: Typed foreign C function
    ForeignFuncCTyped {
        /// Function name
        name: Id,
        /// Function type (internal representation)
        ty: CType,
        /// Source span
        span: Span,
    },

    // ========================================================================
    // Deriving/Internal Variants (from CSyntax.hs:290-306)
    // ========================================================================

    /// Internal: Constructor with single argument (from deriving)
    /// CCon1 Id Id CExpr - type_id, con_id, arg
    Con1 {
        /// Type constructor name
        type_id: Id,
        /// Data constructor name
        con_id: Id,
        /// Single argument
        arg: Box<CExpr>,
        /// Source span
        span: Span,
    },
    /// Internal: Typed selection with expression type
    /// CSelectTT Id CExpr Id - type_id, expr, field_id
    SelectTT {
        /// Type constructor name
        type_id: Id,
        /// Expression being selected from
        expr: Box<CExpr>,
        /// Field name
        field_id: Id,
        /// Source span
        span: Span,
    },
    /// Internal: Nullary constructor
    /// CCon0 (Maybe Id) Id - optional type_id, con_id
    Con0 {
        /// Type constructor name (optional for some contexts)
        type_id: Option<Id>,
        /// Data constructor name
        con_id: Id,
        /// Source span
        span: Span,
    },
    /// Internal: Typed selector (no expression, just selector function)
    /// CSelectT Id Id - type_id, field_id
    SelectT {
        /// Type constructor name
        type_id: Id,
        /// Field name
        field_id: Id,
        /// Source span
        span: Span,
    },
}

/// Lambda parameter - either an explicit Id or implicit (represented by position).
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum LambdaParam {
    /// Implicit parameter (just a position)
    Implicit(Position),
    /// Explicit parameter with name
    Explicit(Id),
}

/// An operand in an operator chain (before fixity resolution).
///
/// Mirrors `COp` from CSyntax.hs:581-584:
/// ```haskell
/// data COp = CRand CExpr | CRator Int Id
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum COperand {
    /// `CRand CExpr` - An expression operand
    Expr(CExpr),
    /// `CRator Int Id` - An operator with its arity
    /// Uses i64 to match Haskell Int semantics.
    Operator {
        /// Arity of the operator
        arity: i64,
        /// Operator name
        name: Id,
    },
}

impl CExpr {
    /// Get the span of this expression.
    #[must_use]
    pub fn span(&self) -> Span {
        match self {
            // Variable gets span from Id's position
            CExpr::Var(id) => {
                let pos = id.position();
                if pos.is_valid() {
                    // Convert position to approximate span
                    let start = ((pos.line - 1) * 100 + pos.column - 1) as u32;
                    Span::new(start, start + id.name().len() as u32)
                } else {
                    Span::DUMMY
                }
            }
            // Constructor has explicit span
            CExpr::Con(_, _, span) => *span,
            // Expressions with explicit spans
            CExpr::Lit(_, _) => Span::DUMMY,  // Lit stores Position not Span
            CExpr::Action(_, _) => Span::DUMMY,  // Action stores Position not Span
            CExpr::Case(_, _, _) => Span::DUMMY,  // Case stores Position not Span
            CExpr::Lambda(_, _, span)
            | CExpr::LambdaTyped { span, .. }
            | CExpr::Apply(_, _, span)
            | CExpr::Infix(_, _, _, span)
            | CExpr::OperChain(_, span)
            | CExpr::SectionL(_, _, span)
            | CExpr::SectionR(_, _, span)
            | CExpr::LetSeq(_, _, span)
            | CExpr::LetRec(_, _, span)
            | CExpr::Do { span, .. }
            | CExpr::Rules(_, _, span)
            | CExpr::Struct(_, _, _, span)
            | CExpr::Update(_, _, span)
            | CExpr::Select(_, _, span)
            | CExpr::Write { span, .. }
            | CExpr::Any { span, .. }
            | CExpr::Index { span, .. }
            | CExpr::IndexRange { span, .. }
            | CExpr::IndexUpdate { span, .. }
            | CExpr::TaskApply(_, _, span)
            | CExpr::TaskApplyTyped(_, _, _, span)
            | CExpr::TypeAscription(_, _, span)
            | CExpr::TypeApply(_, _, span)
            | CExpr::ValueOf(_, span)
            | CExpr::StringOf(_, span)
            | CExpr::Paren(_, span)
            | CExpr::List(_, span)
            | CExpr::Tuple(_, span)
            | CExpr::Verilog(_, span)
            | CExpr::ForeignFuncC { span, .. }
            | CExpr::ActionValue(_, span)
            | CExpr::Attributed(_, _, span)
            | CExpr::ConTyped { span, .. }
            | CExpr::LitTyped(_, _, span)
            | CExpr::AnyTyped { span, .. }
            | CExpr::SelectTyped { span, .. }
            | CExpr::StructTyped(_, _, span)
            | CExpr::VerilogTyped(_, _, span)
            | CExpr::ForeignFuncCTyped { span, .. }
            | CExpr::Con1 { span, .. }
            | CExpr::SelectTT { span, .. }
            | CExpr::Con0 { span, .. }
            | CExpr::SelectT { span, .. } => *span,
            // These store Position not Span (like Haskell)
            CExpr::If(_, _, _, _) => Span::DUMMY,
            CExpr::Module(_, _) => Span::DUMMY,
            CExpr::Interface(_, _, _) => Span::DUMMY,
            // ModuleVerilog doesn't have a span
            CExpr::ModuleVerilog { .. } => Span::DUMMY,
        }
    }
}

// ============================================================================
// CDefl - Local Definition in Let/Where
// ============================================================================

/// A local definition (in let expressions or where clauses).
///
/// Mirrors `CDefl` from CSyntax.hs. This represents definitions that appear
/// inside expressions, as opposed to top-level definitions.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum CDefl {
    /// Value definition with signature: f :: T; f x = e
    ValueSign(CDef, Vec<CQual>, Span),
    /// Value definition without signature
    Value(Id, Vec<CClause>, Vec<CQual>, Span),
    /// Pattern binding: p = e
    Match(CPat, CExpr, Span),
}

/// A qualifier in a let binding (guards).
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum CQual {
    /// Generator: pat <- expr
    Gen(CType, CPat, CExpr),
    /// Filter/guard: expr
    Filter(CExpr),
}

// ============================================================================
// Pragma Types
// ============================================================================

/// Scheduling pragma for rules.
///
/// Mirrors `CSchedulePragma` from CSyntax.hs.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum CSchedulePragma {
    /// Rules that should not fire together
    Mutually {
        exclusive: Vec<CExpr>,
    },
    /// Rules that can fire together
    Conflict {
        rules: Vec<CExpr>,
    },
    /// Preemption: first rule preempts second
    Preempt {
        first: Vec<CExpr>,
        second: Vec<CExpr>,
    },
    /// Sequencing: first before second
    Before {
        first: Vec<CExpr>,
        second: Vec<CExpr>,
    },
    /// Execution order within a clock cycle
    ExecutionOrder(Vec<CExpr>),
}

/// Rule pragma (attributes on individual rules).
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum RulePragma {
    /// Fire when enabled
    FireWhenEnabled,
    /// No implicit conditions
    NoImplicitConditions,
    /// Can fire multiple times per cycle
    CanFire,
    /// Cannot fire
    NoFire,
    /// Aggressive conditions
    AggressiveConditions,
    /// Conservative conditions
    ConservativeConditions,
    /// Clock domain
    Clock(Id),
    /// Reset
    Reset(Id),
    /// Documentation string
    Doc(String),
    /// Hide from scheduling report
    Hide,
    /// No warning
    NoWarn,
    /// Warn all conflicts
    WarnAllConflicts,
    /// Clock crossing rule
    ClockCrossingRule,
}

/// A case arm.
///
/// Mirrors `CCaseArm` from CSyntax.hs:
/// ```haskell
/// data CCaseArm = CCaseArm {
///     cca_pattern :: CPat,
///     cca_filters :: [CQual],
///     cca_consequent :: CExpr
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CCaseArm {
    /// Pattern to match
    pub pattern: CPat,
    /// Qualifiers (guards/filters)
    pub qualifiers: Vec<CQual>,
    /// Body expression (single consequent)
    pub body: CExpr,
    /// Source span
    pub span: Span,
}

/// A statement in do/action blocks.
///
/// Mirrors `CStmt` from CSyntax.hs:
/// ```haskell
/// data CStmt
///     = CSBindT CPat (Maybe CExpr) [(Position,PProp)] CQType CExpr
///     | CSBind CPat (Maybe CExpr) [(Position,PProp)] CExpr
///     | CSletseq [CDefl]
///     | CSletrec [CDefl]
///     | CSExpr (Maybe CExpr) CExpr
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum CStmt {
    /// Typed bind: pat :: type <- expr
    /// With optional instance name and pragmas
    BindT {
        /// Pattern to bind
        pattern: CPat,
        /// Optional instance name
        instance_name: Option<Box<CExpr>>,
        /// Pragmas with positions
        pragmas: Vec<(Position, PProp)>,
        /// Type annotation
        ty: CQType,
        /// Expression to bind
        expr: CExpr,
        /// Source span
        span: Span,
    },
    /// Untyped bind: pat <- expr
    /// With optional instance name and pragmas
    Bind {
        /// Pattern to bind
        pattern: CPat,
        /// Optional instance name
        instance_name: Option<Box<CExpr>>,
        /// Pragmas with positions
        pragmas: Vec<(Position, PProp)>,
        /// Expression to bind
        expr: CExpr,
        /// Source span
        span: Span,
    },
    /// Sequential let: rhs of "let x = x" refers to previous def
    LetSeq(Vec<CDefl>, Span),
    /// Recursive let: rhs of "let x = x" refers to self
    LetRec(Vec<CDefl>, Span),
    /// Expression statement with optional instance name
    Expr {
        /// Optional instance name
        instance_name: Option<Box<CExpr>>,
        /// Expression
        expr: CExpr,
        /// Source span
        span: Span,
    },
}

/// Longname is a path of identifiers.
/// Mirrors `type Longname = [Id]` from Id.hs.
pub type Longname = Vec<Id>;

/// Method scheduling conflict information.
///
/// Mirrors `MethodConflictInfo` from SchedInfo.hs:
/// ```haskell
/// data MethodConflictInfo idtype = MethodConflictInfo {
///     sCF  :: [(idtype, idtype)],  -- conflict-free
///     sSB  :: [(idtype, idtype)],  -- sequenced-before
///     sME  :: [[idtype]],          -- mutually exclusive
///     sP   :: [(idtype, idtype)],  -- preempts
///     sSBR :: [(idtype, idtype)],  -- sequenced-before (reverse)
///     sC   :: [(idtype, idtype)],  -- conflicts
///     sEXT :: [idtype]             -- external
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct MethodConflictInfo<T> {
    /// Conflict-free pairs
    pub conflict_free: Vec<(T, T)>,
    /// Sequenced-before pairs
    pub sequenced_before: Vec<(T, T)>,
    /// Mutually exclusive groups
    pub mutually_exclusive: Vec<Vec<T>>,
    /// Preempts pairs
    pub preempts: Vec<(T, T)>,
    /// Sequenced-before reverse pairs
    pub sequenced_before_reverse: Vec<(T, T)>,
    /// Conflict pairs
    pub conflicts: Vec<(T, T)>,
    /// External methods
    pub external: Vec<T>,
}

/// Module definition property pragma.
///
/// Mirrors `PProp` from Pragma.hs exactly:
/// ```haskell
/// data PProp
///     = PPverilog
///     | PPforeignImport Id
///     | PPalwaysReady [Longname]
///     | PPalwaysEnabled [Longname]
///     | PPenabledWhenReady [Longname]
///     | PPscanInsert Integer
///     | PPbitBlast
///     | PPCLK String
///     | PPGATE String
///     | PPRSTN String
///     | PPclock_osc [(Id,String)]
///     | PPclock_gate [(Id,String)]
///     | PPgate_inhigh [Id]
///     | PPgate_unused [Id]
///     | PPreset_port [(Id,String)]
///     | PParg_param [(Id,String)]
///     | PParg_port [(Id,String)]
///     | PParg_clocked_by [(Id,String)]
///     | PParg_reset_by [(Id,String)]
///     | PPoptions [String]
///     | PPgate_input_clocks [Id]
///     | PPmethod_scheduling (MethodConflictInfo Longname)
///     | PPdoc String
///     | PPperf_spec [[Id]]
///     | PPclock_family [Id]
///     | PPclock_ancestors [[Id]]
///     | PPparam [Id]
///     | PPinst_name Id
///     | PPinst_hide
///     | PPinst_hide_all
///     | PPdeprecate String
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum PProp {
    /// Generate Verilog
    Verilog,
    /// Foreign import wrapper (Id is link name)
    ForeignImport(Id),
    /// No ready signals for these methods ([] means all)
    AlwaysReady(Vec<Longname>),
    /// Execute on every cycle
    AlwaysEnabled(Vec<Longname>),
    /// Enable is equivalent to ready
    EnabledWhenReady(Vec<Longname>),
    /// Insert scan chain ports
    ScanInsert(i64),
    /// Do "bit blasting" (split multibit ports)
    BitBlast,
    /// Clock port prefix
    ClockPrefix(String),
    /// Gate port prefix
    GatePrefix(String),
    /// Reset port prefix
    ResetPrefix(String),
    /// Port name for clock oscillator
    ClockOsc(Vec<(Id, String)>),
    /// Port name for clock gate
    ClockGate(Vec<(Id, String)>),
    /// Clock args with inhigh gates
    GateInhigh(Vec<Id>),
    /// Clock args with unused gates
    GateUnused(Vec<Id>),
    /// Port name for reset
    ResetPort(Vec<(Id, String)>),
    /// Name for parameter argument
    ArgParam(Vec<(Id, String)>),
    /// Port name for other arguments
    ArgPort(Vec<(Id, String)>),
    /// Clocks of module arguments
    ArgClockedBy(Vec<(Id, String)>),
    /// Resets of module arguments
    ArgResetBy(Vec<(Id, String)>),
    /// Compiler options
    Options(Vec<String>),
    /// List of clock args with gates
    GateInputClocks(Vec<Id>),
    /// Scheduling constraints for interface arg methods
    MethodScheduling(MethodConflictInfo<Longname>),
    /// Comment to carry through to Verilog
    Doc(String),
    /// Method composition order for performance specs
    PerfSpec(Vec<Vec<Id>>),
    /// Ids of input clocks in the same family
    ClockFamily(Vec<Id>),
    /// Input clock ancestry sequences
    ClockAncestors(Vec<Vec<Id>>),
    /// Module arguments which should generate to params instead of ports
    Param(Vec<Id>),
    /// Instance name
    InstName(Id),
    /// Hide instance from hierarchy
    InstHide,
    /// Hide instance completely from all output
    InstHideAll,
    /// Deprecation message
    Deprecate(String),
}

/// A module statement (mirrors Haskell's CMStmt).
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum CModuleItem {
    /// General statement: CSExpr, CSletrec, CSletseq, CSBind, etc.
    /// (mirrors CMStmt CStmt)
    Stmt(CStmt),
    /// Rules expression (mirrors CMrules CExpr)
    Rules(CExpr),
    /// Interface expression (mirrors CMinterface CExpr)
    Interface(CExpr),
    /// Tuple interface expression (mirrors CMTupleInterface Position [CExpr])
    TupleInterface(Position, Vec<CExpr>),
}

/// A method definition in a module.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CMethodDef {
    /// Method name
    pub name: Id,
    /// Parameters
    pub params: Vec<CPat>,
    /// Implicit condition
    pub condition: Option<CExpr>,
    /// Body
    pub body: CExpr,
    /// Source span
    pub span: Span,
}

/// An interface item.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum CInterfaceItem {
    /// Method
    Method(CMethodDef),
    /// Sub-interface
    SubInterface(Id, CExpr, Span),
}

/// A rule definition.
///
/// Mirrors `CRule` from CSyntax.hs:426-428.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum CRule {
    /// Simple rule
    Rule {
        /// Rule pragmas
        pragmas: Vec<RulePragma>,
        /// Rule name (expression, often just a string literal)
        name: Option<CExpr>,
        /// Qualifiers (guards and generators)
        qualifiers: Vec<CQual>,
        /// Body
        body: CExpr,
        /// Source span
        span: Span,
    },
    /// Nested rules (CRuleNest)
    Nested {
        /// Rule pragmas
        pragmas: Vec<RulePragma>,
        /// Rule name (expression)
        name: Option<CExpr>,
        /// Qualifiers
        qualifiers: Vec<CQual>,
        /// Nested rules
        rules: Vec<CRule>,
        /// Source span
        span: Span,
    },
}

impl CRule {
    /// Get the span of this rule.
    #[must_use]
    pub fn span(&self) -> Span {
        match self {
            CRule::Rule { span, .. } | CRule::Nested { span, .. } => *span,
        }
    }
}

/// A submodule instantiation.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CSubmodule {
    /// Binding name
    pub name: Id,
    /// Module expression
    pub module: CExpr,
    /// Source span
    pub span: Span,
}

/// A field initialization in a struct literal.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CFieldInit {
    /// Field name
    pub name: Id,
    /// Field value
    pub value: CExpr,
    /// Source span
    pub span: Span,
}

/// Verilog module instantiation.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CVerilog {
    /// Module name
    pub name: String,
    /// Parameters
    pub params: Vec<(String, CExpr)>,
    /// Port connections
    pub ports: Vec<CVerilogPort>,
}

/// A Verilog port connection.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CVerilogPort {
    /// Port name
    pub name: String,
    /// Port direction
    pub direction: CVerilogDir,
    /// Port expression
    pub expr: CExpr,
}

/// Verilog port direction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum CVerilogDir {
    Input,
    Output,
    Inout,
}

/// An attribute.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CAttribute {
    /// Attribute name
    pub name: String,
    /// Attribute value
    pub value: Option<CExpr>,
    /// Source span
    pub span: Span,
}

// ============================================================================
// Patterns
// ============================================================================

/// A pattern.
///
/// Mirrors `CPat` from CSyntax.hs:355-373.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum CPat {
    /// Variable pattern (CPVar)
    Var(Id),
    /// Wildcard pattern (CPAny Position) - stores Position like Haskell
    Wildcard(Position),
    /// Constructor pattern (CPCon)
    Con(Id, Vec<CPat>, Span),
    /// Struct pattern (CPstruct)
    /// The Option<bool> indicates visibility (from Haskell)
    Struct(Option<bool>, Id, Vec<CPatField>, Span),
    /// Literal pattern (CPLit CLiteral) - stores Position like Haskell's CLiteral
    Lit(Literal, Position),
    /// As pattern: x@p (CPAs)
    As(Id, Box<CPat>, Span),
    /// Typed pattern: p :: T
    Typed(Box<CPat>, CType, Span),
    /// Parenthesized pattern
    Paren(Box<CPat>, Span),
    /// Tuple pattern
    Tuple(Vec<CPat>, Span),
    /// List pattern
    List(Vec<CPat>, Span),
    /// Infix pattern operator chain (CPOper)
    Infix(Box<CPat>, Id, Box<CPat>, Span),

    // ========================================================================
    // Internal/Deriving Variants (from CSyntax.hs:365-373)
    // ========================================================================

    /// Mixed literal pattern (for bit patterns with don't-cares)
    /// CPMixedLit Position Integer [(Integer, Maybe Integer)]
    MixedLit {
        /// Position
        position: Position,
        /// Base (e.g., 2 for binary, 16 for hex)
        base: i64,
        /// Parts: (length in digits, value or None for don't-care)
        parts: Vec<(i64, Option<i64>)>,
        /// Source span
        span: Span,
    },
    /// Internal: Constructor with single arg and type (from deriving)
    /// CPCon1 Id Id CPat - type_id, con_id, arg
    Con1 {
        /// Type constructor name
        type_id: Id,
        /// Data constructor name
        con_id: Id,
        /// Argument pattern
        arg: Box<CPat>,
        /// Source span
        span: Span,
    },
    /// Internal: After type checking - constructor with type args
    /// CPConTs Id Id [CType] [CPat] - type_id, con_id, type_args, args
    ConTs {
        /// Type constructor name
        type_id: Id,
        /// Data constructor name
        con_id: Id,
        /// Type arguments
        type_args: Vec<CType>,
        /// Pattern arguments
        args: Vec<CPat>,
        /// Source span
        span: Span,
    },
}

/// A field in a struct pattern.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CPatField {
    /// Field name
    pub name: Id,
    /// Field pattern
    pub pattern: CPat,
    /// Source span
    pub span: Span,
}

// ============================================================================
// Types
// ============================================================================

/// A qualified type (with context).
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CQType {
    /// Type class constraints
    pub context: Vec<CPred>,
    /// The type
    pub ty: CType,
    /// Source span
    pub span: Span,
}

/// A type class predicate.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CPred {
    /// Type class name
    pub class: Id,
    /// Type arguments
    pub args: Vec<CType>,
    /// Source span
    pub span: Span,
}

/// A type.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum CType {
    /// No type specified (placeholder for type inference)
    /// Mirrors Haskell's `noType = TGen noPosition (-1)`
    NoType,
    /// Type variable
    Var(Id),
    /// Type constructor
    Con(Id),
    /// Type application
    Apply(Box<CType>, Box<CType>, Span),
    /// Numeric type literal (mirrors Haskell's TyNum)
    Num(i128, Position),
    /// String type literal (mirrors Haskell's TyStr)
    Str(String, Position),
    /// Function type: a -> b
    Fun(Box<CType>, Box<CType>, Span),
    /// Forall type: forall a. T
    Forall(Vec<CTypeParam>, Box<CType>, Span),
    /// Parenthesized type
    Paren(Box<CType>, Span),
    /// Tuple type
    Tuple(Vec<CType>, Span),
    /// List type: [a]
    List(Box<CType>, Span),
    /// Infix type operator (before fixity resolution)
    Infix(Box<CType>, Id, Box<CType>, Span),
    /// Default monad type (the `module` keyword)
    /// Mirrors Haskell's `TDefMonad Position`
    DefMonad(Position),
}

/// A type parameter with optional kind annotation.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CTypeParam {
    /// Parameter name
    pub name: Id,
    /// Optional kind
    pub kind: Option<CKind>,
    /// Source span
    pub span: Span,
}

/// A kind.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum CKind {
    /// Type kind (*)
    Star(Span),
    /// Numeric kind (#)
    Num(Span),
    /// String kind ($)
    Str(Span),
    /// Function kind: k1 -> k2
    Fun(Box<CKind>, Box<CKind>, Span),
    /// Parenthesized kind
    Paren(Box<CKind>, Span),
}

