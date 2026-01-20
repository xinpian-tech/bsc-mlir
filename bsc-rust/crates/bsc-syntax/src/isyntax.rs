//! Internal Syntax AST (ISyntax).
//!
//! Mirrors `src/comp/ISyntax.hs` from the Haskell implementation.
//! This is the type-checked representation, ready for backends.

use bsc_diagnostics::Position;

use crate::csyntax::{CSchedulePragma, RulePragma, UndefKind};
use crate::id::Id;
use crate::literal::IntLiteral;

// ============================================================================
// Package and Definitions
// ============================================================================

/// A package in internal syntax.
///
/// Mirrors `IPackage` from ISyntax.hs:103-109.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct IPackage {
    /// Package name
    pub name: Id,
    /// Dependent packages (name, signature)
    pub depends: Vec<(Id, String)>,
    /// Pragmas
    pub pragmas: Vec<IPragma>,
    /// Definitions
    pub defs: Vec<IDef>,
}

/// A pragma in ISyntax.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum IPragma {
    /// Properties
    Properties(Id, Vec<IProperty>),
}

/// A property in a pragma.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct IProperty {
    pub name: String,
    pub value: Option<String>,
}

/// A definition in internal syntax.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct IDef {
    /// Name
    pub name: Id,
    /// Type
    pub ty: IType,
    /// Expression
    pub expr: IExpr,
    /// Definition properties
    pub props: Vec<DefProp>,
}

/// Definition properties.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum DefProp {
    /// Should not be inlined
    NoInline,
    /// Can always be inlined
    AlwaysInline,
    /// Has a specific arity
    Arity(u32),
    /// Is a primitive
    Primitive,
}

// ============================================================================
// Expressions
// ============================================================================

/// An expression in internal syntax.
///
/// Mirrors `IExpr a` from ISyntax.hs:180-186:
/// ```haskell
/// data IExpr a = ILam Id IType (IExpr a)
///              | IAps (IExpr a) [Either IType (IExpr a)]
///              | IVar Id
///              | ILAM Id IKind (IExpr a)
///              | ICon Id (IConInfo a)
///              | IRefT IType (IExpr a) Position
/// ```
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum IExpr {
    /// `ILam Id IType (IExpr a)` - Lambda: \(x :: T) -> e
    Lam(Id, IType, Box<IExpr>),
    /// `ILAM Id IKind (IExpr a)` - Type lambda: /\a -> e
    TyLam(Id, IKind, Box<IExpr>),
    /// `IAps (IExpr a) [Either IType (IExpr a)]` - Application (including type applications)
    App(Box<IExpr>, Vec<IArg>),
    /// `IVar Id` - Variable reference
    /// NOTE: In Haskell, IVar does NOT store a type - type comes from environment.
    Var(Id),
    /// `ICon Id (IConInfo a)` - Constant/constructor
    Con(Id, IConInfo),
    /// `IRefT IType (IExpr a) Position` - Heap reference used during evaluation.
    /// This is only used during IExpand evaluation, not in final output.
    RefT {
        ty: IType,
        expr: Box<IExpr>,
        position: bsc_diagnostics::Position,
    },
}

/// An argument in an application.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum IArg {
    /// Expression argument
    Expr(IExpr),
    /// Type argument
    Type(IType),
}

// ============================================================================
// IConInfo - Constant/Constructor Information (32 variants)
// ============================================================================

/// Information about a constant/constructor.
///
/// This mirrors the 32 variants from Haskell ISyntax.hs.
/// Each variant contains `iConType` as the first field.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum IConInfo {
    // ========================================================================
    // Definition references (ordC 0, 19)
    // ========================================================================
    /// Reference to a package definition (ICDef)
    /// May be incomplete if read from .bo file and not fixed-up yet
    Def {
        ty: IType,
        def: Box<IExpr>,
    },

    /// Value definition within a module (ICValue)
    /// Similar to Def, but for module-level values
    Value {
        ty: IType,
        def: Box<IExpr>,
    },

    // ========================================================================
    // Primitives and foreign (ordC 1, 2)
    // ========================================================================
    /// Primitive operation (ICPrim)
    Prim {
        ty: IType,
        op: PrimOp,
    },

    /// Foreign function call (ICForeign)
    Foreign {
        ty: IType,
        name: String,
        is_c: bool,
        ports: Option<Vec<ForeignPort>>,
        call_no: Option<i64>,
    },

    // ========================================================================
    // Data constructors (ordC 3, 4, 5)
    // ========================================================================
    /// Data constructor (ICCon)
    Con {
        ty: IType,
        tag_info: ConTagInfo,
    },

    /// Constructor test - "is this constructor?" (ICIs)
    /// Eventually evaluates to ICInt 0 (false) or 1 (true)
    Is {
        ty: IType,
        tag_info: ConTagInfo,
    },

    /// Constructor extraction - get value if this constructor (ICOut)
    /// Only used after doing appropriate Is check
    Out {
        ty: IType,
        tag_info: ConTagInfo,
    },

    // ========================================================================
    // Tuples and selectors (ordC 6, 7)
    // ========================================================================
    /// Tuple constructor (ICTuple)
    Tuple {
        ty: IType,
        field_ids: Vec<Id>,
    },

    /// Field selector (ICSel)
    Sel {
        ty: IType,
        sel_no: i64,
        num_sel: i64,
    },

    // ========================================================================
    // Verilog (ordC 8)
    // ========================================================================
    /// Verilog module (ICVerilog)
    Verilog {
        ty: IType,
        is_user_import: bool,
        info: VModInfo,
        meth_types: Vec<Vec<IType>>,
    },

    // ========================================================================
    // Undefined values (ordC 9)
    // ========================================================================
    /// Undefined value (ICUndet)
    Undet {
        ty: IType,
        kind: UndefKind,
        value: Option<Box<IExpr>>,
    },

    // ========================================================================
    // Literals (ordC 10, 11, 12, 13)
    // ========================================================================
    /// Integer literal (ICInt)
    Int {
        ty: IType,
        value: IntLiteral,
    },

    /// Real/floating-point literal (ICReal)
    Real {
        ty: IType,
        value: f64,
    },

    /// String literal (ICString)
    String {
        ty: IType,
        value: String,
    },

    /// Character literal (ICChar)
    Char {
        ty: IType,
        value: char,
    },

    // ========================================================================
    // Handles (ordC 14)
    // ========================================================================
    /// File/IO handle (ICHandle)
    Handle {
        ty: IType,
        // In Haskell this is Handle from System.IO
        // We use an opaque identifier
        handle_id: i64,
    },

    // ========================================================================
    // State and module ports (ordC 15, 16, 17, 18)
    // ========================================================================
    /// State variable (ICStateVar)
    StateVar {
        ty: IType,
        var: IStateVar,
    },

    /// Method argument placeholder (ICMethArg)
    MethArg {
        ty: IType,
    },

    /// Module port - dynamic inputs including clock/reset wires (ICModPort)
    ModPort {
        ty: IType,
    },

    /// Module parameter (ICModParam)
    ModParam {
        ty: IType,
    },

    // ========================================================================
    // Interface (ordC 20)
    // ========================================================================
    /// Interface definition (ICIFace)
    IFace {
        ty: IType,
        ifc_ty_id: Id,
        /// (method_id, index, is_action)
        ifc_ids: Vec<(Id, i64, bool)>,
    },

    // ========================================================================
    // Scheduling pragmas (ordC 21, 22)
    // ========================================================================
    /// Rule assertions (ICRuleAssert)
    RuleAssert {
        ty: IType,
        asserts: Vec<RulePragma>,
    },

    /// Schedule pragmas (ICSchedPragmas)
    SchedPragmas {
        ty: IType,
        pragmas: Vec<CSchedulePragma>,
    },

    // ========================================================================
    // Clock, Reset, Inout (ordC 23, 24, 25)
    // ========================================================================
    /// Clock (ICClock)
    Clock {
        ty: IType,
        clock: IClock,
    },

    /// Reset (ICReset)
    Reset {
        ty: IType,
        reset: IReset,
    },

    /// Inout (bidirectional) port (ICInout)
    Inout {
        ty: IType,
        inout: IInout,
    },

    // ========================================================================
    // Arrays (ordC 26)
    // ========================================================================
    /// Lazy array (ICLazyArray)
    /// Elements are references during IExpand, converted after
    LazyArray {
        ty: IType,
        array: ILazyArray,
        uninit: Option<(Box<IExpr>, Box<IExpr>)>,
    },

    // ========================================================================
    // Metadata (ordC 27, 28, 29)
    // ========================================================================
    /// Name reference (ICName)
    Name {
        ty: IType,
        name: Id,
    },

    /// Attributes (ICAttrib)
    Attrib {
        ty: IType,
        attributes: Vec<(Position, PProp)>,
    },

    /// Position information (ICPosition)
    Position {
        ty: IType,
        positions: Vec<Position>,
    },

    // ========================================================================
    // Type-level (ordC 30, 31)
    // ========================================================================
    /// Type as a value (ICType)
    Type {
        ty: IType,
        inner_type: IType,
    },

    /// Predicate (ICPred)
    Pred {
        ty: IType,
        pred: IPred,
    },
}

impl IConInfo {
    /// Get the type of this constant/constructor.
    #[must_use]
    pub fn ty(&self) -> &IType {
        match self {
            IConInfo::Def { ty, .. }
            | IConInfo::Value { ty, .. }
            | IConInfo::Prim { ty, .. }
            | IConInfo::Foreign { ty, .. }
            | IConInfo::Con { ty, .. }
            | IConInfo::Is { ty, .. }
            | IConInfo::Out { ty, .. }
            | IConInfo::Tuple { ty, .. }
            | IConInfo::Sel { ty, .. }
            | IConInfo::Verilog { ty, .. }
            | IConInfo::Undet { ty, .. }
            | IConInfo::Int { ty, .. }
            | IConInfo::Real { ty, .. }
            | IConInfo::String { ty, .. }
            | IConInfo::Char { ty, .. }
            | IConInfo::Handle { ty, .. }
            | IConInfo::StateVar { ty, .. }
            | IConInfo::MethArg { ty }
            | IConInfo::ModPort { ty }
            | IConInfo::ModParam { ty }
            | IConInfo::IFace { ty, .. }
            | IConInfo::RuleAssert { ty, .. }
            | IConInfo::SchedPragmas { ty, .. }
            | IConInfo::Clock { ty, .. }
            | IConInfo::Reset { ty, .. }
            | IConInfo::Inout { ty, .. }
            | IConInfo::LazyArray { ty, .. }
            | IConInfo::Name { ty, .. }
            | IConInfo::Attrib { ty, .. }
            | IConInfo::Position { ty, .. }
            | IConInfo::Type { ty, .. }
            | IConInfo::Pred { ty, .. } => ty,
        }
    }

    /// Get the ordinal for this variant (matches Haskell ordC).
    #[must_use]
    pub fn ord(&self) -> u8 {
        match self {
            IConInfo::Def { .. } => 0,
            IConInfo::Prim { .. } => 1,
            IConInfo::Foreign { .. } => 2,
            IConInfo::Con { .. } => 3,
            IConInfo::Is { .. } => 4,
            IConInfo::Out { .. } => 5,
            IConInfo::Tuple { .. } => 6,
            IConInfo::Sel { .. } => 7,
            IConInfo::Verilog { .. } => 8,
            IConInfo::Undet { .. } => 9,
            IConInfo::Int { .. } => 10,
            IConInfo::Real { .. } => 11,
            IConInfo::String { .. } => 12,
            IConInfo::Char { .. } => 13,
            IConInfo::Handle { .. } => 14,
            IConInfo::StateVar { .. } => 15,
            IConInfo::MethArg { .. } => 16,
            IConInfo::ModPort { .. } => 17,
            IConInfo::ModParam { .. } => 18,
            IConInfo::Value { .. } => 19,
            IConInfo::IFace { .. } => 20,
            IConInfo::RuleAssert { .. } => 21,
            IConInfo::SchedPragmas { .. } => 22,
            IConInfo::Clock { .. } => 23,
            IConInfo::Reset { .. } => 24,
            IConInfo::Inout { .. } => 25,
            IConInfo::LazyArray { .. } => 26,
            IConInfo::Name { .. } => 27,
            IConInfo::Attrib { .. } => 28,
            IConInfo::Position { .. } => 29,
            IConInfo::Type { .. } => 30,
            IConInfo::Pred { .. } => 31,
        }
    }

    /// Check if this is an integer constant.
    #[must_use]
    pub fn is_int(&self) -> bool {
        matches!(self, IConInfo::Int { .. })
    }

    /// Check if this is a real constant.
    #[must_use]
    pub fn is_real(&self) -> bool {
        matches!(self, IConInfo::Real { .. })
    }

    /// Check if this is a module parameter.
    #[must_use]
    pub fn is_param(&self) -> bool {
        matches!(self, IConInfo::ModParam { .. })
    }
}

// ============================================================================
// Supporting Types for IConInfo
// ============================================================================

/// Constructor tag information.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ConTagInfo {
    /// Position of constructor in the data type
    pub con_no: i64,
    /// Total number of constructors in the data type
    pub num_con: i64,
    /// Tag value when packed
    pub con_tag: i64,
    /// Bits required to represent the tag
    pub tag_size: i64,
}

/// Primitive operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum PrimOp {
    // Arithmetic
    Add,
    Sub,
    Mul,
    Quot,
    Rem,
    Neg,
    Abs,
    SignExt,
    ZeroExt,

    // Bitwise
    And,
    Or,
    Xor,
    Not,
    Inv,

    // Shifts
    Shl,
    Shr,
    Sra,

    // Comparisons
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,

    // Bit operations
    Extract,
    Concat,
    Truncate,
    Split,

    // Conversions
    ToReal,
    FromReal,

    // Conditionals
    If,
    Case,
    ArrayDynSelect,
    ArrayDynUpdate,

    // Actions
    Return,
    Bind,
    JoinActions,
    NoActions,
    ActionValue,
    ActionValueRet,

    // Registers
    RegRead,
    RegWrite,

    // Array operations
    BuildArray,
    ArrayLength,
    ArraySelect,
    ArrayUpdate,

    // Primitives for strings/names
    StringEq,
    StringConcat,

    // Special
    Error,
    Message,
    UndefinedValue,
    RawUndefinedValue,

    // Simulation
    Finish,
    Stop,
    Display,
    DisplayHex,
    Write,

    // Type-related
    TypeOf,
    Bits,
    Unpack,
    Pack,

    // Clock/Reset
    ClockEq,
    ResetEq,
    SameClock,
    IsAncestorClock,
    ClockOf,
    ResetOf,

    // Misc
    ParAction,
    ParActionValue,
    Seq,
    SeqCond,
    ExpIf,
}

/// Foreign port direction/info.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ForeignPort {
    pub name: String,
    pub ty: IType,
}

/// Verilog module information.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct VModInfo {
    /// Module name
    pub name: String,
    /// Clock ports
    pub clock_ports: Vec<VClockPort>,
    /// Reset ports
    pub reset_ports: Vec<VResetPort>,
    /// Argument ports
    pub arg_ports: Vec<VArgPort>,
    /// Interface fields
    pub fields: Vec<VFieldInfo>,
    /// Schedule information
    pub schedule: VSchedInfo,
}

/// Verilog clock port.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct VClockPort {
    pub name: String,
    pub gate: Option<String>,
}

/// Verilog reset port.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct VResetPort {
    pub name: String,
}

/// Verilog argument port.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct VArgPort {
    pub name: String,
    pub ports: Vec<String>,
}

/// Verilog field information.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct VFieldInfo {
    /// Field name
    pub name: Id,
    /// Clock index
    pub clock: Option<usize>,
    /// Reset index
    pub reset: Option<usize>,
    /// Port multiplicity
    pub mult: i64,
    /// Input ports
    pub inputs: Vec<VPort>,
    /// Output port
    pub output: Option<VPort>,
    /// Enable port
    pub enable: Option<String>,
    /// Ready port
    pub ready: Option<String>,
}

/// Verilog port.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct VPort {
    pub name: String,
    pub size: i64,
}

/// Verilog schedule information.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct VSchedInfo {
    /// Conflict-free pairs
    pub cf: Vec<(Id, Id)>,
    /// Sequentially composable pairs (first before second)
    pub sb: Vec<(Id, Id)>,
    /// Mutually exclusive pairs
    pub me: Vec<(Id, Id)>,
}

/// Property (used in attributes).
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum PProp {
    /// Named property
    Named(String),
    /// Integer property
    Int(String, i64),
    /// String property
    String(String, String),
}

/// A predicate (type class constraint).
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct IPred {
    /// Class name
    pub class: Id,
    /// Type arguments
    pub args: Vec<IType>,
}

/// Lazy array type.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ILazyArray {
    /// Array elements (as expression references)
    pub elements: Vec<Box<IExpr>>,
}

// ============================================================================
// Clock, Reset, Inout Infrastructure
// ============================================================================

/// Unique identifier for clocks.
pub type ClockId = i64;

/// Clock domain identifier.
pub type ClockDomain = i64;

/// Unique identifier for resets.
pub type ResetId = i64;

/// Clock representation in ISyntax.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct IClock {
    /// Unique clock ID
    pub id: ClockId,
    /// Clock domain (for related clocks)
    pub domain: ClockDomain,
    /// Expression for clock wires
    /// Will be ICSel of ICStateVar, or ICTuple of ICModPorts/ICInt(1) for ungated clocks
    pub wires: Box<IExpr>,
}

/// Reset representation in ISyntax.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct IReset {
    /// Unique reset ID
    pub id: ResetId,
    /// Associated clock (may be noClock)
    pub clock: IClock,
    /// Expression for reset wire
    /// Currently must be ICModPort or 0
    pub wire: Box<IExpr>,
}

/// Inout (bidirectional) port representation.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct IInout {
    /// Associated clock (may be noClock)
    pub clock: IClock,
    /// Associated reset (may be noReset)
    pub reset: IReset,
    /// Expression for inout wire
    pub wire: Box<IExpr>,
}

/// State variable (foreign module instantiation).
///
/// Mirrors `IStateVar` from ISyntax.hs exactly:
/// ```haskell
/// data IStateVar a = IStateVar {
///     isv_is_arg :: Bool,
///     isv_is_user_import :: Bool,
///     isv_uid :: Int,
///     isv_vmi :: VModInfo,
///     isv_iargs :: [IExpr a],
///     isv_type :: IType,
///     isv_meth_types :: [[IType]],
///     isv_clocks :: [(Id, IClock a)],
///     isv_resets :: [(Id, IReset a)],
///     isv_isloc :: IStateLoc
/// }
/// ```
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct IStateVar {
    /// Is this a real state variable (vs argument)?
    pub is_arg: bool,
    /// Is this a user-imported foreign module?
    pub is_user_import: bool,
    /// Unique identifier
    pub uid: i64,
    /// Verilog module info
    pub vmi: VModInfo,
    /// Parameters and arguments
    pub iargs: Vec<IExpr>,
    /// Type of the state variable (like "Prelude.VReg")
    pub ty: IType,
    /// Method types (corresponds to vFields in VModInfo)
    pub meth_types: Vec<Vec<IType>>,
    /// Named clocks
    pub clocks: Vec<(Id, IClock)>,
    /// Named resets
    pub resets: Vec<(Id, IReset)>,
    /// Instantiation path
    pub state_loc: IStateLoc,
}

// ============================================================================
// Types and Kinds
// ============================================================================

/// A type in internal syntax.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum IType {
    /// Type variable
    Var(ITyVar),
    /// Type constructor
    Con(ITyCon),
    /// Type application
    App(Box<IType>, Box<IType>),
    /// Generic type variable (bound by forall)
    /// Uses i64 to match Haskell Int semantics.
    Gen(i64),
}

/// A type variable.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ITyVar {
    /// Variable name
    pub name: Id,
    /// Unique number
    pub num: u32,
    /// Kind
    pub kind: IKind,
}

/// A type constructor.
///
/// Mirrors Haskell ISyntax types. Uses BigInt for numeric literals to match
/// Haskell's unbounded Integer type.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ITyCon {
    /// Named type constructor
    Named(ITyConInfo),
    /// Numeric type literal (uses BigInt for Haskell Integer compatibility)
    Num(num_bigint::BigInt),
    /// String type literal
    Str(String),
}

/// Type constructor info.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ITyConInfo {
    /// Constructor name
    pub name: Id,
    /// Kind
    pub kind: IKind,
    /// Type sort (how it was defined)
    pub sort: ITySort,
}

/// How a type was defined.
///
/// Mirrors Haskell ISyntax. Uses BigInt for arity to match Haskell Integer.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ITySort {
    /// Type synonym (with arity and expansion)
    /// Arity uses BigInt to match Haskell's unbounded Integer.
    Synonym(num_bigint::BigInt, Box<IType>),
    /// Data type (with constructor names)
    Data(Vec<Id>),
    /// Struct type (with field names)
    Struct(Vec<Id>),
    /// Abstract/primitive type
    Abstract,
}

/// A kind.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum IKind {
    /// Type kind (*)
    Star,
    /// Numeric kind (#)
    Num,
    /// String kind ($)
    Str,
    /// Function kind
    Fun(Box<IKind>, Box<IKind>),
    /// Kind variable (during inference)
    Var(u32),
}

impl IKind {
    /// Check if this is a simple (non-function) kind.
    #[must_use]
    pub fn is_simple(&self) -> bool {
        matches!(self, IKind::Star | IKind::Num | IKind::Str)
    }

    /// Count the arity of a function kind.
    #[must_use]
    pub fn arity(&self) -> u32 {
        match self {
            IKind::Fun(_, k) => 1 + k.arity(),
            _ => 0,
        }
    }
}

// ============================================================================
// Module (elaborated)
// ============================================================================

/// An elaborated module.
///
/// Mirrors `IModule` from ISyntax.hs:136-168.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct IModule {
    /// Module name
    pub name: Id,
    /// Whether this module is wrapped
    pub is_wrapped: bool,
    /// Backend-specific information
    pub backend: Option<Backend>,
    /// External wires info
    pub external_wires: VWireInfo,
    /// Module pragmas
    pub pragmas: Vec<IPragma>,
    /// Type arguments
    pub type_args: Vec<(Id, IKind)>,
    /// Wire arguments (abstract inputs)
    pub wire_args: Vec<IAbstractInput>,
    /// Clock domains with their clocks
    pub clock_domains: Vec<(ClockDomain, Vec<IClock>)>,
    /// Resets
    pub resets: Vec<IReset>,
    /// State instantiations (submodules)
    pub state_insts: Vec<(Id, IStateVar)>,
    /// Port type map
    pub port_types: PortTypeMap,
    /// Local definitions
    pub local_defs: Vec<IDef>,
    /// Rules (with pragmas)
    pub rules: IRules,
    /// Interface faces/methods
    pub interface: Vec<IEFace>,
    /// `imod_ffcallNo :: Int` - Foreign function call counter
    /// Uses i64 to match Haskell Int semantics.
    pub ffcall_no: i64,
    /// Instance comments
    pub instance_comments: Vec<(Id, Vec<String>)>,
}

/// Backend identifier.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Backend {
    Verilog,
    Bluesim,
    C,
}

/// Wire info for module boundary.
#[derive(Debug, Clone, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct VWireInfo {
    /// Clock wires
    pub clocks: Vec<VClockWire>,
    /// Reset wires
    pub resets: Vec<VResetWire>,
    /// Inout wires
    pub inouts: Vec<VInoutWire>,
    /// Argument wires
    pub args: Vec<VArgWire>,
}

/// Clock wire at module boundary.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct VClockWire {
    pub name: String,
    pub id: ClockId,
}

/// Reset wire at module boundary.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct VResetWire {
    pub name: String,
    pub id: ResetId,
}

/// Inout wire at module boundary.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct VInoutWire {
    pub name: String,
}

/// Argument wire at module boundary.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct VArgWire {
    pub name: String,
    pub ty: IType,
}

/// Abstract input to a module.
///
/// Mirrors `IAbstractInput` from ISyntax.hs exactly:
/// ```haskell
/// data IAbstractInput =
///     IAI_Port (Id, IType) |       -- simple input using one port
///     IAI_Clock Id (Maybe Id) |    -- clock osc and maybe gate
///     IAI_Reset Id |
///     IAI_Inout Id Integer         -- with width
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum IAbstractInput {
    /// Simple port input (id, type)
    Port(Id, IType),
    /// Clock input with oscillator and optional gate
    Clock {
        /// Clock oscillator identifier
        oscillator: Id,
        /// Optional clock gate identifier
        gate: Option<Id>,
    },
    /// Reset input
    Reset(Id),
    /// `IAI_Inout Id Integer` - Inout (bidirectional) input with width
    Inout {
        /// Inout identifier
        name: Id,
        /// Width in bits (Haskell Integer → BigInt for strict alignment)
        width: num_bigint::BigInt,
    },
}

/// Port type map.
pub type PortTypeMap = Vec<(Id, IType)>;

/// A state element in a module (old-style, kept for compatibility).
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct IStateElement {
    /// Name
    pub name: Id,
    /// Type
    pub ty: IType,
    /// Initialization
    pub init: IExpr,
}

/// Rules collection with scheduling pragmas.
///
/// Mirrors `IRules` from ISyntax.hs:192.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct IRules {
    /// Schedule pragmas
    pub pragmas: Vec<ISchedulePragma>,
    /// Rules
    pub rules: Vec<IRule>,
}

/// Schedule pragma for internal syntax.
///
/// Mirrors `ISchedulePragma` from ISyntax.hs.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ISchedulePragma {
    /// Mutually exclusive rules
    MutuallyExclusive(Vec<Id>),
    /// Conflict free rules
    ConflictFree(Vec<Id>),
    /// Preemption
    Preempt(Vec<Id>, Vec<Id>),
    /// Scheduling order
    Before(Vec<Id>, Vec<Id>),
    /// Execution order
    ExecutionOrder(Vec<Id>),
}

/// A rule.
///
/// Mirrors `IRule` from ISyntax.hs:196-209.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct IRule {
    /// Rule name
    pub name: Id,
    /// Rule pragmas
    pub pragmas: Vec<RulePragma>,
    /// Description string
    pub description: String,
    /// Wire properties
    pub wire_properties: WireProps,
    /// Condition (guard)
    pub condition: IExpr,
    /// Body
    pub body: IExpr,
    /// Original rule name (if split)
    pub original: Option<Id>,
    /// State location (instantiation path)
    pub state_loc: IStateLoc,
}

/// Wire properties for methods and rules.
///
/// Mirrors `WireProps` from ISyntax.hs.
#[derive(Debug, Clone, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct WireProps {
    /// Clock domain
    pub clock: Option<IClock>,
    /// Reset
    pub reset: Option<IReset>,
}

/// Name generation state.
///
/// Mirrors `NameGenerate` from IStateLoc.hs exactly:
/// ```haskell
/// data NameGenerate = NameEmpty           -- No name so far
///                   | NameIndex [Integer] -- loop indexes
///                   | Name Id             -- a real name
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum NameGenerate {
    /// No name so far
    Empty,
    /// Loop indexes
    Index(Vec<i64>),
    /// A real name
    Name(Id),
}

/// State location path component.
///
/// Mirrors `IStateLocPathComponent` from IStateLoc.hs exactly:
/// ```haskell
/// data IStateLocPathComponent = IStateLocPathComponent {
///   isl_inst_id :: Id,
///   isl_ifc_id :: Id,
///   isl_ifc_type :: IType,
///   isl_vector :: Bool,
///   isl_inst_ignore :: Bool,
///   isl_inst_ignore_name :: Bool,
///   isl_ifc_skip :: Bool,
///   isl_unique_index :: Maybe Integer,
///   isl_prefix :: NameGenerate,
///   isl_loop_suffix :: NameGenerate
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct IStateLocPathComponent {
    /// Instance id (from SV instantiation or <- syntax)
    pub inst_id: Id,
    /// Interface id (used in source code to access module)
    pub ifc_id: Id,
    /// Interface type
    pub ifc_type: IType,
    /// Is a vector name
    pub vector: bool,
    /// Instance may be eliminated from the istateloc
    pub inst_ignore: bool,
    /// Instance id is ignored when making a hierarchical name
    pub inst_ignore_name: bool,
    /// Skip this level in the rule name scope lookup
    pub ifc_skip: bool,
    /// Unique index to uniquify InstTree (loops, common names)
    /// Nothing if not unique, otherwise disambiguating integer
    pub unique_index: Option<i64>,
    /// Currently computed hierarchical prefix
    pub prefix: NameGenerate,
    /// Loop indexes to add once a "real" name is found
    pub loop_suffix: NameGenerate,
}

/// State location - path through instantiation hierarchy.
///
/// Mirrors `type IStateLoc = [IStateLocPathComponent]` from IStateLoc.hs.
/// Lowest level of hierarchy is at the head.
pub type IStateLoc = Vec<IStateLocPathComponent>;

/// Interface face (method or subinterface).
///
/// Mirrors `IEFace` from ISyntax.hs:212-221.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct IEFace {
    /// Method/face name
    pub name: Id,
    /// Arguments with types
    pub args: Vec<(Id, IType)>,
    /// Value (expression and type) - None for action methods
    pub value: Option<(IExpr, IType)>,
    /// Rules body (for action/actionvalue methods)
    pub body: Option<IRules>,
    /// Wire properties (clock/reset)
    pub wire_props: WireProps,
    /// Field info (for Verilog generation)
    pub field_info: VFieldInfo,
}

/// Interface definition (legacy, kept for compatibility).
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct IInterface {
    /// Interface type
    pub ty: IType,
    /// Methods
    pub methods: Vec<IMethod>,
}

/// An interface method (legacy, kept for compatibility).
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct IMethod {
    /// Method name
    pub name: Id,
    /// Method type
    pub ty: IType,
    /// Method body
    pub body: IExpr,
    /// Implicit condition
    pub condition: Option<IExpr>,
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_kind_arity() {
        let k = IKind::Star;
        assert_eq!(k.arity(), 0);

        let k = IKind::Fun(Box::new(IKind::Star), Box::new(IKind::Star));
        assert_eq!(k.arity(), 1);

        let k = IKind::Fun(
            Box::new(IKind::Star),
            Box::new(IKind::Fun(Box::new(IKind::Num), Box::new(IKind::Star))),
        );
        assert_eq!(k.arity(), 2);
    }

    #[test]
    fn test_icon_info_ord() {
        let ty = IType::Con(ITyCon::Num(num_bigint::BigInt::from(0)));

        let int_con = IConInfo::Int {
            ty: ty.clone(),
            value: IntLiteral::decimal(42),
        };
        assert_eq!(int_con.ord(), 10);
        assert!(int_con.is_int());

        let prim_con = IConInfo::Prim {
            ty: ty.clone(),
            op: PrimOp::Add,
        };
        assert_eq!(prim_con.ord(), 1);
    }
}
