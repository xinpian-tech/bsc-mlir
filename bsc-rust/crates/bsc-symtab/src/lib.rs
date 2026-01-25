//! Symbol table for BSC (Bluespec Compiler).
//!
//! Mirrors `src/comp/SymTab.hs` from the Haskell implementation.
//!
//! The symbol table stores information about:
//! - Variables (functions, values, primitives, foreign imports)
//! - Types (data types, type synonyms, structs, interfaces, abstract types)
//! - Constructors (data constructors with tag information)
//! - Fields (struct/interface fields with type info)
//! - Type classes (with superclasses, methods, and instances)

use bsc_syntax::{CClause, CType, IKind, IType, Id};
use bsc_types::{Kind, Pred, QualType, Type};
use rustc_hash::FxHashMap;
use std::fmt;

// ============================================================================
// Error types
// ============================================================================

/// Errors that can occur during symbol table operations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SymTabError {
    /// Variable not found
    VarNotFound(Id),
    /// Type not found
    TypeNotFound(Id),
    /// Constructor not found
    ConNotFound(Id),
    /// Field not found
    FieldNotFound(Id),
    /// Class not found
    ClassNotFound(Id),
}

impl fmt::Display for SymTabError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SymTabError::VarNotFound(id) => write!(f, "variable not found: {id}"),
            SymTabError::TypeNotFound(id) => write!(f, "type not found: {id}"),
            SymTabError::ConNotFound(id) => write!(f, "constructor not found: {id}"),
            SymTabError::FieldNotFound(id) => write!(f, "field not found: {id}"),
            SymTabError::ClassNotFound(id) => write!(f, "class not found: {id}"),
        }
    }
}

impl std::error::Error for SymTabError {}

/// Result type for symbol table operations.
pub type SymTabResult<T> = Result<T, SymTabError>;

// ============================================================================
// Scheme - Type scheme (mirrors Scheme.hs)
// ============================================================================

/// A type scheme - a possibly polymorphic type.
///
/// Mirrors the Haskell `Scheme` type from `Scheme.hs`.
/// `Forall ks qt` represents a type polymorphic over type variables
/// with the given kinds, where the variables are referenced as `TGen n`.
#[derive(Debug, Clone, PartialEq)]
pub struct Scheme {
    /// Kinds of quantified type variables (referenced by index)
    pub kinds: Vec<Kind>,
    /// The qualified type (predicates :=> type)
    pub qual_type: QualType,
}

impl Scheme {
    /// Create a monomorphic scheme (no quantified variables).
    #[must_use]
    pub fn mono(ty: Type) -> Self {
        Scheme {
            kinds: Vec::new(),
            qual_type: QualType::unqualified(ty),
        }
    }

    /// Create a scheme with the given kinds and qualified type.
    #[must_use]
    pub fn forall(kinds: Vec<Kind>, qual_type: QualType) -> Self {
        Scheme { kinds, qual_type }
    }

    /// Check if this scheme is monomorphic (no quantified variables).
    #[must_use]
    pub fn is_mono(&self) -> bool {
        self.kinds.is_empty()
    }

    /// Get the underlying type.
    #[must_use]
    pub fn ty(&self) -> &Type {
        &self.qual_type.ty
    }

    /// Get the predicates (constraints).
    #[must_use]
    pub fn preds(&self) -> &[Pred] {
        &self.qual_type.preds
    }
}

impl fmt::Display for Scheme {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.kinds.is_empty() {
            write!(f, "{}", self.qual_type)
        } else {
            write!(f, "forall")?;
            for (i, k) in self.kinds.iter().enumerate() {
                write!(f, " (t{i} :: {k})")?;
            }
            write!(f, ". {}", self.qual_type)
        }
    }
}

// ============================================================================
// Assump - Type assumption (mirrors Assump.hs)
// ============================================================================

/// An assumption - a binding of an identifier to a type scheme.
///
/// Mirrors the Haskell `Assump` type from `Assump.hs`.
/// Written as `id :>: scheme` in Haskell.
#[derive(Debug, Clone, PartialEq)]
pub struct Assump {
    /// The identifier
    pub id: Id,
    /// The type scheme
    pub scheme: Scheme,
}

impl Assump {
    /// Create a new assumption.
    #[must_use]
    pub fn new(id: Id, scheme: Scheme) -> Self {
        Assump { id, scheme }
    }

    /// Create a monomorphic assumption (no quantified variables).
    #[must_use]
    pub fn mono(id: Id, ty: Type) -> Self {
        Assump {
            id,
            scheme: Scheme::mono(ty),
        }
    }
}

impl fmt::Display for Assump {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} :>: {}", self.id, self.scheme)
    }
}

// ============================================================================
// TISort - Type Info Sort (mirrors CType.hs)
// ============================================================================

/// The sort/kind of a type in the symbol table.
///
/// Mirrors the Haskell `TISort` type from `CType.hs`.
#[derive(Debug, Clone, PartialEq)]
pub enum TISort {
    /// Type synonym: `type T a = Body`
    Synonym {
        /// Number of type parameters
        arity: i64,
        /// The expansion
        body: CType,
    },
    /// Data type: `data T = C1 | C2 ...`
    Data {
        /// Constructor names
        constructors: Vec<Id>,
        /// Is this an enum (all constructors have no arguments)?
        is_enum: bool,
    },
    /// Struct/interface/class type
    Struct {
        /// Sub-type classification
        subtype: StructSubType,
        /// Field names
        fields: Vec<Id>,
    },
    /// Primitive abstract type (Integer, Bit, Module, etc.)
    Abstract,
}

/// Sub-categories of struct types.
///
/// Mirrors the Haskell `StructSubType` from `CType.hs`.
#[derive(Debug, Clone, PartialEq)]
pub enum StructSubType {
    /// Regular struct
    Struct,
    /// Type class dictionary
    Class,
    /// Data constructor with record fields
    DataCon {
        /// Data constructor identifier
        con_id: Id,
        /// Whether fields are named
        has_named_fields: bool,
    },
    /// Interface type
    ///
    /// Mirrors `SInterface [IfcPragma]` from CType.hs:132.
    Interface(Vec<IfcPragma>),
    /// Polymorphic wrapper type
    PolyWrap {
        /// Name of the type with the wrapped field
        type_id: Id,
        /// Name of the data constructor (if any)
        ctor: Option<Id>,
        /// Name of the wrapped field
        field: Id,
    },
}

/// Interface pragmas (simplified from Pragma.hs).
#[derive(Debug, Clone, PartialEq)]
pub enum IfcPragma {
    /// Prefix for method signals
    Prefix(String),
    /// Result signal name
    Result(String),
    /// Ready signal name
    Ready(String),
    /// Enable signal name
    Enable(String),
    /// Argument names
    ArgNames(Vec<Id>),
    /// Always ready
    AlwaysReady,
    /// Always enabled
    AlwaysEnabled,
}

// ============================================================================
// ConTagInfo - Constructor tag metadata (mirrors ConTagInfo.hs)
// ============================================================================

/// Constructor and tag metadata for data constructors.
///
/// Mirrors the Haskell `ConTagInfo` from `ConTagInfo.hs`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ConTagInfo {
    /// Position of constructor in declaration (0-indexed)
    pub con_no: i64,
    /// Total number of constructors
    pub num_con: i64,
    /// Tag value when packed
    pub con_tag: i64,
    /// Bits required to represent the tag
    pub tag_size: i64,
}

impl ConTagInfo {
    /// Create a new `ConTagInfo` with default tag values.
    ///
    /// The tag defaults to the constructor number, and tag size is
    /// calculated as ceil(log2(num_con)).
    #[must_use]
    pub fn new(con_no: i64, num_con: i64) -> Self {
        let tag_size = if num_con <= 1 {
            0
        } else {
            // ceil(log2(num_con))
            64 - (num_con - 1).leading_zeros() as i64
        };
        ConTagInfo {
            con_no,
            num_con,
            con_tag: con_no,
            tag_size,
        }
    }

    /// Create a `ConTagInfo` with custom tag value and size.
    #[must_use]
    pub fn with_custom_tag(con_no: i64, num_con: i64, con_tag: i64, tag_size: i64) -> Self {
        ConTagInfo {
            con_no,
            num_con,
            con_tag,
            tag_size,
        }
    }

    /// Check if this is a single constructor type (no tag needed).
    #[must_use]
    pub fn is_single(&self) -> bool {
        self.num_con == 1
    }
}

impl fmt::Display for ConTagInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "({} of {}, tag = {} :: Bit {})",
            self.con_no, self.num_con, self.con_tag, self.tag_size
        )
    }
}

// ============================================================================
// VarKind - Variable kinds (mirrors SymTab.hs)
// ============================================================================

/// The kind of a variable binding.
///
/// Mirrors the Haskell `VarKind` from `SymTab.hs`.
#[derive(Debug, Clone, PartialEq)]
pub enum VarKind {
    /// Primitive built-in
    Prim,
    /// User-defined value
    Defn,
    /// Method of a type class
    Meth,
    /// Foreign import/export
    Foreign {
        /// Foreign link name
        link_name: String,
        /// For Verilog foreign funcs: (input ports, output ports)
        verilog_ports: Option<(Vec<String>, Vec<String>)>,
    },
}

// ============================================================================
// VarInfo - Variable information (mirrors SymTab.hs)
// ============================================================================

/// Information about a variable in the symbol table.
///
/// Mirrors the Haskell `VarInfo` from `SymTab.hs`.
#[derive(Debug, Clone, PartialEq)]
pub struct VarInfo {
    /// The kind of variable (primitive, definition, method, foreign)
    pub kind: VarKind,
    /// The type assumption (id :>: scheme)
    pub assump: Assump,
    /// Deprecation message if this identifier is deprecated
    pub deprecated: Option<String>,
}

impl VarInfo {
    /// Create a new `VarInfo`.
    #[must_use]
    pub fn new(kind: VarKind, assump: Assump) -> Self {
        VarInfo {
            kind,
            assump,
            deprecated: None,
        }
    }

    /// Create a new `VarInfo` with a deprecation message.
    #[must_use]
    pub fn deprecated(kind: VarKind, assump: Assump, message: String) -> Self {
        VarInfo {
            kind,
            assump,
            deprecated: Some(message),
        }
    }

    /// Check if this variable is deprecated.
    #[must_use]
    pub fn is_deprecated(&self) -> bool {
        self.deprecated.is_some()
    }
}

// ============================================================================
// TypeInfo - Type information (mirrors SymTab.hs)
// ============================================================================

/// Information about a type in the symbol table.
///
/// Mirrors the Haskell `TypeInfo` from `SymTab.hs`.
#[derive(Debug, Clone, PartialEq)]
pub struct TypeInfo {
    /// Qualified name (None for numeric/string literal types)
    pub qualified_id: Option<Id>,
    /// Kind of the type constructor
    pub kind: Kind,
    /// Type variable parameters
    pub type_vars: Vec<Id>,
    /// The sort of type (synonym, data, struct, abstract)
    pub sort: TISort,
}

impl TypeInfo {
    /// Create a new `TypeInfo`.
    #[must_use]
    pub fn new(qualified_id: Option<Id>, kind: Kind, type_vars: Vec<Id>, sort: TISort) -> Self {
        TypeInfo {
            qualified_id,
            kind,
            type_vars,
            sort,
        }
    }

    /// Create info for an abstract type.
    #[must_use]
    pub fn abstract_type(qualified_id: Id, kind: Kind) -> Self {
        TypeInfo {
            qualified_id: Some(qualified_id),
            kind,
            type_vars: Vec::new(),
            sort: TISort::Abstract,
        }
    }

    /// Create info for a type synonym.
    #[must_use]
    pub fn synonym(qualified_id: Id, kind: Kind, type_vars: Vec<Id>, body: CType) -> Self {
        let arity = type_vars.len() as i64;
        TypeInfo {
            qualified_id: Some(qualified_id),
            kind,
            type_vars,
            sort: TISort::Synonym { arity, body },
        }
    }

    /// Create info for a data type.
    #[must_use]
    pub fn data_type(
        qualified_id: Id,
        kind: Kind,
        type_vars: Vec<Id>,
        constructors: Vec<Id>,
        is_enum: bool,
    ) -> Self {
        TypeInfo {
            qualified_id: Some(qualified_id),
            kind,
            type_vars,
            sort: TISort::Data {
                constructors,
                is_enum,
            },
        }
    }

    /// Create info for a struct type.
    #[must_use]
    pub fn struct_type(qualified_id: Id, kind: Kind, type_vars: Vec<Id>, fields: Vec<Id>) -> Self {
        TypeInfo {
            qualified_id: Some(qualified_id),
            kind,
            type_vars,
            sort: TISort::Struct {
                subtype: StructSubType::Struct,
                fields,
            },
        }
    }

    /// Create info for an interface type.
    #[must_use]
    pub fn interface_type(
        qualified_id: Id,
        kind: Kind,
        type_vars: Vec<Id>,
        fields: Vec<Id>,
        pragmas: Vec<IfcPragma>,
    ) -> Self {
        TypeInfo {
            qualified_id: Some(qualified_id),
            kind,
            type_vars,
            sort: TISort::Struct {
                subtype: StructSubType::Interface(pragmas),
                fields,
            },
        }
    }

    /// Check if this is an abstract type (has no visible structure).
    #[must_use]
    pub fn is_abstract(&self) -> bool {
        matches!(self.sort, TISort::Abstract)
    }

    /// Check if this is an interface type.
    #[must_use]
    pub fn is_interface(&self) -> bool {
        matches!(
            self.sort,
            TISort::Struct {
                subtype: StructSubType::Interface(_),
                ..
            }
        )
    }

    /// Get the field names if this is a struct or interface.
    #[must_use]
    pub fn fields(&self) -> Option<&[Id]> {
        match &self.sort {
            TISort::Struct { fields, .. } => Some(fields),
            _ => None,
        }
    }

    /// Get the constructor names if this is a data type.
    #[must_use]
    pub fn constructors(&self) -> Option<&[Id]> {
        match &self.sort {
            TISort::Data { constructors, .. } => Some(constructors),
            _ => None,
        }
    }
}

// ============================================================================
// ConInfo - Constructor information (mirrors SymTab.hs)
// ============================================================================

/// Information about a data constructor in the symbol table.
///
/// Mirrors the Haskell `ConInfo` from `SymTab.hs`.
#[derive(Debug, Clone, PartialEq)]
pub struct ConInfo {
    /// The type this constructor belongs to
    pub type_id: Id,
    /// Whether the constructor is visible to users
    pub visible: bool,
    /// The type assumption
    pub assump: Assump,
    /// Tag and numbering information
    pub tag_info: ConTagInfo,
}

impl ConInfo {
    /// Create a new `ConInfo`.
    #[must_use]
    pub fn new(type_id: Id, visible: bool, assump: Assump, tag_info: ConTagInfo) -> Self {
        ConInfo {
            type_id,
            visible,
            assump,
            tag_info,
        }
    }

    /// Check if two `ConInfo` are equal except for visibility.
    #[must_use]
    pub fn eq_ignoring_visibility(&self, other: &ConInfo) -> bool {
        self.type_id == other.type_id
            && self.assump == other.assump
            && self.tag_info == other.tag_info
    }
}

// ============================================================================
// FieldInfo - Field information (mirrors SymTab.hs)
// ============================================================================

/// Information about a struct/interface field in the symbol table.
///
/// Mirrors the Haskell `FieldInfo` from `SymTab.hs`.
#[derive(Debug, Clone, PartialEq)]
pub struct FieldInfo {
    /// The name of this field
    pub name: Id,
    /// The type that has this field
    pub type_id: Id,
    /// Whether the field is visible to users
    pub visible: bool,
    /// Arity of the containing type
    pub arity: i32,
    /// The type assumption for accessing this field
    pub assump: Assump,
    /// Interface pragmas for this field
    pub pragmas: Vec<IfcPragma>,
    /// Default implementation clauses
    pub default_impl: Vec<CClause>,
    /// Original field type (for wrapped fields)
    pub orig_type: Option<CType>,
}

impl FieldInfo {
    /// Create a new `FieldInfo`.
    #[must_use]
    pub fn new(name: Id, type_id: Id, visible: bool, arity: i32, assump: Assump) -> Self {
        FieldInfo {
            name,
            type_id,
            visible,
            arity,
            assump,
            pragmas: Vec::new(),
            default_impl: Vec::new(),
            orig_type: None,
        }
    }

    /// Add pragmas to the field info.
    #[must_use]
    pub fn with_pragmas(mut self, pragmas: Vec<IfcPragma>) -> Self {
        self.pragmas = pragmas;
        self
    }

    /// Add default implementation to the field info.
    #[must_use]
    pub fn with_default(mut self, clauses: Vec<CClause>) -> Self {
        self.default_impl = clauses;
        self
    }

    /// Add original type to the field info.
    #[must_use]
    pub fn with_orig_type(mut self, ty: CType) -> Self {
        self.orig_type = Some(ty);
        self
    }

    /// Check if two `FieldInfo` are equal except for visibility and default impl.
    #[must_use]
    pub fn eq_ignoring_visibility(&self, other: &FieldInfo) -> bool {
        self.name == other.name
            && self.type_id == other.type_id
            && self.arity == other.arity
            && self.assump == other.assump
            && self.pragmas == other.pragmas
            && self.orig_type == other.orig_type
    }
}

// ============================================================================
// ClassInfo - Type class information (mirrors Pred.hs Class)
// ============================================================================

/// Information about a type class instance.
#[derive(Debug, Clone, PartialEq)]
pub struct Instance {
    /// Context predicates required for this instance
    pub context: Vec<Pred>,
    /// The instance head predicate
    pub head: Pred,
}

impl Instance {
    /// Create a new instance.
    #[must_use]
    pub fn new(context: Vec<Pred>, head: Pred) -> Self {
        Instance { context, head }
    }
}

/// Information about a type class in the symbol table.
///
/// Mirrors parts of the Haskell `Class` type from `Pred.hs`.
#[derive(Debug, Clone, PartialEq)]
pub struct ClassInfo {
    /// Superclass identifiers
    pub supers: Vec<Id>,
    /// The type class parameter
    pub param: Id,
    /// Method identifiers
    pub methods: Vec<Id>,
    /// Known instances
    pub instances: Vec<Instance>,
    /// Functional dependencies: each is a pair (from_indices, to_indices)
    pub fun_deps: Vec<(Vec<usize>, Vec<usize>)>,
    /// Whether the class is commutative (like Add, Mul)
    pub is_commutative: bool,
    /// Incoherence control: None = flag-controlled, Some(true) = always incoherent
    pub allow_incoherent: Option<bool>,
}

impl ClassInfo {
    /// Create a new `ClassInfo`.
    #[must_use]
    pub fn new(supers: Vec<Id>, param: Id, methods: Vec<Id>) -> Self {
        ClassInfo {
            supers,
            param,
            methods,
            instances: Vec::new(),
            fun_deps: Vec::new(),
            is_commutative: false,
            allow_incoherent: None,
        }
    }

    /// Add an instance to this class.
    pub fn add_instance(&mut self, instance: Instance) {
        self.instances.push(instance);
    }

    /// Set functional dependencies.
    #[must_use]
    pub fn with_fun_deps(mut self, fun_deps: Vec<(Vec<usize>, Vec<usize>)>) -> Self {
        self.fun_deps = fun_deps;
        self
    }

    /// Mark this class as commutative.
    #[must_use]
    pub fn commutative(mut self) -> Self {
        self.is_commutative = true;
        self
    }
}

// ============================================================================
// SymTab - The main symbol table (mirrors SymTab.hs)
// ============================================================================

/// The main symbol table structure.
///
/// Mirrors the Haskell `SymTab` from `SymTab.hs`.
/// Stores information about variables, types, constructors, fields, and classes.
#[derive(Debug, Clone, Default)]
pub struct SymTab {
    /// Variable bindings (indexed by both qualified and unqualified names)
    vars: FxHashMap<Id, VarInfo>,
    /// Constructor bindings (multiple constructors can have the same name)
    cons: FxHashMap<Id, Vec<ConInfo>>,
    /// Type bindings
    types: FxHashMap<Id, TypeInfo>,
    /// Field bindings (multiple types can have fields with the same name)
    fields: FxHashMap<Id, Vec<FieldInfo>>,
    /// Type class bindings
    classes: FxHashMap<Id, ClassInfo>,
}

impl SymTab {
    /// Create a new empty symbol table.
    #[must_use]
    pub fn new() -> Self {
        SymTab::default()
    }

    // ========================================================================
    // Variable operations
    // ========================================================================

    /// Add a variable to the symbol table.
    ///
    /// The variable is added under both its qualified and unqualified names.
    pub fn add_var(&mut self, id: Id, info: VarInfo) {
        // Add under the original (possibly qualified) name
        self.vars.insert(id.clone(), info.clone());

        // Also add under unqualified name if it's qualified
        if id.is_qualified() {
            let unqual = Id::unpositioned(id.name().clone());
            self.vars.insert(unqual, info);
        }
    }

    /// Add a variable under only its exact name (no unqualified alias).
    pub fn add_var_qualified(&mut self, id: Id, info: VarInfo) {
        self.vars.insert(id, info);
    }

    /// Look up a variable by name.
    #[must_use]
    pub fn lookup_var(&self, id: &Id) -> Option<&VarInfo> {
        self.vars.get(id)
    }

    /// Look up a variable, returning an error if not found.
    pub fn get_var(&self, id: &Id) -> SymTabResult<&VarInfo> {
        self.vars
            .get(id)
            .ok_or_else(|| SymTabError::VarNotFound(id.clone()))
    }

    /// Check if a variable exists.
    #[must_use]
    pub fn has_var(&self, id: &Id) -> bool {
        self.vars.contains_key(id)
    }

    /// Find a variable by name.
    ///
    /// Alias for `lookup_var` for API compatibility.
    #[must_use]
    pub fn find_var(&self, name: &Id) -> Option<&VarInfo> {
        self.lookup_var(name)
    }

    // ========================================================================
    // Type operations
    // ========================================================================

    /// Add a type to the symbol table.
    ///
    /// If the type already exists, the new info may replace an abstract
    /// export with a full export.
    pub fn add_type(&mut self, id: Id, info: TypeInfo) {
        // Add under the original (possibly qualified) name
        self.types
            .entry(id.clone())
            .and_modify(|existing| {
                // Replace abstract with concrete
                if existing.is_abstract() && !info.is_abstract() {
                    *existing = info.clone();
                }
                // For struct classes, prefer the one with more fields
                else if let (
                    TISort::Struct {
                        subtype: StructSubType::Class,
                        fields: existing_fields,
                    },
                    TISort::Struct {
                        subtype: StructSubType::Class,
                        fields: new_fields,
                    },
                ) = (&existing.sort, &info.sort)
                {
                    if new_fields.len() > existing_fields.len() {
                        *existing = info.clone();
                    }
                }
            })
            .or_insert_with(|| info.clone());

        // Also add under unqualified name if it's qualified
        if id.is_qualified() {
            let unqual = Id::unpositioned(id.name().clone());
            self.types
                .entry(unqual)
                .and_modify(|existing| {
                    if existing.is_abstract() && !info.is_abstract() {
                        *existing = info.clone();
                    }
                })
                .or_insert(info);
        }
    }

    /// Add a type under only its exact name (no unqualified alias).
    pub fn add_type_qualified(&mut self, id: Id, info: TypeInfo) {
        self.types
            .entry(id)
            .and_modify(|existing| {
                if existing.is_abstract() && !info.is_abstract() {
                    *existing = info.clone();
                }
            })
            .or_insert(info);
    }

    /// Look up a type by name.
    #[must_use]
    pub fn lookup_type(&self, id: &Id) -> Option<&TypeInfo> {
        self.types.get(id)
    }

    /// Look up a type, returning an error if not found.
    pub fn get_type(&self, id: &Id) -> SymTabResult<&TypeInfo> {
        self.types
            .get(id)
            .ok_or_else(|| SymTabError::TypeNotFound(id.clone()))
    }

    /// Check if a type exists.
    #[must_use]
    pub fn has_type(&self, id: &Id) -> bool {
        self.types.contains_key(id)
    }

    /// Get all types in the symbol table.
    #[must_use]
    pub fn all_types(&self) -> Vec<(&Id, &TypeInfo)> {
        self.types.iter().collect()
    }

    /// Find a type by name.
    ///
    /// Alias for `lookup_type` for API compatibility.
    #[must_use]
    pub fn find_type(&self, name: &Id) -> Option<&TypeInfo> {
        self.lookup_type(name)
    }

    // ========================================================================
    // Constructor operations
    // ========================================================================

    /// Add a constructor to the symbol table.
    ///
    /// Multiple constructors can have the same name (from different types).
    /// Visible constructors override hidden ones with the same signature.
    pub fn add_con(&mut self, id: Id, info: ConInfo) {
        self.cons
            .entry(id.clone())
            .and_modify(|existing| {
                // Merge: visible entries override hidden ones
                let mut found = false;
                for existing_info in existing.iter_mut() {
                    if existing_info.eq_ignoring_visibility(&info) {
                        if info.visible && !existing_info.visible {
                            *existing_info = info.clone();
                        }
                        found = true;
                        break;
                    }
                }
                if !found {
                    existing.push(info.clone());
                }
            })
            .or_insert_with(|| vec![info.clone()]);

        // Also add under unqualified name if it's qualified
        if id.is_qualified() {
            let unqual = Id::unpositioned(id.name().clone());
            self.cons
                .entry(unqual)
                .and_modify(|existing| {
                    let mut found = false;
                    for existing_info in existing.iter_mut() {
                        if existing_info.eq_ignoring_visibility(&info) {
                            if info.visible && !existing_info.visible {
                                *existing_info = info.clone();
                            }
                            found = true;
                            break;
                        }
                    }
                    if !found {
                        existing.push(info.clone());
                    }
                })
                .or_insert_with(|| vec![info]);
        }
    }

    /// Look up constructors by name.
    ///
    /// Returns all constructors with this name (possibly from different types).
    #[must_use]
    pub fn lookup_con(&self, id: &Id) -> Option<&[ConInfo]> {
        self.cons.get(id).map(Vec::as_slice)
    }

    /// Look up only visible constructors by name.
    #[must_use]
    pub fn lookup_con_visible(&self, id: &Id) -> Option<Vec<&ConInfo>> {
        self.cons
            .get(id)
            .map(|cons| cons.iter().filter(|c| c.visible).collect())
    }

    /// Look up constructors, returning an error if not found.
    pub fn get_con(&self, id: &Id) -> SymTabResult<&[ConInfo]> {
        self.cons
            .get(id)
            .map(Vec::as_slice)
            .ok_or_else(|| SymTabError::ConNotFound(id.clone()))
    }

    /// Check if a constructor exists.
    #[must_use]
    pub fn has_con(&self, id: &Id) -> bool {
        self.cons.contains_key(id)
    }

    /// Find constructors by name.
    ///
    /// Returns all constructors with this name (possibly from different types).
    /// Alias for `lookup_con` for API compatibility.
    #[must_use]
    pub fn find_con(&self, name: &Id) -> Option<&[ConInfo]> {
        self.lookup_con(name)
    }

    /// Find a constructor by name for a specific type.
    ///
    /// Returns the constructor info if found for the given type.
    #[must_use]
    pub fn find_con_for_type(&self, con_name: &Id, type_id: &Id) -> Option<&ConInfo> {
        self.cons
            .get(con_name)
            .and_then(|cons| cons.iter().find(|c| &c.type_id == type_id))
    }

    // ========================================================================
    // Field operations
    // ========================================================================

    /// Add a field to the symbol table.
    ///
    /// Multiple types can have fields with the same name.
    /// Visible fields override hidden ones with the same signature.
    pub fn add_field(&mut self, id: Id, info: FieldInfo) {
        self.fields
            .entry(id.clone())
            .and_modify(|existing| {
                // Merge: visible entries override hidden ones
                let mut found = false;
                for existing_info in existing.iter_mut() {
                    if existing_info.eq_ignoring_visibility(&info) {
                        if info.visible && !existing_info.visible {
                            *existing_info = info.clone();
                        }
                        found = true;
                        break;
                    }
                }
                if !found {
                    existing.push(info.clone());
                }
            })
            .or_insert_with(|| vec![info.clone()]);

        // Also add under unqualified name if it's qualified
        if id.is_qualified() {
            let unqual = Id::unpositioned(id.name().clone());
            self.fields
                .entry(unqual)
                .and_modify(|existing| {
                    let mut found = false;
                    for existing_info in existing.iter_mut() {
                        if existing_info.eq_ignoring_visibility(&info) {
                            if info.visible && !existing_info.visible {
                                *existing_info = info.clone();
                            }
                            found = true;
                            break;
                        }
                    }
                    if !found {
                        existing.push(info.clone());
                    }
                })
                .or_insert_with(|| vec![info]);
        }
    }

    /// Add a field under only its exact name (no unqualified alias).
    pub fn add_field_qualified(&mut self, id: Id, info: FieldInfo) {
        self.fields
            .entry(id)
            .and_modify(|existing| {
                let mut found = false;
                for existing_info in existing.iter_mut() {
                    if existing_info.eq_ignoring_visibility(&info) {
                        if info.visible && !existing_info.visible {
                            *existing_info = info.clone();
                        }
                        found = true;
                        break;
                    }
                }
                if !found {
                    existing.push(info.clone());
                }
            })
            .or_insert_with(|| vec![info]);
    }

    /// Look up fields by name.
    ///
    /// Returns all fields with this name (possibly from different types).
    #[must_use]
    pub fn lookup_field(&self, id: &Id) -> Option<&[FieldInfo]> {
        self.fields.get(id).map(Vec::as_slice)
    }

    /// Look up only visible fields by name.
    #[must_use]
    pub fn lookup_field_visible(&self, id: &Id) -> Option<Vec<&FieldInfo>> {
        self.fields
            .get(id)
            .map(|fields| fields.iter().filter(|f| f.visible).collect())
    }

    /// Look up a specific field by field name and type name.
    ///
    /// Useful when you know both the interface/struct type and the field name.
    #[must_use]
    pub fn lookup_field_in_type(&self, field_name: &Id, type_name: &Id) -> Option<&FieldInfo> {
        self.fields
            .get(field_name)
            .and_then(|fields| fields.iter().find(|f| &f.type_id == type_name))
    }

    /// Look up fields, returning an error if not found.
    pub fn get_field(&self, id: &Id) -> SymTabResult<&[FieldInfo]> {
        self.fields
            .get(id)
            .map(Vec::as_slice)
            .ok_or_else(|| SymTabError::FieldNotFound(id.clone()))
    }

    /// Check if a field exists.
    #[must_use]
    pub fn has_field(&self, id: &Id) -> bool {
        self.fields.contains_key(id)
    }

    /// Find a field by field name and type name.
    ///
    /// Useful when you know both the interface/struct type and the field name.
    /// Alias for `lookup_field_in_type` for API compatibility.
    #[must_use]
    pub fn find_field_for_type(&self, field_name: &Id, type_name: &Id) -> Option<&FieldInfo> {
        self.lookup_field_in_type(field_name, type_name)
    }

    // ========================================================================
    // Class operations
    // ========================================================================

    /// Add a type class to the symbol table.
    pub fn add_class(&mut self, id: Id, info: ClassInfo) {
        // Add under the original (possibly qualified) name
        self.classes.insert(id.clone(), info.clone());

        // Also add under unqualified name if it's qualified
        if id.is_qualified() {
            let unqual = Id::unpositioned(id.name().clone());
            self.classes.insert(unqual, info);
        }
    }

    /// Add a class under only its exact name (no unqualified alias).
    pub fn add_class_qualified(&mut self, id: Id, info: ClassInfo) {
        self.classes.insert(id, info);
    }

    /// Look up a type class by name.
    #[must_use]
    pub fn lookup_class(&self, id: &Id) -> Option<&ClassInfo> {
        self.classes.get(id)
    }

    /// Look up a class mutably (for adding instances).
    #[must_use]
    pub fn lookup_class_mut(&mut self, id: &Id) -> Option<&mut ClassInfo> {
        self.classes.get_mut(id)
    }

    /// Look up a class, returning an error if not found.
    pub fn get_class(&self, id: &Id) -> SymTabResult<&ClassInfo> {
        self.classes
            .get(id)
            .ok_or_else(|| SymTabError::ClassNotFound(id.clone()))
    }

    /// Look up a class, panicking if not found (for internal use).
    ///
    /// # Panics
    /// Panics if the class is not found.
    #[must_use]
    pub fn must_find_class(&self, id: &Id) -> &ClassInfo {
        self.classes
            .get(id)
            .unwrap_or_else(|| panic!("internal error: class not found: {id}"))
    }

    /// Check if a class exists.
    #[must_use]
    pub fn has_class(&self, id: &Id) -> bool {
        self.classes.contains_key(id)
    }

    // ========================================================================
    // Merge operation
    // ========================================================================

    /// Merge another symbol table into this one.
    ///
    /// Entries from `other` are added to this table. For types, abstract
    /// entries may be replaced with concrete ones. For constructors and
    /// fields, visible entries override hidden ones.
    pub fn merge(&mut self, other: SymTab) {
        // Merge variables (other overwrites self for conflicts)
        for (id, info) in other.vars {
            self.vars.insert(id, info);
        }

        // Merge types with abstract/concrete priority
        for (id, info) in other.types {
            self.types
                .entry(id)
                .and_modify(|existing| {
                    if existing.is_abstract() && !info.is_abstract() {
                        *existing = info.clone();
                    } else if let (
                        TISort::Struct {
                            subtype: StructSubType::Class,
                            fields: existing_fields,
                        },
                        TISort::Struct {
                            subtype: StructSubType::Class,
                            fields: new_fields,
                        },
                    ) = (&existing.sort, &info.sort)
                    {
                        if new_fields.len() > existing_fields.len() {
                            *existing = info.clone();
                        }
                    }
                })
                .or_insert(info);
        }

        // Merge constructors
        for (id, infos) in other.cons {
            for info in infos {
                self.cons
                    .entry(id.clone())
                    .and_modify(|existing| {
                        let mut found = false;
                        for existing_info in existing.iter_mut() {
                            if existing_info.eq_ignoring_visibility(&info) {
                                if info.visible && !existing_info.visible {
                                    *existing_info = info.clone();
                                }
                                found = true;
                                break;
                            }
                        }
                        if !found {
                            existing.push(info.clone());
                        }
                    })
                    .or_insert_with(|| vec![info]);
            }
        }

        // Merge fields
        for (id, infos) in other.fields {
            for info in infos {
                self.fields
                    .entry(id.clone())
                    .and_modify(|existing| {
                        let mut found = false;
                        for existing_info in existing.iter_mut() {
                            if existing_info.eq_ignoring_visibility(&info) {
                                if info.visible && !existing_info.visible {
                                    *existing_info = info.clone();
                                }
                                found = true;
                                break;
                            }
                        }
                        if !found {
                            existing.push(info.clone());
                        }
                    })
                    .or_insert_with(|| vec![info]);
            }
        }

        // Merge classes (other overwrites self for conflicts)
        for (id, info) in other.classes {
            self.classes.insert(id, info);
        }
    }

    // ========================================================================
    // Utility methods
    // ========================================================================

    /// Get method argument names for an interface method.
    ///
    /// Looks up the field info for the given method in the given interface
    /// and extracts the argument names from its pragmas.
    #[must_use]
    pub fn get_method_arg_names(&self, ifc_id: &Id, method_id: &Id) -> Vec<Id> {
        self.lookup_field_in_type(method_id, ifc_id)
            .map(|fi| {
                fi.pragmas
                    .iter()
                    .filter_map(|p| {
                        if let IfcPragma::ArgNames(names) = p {
                            Some(names.clone())
                        } else {
                            None
                        }
                    })
                    .flatten()
                    .collect()
            })
            .unwrap_or_default()
    }

    /// Get field names for an interface type.
    #[must_use]
    pub fn get_ifc_field_names(&self, ifc_id: &Id) -> Vec<Id> {
        self.lookup_type(ifc_id)
            .and_then(|ti| {
                if let TISort::Struct {
                    subtype: StructSubType::Interface(_),
                    fields,
                } = &ti.sort
                {
                    Some(fields.clone())
                } else {
                    None
                }
            })
            .unwrap_or_default()
    }

    /// Get the number of variables in the symbol table.
    #[must_use]
    pub fn var_count(&self) -> usize {
        self.vars.len()
    }

    /// Get the number of types in the symbol table.
    #[must_use]
    pub fn type_count(&self) -> usize {
        self.types.len()
    }

    /// Get the number of constructor entries in the symbol table.
    #[must_use]
    pub fn con_count(&self) -> usize {
        self.cons.len()
    }

    /// Get the number of field entries in the symbol table.
    #[must_use]
    pub fn field_count(&self) -> usize {
        self.fields.len()
    }

    /// Get the number of classes in the symbol table.
    #[must_use]
    pub fn class_count(&self) -> usize {
        self.classes.len()
    }

    /// Check if the symbol table is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.vars.is_empty()
            && self.types.is_empty()
            && self.cons.is_empty()
            && self.fields.is_empty()
            && self.classes.is_empty()
    }
}

impl fmt::Display for SymTab {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "SymTab {{")?;
        writeln!(f, "  vars: {} entries", self.vars.len())?;
        writeln!(f, "  types: {} entries", self.types.len())?;
        writeln!(f, "  cons: {} entries", self.cons.len())?;
        writeln!(f, "  fields: {} entries", self.fields.len())?;
        writeln!(f, "  classes: {} entries", self.classes.len())?;
        write!(f, "}}")
    }
}

// ============================================================================
// Tests
// ============================================================================

