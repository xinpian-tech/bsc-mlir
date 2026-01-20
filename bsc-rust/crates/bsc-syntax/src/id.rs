//! Identifier types for BSC.
//!
//! Mirrors `src/comp/Id.hs` from the Haskell implementation.
//! This is a complete implementation including IdProp properties,
//! suffix operations, fixity, and all accessor methods.

use bsc_diagnostics::Position;
use smol_str::SmolStr;
use std::fmt;

// ============================================================================
// Fixity
// ============================================================================

/// Fixity of an operator.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Fixity {
    /// Non-associative infix operator
    Infix(i32),
    /// Left-associative infix operator
    InfixL(i32),
    /// Right-associative infix operator
    InfixR(i32),
    /// Prefix operator (not really used in BSC)
    Prefix,
}

impl Fixity {
    /// Default fixity for operators (infixl 9).
    pub const DEFAULT: Fixity = Fixity::InfixL(9);

    /// Get the precedence level.
    #[must_use]
    pub fn precedence(&self) -> i32 {
        match self {
            Fixity::Infix(p) | Fixity::InfixL(p) | Fixity::InfixR(p) => *p,
            Fixity::Prefix => 10,
        }
    }
}

impl Default for Fixity {
    fn default() -> Self {
        Fixity::DEFAULT
    }
}

// ============================================================================
// IdProp - Identifier Properties
// ============================================================================

/// Properties that can be attached to identifiers.
///
/// Mirrors `IdProp` from `src/comp/Id.hs`.
/// These properties are used throughout the compiler to track metadata
/// about identifiers such as whether they are internally generated,
/// represent specific signals, etc.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum IdProp {
    /// can_fire signal for a rule
    CanFire,
    /// will_fire signal for a rule
    WillFire,
    /// Probe marker (for debugging)
    Probe,
    /// Internally generated identifier (not from user source)
    Internal,
    /// Interface ready signal (RDY_*)
    Ready,
    /// Generated interface name
    GeneratedIfc,
    /// Method identifier
    Meth,
    /// Commutative type constructor (order of arguments doesn't matter)
    CommutativeTCon,
    /// Enable signal (EN_*)
    Enable,
    /// Keep this signal even if unused (synthesis attribute)
    Keep,
    /// Keep even when unused (stronger than Keep)
    KeepEvenUnused,
    /// Rule identifier
    Rule,
    /// Split rule (from rule splitting optimization)
    SplitRule,
    /// Dictionary for typeclass instance
    Dict,
    /// Temporary renaming identifier
    Renaming,
    /// Has a _nn numeric suffix
    Suffixed,
    /// Count of numeric suffixes added (alternative to Suffixed)
    SuffixCount(i64),
    /// Name generated without good information (e.g., __d5)
    BadName,
    /// Name generated from right-hand-side of assignment
    FromRhs,
    /// C backend: identifier from $signed()
    Signed,
    /// Naked instantiation (module instantiation without bind)
    NakedInst,
    /// Alternate display string for pretty printing
    DisplayName(SmolStr),
    /// Hide from output (partial hiding)
    Hide,
    /// Hide completely from all output
    HideAll,
    /// Anonymous type join - stores original type and constructor
    TypeJoin {
        original_type: Box<Id>,
        constructor: Box<Id>,
    },
    /// Method predicate in a rule
    MethodPredicate,
    /// Positions of inlined method calls (for error reporting)
    InlinedPositions(Vec<Position>),
    /// Parser-generated identifier (from bracket syntax)
    ParserGenerated,
}

impl fmt::Display for IdProp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IdProp::CanFire => write!(f, "IdPCanFire"),
            IdProp::WillFire => write!(f, "IdPWillFire"),
            IdProp::Probe => write!(f, "IdPProbe"),
            IdProp::Internal => write!(f, "IdPInternal"),
            IdProp::Ready => write!(f, "IdPReady"),
            IdProp::GeneratedIfc => write!(f, "IdPGeneratedIfc"),
            IdProp::Meth => write!(f, "IdPMeth"),
            IdProp::CommutativeTCon => write!(f, "IdPCommutativeTCon"),
            IdProp::Enable => write!(f, "IdP_enable"),
            IdProp::Keep => write!(f, "IdP_keep"),
            IdProp::KeepEvenUnused => write!(f, "IdP_keepEvenUnused"),
            IdProp::Rule => write!(f, "IdPRule"),
            IdProp::SplitRule => write!(f, "IdPSplitRule"),
            IdProp::Dict => write!(f, "IdPDict"),
            IdProp::Renaming => write!(f, "IdPRenaming"),
            IdProp::Suffixed => write!(f, "IdP_suffixed"),
            IdProp::SuffixCount(n) => write!(f, "IdP_SuffixCount {}", n),
            IdProp::BadName => write!(f, "IdP_bad_name"),
            IdProp::FromRhs => write!(f, "IdP_from_rhs"),
            IdProp::Signed => write!(f, "IdP_signed"),
            IdProp::NakedInst => write!(f, "IdP_NakedInst"),
            IdProp::DisplayName(s) => write!(f, "IdPDisplayName \"{}\"", s),
            IdProp::Hide => write!(f, "IdP_hide"),
            IdProp::HideAll => write!(f, "IdP_hide_all"),
            IdProp::TypeJoin { original_type, constructor } => {
                write!(f, "IdP_TypeJoin {} {}", original_type, constructor)
            }
            IdProp::MethodPredicate => write!(f, "IdPMethodPredicate"),
            IdProp::InlinedPositions(poses) => {
                write!(f, "IdP_InlinedPositions [")?;
                for (i, p) in poses.iter().enumerate() {
                    if i > 0 {
                        write!(f, ",")?;
                    }
                    write!(f, "{}", p)?;
                }
                write!(f, "]")
            }
            IdProp::ParserGenerated => write!(f, "IdPParserGenerated"),
        }
    }
}

// ============================================================================
// Qualifier
// ============================================================================

/// A qualifier for identifiers (package/module path).
///
/// In BSC, qualifiers are typically module or package names that prefix
/// an identifier, like `Prelude.map` where `Prelude` is the qualifier.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Qualifier {
    /// The qualifier string (empty if unqualified)
    /// Using SmolStr for efficient small string storage
    value: SmolStr,
}

impl Qualifier {
    /// Create a new empty qualifier.
    #[must_use]
    pub fn empty() -> Self {
        Self {
            value: SmolStr::default(),
        }
    }

    /// Create a qualifier from a string.
    #[must_use]
    pub fn new(value: impl Into<SmolStr>) -> Self {
        Self {
            value: value.into(),
        }
    }

    /// Check if the qualifier is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.value.is_empty()
    }

    /// Get the qualifier string.
    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.value
    }

    /// Get the qualifier as SmolStr.
    #[must_use]
    pub fn as_smol_str(&self) -> &SmolStr {
        &self.value
    }
}

impl fmt::Debug for Qualifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_empty() {
            write!(f, "Qualifier()")
        } else {
            write!(f, "Qualifier({:?})", self.value)
        }
    }
}

impl fmt::Display for Qualifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}

impl From<&str> for Qualifier {
    fn from(s: &str) -> Self {
        if s.is_empty() {
            Self::empty()
        } else {
            Self::new(s)
        }
    }
}

impl From<String> for Qualifier {
    fn from(s: String) -> Self {
        if s.is_empty() {
            Self::empty()
        } else {
            Self::new(s)
        }
    }
}

impl From<SmolStr> for Qualifier {
    fn from(s: SmolStr) -> Self {
        if s.is_empty() {
            Self::empty()
        } else {
            Self { value: s }
        }
    }
}

// ============================================================================
// Longname
// ============================================================================

/// A long name is a path of identifiers.
///
/// Used for hierarchical names like instance paths.
pub type Longname = Vec<Id>;

// ============================================================================
// Id - The Core Identifier Type
// ============================================================================

/// An identifier with optional qualification, position, and properties.
///
/// This is the core identifier type used throughout the compiler.
/// Mirrors the `Id` type from `src/comp/Id.hs`.
///
/// # Equality
///
/// Identifiers are compared by name, qualifier, and properties.
/// Position is ignored in equality comparisons.
#[derive(Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Id {
    /// The base name of the identifier
    name: SmolStr,
    /// Optional qualifier (module/package path)
    qualifier: Qualifier,
    /// Source position where this identifier appears
    position: Position,
    /// Properties attached to this identifier
    props: Vec<IdProp>,
}

impl Id {
    // ========================================================================
    // Constructors
    // ========================================================================

    /// Create a new unqualified identifier.
    #[must_use]
    pub fn new(name: impl Into<SmolStr>, position: Position) -> Self {
        Self {
            name: name.into(),
            qualifier: Qualifier::empty(),
            position,
            props: Vec::new(),
        }
    }

    /// Create a new qualified identifier.
    #[must_use]
    pub fn qualified(
        qualifier: impl Into<Qualifier>,
        name: impl Into<SmolStr>,
        position: Position,
    ) -> Self {
        Self {
            name: name.into(),
            qualifier: qualifier.into(),
            position,
            props: Vec::new(),
        }
    }

    /// Create an identifier with unknown position.
    #[must_use]
    pub fn unpositioned(name: impl Into<SmolStr>) -> Self {
        Self {
            name: name.into(),
            qualifier: Qualifier::empty(),
            position: Position::unknown(),
            props: Vec::new(),
        }
    }

    /// Create a dummy identifier (underscore).
    #[must_use]
    pub fn dummy(position: Position) -> Self {
        Self::new("_", position)
    }

    /// Create an empty identifier.
    #[must_use]
    pub fn empty() -> Self {
        Self {
            name: SmolStr::default(),
            qualifier: Qualifier::empty(),
            position: Position::unknown(),
            props: Vec::new(),
        }
    }

    /// Create an identifier without a home (no position info).
    /// Mirrors `mk_homeless_id` from Haskell.
    #[must_use]
    pub fn homeless(name: impl Into<SmolStr>) -> Self {
        Self::unpositioned(name)
    }

    /// Create an enumerated identifier with a numeric suffix.
    /// Used for generating unique names like `x_0`, `x_1`, etc.
    #[must_use]
    pub fn enumerated(base: impl Into<SmolStr>, position: Position, index: u32) -> Self {
        let base_str: SmolStr = base.into();
        let name = format!("_{}{}", base_str, index);
        let mut id = Self::new(name, position);
        id.add_prop(IdProp::BadName);
        id
    }

    // ========================================================================
    // Basic Accessors
    // ========================================================================

    /// Get the base name.
    #[must_use]
    pub fn name(&self) -> &SmolStr {
        &self.name
    }

    /// Get the base name as a string slice.
    #[must_use]
    pub fn name_str(&self) -> &str {
        &self.name
    }

    /// Get the qualifier.
    #[must_use]
    pub fn qualifier(&self) -> &Qualifier {
        &self.qualifier
    }

    /// Get the position.
    #[must_use]
    pub fn position(&self) -> Position {
        self.position.clone()
    }

    /// Get the properties.
    #[must_use]
    pub fn props(&self) -> &[IdProp] {
        &self.props
    }

    /// Check if this identifier is empty (no name).
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.name.is_empty()
    }

    /// Check if this identifier is qualified.
    #[must_use]
    pub fn is_qualified(&self) -> bool {
        !self.qualifier.is_empty()
    }

    /// Check if this identifier is unqualified.
    #[must_use]
    pub fn is_unqualified(&self) -> bool {
        self.qualifier.is_empty()
    }

    /// Get the fully qualified name as a string.
    /// Format: "Qualifier.Name" or just "Name" if unqualified.
    #[must_use]
    pub fn full_name(&self) -> String {
        if self.qualifier.is_empty() {
            self.name.to_string()
        } else {
            format!("{}.{}", self.qualifier, self.name)
        }
    }

    /// Get the string representation (same as full_name).
    #[must_use]
    pub fn to_string_full(&self) -> String {
        self.full_name()
    }

    // ========================================================================
    // Modifiers (Builder Pattern)
    // ========================================================================

    /// Set the base name.
    #[must_use]
    pub fn with_name(mut self, name: impl Into<SmolStr>) -> Self {
        self.name = name.into();
        self
    }

    /// Set the qualifier.
    #[must_use]
    pub fn with_qualifier(mut self, qualifier: impl Into<Qualifier>) -> Self {
        self.qualifier = qualifier.into();
        self
    }

    /// Set the position.
    #[must_use]
    pub fn with_position(mut self, position: Position) -> Self {
        self.position = position;
        self
    }

    /// Set the properties.
    #[must_use]
    pub fn with_props(mut self, props: Vec<IdProp>) -> Self {
        self.props = props;
        self
    }

    /// Remove the qualifier (make unqualified).
    #[must_use]
    pub fn unqualified(mut self) -> Self {
        self.qualifier = Qualifier::empty();
        self
    }

    // ========================================================================
    // Mutable Setters
    // ========================================================================

    /// Set the base name (mutating).
    pub fn set_name(&mut self, name: impl Into<SmolStr>) {
        self.name = name.into();
    }

    /// Set the qualifier (mutating).
    pub fn set_qualifier(&mut self, qualifier: impl Into<Qualifier>) {
        self.qualifier = qualifier.into();
    }

    /// Set the position (mutating).
    pub fn set_position(&mut self, position: Position) {
        self.position = position;
    }

    // ========================================================================
    // Property Operations
    // ========================================================================

    /// Add a property to this identifier.
    pub fn add_prop(&mut self, prop: IdProp) {
        if !self.props.contains(&prop) {
            self.props.push(prop);
        }
    }

    /// Add multiple properties.
    pub fn add_props(&mut self, props: impl IntoIterator<Item = IdProp>) {
        for prop in props {
            self.add_prop(prop);
        }
    }

    /// Remove a property.
    pub fn remove_prop(&mut self, prop: &IdProp) {
        self.props.retain(|p| p != prop);
    }

    /// Remove properties matching a predicate.
    pub fn remove_props_by(&mut self, predicate: impl Fn(&IdProp) -> bool) {
        self.props.retain(|p| !predicate(p));
    }

    /// Check if this identifier has a specific property.
    #[must_use]
    pub fn has_prop(&self, prop: &IdProp) -> bool {
        self.props.contains(prop)
    }

    /// Check if this identifier has any of the given properties.
    #[must_use]
    pub fn has_any_prop(&self, props: &[IdProp]) -> bool {
        props.iter().any(|p| self.has_prop(p))
    }

    /// Copy properties from another identifier.
    pub fn copy_props_from(&mut self, other: &Id) {
        self.add_props(other.props.iter().cloned());
    }

    // ========================================================================
    // Specific Property Checks (mirrors Id.hs functions)
    // ========================================================================

    /// Check if this is an internally generated identifier.
    #[must_use]
    pub fn is_internal(&self) -> bool {
        self.has_prop(&IdProp::Internal)
    }

    /// Mark as internally generated.
    pub fn set_internal(&mut self) {
        self.add_prop(IdProp::Internal);
    }

    /// Check if this is a ready signal (RDY_*).
    #[must_use]
    pub fn is_ready(&self) -> bool {
        self.has_prop(&IdProp::Ready)
    }

    /// Check if this is a can_fire signal.
    #[must_use]
    pub fn is_can_fire(&self) -> bool {
        self.has_prop(&IdProp::CanFire)
    }

    /// Check if this is a will_fire signal.
    #[must_use]
    pub fn is_will_fire(&self) -> bool {
        self.has_prop(&IdProp::WillFire)
    }

    /// Check if this is either can_fire or will_fire.
    #[must_use]
    pub fn is_fire(&self) -> bool {
        self.is_can_fire() || self.is_will_fire()
    }

    /// Check if this is an enable signal.
    #[must_use]
    pub fn is_enable(&self) -> bool {
        self.has_prop(&IdProp::Enable)
    }

    /// Check if this is a rule identifier.
    #[must_use]
    pub fn is_rule(&self) -> bool {
        self.has_prop(&IdProp::Rule)
    }

    /// Check if this is a split rule.
    #[must_use]
    pub fn is_split_rule(&self) -> bool {
        self.has_prop(&IdProp::SplitRule)
    }

    /// Check if this is a dictionary.
    #[must_use]
    pub fn is_dict(&self) -> bool {
        self.has_prop(&IdProp::Dict)
    }

    /// Check if this is a temporary renaming.
    #[must_use]
    pub fn is_renaming(&self) -> bool {
        self.has_prop(&IdProp::Renaming)
    }

    /// Check if this should be kept.
    #[must_use]
    pub fn is_keep(&self) -> bool {
        self.has_prop(&IdProp::Keep)
    }

    /// Mark as keep.
    pub fn set_keep(&mut self) {
        self.add_prop(IdProp::Keep);
    }

    /// Remove keep property.
    pub fn remove_keep(&mut self) {
        self.remove_prop(&IdProp::Keep);
    }

    /// Check if this should be hidden.
    #[must_use]
    pub fn is_hide(&self) -> bool {
        self.has_prop(&IdProp::Hide)
    }

    /// Mark as hidden.
    pub fn set_hide(&mut self) {
        self.add_prop(IdProp::Hide);
    }

    /// Remove hide property.
    pub fn remove_hide(&mut self) {
        self.remove_prop(&IdProp::Hide);
    }

    /// Check if this should be completely hidden.
    #[must_use]
    pub fn is_hide_all(&self) -> bool {
        self.has_prop(&IdProp::HideAll)
    }

    /// Mark as completely hidden.
    pub fn set_hide_all(&mut self) {
        self.add_prop(IdProp::HideAll);
    }

    /// Remove hide_all property.
    pub fn remove_hide_all(&mut self) {
        self.remove_prop(&IdProp::HideAll);
    }

    /// Check if this has a bad name (generated without good info).
    #[must_use]
    pub fn is_bad_name(&self) -> bool {
        self.has_prop(&IdProp::BadName)
    }

    /// Mark as bad name.
    pub fn set_bad_name(&mut self) {
        self.add_prop(IdProp::BadName);
    }

    /// Check if generated from RHS.
    #[must_use]
    pub fn is_from_rhs(&self) -> bool {
        self.has_prop(&IdProp::FromRhs)
    }

    /// Mark as from RHS.
    pub fn set_from_rhs(&mut self) {
        self.add_prop(IdProp::FromRhs);
    }

    /// Check if signed (C backend).
    #[must_use]
    pub fn is_signed(&self) -> bool {
        self.has_prop(&IdProp::Signed)
    }

    /// Mark as signed.
    pub fn set_signed(&mut self) {
        self.add_prop(IdProp::Signed);
    }

    /// Check if naked instantiation.
    #[must_use]
    pub fn is_naked_inst(&self) -> bool {
        self.has_prop(&IdProp::NakedInst)
    }

    /// Mark as naked instantiation.
    pub fn set_naked_inst(&mut self) {
        self.add_prop(IdProp::NakedInst);
    }

    // ========================================================================
    // Display Name Operations
    // ========================================================================

    /// Get the display name if set.
    #[must_use]
    pub fn display_name(&self) -> Option<&SmolStr> {
        for prop in &self.props {
            if let IdProp::DisplayName(name) = prop {
                return Some(name);
            }
        }
        None
    }

    /// Set the display name.
    pub fn set_display_name(&mut self, name: impl Into<SmolStr>) {
        // Remove any existing display name
        self.remove_props_by(|p| matches!(p, IdProp::DisplayName(_)));
        self.add_prop(IdProp::DisplayName(name.into()));
    }

    // ========================================================================
    // Inlined Positions Operations
    // ========================================================================

    /// Get inlined positions if any.
    #[must_use]
    pub fn inlined_positions(&self) -> Option<&[Position]> {
        for prop in &self.props {
            if let IdProp::InlinedPositions(positions) = prop {
                return Some(positions);
            }
        }
        None
    }

    /// Add inlined positions.
    pub fn add_inlined_positions(&mut self, new_positions: Vec<Position>) {
        if new_positions.is_empty() {
            return;
        }

        // Find existing and merge
        let mut found = false;
        for prop in &mut self.props {
            if let IdProp::InlinedPositions(positions) = prop {
                positions.extend(new_positions.iter().cloned());
                found = true;
                break;
            }
        }

        if !found {
            self.add_prop(IdProp::InlinedPositions(new_positions));
        }
    }

    /// Remove inlined positions.
    pub fn remove_inlined_positions(&mut self) {
        self.remove_props_by(|p| matches!(p, IdProp::InlinedPositions(_)));
    }

    // ========================================================================
    // Suffix Operations
    // ========================================================================

    /// Get the suffix count.
    #[must_use]
    pub fn suffix_count(&self) -> i64 {
        for prop in &self.props {
            if let IdProp::SuffixCount(count) = prop {
                return *count;
            }
        }
        0
    }

    /// Check if this identifier has the Suffixed property.
    #[must_use]
    pub fn is_suffixed(&self) -> bool {
        self.has_prop(&IdProp::Suffixed)
    }

    /// Add a numeric suffix to the identifier.
    ///
    /// Creates names like `foo_0`, `foo_1`, etc.
    /// This uses the SuffixCount system (not the simple Suffixed flag).
    #[must_use]
    pub fn add_suffix(mut self, n: i64) -> Self {
        let count = self.suffix_count();

        // Remove existing suffix count property
        self.remove_props_by(|p| matches!(p, IdProp::SuffixCount(_)));

        // Create new name with suffix
        let new_name = format!("{}_{}", self.name, n);
        self.name = new_name.into();
        self.add_prop(IdProp::SuffixCount(count + 1));
        self
    }

    /// Add a suffix using the simple Suffixed system.
    ///
    /// Returns an error if already suffixed.
    pub fn add_simple_suffix(&mut self, n: i64) -> Result<(), IdError> {
        if self.is_suffixed() {
            return Err(IdError::AlreadySuffixed {
                id: self.full_name(),
            });
        }

        // If empty name, give it a name first
        if self.is_empty() {
            self.name = "_unnamed".into();
        }

        let new_name = format!("{}_{}", self.name, n);
        self.name = new_name.into();
        self.add_prop(IdProp::Suffixed);
        Ok(())
    }

    /// Remove the last suffix and return the base and suffix value.
    ///
    /// Returns an error if no suffix exists.
    pub fn remove_suffix(mut self) -> Result<(Self, i64), IdError> {
        let count = self.suffix_count();

        if count == 0 {
            return Err(IdError::NoSuffix {
                id: self.full_name(),
            });
        }

        // Find the last underscore
        let name_str = self.name.as_str();
        let last_underscore = name_str.rfind('_').ok_or_else(|| IdError::NoSuffix {
            id: self.full_name(),
        })?;

        // Parse the suffix
        let suffix_str = &name_str[last_underscore + 1..];
        let suffix: i64 = suffix_str.parse().map_err(|_| IdError::InvalidSuffix {
            id: self.full_name(),
            suffix: suffix_str.to_string(),
        })?;

        // Create the new base name
        let base_name = &name_str[..last_underscore];
        self.name = base_name.into();

        // Update suffix count
        self.remove_props_by(|p| matches!(p, IdProp::SuffixCount(_)));
        if count > 1 {
            self.add_prop(IdProp::SuffixCount(count - 1));
        }

        Ok((self, suffix))
    }

    /// Remove all suffixes, returning the base identifier.
    #[must_use]
    pub fn remove_all_suffixes(self) -> Self {
        // Early return if no suffixes
        if self.suffix_count() == 0 {
            return self;
        }

        // Remove first suffix and recurse
        match self.remove_suffix() {
            Ok((base, _)) => base.remove_all_suffixes(),
            Err(_) => {
                // This shouldn't happen since we checked suffix_count > 0,
                // but the error consumed self, so we can't return it.
                // This indicates a bug in remove_suffix or suffix_count.
                panic!("remove_suffix failed despite suffix_count > 0")
            }
        }
    }

    /// Strip the simple suffix (Suffixed flag system).
    ///
    /// Returns the base identifier and the suffix value.
    pub fn strip_simple_suffix(mut self) -> Result<(Self, i64), IdError> {
        if !self.is_suffixed() {
            return Ok((self, 0));
        }

        let name_str = self.name.as_str();
        let last_underscore = name_str.rfind('_').ok_or_else(|| IdError::InvalidSuffix {
            id: self.full_name(),
            suffix: String::new(),
        })?;

        let suffix_str = &name_str[last_underscore + 1..];
        let suffix: i64 = suffix_str.parse().map_err(|_| IdError::InvalidSuffix {
            id: self.full_name(),
            suffix: suffix_str.to_string(),
        })?;

        let base_name = &name_str[..last_underscore];
        self.name = base_name.into();
        self.remove_prop(&IdProp::Suffixed);

        Ok((self, suffix))
    }

    // ========================================================================
    // Name Manipulation
    // ========================================================================

    /// Prepend a string to the name.
    #[must_use]
    pub fn prepend(mut self, prefix: &str) -> Self {
        let new_name = format!("{}{}", prefix, self.name);
        self.name = new_name.into();
        self
    }

    /// Append a string to the name.
    #[must_use]
    pub fn append(mut self, suffix: &str) -> Self {
        let new_name = format!("{}{}", self.name, suffix);
        self.name = new_name.into();
        self
    }

    /// Make a ready signal identifier (RDY_name).
    #[must_use]
    pub fn make_ready(self) -> Self {
        let mut id = self.prepend("RDY_");
        id.add_prop(IdProp::Ready);
        id
    }

    /// Make a can_fire signal identifier (CAN_FIRE_name).
    #[must_use]
    pub fn make_can_fire(self) -> Self {
        let mut id = self.prepend("CAN_FIRE_");
        id.add_prop(IdProp::CanFire);
        id
    }

    /// Make a will_fire signal identifier (WILL_FIRE_name).
    #[must_use]
    pub fn make_will_fire(self) -> Self {
        let mut id = self.prepend("WILL_FIRE_");
        id.add_prop(IdProp::WillFire);
        id
    }

    /// Make an enable signal identifier (EN_name).
    #[must_use]
    pub fn make_enable(self) -> Self {
        let mut id = self.prepend("EN_");
        id.add_prop(IdProp::Enable);
        id
    }

    /// Make a rule identifier (RL_name).
    #[must_use]
    pub fn make_rule(self) -> Self {
        let mut id = self.prepend("RL_");
        id.add_prop(IdProp::Rule);
        id
    }

    /// Join two identifiers with underscore.
    #[must_use]
    pub fn join_with_underscore(&self, other: &Id) -> Self {
        if self.is_empty() {
            return other.clone();
        }
        if other.is_empty() {
            return self.clone();
        }

        let new_name = format!("{}_{}", self.name, other.name);
        let mut result = Self::new(new_name, self.position.clone());
        result.qualifier = self.qualifier.clone();
        result.copy_props_from(self);
        result.copy_props_from(other);
        result
    }

    /// Join two identifiers with dot (for hierarchical names).
    #[must_use]
    pub fn join_with_dot(&self, other: &Id) -> Self {
        if self.is_empty() {
            return other.clone();
        }
        if other.is_empty() {
            return self.clone();
        }

        let new_name = format!("{}.{}", self.name, other.name);
        let mut result = Self::new(new_name, self.position.clone());
        result.qualifier = self.qualifier.clone();
        result.copy_props_from(self);
        result.copy_props_from(other);
        result
    }

    // ========================================================================
    // Fixity
    // ========================================================================

    /// Get the fixity of this identifier (for operators).
    #[must_use]
    pub fn fixity(&self) -> Fixity {
        match self.name.as_str() {
            "," => Fixity::InfixR(-1),
            _ => Fixity::DEFAULT,
        }
    }

    // ========================================================================
    // Comparison
    // ========================================================================

    /// Qualified equality - if either is unqualified, compare only base names.
    /// Mirrors `qualEq` from Haskell.
    #[must_use]
    pub fn qual_eq(&self, other: &Id) -> bool {
        if self.qualifier.is_empty() || other.qualifier.is_empty() {
            self.name == other.name
        } else {
            self == other
        }
    }

    /// Unqualified base name equality.
    #[must_use]
    pub fn base_eq(&self, name: &str) -> bool {
        self.name.as_str() == name
    }

    /// Compare by name only (ignoring qualifier and position).
    #[must_use]
    pub fn cmp_by_name(&self, other: &Id) -> std::cmp::Ordering {
        self.full_name().cmp(&other.full_name())
    }

    /// Compare including position.
    #[must_use]
    pub fn cmp_with_position(&self, other: &Id) -> std::cmp::Ordering {
        match self.cmp(other) {
            std::cmp::Ordering::Equal => {
                // Compare positions: line first, then column
                match self.position.line.cmp(&other.position.line) {
                    std::cmp::Ordering::Equal => {
                        self.position.column.cmp(&other.position.column)
                    }
                    ord => ord,
                }
            }
            ord => ord,
        }
    }
}

// ============================================================================
// Trait Implementations for Id
// ============================================================================

impl fmt::Debug for Id {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.qualifier.is_empty() {
            if self.props.is_empty() {
                write!(f, "Id({:?} @ {})", self.name, self.position)
            } else {
                write!(
                    f,
                    "Id({:?} @ {} {:?})",
                    self.name, self.position, self.props
                )
            }
        } else {
            if self.props.is_empty() {
                write!(
                    f,
                    "Id({}.{:?} @ {})",
                    self.qualifier, self.name, self.position
                )
            } else {
                write!(
                    f,
                    "Id({}.{:?} @ {} {:?})",
                    self.qualifier, self.name, self.position, self.props
                )
            }
        }
    }
}

impl fmt::Display for Id {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.qualifier.is_empty() {
            write!(f, "{}", self.name)?;
        } else {
            write!(f, "{}::{}", self.qualifier, self.name)?;
        }
        if !self.props.is_empty() {
            write!(f, "[")?;
            for (i, prop) in self.props.iter().enumerate() {
                if i > 0 {
                    write!(f, ",")?;
                }
                write!(f, "{}", prop)?;
            }
            write!(f, "]")?;
        }
        Ok(())
    }
}

// Equality ignores position but includes properties
impl PartialEq for Id {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && self.qualifier == other.qualifier
        // Note: Haskell version ignores properties in equality
        // We follow that convention
    }
}

impl Eq for Id {}

impl std::hash::Hash for Id {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.name.hash(state);
        self.qualifier.hash(state);
        // Properties not included in hash (matches equality semantics)
    }
}

impl PartialOrd for Id {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Id {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // Compare by base name first, then qualifier
        match self.name.cmp(&other.name) {
            std::cmp::Ordering::Equal => self.qualifier.cmp(&other.qualifier),
            ord => ord,
        }
    }
}

// ============================================================================
// Errors
// ============================================================================

/// Errors that can occur during Id operations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IdError {
    /// Attempted to add suffix to already suffixed identifier.
    AlreadySuffixed { id: String },
    /// Attempted to remove suffix from identifier without suffix.
    NoSuffix { id: String },
    /// Invalid suffix format.
    InvalidSuffix { id: String, suffix: String },
}

impl fmt::Display for IdError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IdError::AlreadySuffixed { id } => {
                write!(f, "identifier '{}' already has a suffix", id)
            }
            IdError::NoSuffix { id } => {
                write!(f, "identifier '{}' has no suffix to remove", id)
            }
            IdError::InvalidSuffix { id, suffix } => {
                write!(
                    f,
                    "identifier '{}' has invalid suffix '{}'",
                    id, suffix
                )
            }
        }
    }
}

impl std::error::Error for IdError {}

// ============================================================================
// Utility Functions
// ============================================================================

/// Flatten a Longname to an Id using underscore as separator.
#[must_use]
pub fn flatten_longname(longname: &Longname) -> Id {
    if longname.is_empty() {
        return Id::empty();
    }

    let mut result = longname[0].clone();
    for id in &longname[1..] {
        result = result.join_with_underscore(id);
    }
    result
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unqualified_id() {
        let id = Id::new("foo", Position::new("", 1, 1));
        assert_eq!(id.name().as_str(), "foo");
        assert!(!id.is_qualified());
        assert_eq!(id.full_name(), "foo");
    }

    #[test]
    fn test_qualified_id() {
        let id = Id::qualified("Prelude", "map", Position::new("", 1, 1));
        assert!(id.is_qualified());
        assert_eq!(id.full_name(), "Prelude.map");
    }

    #[test]
    fn test_id_equality_ignores_position() {
        let id1 = Id::new("foo", Position::new("", 1, 1));
        let id2 = Id::new("foo", Position::new("", 2, 5));
        assert_eq!(id1, id2);
    }

    #[test]
    fn test_id_props() {
        let mut id = Id::new("foo", Position::new("", 1, 1));
        assert!(!id.is_internal());

        id.set_internal();
        assert!(id.is_internal());

        id.add_prop(IdProp::Keep);
        assert!(id.is_keep());

        id.remove_keep();
        assert!(!id.is_keep());
    }

    #[test]
    fn test_suffix_operations() {
        let id = Id::new("foo", Position::new("", 1, 1));
        let id_suffixed = id.add_suffix(42);
        assert_eq!(id_suffixed.name().as_str(), "foo_42");
        assert_eq!(id_suffixed.suffix_count(), 1);

        let (base, suffix) = id_suffixed.remove_suffix().unwrap();
        assert_eq!(base.name().as_str(), "foo");
        assert_eq!(suffix, 42);
        assert_eq!(base.suffix_count(), 0);
    }

    #[test]
    fn test_multiple_suffixes() {
        let id = Id::new("foo", Position::new("", 1, 1));
        let id = id.add_suffix(1).add_suffix(2).add_suffix(3);
        assert_eq!(id.name().as_str(), "foo_1_2_3");
        assert_eq!(id.suffix_count(), 3);

        let base = id.remove_all_suffixes();
        assert_eq!(base.name().as_str(), "foo");
        assert_eq!(base.suffix_count(), 0);
    }

    #[test]
    fn test_signal_names() {
        let id = Id::new("method", Position::new("", 1, 1));

        let rdy = id.clone().make_ready();
        assert_eq!(rdy.name().as_str(), "RDY_method");
        assert!(rdy.is_ready());

        let can_fire = id.clone().make_can_fire();
        assert_eq!(can_fire.name().as_str(), "CAN_FIRE_method");
        assert!(can_fire.is_can_fire());
        assert!(can_fire.is_fire());

        let will_fire = id.clone().make_will_fire();
        assert_eq!(will_fire.name().as_str(), "WILL_FIRE_method");
        assert!(will_fire.is_will_fire());
        assert!(will_fire.is_fire());

        let enable = id.clone().make_enable();
        assert_eq!(enable.name().as_str(), "EN_method");
        assert!(enable.is_enable());
    }

    #[test]
    fn test_qual_eq() {
        let id1 = Id::new("foo", Position::new("", 1, 1));
        let id2 = Id::qualified("Prelude", "foo", Position::new("", 1, 1));
        let id3 = Id::qualified("Other", "foo", Position::new("", 1, 1));

        // Unqualified matches any qualifier
        assert!(id1.qual_eq(&id2));
        assert!(id1.qual_eq(&id3));

        // Different qualifiers don't match each other
        assert!(!id2.qual_eq(&id3));
    }

    #[test]
    fn test_join_operations() {
        let a = Id::new("foo", Position::new("", 1, 1));
        let b = Id::new("bar", Position::new("", 1, 5));

        let joined = a.join_with_underscore(&b);
        assert_eq!(joined.name().as_str(), "foo_bar");

        let a = Id::new("foo", Position::new("", 1, 1));
        let b = Id::new("bar", Position::new("", 1, 5));
        let dotted = a.join_with_dot(&b);
        assert_eq!(dotted.name().as_str(), "foo.bar");
    }

    #[test]
    fn test_flatten_longname() {
        let longname = vec![
            Id::new("a", Position::unknown()),
            Id::new("b", Position::unknown()),
            Id::new("c", Position::unknown()),
        ];

        let flattened = flatten_longname(&longname);
        assert_eq!(flattened.name().as_str(), "a_b_c");
    }

    #[test]
    fn test_display_name() {
        let mut id = Id::new("internal_name", Position::new("", 1, 1));
        assert!(id.display_name().is_none());

        id.set_display_name("user_friendly_name");
        assert_eq!(id.display_name().unwrap().as_str(), "user_friendly_name");
    }
}
