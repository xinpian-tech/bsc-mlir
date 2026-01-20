//! Verilog Module Information types.
//!
//! Mirrors `src/comp/VModInfo.hs` from the Haskell BSC implementation.
//!
//! This module provides the types needed to describe Verilog modules and their
//! interfaces, including clocks, resets, ports, and scheduling information.

use crate::Id;
use num_bigint::BigInt;

// ============================================================================
// VName - Verilog Name
// ============================================================================

/// A Verilog name (port or wire name).
///
/// Mirrors `newtype VName = VName String` from VModInfo.hs:56.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct VName(pub String);

impl VName {
    /// Create a new VName from a string.
    #[must_use]
    pub fn new(s: impl Into<String>) -> Self {
        VName(s.into())
    }

    /// Get the underlying string.
    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }

    /// Convert from an Id to a VName.
    #[must_use]
    pub fn from_id(id: &Id) -> Self {
        VName(id.name().to_string())
    }

    /// Convert to an Id (without position info).
    #[must_use]
    pub fn to_id(&self) -> Id {
        Id::unpositioned(&self.0)
    }
}

impl From<&str> for VName {
    fn from(s: &str) -> Self {
        VName(s.to_string())
    }
}

impl From<String> for VName {
    fn from(s: String) -> Self {
        VName(s)
    }
}

// ============================================================================
// VeriPortProp - Verilog Port Properties
// ============================================================================

/// Verilog port property annotations.
///
/// Mirrors `VeriPortProp` from VModInfo.hs:82-91.
/// The order is important for VIOProps ("unused" should come last).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum VeriPortProp {
    /// `VPreg` - Port has register-style timing
    Reg,
    /// `VPconst` - Port has constant value
    Const,
    /// `VPinhigh` - Input gate is assumed high
    InHigh,
    /// `VPouthigh` - Output gate is driven high
    OutHigh,
    /// `VPclock` - Port is a clock signal
    Clock,
    /// `VPclockgate` - Port is a clock gate
    ClockGate,
    /// `VPreset` - Port is a reset signal
    Reset,
    /// `VPinout` - Port is bidirectional
    Inout,
    /// `VPunused` - Port is unused
    Unused,
}

// ============================================================================
// VPort - Verilog Port
// ============================================================================

/// A Verilog port with optional properties.
///
/// Mirrors `type VPort = (VName, [VeriPortProp])` from VModInfo.hs:119.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct VPort {
    /// Port name
    pub name: VName,
    /// Port properties
    pub props: Vec<VeriPortProp>,
}

impl VPort {
    /// Create a new VPort with no properties.
    #[must_use]
    pub fn new(name: VName) -> Self {
        VPort {
            name,
            props: Vec::new(),
        }
    }

    /// Create a VPort with properties.
    #[must_use]
    pub fn with_props(name: VName, props: Vec<VeriPortProp>) -> Self {
        VPort { name, props }
    }

    /// Create from an Id.
    #[must_use]
    pub fn from_id(id: &Id) -> Self {
        VPort {
            name: VName::from_id(id),
            props: Vec::new(),
        }
    }

    /// Get the port name as a string.
    #[must_use]
    pub fn name_str(&self) -> &str {
        self.name.as_str()
    }
}

// ============================================================================
// Either - Haskell-style Either type
// ============================================================================

/// Either type (matching Haskell's Either a b).
///
/// Used for representing values that can be one of two types.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Either<L, R> {
    Left(L),
    Right(R),
}

impl<L, R> Either<L, R> {
    /// Check if this is a Left value.
    #[must_use]
    pub fn is_left(&self) -> bool {
        matches!(self, Either::Left(_))
    }

    /// Check if this is a Right value.
    #[must_use]
    pub fn is_right(&self) -> bool {
        matches!(self, Either::Right(_))
    }

    /// Get the Left value, if any.
    #[must_use]
    pub fn left(self) -> Option<L> {
        match self {
            Either::Left(l) => Some(l),
            Either::Right(_) => None,
        }
    }

    /// Get the Right value, if any.
    #[must_use]
    pub fn right(self) -> Option<R> {
        match self {
            Either::Left(_) => None,
            Either::Right(r) => Some(r),
        }
    }

    /// Get a reference to the Left value, if any.
    #[must_use]
    pub fn left_ref(&self) -> Option<&L> {
        match self {
            Either::Left(l) => Some(l),
            Either::Right(_) => None,
        }
    }

    /// Get a reference to the Right value, if any.
    #[must_use]
    pub fn right_ref(&self) -> Option<&R> {
        match self {
            Either::Left(_) => None,
            Either::Right(r) => Some(r),
        }
    }
}

// ============================================================================
// VArgInfo - Verilog Argument Information
// ============================================================================

/// Describes what an argument to a Verilog module is.
///
/// Mirrors `VArgInfo` from VModInfo.hs:178-185:
/// ```haskell
/// data VArgInfo = Param VName
///               | Port VPort (Maybe Id) (Maybe Id)
///               | ClockArg Id
///               | ResetArg Id
///               | InoutArg VName (Maybe Id) (Maybe Id)
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum VArgInfo {
    /// `Param VName` - Named module parameter (compile-time constant)
    Param(VName),
    /// `Port VPort (Maybe Id) (Maybe Id)` - Named module port with clock and reset
    Port {
        /// The port
        port: VPort,
        /// Associated clock (if any)
        clock: Option<Id>,
        /// Associated reset (if any)
        reset: Option<Id>,
    },
    /// `ClockArg Id` - Named clock argument
    ClockArg(Id),
    /// `ResetArg Id` - Named reset argument
    ResetArg(Id),
    /// `InoutArg VName (Maybe Id) (Maybe Id)` - Named inout with clock and reset
    InoutArg {
        /// The inout name
        name: VName,
        /// Associated clock (if any)
        clock: Option<Id>,
        /// Associated reset (if any)
        reset: Option<Id>,
    },
}

impl VArgInfo {
    /// Check if this is a parameter argument.
    #[must_use]
    pub fn is_param(&self) -> bool {
        matches!(self, VArgInfo::Param(_))
    }

    /// Check if this is a port argument.
    #[must_use]
    pub fn is_port(&self) -> bool {
        matches!(self, VArgInfo::Port { .. })
    }

    /// Check if this is a clock argument.
    #[must_use]
    pub fn is_clock(&self) -> bool {
        matches!(self, VArgInfo::ClockArg(_))
    }

    /// Check if this is a reset argument.
    #[must_use]
    pub fn is_reset(&self) -> bool {
        matches!(self, VArgInfo::ResetArg(_))
    }

    /// Check if this is an inout argument.
    #[must_use]
    pub fn is_inout(&self) -> bool {
        matches!(self, VArgInfo::InoutArg { .. })
    }

    /// Get the name/identifier for this argument.
    #[must_use]
    pub fn get_name(&self) -> Id {
        match self {
            VArgInfo::Param(vn) => vn.to_id(),
            VArgInfo::Port { port, .. } => port.name.to_id(),
            VArgInfo::ClockArg(id) => id.clone(),
            VArgInfo::ResetArg(id) => id.clone(),
            VArgInfo::InoutArg { name, .. } => name.to_id(),
        }
    }
}

// ============================================================================
// VFieldInfo - Verilog Field Information
// ============================================================================

/// Describes a field in a Verilog module's interface.
///
/// Mirrors `VFieldInfo` from VModInfo.hs:270-287:
/// ```haskell
/// data VFieldInfo = Method { vf_name, vf_clock, vf_reset, vf_mult, vf_inputs, vf_output, vf_enable }
///                 | Clock { vf_name }
///                 | Reset { vf_name }
///                 | Inout { vf_name, vf_inout, vf_clock, vf_reset }
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum VFieldInfo {
    /// Method field
    Method {
        /// `vf_name` - Method name
        name: Id,
        /// `vf_clock` - Optional clock
        clock: Option<Id>,
        /// `vf_reset` - Optional reset
        reset: Option<Id>,
        /// `vf_mult` - Multiplicity (uses BigInt for Haskell Integer)
        multiplicity: BigInt,
        /// `vf_inputs` - Input ports
        inputs: Vec<VPort>,
        /// `vf_output` - Output port (if any)
        output: Option<VPort>,
        /// `vf_enable` - Enable port (if any)
        enable: Option<VPort>,
    },
    /// Clock output field
    Clock {
        /// `vf_name` - Clock name
        name: Id,
    },
    /// Reset output field
    Reset {
        /// `vf_name` - Reset name
        name: Id,
    },
    /// Inout field
    Inout {
        /// `vf_name` - Inout name
        name: Id,
        /// `vf_inout` - The inout port
        inout: VName,
        /// `vf_clock` - Optional clock
        clock: Option<Id>,
        /// `vf_reset` - Optional reset
        reset: Option<Id>,
    },
}

impl VFieldInfo {
    /// Get the field name.
    #[must_use]
    pub fn name(&self) -> &Id {
        match self {
            VFieldInfo::Method { name, .. }
            | VFieldInfo::Clock { name }
            | VFieldInfo::Reset { name }
            | VFieldInfo::Inout { name, .. } => name,
        }
    }
}

// ============================================================================
// VClockInfo - Clock Information
// ============================================================================

/// Oscillator port type.
pub type VOscPort = VName;

/// Gate port for input clocks.
///
/// Either there is no port (bool indicates if gate is assumed True or unused),
/// or there is a gate port.
///
/// Mirrors `type VInputGatePort = Either Bool VName` from VModInfo.hs:337.
pub type VInputGatePort = Either<bool, VName>;

/// Gate port for output clocks.
///
/// Either there is no port, or there is a port (possibly with VPouthigh property).
///
/// Mirrors `type VOutputGatePort = Maybe VPort` from VModInfo.hs:343.
pub type VOutputGatePort = Option<VPort>;

/// Information about an input clock.
///
/// Mirrors `type InputClockInf = (Id, Maybe (VOscPort, VInputGatePort))` from VModInfo.hs:326.
pub type InputClockInf = (Id, Option<(VOscPort, VInputGatePort)>);

/// Information about an output clock.
///
/// Mirrors `type OutputClockInf = (Id, Maybe (VOscPort, VOutputGatePort))` from VModInfo.hs:329.
pub type OutputClockInf = (Id, Option<(VOscPort, VOutputGatePort)>);

/// Clock information for a Verilog module.
///
/// Mirrors `VClockInfo` from VModInfo.hs:345-357:
/// ```haskell
/// data VClockInfo = ClockInfo {
///     input_clocks :: [InputClockInf],
///     output_clocks :: [OutputClockInf],
///     ancestorClocks :: [(Id, Id)],
///     siblingClocks :: [(Id, Id)]
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct VClockInfo {
    /// `input_clocks` - Named list of input clocks
    pub input_clocks: Vec<InputClockInf>,
    /// `output_clocks` - Named list of output clocks
    pub output_clocks: Vec<OutputClockInf>,
    /// `ancestorClocks` - Edges in ancestor relationships (parent, child)
    pub ancestor_clocks: Vec<(Id, Id)>,
    /// `siblingClocks` - Sibling clock relationships
    pub sibling_clocks: Vec<(Id, Id)>,
}

impl Default for VClockInfo {
    fn default() -> Self {
        VClockInfo {
            input_clocks: Vec::new(),
            output_clocks: Vec::new(),
            ancestor_clocks: Vec::new(),
            sibling_clocks: Vec::new(),
        }
    }
}

// ============================================================================
// VResetInfo - Reset Information
// ============================================================================

/// Information about a reset signal.
///
/// Mirrors `type ResetInf = (Id, (Maybe VName, Maybe Id))` from VModInfo.hs:474.
/// (reset name, (optional Verilog port, optional clock))
pub type ResetInf = (Id, (Option<VName>, Option<Id>));

/// Reset information for a Verilog module.
///
/// Mirrors `VResetInfo` from VModInfo.hs:478-481:
/// ```haskell
/// data VResetInfo = ResetInfo {
///     input_resets :: [ResetInf],
///     output_resets :: [ResetInf]
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct VResetInfo {
    /// `input_resets` - Input reset signals
    pub input_resets: Vec<ResetInf>,
    /// `output_resets` - Output reset signals
    pub output_resets: Vec<ResetInf>,
}

impl Default for VResetInfo {
    fn default() -> Self {
        VResetInfo {
            input_resets: Vec::new(),
            output_resets: Vec::new(),
        }
    }
}

// ============================================================================
// VPathInfo - Path Timing Information
// ============================================================================

/// Path timing information for combinational paths.
///
/// Mirrors `newtype VPathInfo = VPathInfo [(VName, VName)]` from VModInfo.hs:141.
/// Contains pairs of (input, output) for combinational paths.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct VPathInfo(pub Vec<(VName, VName)>);

impl VPathInfo {
    /// Create empty path info (no combinational paths).
    #[must_use]
    pub fn empty() -> Self {
        VPathInfo(Vec::new())
    }

    /// Create path info from a list of (input, output) pairs.
    #[must_use]
    pub fn new(paths: Vec<(VName, VName)>) -> Self {
        VPathInfo(paths)
    }

    /// Check if there are any combinational paths.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

// ============================================================================
// VSchedInfo - Scheduling Information (re-export from SchedInfo)
// ============================================================================

/// Method conflict information.
///
/// Mirrors `MethodConflictInfo` from SchedInfo.hs.
/// This is parameterized by the identifier type.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct MethodConflictInfo<T> {
    /// `sCF` - Conflict-free pairs
    pub conflict_free: Vec<(T, T)>,
    /// `sSB` - Sequenced-before pairs
    pub sequenced_before: Vec<(T, T)>,
    /// `sME` - Mutually exclusive groups
    pub mutually_exclusive: Vec<Vec<T>>,
    /// `sP` - Preempts pairs
    pub preempts: Vec<(T, T)>,
    /// `sSBR` - Sequenced-before reverse pairs
    pub sequenced_before_reverse: Vec<(T, T)>,
    /// `sC` - Conflict pairs
    pub conflicts: Vec<(T, T)>,
    /// `sEXT` - External methods
    pub external: Vec<T>,
}

/// Scheduling information type (using Id).
///
/// Mirrors `type VSchedInfo = SchedInfo Id` from VModInfo.hs:134.
pub type VSchedInfo = SchedInfo<Id>;

/// Scheduling information.
///
/// Mirrors `SchedInfo` from SchedInfo.hs:
/// ```haskell
/// data SchedInfo idtype = SchedInfo {
///     methodConflictInfo :: MethodConflictInfo idtype,
///     rulesBetweenMethods :: [((idtype, idtype), [idtype])],
///     rulesBeforeMethods :: [(idtype,[Either idtype idtype])],
///     clockCrossingMethods :: [idtype]
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct SchedInfo<T> {
    /// `methodConflictInfo` - Method conflict information
    pub method_conflict_info: MethodConflictInfo<T>,
    /// `rulesBetweenMethods` - Methods with rules between them
    pub rules_between_methods: Vec<((T, T), Vec<T>)>,
    /// `rulesBeforeMethods` - Methods with rules before them
    pub rules_before_methods: Vec<(T, Vec<Either<T, T>>)>,
    /// `clockCrossingMethods` - Methods allowing clock domain crossing
    pub clock_crossing_methods: Vec<T>,
}

// ============================================================================
// VWireInfo - Wire Information
// ============================================================================

/// Wire information needed from evaluator to wrapper generation.
///
/// Mirrors `VWireInfo` from VModInfo.hs:652-656:
/// ```haskell
/// data VWireInfo = WireInfo {
///     wClk :: VClockInfo,
///     wRst :: VResetInfo,
///     wArgs :: [VArgInfo]
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct VWireInfo {
    /// `wClk` - Clock information
    pub clock_info: VClockInfo,
    /// `wRst` - Reset information
    pub reset_info: VResetInfo,
    /// `wArgs` - Argument information
    pub args: Vec<VArgInfo>,
}

impl Default for VWireInfo {
    fn default() -> Self {
        VWireInfo {
            clock_info: VClockInfo::default(),
            reset_info: VResetInfo::default(),
            args: Vec::new(),
        }
    }
}

// ============================================================================
// VModInfo - Complete Module Information
// ============================================================================

/// Complete Verilog module information.
///
/// Mirrors `VModInfo` from VModInfo.hs:561-570:
/// ```haskell
/// data VModInfo = VModInfo {
///     vName :: VName,
///     vClk :: VClockInfo,
///     vRst :: VResetInfo,
///     vArgs :: [VArgInfo],
///     vFields :: [VFieldInfo],
///     vSched :: VSchedInfo,
///     vPath :: VPathInfo
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct VModInfo {
    /// `vName` - Name of Verilog module to use
    pub name: VName,
    /// `vClk` - Clock information
    pub clock_info: VClockInfo,
    /// `vRst` - Reset information
    pub reset_info: VResetInfo,
    /// `vArgs` - Module arguments
    pub args: Vec<VArgInfo>,
    /// `vFields` - Interface fields
    pub fields: Vec<VFieldInfo>,
    /// `vSched` - Scheduling information
    pub sched_info: VSchedInfo,
    /// `vPath` - Path timing information
    pub path_info: VPathInfo,
}

impl VModInfo {
    /// Create a new VModInfo.
    #[must_use]
    pub fn new(
        name: VName,
        clock_info: VClockInfo,
        reset_info: VResetInfo,
        args: Vec<VArgInfo>,
        fields: Vec<VFieldInfo>,
        sched_info: VSchedInfo,
        path_info: VPathInfo,
    ) -> Self {
        VModInfo {
            name,
            clock_info,
            reset_info,
            args,
            fields,
            sched_info,
            path_info,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_vname_creation() {
        let vn = VName::new("test_port");
        assert_eq!(vn.as_str(), "test_port");
    }

    #[test]
    fn test_vport_creation() {
        let vp = VPort::new(VName::new("clk"));
        assert_eq!(vp.name_str(), "clk");
        assert!(vp.props.is_empty());
    }

    #[test]
    fn test_varg_info_checks() {
        let param = VArgInfo::Param(VName::new("WIDTH"));
        assert!(param.is_param());
        assert!(!param.is_port());

        let clock = VArgInfo::ClockArg(Id::unpositioned("CLK"));
        assert!(clock.is_clock());
        assert!(!clock.is_reset());
    }

    #[test]
    fn test_either() {
        let left: Either<i32, String> = Either::Left(42);
        assert!(left.is_left());
        assert!(!left.is_right());
        assert_eq!(left.left_ref(), Some(&42));

        let right: Either<i32, String> = Either::Right("hello".to_string());
        assert!(right.is_right());
        assert!(!right.is_left());
    }
}
