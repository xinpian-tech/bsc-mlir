//! Display implementations for VModInfo types.
//!
//! These implementations produce output matching Haskell BSC's Show instances.

use std::fmt::{self, Display, Formatter};
use crate::id::Id;
use crate::vmodinfo::*;

impl Display for VName {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "VName \"{}\"", self.0)
    }
}

impl Display for VeriPortProp {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            VeriPortProp::Reg => write!(f, "VPreg"),
            VeriPortProp::Const => write!(f, "VPconst"),
            VeriPortProp::InHigh => write!(f, "VPinhigh"),
            VeriPortProp::OutHigh => write!(f, "VPouthigh"),
            VeriPortProp::Clock => write!(f, "VPclock"),
            VeriPortProp::ClockGate => write!(f, "VPclockgate"),
            VeriPortProp::Reset => write!(f, "VPreset"),
            VeriPortProp::Inout => write!(f, "VPinout"),
            VeriPortProp::Unused => write!(f, "VPunused"),
        }
    }
}

fn fmt_list<T: Display>(f: &mut Formatter<'_>, items: &[T]) -> fmt::Result {
    write!(f, "[")?;
    for (i, item) in items.iter().enumerate() {
        if i > 0 {
            write!(f, ",")?;
        }
        write!(f, "{}", item)?;
    }
    write!(f, "]")
}

fn fmt_option<T: Display>(f: &mut Formatter<'_>, opt: &Option<T>) -> fmt::Result {
    match opt {
        Some(v) => write!(f, "Just {}", v),
        None => write!(f, "Nothing"),
    }
}

fn fmt_option_id(f: &mut Formatter<'_>, opt: &Option<Id>) -> fmt::Result {
    match opt {
        Some(id) => write!(f, "Just {}", id),
        None => write!(f, "Nothing"),
    }
}

impl Display for VPort {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "({},", self.name)?;
        fmt_list(f, &self.props)?;
        write!(f, ")")
    }
}

impl<L: Display, R: Display> Display for Either<L, R> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Either::Left(l) => write!(f, "Left {}", l),
            Either::Right(r) => write!(f, "Right {}", r),
        }
    }
}

impl Display for VArgInfo {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            VArgInfo::Param(name) => write!(f, "Param ({})", name),
            VArgInfo::Port { port, clock, reset } => {
                write!(f, "Port {} ", port)?;
                fmt_option_id(f, clock)?;
                write!(f, " ")?;
                fmt_option_id(f, reset)
            }
            VArgInfo::ClockArg(id) => write!(f, "ClockArg {}", id),
            VArgInfo::ResetArg(id) => write!(f, "ResetArg {}", id),
            VArgInfo::InoutArg { name, clock, reset } => {
                write!(f, "InoutArg {} ", name)?;
                fmt_option_id(f, clock)?;
                write!(f, " ")?;
                fmt_option_id(f, reset)
            }
        }
    }
}

impl Display for VFieldInfo {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            VFieldInfo::Method { name, clock, reset, multiplicity, inputs, output, enable } => {
                write!(f, "Method {{vf_name = {}, vf_clock = ", name)?;
                fmt_option_id(f, clock)?;
                write!(f, ", vf_reset = ")?;
                fmt_option_id(f, reset)?;
                write!(f, ", vf_mult = {}, vf_inputs = ", multiplicity)?;
                fmt_list(f, inputs)?;
                write!(f, ", vf_output = ")?;
                fmt_option(f, output)?;
                write!(f, ", vf_enable = ")?;
                fmt_option(f, enable)?;
                write!(f, "}}")
            }
            VFieldInfo::Clock { name } => write!(f, "Clock {{vf_name = {}}}", name),
            VFieldInfo::Reset { name } => write!(f, "Reset {{vf_name = {}}}", name),
            VFieldInfo::Inout { name, inout, clock, reset } => {
                write!(f, "Inout {{vf_name = {}, vf_inout = {}, vf_clock = ", name, inout)?;
                fmt_option_id(f, clock)?;
                write!(f, ", vf_reset = ")?;
                fmt_option_id(f, reset)?;
                write!(f, "}}")
            }
        }
    }
}

fn fmt_input_clock_inf(f: &mut Formatter<'_>, icf: &InputClockInf) -> fmt::Result {
    write!(f, "({},", icf.0)?;
    match &icf.1 {
        None => write!(f, "Nothing)")?,
        Some((osc, gate)) => {
            write!(f, "Just ({},", osc)?;
            match gate {
                Either::Left(b) => write!(f, "Left {}", if *b { "True" } else { "False" })?,
                Either::Right(name) => write!(f, "Right {}", name)?,
            }
            write!(f, "))")?;
        }
    }
    Ok(())
}

fn fmt_output_clock_inf(f: &mut Formatter<'_>, ocf: &OutputClockInf) -> fmt::Result {
    write!(f, "({},", ocf.0)?;
    match &ocf.1 {
        None => write!(f, "Nothing)")?,
        Some((osc, gate)) => {
            write!(f, "Just ({},", osc)?;
            match gate {
                None => write!(f, "Nothing")?,
                Some(port) => write!(f, "Just {}", port)?,
            }
            write!(f, "))")?;
        }
    }
    Ok(())
}

fn fmt_input_clock_list(f: &mut Formatter<'_>, clocks: &[InputClockInf]) -> fmt::Result {
    write!(f, "[")?;
    for (i, clk) in clocks.iter().enumerate() {
        if i > 0 {
            write!(f, ",")?;
        }
        fmt_input_clock_inf(f, clk)?;
    }
    write!(f, "]")
}

fn fmt_output_clock_list(f: &mut Formatter<'_>, clocks: &[OutputClockInf]) -> fmt::Result {
    write!(f, "[")?;
    for (i, clk) in clocks.iter().enumerate() {
        if i > 0 {
            write!(f, ",")?;
        }
        fmt_output_clock_inf(f, clk)?;
    }
    write!(f, "]")
}

fn fmt_id_pair_list(f: &mut Formatter<'_>, pairs: &[(Id, Id)]) -> fmt::Result {
    write!(f, "[")?;
    for (i, (a, b)) in pairs.iter().enumerate() {
        if i > 0 {
            write!(f, ",")?;
        }
        write!(f, "({},{})", a, b)?;
    }
    write!(f, "]")
}

impl Display for VClockInfo {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "ClockInfo {{input_clocks = ")?;
        fmt_input_clock_list(f, &self.input_clocks)?;
        write!(f, ", output_clocks = ")?;
        fmt_output_clock_list(f, &self.output_clocks)?;
        write!(f, ", ancestorClocks = ")?;
        fmt_id_pair_list(f, &self.ancestor_clocks)?;
        write!(f, ", siblingClocks = ")?;
        fmt_id_pair_list(f, &self.sibling_clocks)?;
        write!(f, "}}")
    }
}

fn fmt_reset_inf(f: &mut Formatter<'_>, reset: &ResetInf) -> fmt::Result {
    write!(f, "({},", reset.0)?;
    write!(f, "(")?;
    match &reset.1.0 {
        None => write!(f, "Nothing")?,
        Some(name) => write!(f, "Just ({})", name)?,
    }
    write!(f, ",")?;
    fmt_option_id(f, &reset.1.1)?;
    write!(f, "))")
}

fn fmt_reset_list(f: &mut Formatter<'_>, resets: &[ResetInf]) -> fmt::Result {
    write!(f, "[")?;
    for (i, rst) in resets.iter().enumerate() {
        if i > 0 {
            write!(f, ",")?;
        }
        fmt_reset_inf(f, rst)?;
    }
    write!(f, "]")
}

impl Display for VResetInfo {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "ResetInfo {{input_resets = ")?;
        fmt_reset_list(f, &self.input_resets)?;
        write!(f, ", output_resets = ")?;
        fmt_reset_list(f, &self.output_resets)?;
        write!(f, "}}")
    }
}

impl Display for VPathInfo {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "VPathInfo ")?;
        write!(f, "[")?;
        for (i, (inp, out)) in self.0.iter().enumerate() {
            if i > 0 {
                write!(f, ",")?;
            }
            write!(f, "({},{})", inp, out)?;
        }
        write!(f, "]")
    }
}

impl<T: Display> Display for MethodConflictInfo<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "MethodConflictInfo {{sCF = ")?;
        fmt_pair_list(f, &self.conflict_free)?;
        write!(f, ", sSB = ")?;
        fmt_pair_list(f, &self.sequenced_before)?;
        write!(f, ", sME = ")?;
        fmt_list_of_lists(f, &self.mutually_exclusive)?;
        write!(f, ", sP = ")?;
        fmt_pair_list(f, &self.preempts)?;
        write!(f, ", sSBR = ")?;
        fmt_pair_list(f, &self.sequenced_before_reverse)?;
        write!(f, ", sC = ")?;
        fmt_pair_list(f, &self.conflicts)?;
        write!(f, ", sEXT = ")?;
        fmt_list(f, &self.external)?;
        write!(f, "}}")
    }
}

fn fmt_pair_list<T: Display>(f: &mut Formatter<'_>, pairs: &[(T, T)]) -> fmt::Result {
    write!(f, "[")?;
    for (i, (a, b)) in pairs.iter().enumerate() {
        if i > 0 {
            write!(f, ",")?;
        }
        write!(f, "({},{})", a, b)?;
    }
    write!(f, "]")
}

fn fmt_list_of_lists<T: Display>(f: &mut Formatter<'_>, lists: &[Vec<T>]) -> fmt::Result {
    write!(f, "[")?;
    for (i, list) in lists.iter().enumerate() {
        if i > 0 {
            write!(f, ",")?;
        }
        fmt_list(f, list)?;
    }
    write!(f, "]")
}

impl<T: Display + Clone> Display for SchedInfo<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "SchedInfo {{methodConflictInfo = {}", self.method_conflict_info)?;
        write!(f, ", rulesBetweenMethods = ")?;
        fmt_rules_between(f, &self.rules_between_methods)?;
        write!(f, ", rulesBeforeMethods = ")?;
        fmt_rules_before(f, &self.rules_before_methods)?;
        write!(f, ", clockCrossingMethods = ")?;
        fmt_list(f, &self.clock_crossing_methods)?;
        write!(f, "}}")
    }
}

fn fmt_rules_between<T: Display>(f: &mut Formatter<'_>, rules: &[((T, T), Vec<T>)]) -> fmt::Result {
    write!(f, "[")?;
    for (i, ((a, b), rs)) in rules.iter().enumerate() {
        if i > 0 {
            write!(f, ",")?;
        }
        write!(f, "(({},{}),", a, b)?;
        fmt_list(f, rs)?;
        write!(f, ")")?;
    }
    write!(f, "]")
}

fn fmt_rules_before<T: Display + Clone>(f: &mut Formatter<'_>, rules: &[(T, Vec<Either<T, T>>)]) -> fmt::Result {
    write!(f, "[")?;
    for (i, (id, eithers)) in rules.iter().enumerate() {
        if i > 0 {
            write!(f, ",")?;
        }
        write!(f, "({},", id)?;
        fmt_list(f, eithers)?;
        write!(f, ")")?;
    }
    write!(f, "]")
}
