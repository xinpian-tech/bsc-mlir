//! Literal values in BSC source code.

use std::fmt;

/// A literal value in source code.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Literal {
    /// Integer literal with optional size and base info
    Integer(IntLiteral),
    /// Floating point literal
    Float(OrderedFloat),
    /// Character literal
    Char(char),
    /// String literal
    String(String),
    /// Position literal - placeholder for $location in BSV
    /// The actual position is stored in CLiteral, this is just a marker
    Position,
}

/// A wrapper for f64 that implements Eq using bit comparison.
/// This treats NaN values as equal to each other (same bits = equal).
#[derive(Debug, Clone, Copy)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct OrderedFloat(pub f64);

impl OrderedFloat {
    /// Create a new ordered float.
    #[must_use]
    pub const fn new(value: f64) -> Self {
        Self(value)
    }

    /// Get the inner f64 value.
    #[must_use]
    pub const fn value(self) -> f64 {
        self.0
    }
}

impl PartialEq for OrderedFloat {
    fn eq(&self, other: &Self) -> bool {
        self.0.to_bits() == other.0.to_bits()
    }
}

impl Eq for OrderedFloat {}

impl std::hash::Hash for OrderedFloat {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.to_bits().hash(state);
    }
}

impl From<f64> for OrderedFloat {
    fn from(value: f64) -> Self {
        Self(value)
    }
}

impl From<OrderedFloat> for f64 {
    fn from(value: OrderedFloat) -> Self {
        value.0
    }
}

impl PartialEq for Literal {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Literal::Integer(a), Literal::Integer(b)) => a == b,
            (Literal::Float(a), Literal::Float(b)) => a == b,
            (Literal::Char(a), Literal::Char(b)) => a == b,
            (Literal::String(a), Literal::String(b)) => a == b,
            (Literal::Position, Literal::Position) => true,
            _ => false,
        }
    }
}

impl Eq for Literal {}

/// An integer literal with size and base information.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct IntLiteral {
    /// The integer value
    pub value: i128,
    /// Optional bit width (e.g., 8 in 8'hFF)
    pub width: Option<u32>,
    /// The base the literal was written in
    pub base: IntBase,
}

impl IntLiteral {
    /// Create a new integer literal.
    #[must_use]
    pub const fn new(value: i128, width: Option<u32>, base: IntBase) -> Self {
        Self { value, width, base }
    }

    /// Create a simple decimal integer literal.
    #[must_use]
    pub const fn decimal(value: i128) -> Self {
        Self {
            value,
            width: None,
            base: IntBase::Decimal,
        }
    }
}

/// The base of an integer literal.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum IntBase {
    Binary,
    Octal,
    Decimal,
    Hexadecimal,
}

impl fmt::Display for OrderedFloat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Literal::Integer(int) => write!(f, "{int}"),
            Literal::Float(v) => write!(f, "{v}"),
            Literal::Char(c) => write!(f, "'{c}'"),
            Literal::String(s) => write!(f, "\"{s}\""),
            Literal::Position => write!(f, "<Position>"),
        }
    }
}

impl fmt::Display for IntLiteral {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(width) = self.width {
            match self.base {
                IntBase::Binary => write!(f, "{width}'b{:b}", self.value),
                IntBase::Octal => write!(f, "{width}'o{:o}", self.value),
                IntBase::Decimal => write!(f, "{width}'d{}", self.value),
                IntBase::Hexadecimal => write!(f, "{width}'h{:x}", self.value),
            }
        } else {
            match self.base {
                IntBase::Binary => write!(f, "0b{:b}", self.value),
                IntBase::Octal => write!(f, "0o{:o}", self.value),
                IntBase::Decimal => write!(f, "{}", self.value),
                IntBase::Hexadecimal => write!(f, "0x{:X}", self.value),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_int_literal_display() {
        let lit = IntLiteral::new(255, Some(8), IntBase::Hexadecimal);
        assert_eq!(format!("{lit}"), "8'hFF");

        let lit = IntLiteral::decimal(42);
        assert_eq!(format!("{lit}"), "42");
    }
}
