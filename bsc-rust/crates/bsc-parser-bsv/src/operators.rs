//! Operator table and expression parsing infrastructure for BSV parser.
//!
//! Mirrors `opTable` and related functions from `src/comp/Parser/BSV/CVParser.lhs`
//! around lines 3767-3807.
//!
//! The operator table defines precedence and associativity for all BSV operators,
//! including prefix reduction operators and binary infix operators.

use bsc_diagnostics::Position;
use bsc_lexer_bsv::TokenKind;
use bsc_syntax::{CExpr, Id};

/// Associativity of binary operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Associativity {
    /// Left associative (a + b + c = (a + b) + c)
    Left,
    /// Right associative (a = b = c = a = (b = c))
    Right,
    /// Non-associative (a == b == c is an error)
    None,
}

/// Type of operator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OperatorType {
    /// Prefix operator (unary)
    Prefix,
    /// Binary infix operator
    Binary(Associativity),
}

/// An operator in the precedence table.
#[derive(Debug, Clone)]
pub struct Operator {
    /// Token kind that represents this operator
    pub token: TokenKind,
    /// Type and associativity of the operator
    pub op_type: OperatorType,
    /// Function to create the operator Id with position
    pub id_builder: fn(Position) -> Id,
}

impl Operator {
    /// Create a new prefix operator.
    pub const fn prefix(token: TokenKind, id_builder: fn(Position) -> Id) -> Self {
        Self {
            token,
            op_type: OperatorType::Prefix,
            id_builder,
        }
    }

    /// Create a new left-associative binary operator.
    pub const fn binary_left(token: TokenKind, id_builder: fn(Position) -> Id) -> Self {
        Self {
            token,
            op_type: OperatorType::Binary(Associativity::Left),
            id_builder,
        }
    }

    /// Create a new right-associative binary operator.
    pub const fn binary_right(token: TokenKind, id_builder: fn(Position) -> Id) -> Self {
        Self {
            token,
            op_type: OperatorType::Binary(Associativity::Right),
            id_builder,
        }
    }

    /// Create a new non-associative binary operator.
    pub const fn binary_none(token: TokenKind, id_builder: fn(Position) -> Id) -> Self {
        Self {
            token,
            op_type: OperatorType::Binary(Associativity::None),
            id_builder,
        }
    }

    /// Check if this operator matches the given token.
    pub fn matches(&self, token: &TokenKind) -> bool {
        std::mem::discriminant(&self.token) == std::mem::discriminant(token)
    }

    /// Create the operator Id for this operator at the given position.
    pub fn create_id(&self, position: Position) -> Id {
        (self.id_builder)(position)
    }
}

// ============================================================================
// Operator ID builders
//
// These mirror the `id*At` functions from `src/comp/PreIds.hs`.
// Each function creates an Id for the corresponding operator with the given position.
// ============================================================================

/// Create identity operator Id (+expr).
pub fn id_identity_at(pos: Position) -> Id {
    prelude_id(pos, "id")
}

/// Create negation operator Id (-expr).
pub fn id_negate_at(pos: Position) -> Id {
    prelude_id(pos, "negate")
}

/// Create logical not operator Id (!expr).
pub fn id_not_at(pos: Position) -> Id {
    prelude_id(pos, "not")
}

/// Create bitwise invert operator Id (~expr).
pub fn id_invert_at(pos: Position) -> Id {
    prelude_id(pos, "invert")
}

/// Create reduce-and operator Id (&expr).
pub fn id_reduce_and_at(pos: Position) -> Id {
    prelude_id(pos, "reduceAnd")
}

/// Create reduce-or operator Id (|expr).
pub fn id_reduce_or_at(pos: Position) -> Id {
    prelude_id(pos, "reduceOr")
}

/// Create reduce-xor operator Id (^expr).
pub fn id_reduce_xor_at(pos: Position) -> Id {
    prelude_id(pos, "reduceXor")
}

/// Create reduce-nand operator Id (~&expr).
pub fn id_reduce_nand_at(pos: Position) -> Id {
    prelude_id(pos, "reduceNand")
}

/// Create reduce-nor operator Id (~|expr).
pub fn id_reduce_nor_at(pos: Position) -> Id {
    prelude_id(pos, "reduceNor")
}

/// Create reduce-xnor operator Id (~^expr or ^~expr).
pub fn id_reduce_xnor_at(pos: Position) -> Id {
    prelude_id(pos, "reduceXnor")
}

/// Create exponentiation operator Id (a ** b).
pub fn id_star_star_at(pos: Position) -> Id {
    prelude_id(pos, "**")
}

/// Create multiplication operator Id (a * b).
pub fn id_star_at(pos: Position) -> Id {
    prelude_id(pos, "*")
}

/// Create division operator Id (a / b).
pub fn id_slash_at(pos: Position) -> Id {
    prelude_id(pos, "/")
}

/// Create modulo operator Id (a % b).
pub fn id_percent_at(pos: Position) -> Id {
    prelude_id(pos, "%")
}

/// Create addition operator Id (a + b).
pub fn id_plus_at(pos: Position) -> Id {
    prelude_id(pos, "+")
}

/// Create subtraction operator Id (a - b).
pub fn id_minus_at(pos: Position) -> Id {
    prelude_id(pos, "-")
}

/// Create left shift operator Id (a << b).
pub fn id_lsh_at(pos: Position) -> Id {
    prelude_id(pos, "<<")
}

/// Create right shift operator Id (a >> b).
pub fn id_rsh_at(pos: Position) -> Id {
    prelude_id(pos, ">>")
}

/// Create less-than operator Id (a < b).
pub fn id_lt_at(pos: Position) -> Id {
    prelude_id(pos, "<")
}

/// Create less-than-or-equal operator Id (a <= b).
pub fn id_lt_eq_at(pos: Position) -> Id {
    prelude_id(pos, "<=")
}

/// Create greater-than operator Id (a > b).
pub fn id_gt_at(pos: Position) -> Id {
    prelude_id(pos, ">")
}

/// Create greater-than-or-equal operator Id (a >= b).
pub fn id_gt_eq_at(pos: Position) -> Id {
    prelude_id(pos, ">=")
}

/// Create equality operator Id (a == b).
pub fn id_equal_at(pos: Position) -> Id {
    prelude_id(pos, "==")
}

/// Create inequality operator Id (a != b).
pub fn id_not_equal_at(pos: Position) -> Id {
    prelude_id(pos, "!=")
}

/// Create bitwise and operator Id (a & b).
pub fn id_bit_and_at(pos: Position) -> Id {
    prelude_id(pos, "&")
}

/// Create bitwise xor operator Id (a ^ b).
pub fn id_caret_at(pos: Position) -> Id {
    prelude_id(pos, "^")
}

/// Create bitwise xnor operator Id (a ~^ b).
pub fn id_tilde_caret_at(pos: Position) -> Id {
    prelude_id(pos, "~^")
}

/// Create bitwise xnor operator Id (a ^~ b).
pub fn id_caret_tilde_at(pos: Position) -> Id {
    prelude_id(pos, "^~")
}

/// Create bitwise or operator Id (a | b).
pub fn id_bit_or_at(pos: Position) -> Id {
    prelude_id(pos, "|")
}

/// Create logical and operator Id (a && b).
pub fn id_and_at(pos: Position) -> Id {
    prelude_id(pos, "&&")
}

/// Create logical or operator Id (a || b).
pub fn id_or_at(pos: Position) -> Id {
    prelude_id(pos, "||")
}

/// Helper function to create prelude identifiers.
///
/// This mirrors `prelude_id` from the Haskell implementation.
/// Prelude identifiers are qualified with the "Prelude" module.
fn prelude_id(pos: Position, name: &str) -> Id {
    Id::qualified("Prelude", name, pos)
}

// ============================================================================
// Operator Precedence Table
//
// This mirrors the `opTable` from `src/comp/Parser/BSV/CVParser.lhs` lines 3767-3807.
// Each inner Vec represents operators at the same precedence level.
// Higher indices = higher precedence (tighter binding).
// ============================================================================

/// Complete operator precedence table for BSV expressions.
///
/// This table is organized by precedence levels, with each level containing
/// operators of the same precedence. Higher array indices represent higher
/// precedence (tighter binding).
///
/// The table structure matches exactly with the Haskell `opTable`:
/// - Level 0: Prefix operators (+, -, !, ~, &, |, ^, ~&, ~|, ~^, ^~)
/// - Level 1: Exponentiation (**)
/// - Level 2: Multiplicative (*, /, %)
/// - Level 3: Additive (+, -)
/// - Level 4: Shift (<<, >>)
/// - Level 5: Relational (<, <=, >, >=)
/// - Level 6: Equality (==, !=)
/// - Level 7: Bitwise AND (&)
/// - Level 8: Bitwise XOR (^, ~^, ^~)
/// - Level 9: Bitwise OR (|)
/// - Level 10: Logical AND (&&)
/// - Level 11: Logical OR (||)
pub static OPERATOR_TABLE: &[&[Operator]] = &[
    // Level 0: Prefix operators (highest precedence)
    &[
        Operator::prefix(TokenKind::SymPlus, id_identity_at),        // +expr
        Operator::prefix(TokenKind::SymMinus, id_negate_at),         // -expr
        Operator::prefix(TokenKind::SymBang, id_not_at),             // !expr
        Operator::prefix(TokenKind::SymTilde, id_invert_at),         // ~expr
        Operator::prefix(TokenKind::SymAnd, id_reduce_and_at),       // &expr
        Operator::prefix(TokenKind::SymPipe, id_reduce_or_at),       // |expr
        Operator::prefix(TokenKind::SymCaret, id_reduce_xor_at),     // ^expr
        Operator::prefix(TokenKind::SymTildeAnd, id_reduce_nand_at), // ~&expr
        Operator::prefix(TokenKind::SymTildePipe, id_reduce_nor_at), // ~|expr
        Operator::prefix(TokenKind::SymTildeCaret, id_reduce_xnor_at), // ~^expr
        Operator::prefix(TokenKind::SymCaretTilde, id_reduce_xnor_at), // ^~expr
    ],
    // Level 1: Exponentiation
    &[
        Operator::binary_left(TokenKind::SymStarStar, id_star_star_at), // **
    ],
    // Level 2: Multiplicative
    &[
        Operator::binary_left(TokenKind::SymStar, id_star_at),       // *
        Operator::binary_left(TokenKind::SymSlash, id_slash_at),     // /
        Operator::binary_left(TokenKind::SymPercent, id_percent_at), // %
    ],
    // Level 3: Additive
    &[
        Operator::binary_left(TokenKind::SymPlus, id_plus_at),   // +
        Operator::binary_left(TokenKind::SymMinus, id_minus_at), // -
    ],
    // Level 4: Shift
    &[
        Operator::binary_left(TokenKind::SymLtLt, id_lsh_at),  // <<
        Operator::binary_left(TokenKind::SymGtGt, id_rsh_at),  // >>
        // Note: <<< and >>> are commented out in the original Haskell
    ],
    // Level 5: Relational
    &[
        Operator::binary_left(TokenKind::SymLt, id_lt_at),       // <
        Operator::binary_left(TokenKind::SymLtEq, id_lt_eq_at),  // <=
        Operator::binary_left(TokenKind::SymGt, id_gt_at),       // >
        Operator::binary_left(TokenKind::SymGtEq, id_gt_eq_at),  // >=
    ],
    // Level 6: Equality
    &[
        Operator::binary_left(TokenKind::SymEqEq, id_equal_at),       // ==
        Operator::binary_left(TokenKind::SymBangEq, id_not_equal_at), // !=
        // Note: ===, !==, =?=, !?= are commented out in the original Haskell
    ],
    // Level 7: Bitwise AND
    &[
        Operator::binary_left(TokenKind::SymAnd, id_bit_and_at), // &
    ],
    // Level 8: Bitwise XOR
    &[
        Operator::binary_left(TokenKind::SymCaret, id_caret_at),           // ^
        Operator::binary_left(TokenKind::SymTildeCaret, id_tilde_caret_at), // ~^
        Operator::binary_left(TokenKind::SymCaretTilde, id_caret_tilde_at), // ^~
    ],
    // Level 9: Bitwise OR
    &[
        Operator::binary_left(TokenKind::SymPipe, id_bit_or_at), // |
    ],
    // Level 10: Logical AND
    &[
        Operator::binary_left(TokenKind::SymAndAnd, id_and_at), // &&
    ],
    // Level 11: Logical OR (lowest precedence)
    &[
        Operator::binary_left(TokenKind::SymPipePipe, id_or_at), // ||
    ],
];

/// Find an operator by token kind and precedence level.
pub fn find_operator(token: &TokenKind, level: usize) -> Option<&'static Operator> {
    if level >= OPERATOR_TABLE.len() {
        return None;
    }

    OPERATOR_TABLE[level]
        .iter()
        .find(|op| op.matches(token))
}

/// Get all prefix operators (level 0).
pub fn prefix_operators() -> &'static [Operator] {
    OPERATOR_TABLE[0]
}

/// Get all binary operators at the specified precedence level.
pub fn binary_operators(level: usize) -> Option<&'static [Operator]> {
    if level == 0 || level >= OPERATOR_TABLE.len() {
        None
    } else {
        Some(OPERATOR_TABLE[level])
    }
}

/// Get the total number of precedence levels.
pub fn precedence_levels() -> usize {
    OPERATOR_TABLE.len()
}

/// Check if a token is a prefix operator.
pub fn is_prefix_operator(token: &TokenKind) -> bool {
    find_operator(token, 0).is_some()
}

/// Check if a token is a binary operator at any precedence level.
pub fn is_binary_operator(token: &TokenKind) -> bool {
    for level in 1..OPERATOR_TABLE.len() {
        if find_operator(token, level).is_some() {
            return true;
        }
    }
    false
}

/// Get the precedence level of a binary operator (returns None for prefix operators).
pub fn binary_precedence(token: &TokenKind) -> Option<usize> {
    for level in 1..OPERATOR_TABLE.len() {
        if find_operator(token, level).is_some() {
            return Some(level);
        }
    }
    None
}

// ============================================================================
// Expression Construction Helpers
// ============================================================================

/// Create a function application expression.
///
/// This mirrors the pattern from CVParser.lhs where operators are applied
/// as function calls: `CBinOp left op right` becomes `CApply op [left, right]`.
pub fn make_binary_expr(left: CExpr, op_id: Id, right: CExpr) -> CExpr {
    use bsc_diagnostics::Span;
    let op_pos = op_id.position();
    let span = Span::DUMMY;
    CExpr::Apply(Box::new(CExpr::Var(op_id.clone())), vec![left, right], span)
}

/// Create a unary prefix expression.
///
/// This creates a function application for prefix operators.
pub fn make_prefix_expr(op_id: Id, operand: CExpr) -> CExpr {
    use bsc_diagnostics::Span;
    let op_pos = op_id.position();
    let span = Span::DUMMY;
    CExpr::Apply(Box::new(CExpr::Var(op_id.clone())), vec![operand], span)
}

