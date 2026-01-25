//! Type expression parsing for BSV.
//!
//! This module mirrors the type parsing functions from `src/comp/Parser/BSV/CVParser.lhs`.
//! It implements BSV's type syntax including sugar types and type constructors.
//!
//! # BSV Type Syntax
//!
//! BSV supports several forms of type expressions:
//!
//! ## Sugar Types (Built-in syntax shortcuts)
//! - `bit` → `Bit#(1)` (single bit)
//! - `bit[h:0]` → `Bit#(h+1)` (bit vector of size h+1)
//! - `int` → `Int#(32)` (32-bit signed integer)
//! - `real` → `Real` (real/floating point)
//! - `void` → `()` (unit type)
//! - `Action` → `Action` (action type)
//! - `ActionValue` → requires parameters: `ActionValue#(T)`
//!
//! ## Type Constructors
//! - Regular type constructors: `Vector`, `Maybe`, `List`, etc.
//! - Type variables: lowercase identifiers
//! - The special `module` keyword (represents current monad type)
//!
//! ## Function Types
//! ```text
//! function return_type name(arg1_type, arg2_type, ...);
//! ```
//!
//! ## Parametric Types
//! ```text
//! TypeName#(param1, param2, ...)
//! ```
//!
//! ## Provisos (Type Constraints)
//! ```text
//! provisos (constraint1#(types), constraint2#(types), ...)
//! ```
//!
//! # Grammar Rules
//!
//! The main type expression grammar (from CVParser.lhs):
//! ```text
//! pTypeExpr ::= pBitType
//!            |  pIntType
//!            |  pRealType
//!            |  pVoidType
//!            |  pActionType
//!            |  pActionValueType
//!            |  ( pTypeConstructor | pTypeVariable | pDefMonadType ) pTypeExprWith?
//!            |  pFunctionType
//!            |  '(' pTypeExpr ')'
//! ```
//!
//! Where:
//! - `pTypeExprWith` handles optional type parameters: `#(type1, type2, ...)`
//! - `pTypeConstructor` parses qualified type constructors
//! - `pTypeVariable` parses lowercase type variables
//! - `pDefMonadType` parses the `module` keyword
//!
//! # Implementation Notes
//!
//! The Haskell implementation uses these helper functions (from `src/comp/Type.hs`):
//! - `tInt32At pos` → creates `Int#(32)` at position
//! - `tRealAt pos` → creates `Real` at position
//! - `tActionAt pos` → creates `Action` at position
//! - `tActionValueAt pos` → creates base `ActionValue` constructor at position
//!
//! These create the appropriate `CType` AST nodes with position information.

use crate::{BsvParser, ParseResult};
use bsc_diagnostics::{Position, Span};
use bsc_lexer_bsv::TokenKind;
use bsc_syntax::{CType, CPred, Id};

impl<'src> BsvParser<'src> {
    /// Parse a type expression.
    ///
    /// Implements `pTypeExpr` from CVParser.lhs.
    ///
    /// Grammar:
    /// ```text
    /// pTypeExpr ::= pBitType
    ///            |  pIntType
    ///            |  pRealType
    ///            |  pVoidType
    ///            |  pActionType
    ///            |  pActionValueType
    ///            |  ( pTypeConstructor | pTypeVariable | pDefMonadType ) pTypeExprWith?
    ///            |  pFunctionType
    ///            |  '(' pTypeExpr ')'
    /// ```
    pub fn parse_type_expr(&mut self) -> ParseResult<CType> {
        // Try sugar types first
        if let Ok(ty) = self.parse_bit_type() {
            return Ok(ty);
        }
        if let Ok(ty) = self.parse_int_type() {
            return Ok(ty);
        }
        if let Ok(ty) = self.parse_real_type() {
            return Ok(ty);
        }
        if let Ok(ty) = self.parse_void_type() {
            return Ok(ty);
        }
        if let Ok(ty) = self.parse_action_type() {
            return Ok(ty);
        }
        if let Ok(ty) = self.parse_action_value_type() {
            return Ok(ty);
        }

        // Try type constructors, variables, and module keyword
        if let Ok(base_type) = self.parse_type_constructor()
            .or_else(|_| self.parse_type_variable())
            .or_else(|_| self.parse_def_monad_type())
        {
            // Try to parse type parameters with pTypeExprWith
            return self.parse_type_expr_with(base_type);
        }

        // Try function type
        if let Ok(ty) = self.parse_function_type() {
            return Ok(ty);
        }

        // Try parenthesized type expression
        if self.eat(&TokenKind::SymLParen) {
            let ty = self.parse_type_expr()?;
            self.expect(&TokenKind::SymRParen)?;
            let span = Span::DUMMY; // TODO: Calculate proper span
            return Ok(CType::Paren(Box::new(ty), span));
        }

        Err(self.unexpected_token("type expression"))
    }

    /// Parse optional type parameters and apply them to a base type.
    ///
    /// Implements `pTypeExprWith` from CVParser.lhs.
    ///
    /// Grammar: `#(type1, type2, ...)`
    fn parse_type_expr_with(&mut self, base_type: CType) -> ParseResult<CType> {
        if let Some(params) = self.parse_type_parameters_optional()? {
            Ok(self.apply_type_params(base_type, params))
        } else {
            Ok(base_type)
        }
    }

    /// Parse required type parameters and apply them to a base type.
    ///
    /// Implements `pTypeExprRequiredParamsWith` from CVParser.lhs.
    /// Used by ActionValue which requires type parameters.
    fn parse_type_expr_required_params_with(&mut self, base_type: CType) -> ParseResult<CType> {
        let params = self.parse_type_parameters_required()?;
        Ok(self.apply_type_params(base_type, params))
    }

    // ========================================================================
    // Sugar Types - Built-in type syntax shortcuts
    // ========================================================================

    /// Parse `bit` type.
    ///
    /// Implements `pBitType` from CVParser.lhs.
    ///
    /// Grammar:
    /// - `bit` → `Bit#(1)`
    /// - `bit[h:0]` → `Bit#(h+1)`
    fn parse_bit_type(&mut self) -> ParseResult<CType> {
        if !matches!(self.current_kind(), TokenKind::KwBit) {
            return Err(self.unexpected_token("'bit'"));
        }

        let pos = Position::unknown();
        self.advance(); // consume 'bit'

        // Check for bit range: [h:0]
        let width = if self.eat(&TokenKind::SymLBracket) {
            // Parse high index
            let high = self.parse_bit_range()?;
            self.expect(&TokenKind::SymRBracket)?;
            high + 1 // bit[h:0] has h+1 bits
        } else {
            1 // plain 'bit' is Bit#(1)
        };

        // Create Bit#(width)
        let bit_con = CType::Con(Id::new("Bit", pos.clone()));
        let width_type = CType::Num(width as i128, pos.clone());
        let span = Span::DUMMY; // TODO: Calculate proper span

        Ok(CType::Apply(
            Box::new(bit_con),
            Box::new(width_type),
            span,
        ))
    }

    /// Parse bit range (the number inside bit[n:0]).
    fn parse_bit_range(&mut self) -> ParseResult<u32> {
        // TODO: Parse proper bit range expression
        // For now, just parse a simple integer
        match self.current_kind() {
            TokenKind::Integer { value, .. } => {
                if let Ok(n) = value.try_into() {
                    let value: u32 = n;
                    self.advance();
                    Ok(value)
                } else {
                    Err(self.unexpected_token("valid integer"))
                }
            }
            _ => Err(self.unexpected_token("integer")),
        }
    }

    /// Parse `int` type (32-bit signed integer).
    ///
    /// Implements `pIntType` from CVParser.lhs.
    /// Maps to `tInt32At pos` → `Int#(32)`
    fn parse_int_type(&mut self) -> ParseResult<CType> {
        if !matches!(self.current_kind(), TokenKind::KwInt) {
            return Err(self.unexpected_token("'int'"));
        }

        let pos = Position::unknown();
        self.advance(); // consume 'int'

        // Create Int#(32) - mirrors tInt32At from Type.hs
        Ok(create_int32_type(pos.clone()))
    }

    /// Parse `real` type.
    ///
    /// Implements `pRealType` from CVParser.lhs.
    /// Maps to `tRealAt pos` → `Real`
    fn parse_real_type(&mut self) -> ParseResult<CType> {
        if !matches!(self.current_kind(), TokenKind::KwReal) {
            return Err(self.unexpected_token("'real'"));
        }

        let pos = Position::unknown();
        self.advance(); // consume 'real'

        Ok(create_real_type(pos.clone()))
    }

    /// Parse `void` type (unit type).
    ///
    /// Implements `pVoidType` from CVParser.lhs.
    /// Maps to `cTCon idPrimUnit` → `()`
    fn parse_void_type(&mut self) -> ParseResult<CType> {
        if !matches!(self.current_kind(), TokenKind::KwVoid) {
            return Err(self.unexpected_token("'void'"));
        }

        let pos = Position::unknown();
        self.advance(); // consume 'void'

        Ok(CType::Con(Id::new("()", pos.clone())))
    }

    /// Parse `Action` type.
    ///
    /// Implements `pActionType` from CVParser.lhs.
    /// Maps to `tActionAt pos` → `Action`
    fn parse_action_type(&mut self) -> ParseResult<CType> {
        if !matches!(self.current_kind(), TokenKind::KwActionType) {
            return Err(self.unexpected_token("'Action'"));
        }

        let pos = Position::unknown();
        self.advance(); // consume 'Action'

        Ok(create_action_type(pos.clone()))
    }

    /// Parse `ActionValue` type with required type parameters.
    ///
    /// Implements `pActionValueType` from CVParser.lhs.
    /// Grammar: `ActionValue#(T)` - type parameters are required
    fn parse_action_value_type(&mut self) -> ParseResult<CType> {
        if !matches!(self.current_kind(), TokenKind::KwActionValueType) {
            return Err(self.unexpected_token("'ActionValue'"));
        }

        let pos = Position::unknown();
        self.advance(); // consume 'ActionValue'

        let base_type = create_action_value_type(pos.clone());
        self.parse_type_expr_required_params_with(base_type)
    }

    // ========================================================================
    // Type Constructors and Variables
    // ========================================================================

    /// Parse a type constructor.
    ///
    /// Implements `pTypeConstructor` from CVParser.lhs.
    /// Handles qualified constructors and creates `cTCon cons`.
    fn parse_type_constructor(&mut self) -> ParseResult<CType> {
        // TODO: Implement proper qualified constructor parsing
        // For now, just parse a simple uppercase identifier
        if let TokenKind::Id(name) = self.current_kind() {
            // Check if it's an uppercase identifier (type constructor)
            if name.chars().next().unwrap_or('a').is_ascii_uppercase() {
                let pos = Position::unknown();
                let id = Id::new(name.clone(), pos.clone());
                self.advance();
                Ok(CType::Con(id))
            } else {
                Err(self.unexpected_token("type constructor"))
            }
        } else {
            Err(self.unexpected_token("type constructor"))
        }
    }

    /// Parse a type variable.
    ///
    /// Implements `pTypeVariable` from CVParser.lhs.
    /// Maps to `fmap cTVar (pIdentifier <?> "type variable")`
    fn parse_type_variable(&mut self) -> ParseResult<CType> {
        // Type variables are lowercase identifiers
        if let TokenKind::Id(name) = self.current_kind() {
            // Check if it's a lowercase identifier (type variable)
            if name.chars().next().unwrap_or('A').is_ascii_lowercase() {
                let pos = Position::unknown();
                let id = Id::new(name.clone(), pos.clone());
                self.advance();
                Ok(CType::Var(id))
            } else {
                Err(self.unexpected_token("type variable"))
            }
        } else {
            Err(self.unexpected_token("type variable"))
        }
    }

    /// Parse the `module` keyword as a type.
    ///
    /// Implements `pDefMonadType` from CVParser.lhs.
    /// The `module` keyword represents the current default monad type.
    fn parse_def_monad_type(&mut self) -> ParseResult<CType> {
        if !matches!(self.current_kind(), TokenKind::KwModule) {
            return Err(self.unexpected_token("'module'"));
        }

        let pos = Position::unknown();
        self.advance(); // consume 'module'

        // TDefMonad matches the Haskell implementation
        Ok(CType::DefMonad(pos.clone()))
    }

    // ========================================================================
    // Function Types
    // ========================================================================

    /// Parse a function type.
    ///
    /// Implements `pFunctionType` from CVParser.lhs.
    ///
    /// Grammar: `function return_type name(arg1_type, arg2_type, ...);`
    fn parse_function_type(&mut self) -> ParseResult<CType> {
        if !matches!(self.current_kind(), TokenKind::KwFunction) {
            return Err(self.unexpected_token("'function'"));
        }

        // TODO: Implement full function type parsing
        // This requires parsing function prototypes and extracting the type
        Err(self.unexpected_token("function type parsing not yet implemented"))
    }

    // ========================================================================
    // Type Parameters
    // ========================================================================

    /// Parse optional type parameters.
    ///
    /// Implements `pTypeParameters` from CVParser.lhs.
    ///
    /// Grammar: `#(type1, type2, ...)` or nothing
    /// Returns None if no parameters are present.
    fn parse_type_parameters_optional(&mut self) -> ParseResult<Option<Vec<CType>>> {
        if self.eat(&TokenKind::SymHash) {
            self.expect(&TokenKind::SymLParen)?;
            let params = self.parse_comma_separated_types()?;
            self.expect(&TokenKind::SymRParen)?;
            Ok(Some(params))
        } else {
            Ok(None)
        }
    }

    /// Parse required type parameters.
    ///
    /// Implements `pTypeParametersNonOptional` from CVParser.lhs.
    ///
    /// Grammar: `#(type1, type2, ...)` - parameters are required
    fn parse_type_parameters_required(&mut self) -> ParseResult<Vec<CType>> {
        self.expect(&TokenKind::SymHash)?;
        self.expect(&TokenKind::SymLParen)?;
        let params = self.parse_comma_separated_types()?;
        self.expect(&TokenKind::SymRParen)?;
        Ok(params)
    }

    /// Parse a comma-separated list of types.
    fn parse_comma_separated_types(&mut self) -> ParseResult<Vec<CType>> {
        let mut types = Vec::new();

        // Parse first type
        types.push(self.parse_type_expr()?);

        // Parse additional types separated by commas
        while self.eat(&TokenKind::SymComma) {
            types.push(self.parse_type_expr()?);
        }

        Ok(types)
    }

    /// Apply type parameters to a base type.
    ///
    /// Implements the logic from `cTApplys atype params` in CVParser.lhs.
    /// Creates a left-associative chain of type applications.
    fn apply_type_params(&self, mut base_type: CType, params: Vec<CType>) -> CType {
        for param in params {
            let span = Span::DUMMY; // TODO: Calculate proper span
            base_type = CType::Apply(Box::new(base_type), Box::new(param), span);
        }
        base_type
    }

    // ========================================================================
    // Provisos (Type Constraints)
    // ========================================================================

    /// Parse a provisos clause.
    ///
    /// Implements `pProvisos` from CVParser.lhs.
    ///
    /// Grammar: `provisos (constraint1#(types), constraint2#(types), ...)`
    /// Returns the list of type constraints.
    pub fn parse_provisos(&mut self) -> ParseResult<Vec<CPred>> {
        // Check for 'provisos' keyword - it might be KwProvisos if it exists
        if let TokenKind::Id(kw) = self.current_kind() {
            if kw != "provisos" {
                return Err(self.unexpected_token("'provisos'"));
            }
        } else {
            return Err(self.unexpected_token("'provisos'"));
        }

        self.advance(); // consume 'provisos'
        self.expect(&TokenKind::SymLParen)?;

        let constraints = self.parse_comma_separated_constraints()?;

        self.expect(&TokenKind::SymRParen)?;
        Ok(constraints)
    }

    /// Parse a single proviso (type constraint).
    ///
    /// Implements `pProviso` from CVParser.lhs.
    ///
    /// Grammar: `ConstraintName#(type1, type2, ...)`
    pub fn parse_type_proviso(&mut self) -> ParseResult<CPred> {
        // Parse constraint constructor (uppercase identifier)
        let constraint_name = if let TokenKind::Id(name) = self.current_kind() {
            if name.chars().next().unwrap_or('a').is_ascii_uppercase() {
                let pos = Position::unknown();
                let name = name.clone();
                self.advance();
                Id::new(name.clone(), pos.clone())
            } else {
                return Err(self.unexpected_token("constraint name"));
            }
        } else {
            return Err(self.unexpected_token("constraint name"));
        };

        // Parse type parameters - required for constraints
        let params = self.parse_type_parameters_required()?;

        if params.is_empty() {
            return Err(self.unexpected_token("constraint must have type parameters"));
        }

        Ok(CPred {
            class: constraint_name,
            args: params,
            span: Span::new(self.current_span().start, self.current_span().end), // TODO: Calculate proper span
        })
    }

    /// Parse a comma-separated list of type constraints.
    fn parse_comma_separated_constraints(&mut self) -> ParseResult<Vec<CPred>> {
        let mut constraints = Vec::new();

        // Parse first constraint
        constraints.push(self.parse_type_proviso()?);

        // Parse additional constraints separated by commas
        while self.eat(&TokenKind::SymComma) {
            constraints.push(self.parse_type_proviso()?);
        }

        Ok(constraints)
    }

    // ========================================================================
    // Helper Methods
    // ========================================================================

    /// Create an error for an unexpected token.
    fn unexpected_token(&self, expected: &str) -> crate::ParseError {
        use bsc_diagnostics::ParseError;
        ParseError::UnexpectedToken {
            expected: expected.to_string(),
            found: self.current_kind().name().to_string(),
            span: self.current_span().into(),
        }
    }
}

// ============================================================================
// Type Constructor Helpers
// ============================================================================


/// Create an `Int#(32)` type.
///
/// Mirrors `tInt32At pos` from Type.hs.
fn create_int32_type(pos: Position) -> CType {
    let int_con = CType::Con(Id::new("Int", pos.clone()));
    let num_32 = CType::Num(32, pos);
    let span = Span::DUMMY; // TODO: Calculate proper span
    CType::Apply(Box::new(int_con), Box::new(num_32), span)
}

/// Create a `Real` type.
///
/// Mirrors `tRealAt pos` from Type.hs.
fn create_real_type(pos: Position) -> CType {
    CType::Con(Id::new("Real", pos))
}

/// Create an `Action` type.
///
/// Mirrors `tActionAt pos` from Type.hs.
fn create_action_type(pos: Position) -> CType {
    CType::Con(Id::new("Action", pos))
}

/// Create an `ActionValue` constructor.
///
/// Mirrors `tActionValueAt pos` from Type.hs.
/// Note: This creates the base constructor; type parameters must be applied separately.
fn create_action_value_type(pos: Position) -> CType {
    CType::Con(Id::new("ActionValue", pos))
}

// ============================================================================
// Sugar Type Documentation
// ============================================================================

/// BSV Sugar Types Reference
///
/// These are the built-in type syntax shortcuts that BSV provides:
///
/// | BSV Syntax | Desugared Form | Description |
/// |------------|----------------|-------------|
/// | `bit` | `Bit#(1)` | Single bit |
/// | `bit[7:0]` | `Bit#(8)` | 8-bit vector |
/// | `int` | `Int#(32)` | 32-bit signed integer |
/// | `real` | `Real` | Real/floating point |
/// | `void` | `()` | Unit type |
/// | `Action` | `Action` | Action type |
/// | `ActionValue#(T)` | `ActionValue#(T)` | Action with return value |
/// | `module` | `TDefMonad` | Current monad type |
///
/// The sugar types are implemented by the corresponding `parse_xxx_type` methods
/// in this module. Each method recognizes the keyword and creates the appropriate
/// `CType` AST node.
pub struct SugarTypes;

impl SugarTypes {
    /// Documentation for the `bit` type sugar.
    ///
    /// - `bit` → `Bit#(1)` (single bit)
    /// - `bit[n:0]` → `Bit#(n+1)` (bit vector of size n+1)
    ///
    /// This follows SystemVerilog conventions where `bit[7:0]` is an 8-bit vector.
    pub const BIT_TYPE: &'static str = "bit type sugar";

    /// Documentation for the `int` type sugar.
    ///
    /// `int` → `Int#(32)` (32-bit signed integer)
    ///
    /// BSV's `int` is always 32-bit, unlike some other languages where the size
    /// may be platform-dependent.
    pub const INT_TYPE: &'static str = "int type sugar";

    /// Documentation for the `ActionValue` type sugar.
    ///
    /// `ActionValue#(T)` → `ActionValue#(T)`
    ///
    /// Note that `ActionValue` requires type parameters, unlike `Action` which
    /// can stand alone.
    pub const ACTION_VALUE_TYPE: &'static str = "ActionValue type sugar";
}