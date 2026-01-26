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
use bsc_syntax::{CType, CPred, CKind, CTyCon, CTyConSort, StructSubType, Id};

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
            let start_pos = self.tokens[self.pos - 1].span.start; // LParen position
            let ty = self.parse_type_expr()?;
            let end_token = self.expect(&TokenKind::SymRParen)?;
            let span = Span::new(start_pos, end_token.span.end);
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

        let start_pos = self.current_span().start;
        let pos = self.current_position();
        self.advance(); // consume 'bit'

        // Check for bit range: [h:0]
        let (width, end_pos) = if self.eat(&TokenKind::SymLBracket) {
            // Parse high index
            let high = self.parse_bit_range()?;
            let end_token = self.expect(&TokenKind::SymRBracket)?;
            (high + 1, end_token.span.end) // bit[h:0] has h+1 bits
        } else {
            (1, self.tokens.get(self.pos - 1).map(|t| t.span.end).unwrap_or(start_pos)) // plain 'bit' is Bit#(1)
        };

        // Create Bit#(width)
        let bit_con = CType::Con(Id::new("Bit", pos.clone()).into());
        let width_type = CType::Num(width as i128, pos.clone());
        let span = Span::new(start_pos, end_pos);

        Ok(CType::Apply(
            Box::new(bit_con),
            Box::new(width_type),
            span,
        ))
    }

    /// Parse bit range in the format [h:0].
    /// Based on pBitRange' from CVParser.lhs.
    /// Only supports [h:0] format where the low index must be 0.
    fn parse_bit_range(&mut self) -> ParseResult<u32> {
        // Parse high index
        let high = match self.current_kind() {
            TokenKind::Integer { value, .. } => {
                if let Ok(n) = value.try_into() {
                    let high: u32 = n;
                    self.advance();
                    high
                } else {
                    return Err(self.unexpected_token("valid integer"));
                }
            }
            _ => return Err(self.unexpected_token("high bit index")),
        };

        // Expect colon
        self.expect(&TokenKind::SymColon)?;

        // Parse low index (must be 0)
        let low = match self.current_kind() {
            TokenKind::Integer { value, .. } => {
                if let Ok(n) = value.try_into() {
                    let low: u32 = n;
                    self.advance();
                    low
                } else {
                    return Err(self.unexpected_token("valid integer"));
                }
            }
            _ => return Err(self.unexpected_token("low bit index")),
        };

        // BSV only supports [h:0] format - low index must be 0
        if low != 0 {
            return Err(self.unexpected_token("bit range with low index 0"));
        }

        Ok(high)
    }

    /// Parse `int` type (32-bit signed integer).
    ///
    /// Implements `pIntType` from CVParser.lhs.
    /// Maps to `tInt32At pos` → `Int#(32)`
    fn parse_int_type(&mut self) -> ParseResult<CType> {
        if !matches!(self.current_kind(), TokenKind::KwInt) {
            return Err(self.unexpected_token("'int'"));
        }

        let span = self.current_span();
        let pos = self.current_position();
        self.advance(); // consume 'int'

        // Create Int#(32) - mirrors tInt32At from Type.hs
        Ok(create_int32_type(pos, span))
    }

    /// Parse `real` type.
    ///
    /// Implements `pRealType` from CVParser.lhs.
    /// Maps to `tRealAt pos` → `Real`
    fn parse_real_type(&mut self) -> ParseResult<CType> {
        if !matches!(self.current_kind(), TokenKind::KwReal) {
            return Err(self.unexpected_token("'real'"));
        }

        let pos = self.current_position();
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

        let pos = self.current_position();
        self.advance(); // consume 'void'

        Ok(CType::Con(Id::new("()", pos.clone()).into()))
    }

    /// Parse `Action` type.
    ///
    /// Implements `pActionType` from CVParser.lhs.
    /// Maps to `tActionAt pos` → `Action`
    fn parse_action_type(&mut self) -> ParseResult<CType> {
        if !matches!(self.current_kind(), TokenKind::KwActionType) {
            return Err(self.unexpected_token("'Action'"));
        }

        let pos = self.current_position();
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

        let pos = self.current_position();
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
    /// Handles qualified constructors (Package::Constructor) and creates `cTCon cons`.
    fn parse_type_constructor(&mut self) -> ParseResult<CType> {
        let pos = self.current_position();

        // Parse optional package qualifier: Package::
        let package_name = if let TokenKind::Id(name) = self.current_kind() {
            if name.chars().next().unwrap_or('a').is_ascii_uppercase() {
                // Could be either a package name or constructor
                let potential_package = name.clone();
                self.advance();

                // Check for :: to see if this was a package qualifier
                if self.eat(&TokenKind::SymColonColon) {
                    Some(potential_package)
                } else {
                    // No ::, so this was actually the constructor
                    return Ok(CType::Con(Id::new(potential_package, pos).into()));
                }
            } else {
                return Err(self.unexpected_token("type constructor"));
            }
        } else {
            None
        };

        // Parse the constructor name
        if let TokenKind::Id(constructor_name) = self.current_kind() {
            if constructor_name.chars().next().unwrap_or('a').is_ascii_uppercase() {
                let qualified_name = if let Some(pkg) = package_name {
                    format!("{}::{}", pkg, constructor_name)
                } else {
                    constructor_name.to_string()
                };
                let id = Id::new(qualified_name, pos);
                self.advance();
                Ok(CType::Con(id.into()))
            } else {
                Err(self.unexpected_token("type constructor"))
            }
        } else {
            if package_name.is_some() {
                Err(self.unexpected_token("constructor after package qualifier"))
            } else {
                Err(self.unexpected_token("type constructor"))
            }
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
                let pos = self.current_position();
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

        let pos = self.current_position();
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

        let _pos = self.current_position();
        self.advance(); // consume 'function'

        // Parse return type
        let return_type = self.parse_type_expr()?;

        // Parse function name (required for function prototype)
        if !matches!(self.current_kind(), TokenKind::Id(_)) {
            return Err(self.unexpected_token("function name"));
        }
        self.advance(); // consume function name

        // Parse argument list
        let arg_types = if self.eat(&TokenKind::SymLParen) {
            let mut args = Vec::new();

            // Parse arguments: type name, type name, ...
            if !self.check(&TokenKind::SymRParen) {
                loop {
                    // Parse argument type
                    let arg_type = self.parse_type_expr()?;

                    // Parse argument name (required)
                    if !matches!(self.current_kind(), TokenKind::Id(_)) {
                        return Err(self.unexpected_token("argument name"));
                    }
                    self.advance(); // consume argument name

                    args.push(arg_type);

                    if self.eat(&TokenKind::SymComma) {
                        continue;
                    } else {
                        break;
                    }
                }
            }

            self.expect(&TokenKind::SymRParen)?;
            args
        } else {
            Vec::new() // No argument list
        };

        // Construct function type: arg1 -> arg2 -> ... -> return_type
        // In BSV, function types are right-associative
        let mut func_type = return_type;
        for arg_type in arg_types.into_iter().rev() {
            func_type = crate::make_fn_type(arg_type, func_type);
        }

        Ok(func_type)
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
            let base_span = get_type_span(&base_type);
            let param_span = get_type_span(&param);
            let span = Span::new(base_span.start, param_span.end.max(base_span.end));
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
        let start_pos = self.current_span().start;

        // Parse constraint constructor (uppercase identifier)
        let constraint_name = if let TokenKind::Id(name) = self.current_kind() {
            if name.chars().next().unwrap_or('a').is_ascii_uppercase() {
                let pos = self.current_position();
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

        // Calculate span from the start of constraint name to the end of parameters
        let end_pos = self.tokens.get(self.pos.saturating_sub(1))
            .map(|t| t.span.end)
            .unwrap_or(start_pos);

        Ok(CPred {
            class: constraint_name,
            args: params,
            span: Span::new(start_pos, end_pos),
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

/// Get the span from a CType.
///
/// This helper function extracts span information from various CType variants
/// to enable accurate span tracking for type applications.
fn get_type_span(ty: &CType) -> Span {
    match ty {
        CType::Apply(_, _, span) => *span,
        CType::Fun(_, _, span) => *span,
        CType::Paren(_, span) => *span,
        CType::Forall(_, _, span) => *span,
        CType::Tuple(_, span) => *span,
        CType::List(_, span) => *span,
        CType::Infix(_, _, _, span) => *span,
        // For types without explicit span, return DUMMY
        CType::Con(_) | CType::Var(_) | CType::Num(_, _) | CType::Str(_, _)
        | CType::DefMonad(_) | CType::NoType => Span::DUMMY,
    }
}


/// Mirrors `tInt32At pos` from Type.hs:
/// `tInt32At pos = TAp (tIntAt pos) (t32At pos)`
fn create_int32_type(pos: Position, span: Span) -> CType {
    let int_con = CType::Con(CTyCon::full(
        Id::qualified("Prelude", "Int", pos.clone()),
        Some(CKind::Fun(Box::new(CKind::Num(Span::DUMMY)), Box::new(CKind::Star(Span::DUMMY)), Span::DUMMY)),
        CTyConSort::Abstract,
    ));
    let num_32 = CType::Num(32, pos.clone());
    CType::Apply(Box::new(int_con), Box::new(num_32), span)
}

/// Mirrors `tRealAt pos` from Type.hs:
/// `tRealAt pos = TCon (TyCon (idRealAt pos) (Just KStar) TIabstract)`
fn create_real_type(pos: Position) -> CType {
    CType::Con(CTyCon::full(
        Id::qualified("Prelude", "Real", pos),
        Some(CKind::Star(Span::DUMMY)),
        CTyConSort::Abstract,
    ))
}

/// Mirrors `tPrimUnitAt pos` from Type.hs:
/// `tPrimUnitAt pos = TCon (TyCon (idPrimUnitAt pos) (Just KStar) (TIstruct SStruct []))`
fn create_prim_unit_type(pos: Position) -> CType {
    CType::Con(CTyCon::full(
        Id::qualified("Prelude", "PrimUnit", pos),
        Some(CKind::Star(Span::DUMMY)),
        CTyConSort::Struct(StructSubType::Struct, vec![]),
    ))
}

/// Mirrors `tActionValueAt pos` from Type.hs:
/// `tActionValueAt pos = TCon (TyCon (idActionValueAt pos) (Just (Kfun KStar KStar)) (TIstruct SStruct [id__value_at pos, id__action_at pos]))`
fn create_action_value_type(pos: Position) -> CType {
    CType::Con(CTyCon::full(
        Id::qualified("Prelude", "ActionValue", pos.clone()),
        Some(CKind::Fun(Box::new(CKind::Star(Span::DUMMY)), Box::new(CKind::Star(Span::DUMMY)), Span::DUMMY)),
        CTyConSort::Struct(StructSubType::Struct, vec![
            Id::qualified("Prelude", "__value", pos.clone()),
            Id::qualified("Prelude", "__action", pos),
        ]),
    ))
}

/// Mirrors `tActionAt pos` from Type.hs:
/// `tActionAt pos = TCon (TyCon (idActionAt pos) (Just KStar) (TItype 0 (TAp (tActionValueAt pos) (tPrimUnitAt pos))))`
fn create_action_type(pos: Position) -> CType {
    let expansion = CType::Apply(
        Box::new(create_action_value_type(pos.clone())),
        Box::new(create_prim_unit_type(pos.clone())),
        Span::DUMMY,
    );
    CType::Con(CTyCon::full(
        Id::qualified("Prelude", "Action", pos),
        Some(CKind::Star(Span::DUMMY)),
        CTyConSort::TypeSyn(0, Box::new(expansion)),
    ))
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