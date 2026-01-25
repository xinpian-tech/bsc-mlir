//! BSV pattern parsing.
//!
//! Mirrors the pattern parsing functions in `src/comp/Parser/BSV/CVParser.lhs`
//! starting around line 2669.
//!
//! BSV patterns are used in case statement matching and pattern matching expressions.
//! They support variable binding, constructor matching, struct destructuring,
//! tuple patterns, and wildcard patterns.
//!
//! # Pattern Grammar
//!
//! The BSV pattern grammar (simplified) is:
//!
//! ```text
//! Pattern :=
//!     | .name                              -- Variable pattern (binds name)
//!     | .*                                 -- Wildcard pattern (matches anything)
//!     | tagged Constructor Pattern         -- Tagged union pattern
//!     | Constructor { field: Pattern, ... } -- Struct pattern
//!     | Constructor Pattern                 -- Constructor pattern
//!     | Constructor                        -- Enum pattern (no args)
//!     | { Pattern, Pattern, ... }          -- Tuple pattern
//!     | ( Pattern )                        -- Parenthesized pattern
//!     | 42                                 -- Numeric literal pattern
//!     | "string"                           -- String literal pattern
//! ```
//!
//! # Examples
//!
//! ## Variable Patterns
//! ```text
//! .x          -- Binds variable x
//! .my_var     -- Binds variable my_var
//! ```
//!
//! ## Wildcard Pattern
//! ```text
//! .*          -- Matches anything, doesn't bind
//! ```
//!
//! ## Tagged Union Patterns
//! ```text
//! tagged Valid .x           -- Matches Valid constructor, binds inner value to x
//! tagged Invalid            -- Matches Invalid constructor with no payload
//! tagged Some .*            -- Matches Some constructor, ignores payload
//! ```
//!
//! ## Struct Patterns
//! ```text
//! Point { x: .px, y: .py }  -- Matches Point struct, binds x field to px, y field to py
//! Color { r: .red }         -- Matches Color struct, binds r field to red
//! ```
//!
//! ## Constructor Patterns
//! ```text
//! Some .value               -- Matches Some constructor with one argument
//! Cons .head .tail          -- Matches Cons constructor with two arguments
//! ```
//!
//! ## Tuple Patterns
//! ```text
//! { .x, .y }                -- Matches 2-tuple, binds first element to x, second to y
//! { .a, .b, .c }            -- Matches 3-tuple
//! { .first, .* }            -- Matches tuple, binds first element, ignores rest
//! ```
//!
//! ## Literal Patterns
//! ```text
//! 42                        -- Matches integer 42
//! 'h0A                      -- Matches hexadecimal 0x0A
//! "hello"                   -- Matches string "hello"
//! ```
//!
//! # Implementation Notes
//!
//! This module implements the pattern parsing functions from CVParser.lhs:
//!
//! - `pPattern` - Main pattern entry point
//! - `pPatternVariable` - `.name` syntax
//! - `pConstrPatternWith` - `tagged Constructor ...`
//! - `pStructOrEnumPatternWith` - struct patterns
//! - `pConstrFieldsOrTuplePatternWith`
//! - `pFieldPattern` - `name: pattern`
//! - `pNumericLiteralPattern` - number patterns
//! - `pStringLiteralPattern` - string patterns
//! - `pConstPattern` - constant patterns
//! - `pEnumPattern` - enum patterns
//! - `pWildcardPattern` - `.*` syntax
//! - `pTuplePattern` - `{p1, p2}` syntax
//!
//! The patterns create `CPat` AST nodes that exactly mirror the Haskell
//! CSyntax.hs data structures.

use crate::{BsvParser, ParseResult};
use bsc_lexer_bsv::TokenKind;
use bsc_diagnostics::{Position, Span};
use bsc_syntax::{
    id::Id, literal::{IntLiteral, Literal}, CPat, CPatField
};

/// Parse a BSV pattern using the given parser.
///
/// This is the main entry point for pattern parsing, delegating to the
/// `BsvParser::parse_pattern` method implementation.
pub fn parse_pattern(parser: &mut BsvParser<'_>) -> ParseResult<CPat> {
    parser.parse_pattern_impl()
}

impl<'src> BsvParser<'src> {
    /// Parse a BSV pattern.
    ///
    /// Corresponds to `pPattern` in CVParser.lhs line 2669.
    ///
    /// Grammar:
    /// ```text
    /// Pattern :=
    ///     | .identifier                     -- Variable pattern
    ///     | tagged Constructor Pattern      -- Tagged union pattern
    ///     | Constructor { ... }             -- Struct pattern
    ///     | Constructor                     -- Enum pattern
    ///     | ( Pattern )                     -- Parenthesized pattern
    ///     | { Pattern, ... }                -- Tuple pattern
    ///     | .*                              -- Wildcard pattern
    ///     | Literal                         -- Constant pattern
    /// ```
    ///
    /// # Errors
    ///
    /// Returns an error if the current tokens do not form a valid pattern.
    pub fn parse_pattern_impl(&mut self) -> ParseResult<CPat> {
        // Try each pattern type in order (mirrors the Haskell <|> chain)

        // .name - variable pattern
        if self.check(&TokenKind::SymDot) {
            return self.parse_pattern_variable();
        }

        // tagged Constructor ... - tagged union pattern
        if self.check(&TokenKind::KwTagged) {
            return self.parse_tagged_pattern();
        }

        // Constructor ... - check for constructor (identifier starting with uppercase)
        if let TokenKind::Id(id) = &self.current_kind() {
            if is_constructor_name(id) {
                return self.parse_constructor_or_struct_pattern();
            }
        }

        // ( Pattern ) - parenthesized pattern
        if self.check(&TokenKind::SymLParen) {
            return self.parse_parenthesized_pattern();
        }

        // { Pattern, ... } - tuple pattern
        if self.check(&TokenKind::SymLBrace) {
            return self.parse_tuple_pattern();
        }

        // .* - wildcard pattern
        if self.check(&TokenKind::SymDotStar) {
            return self.parse_wildcard_pattern();
        }

        // Literal patterns (numbers, strings)
        if self.is_literal_token() {
            return self.parse_const_pattern();
        }

        Err(self.error("pattern"))
    }

    /// Parse a variable pattern (.identifier).
    ///
    /// Corresponds to `pPatternVariable` in CVParser.lhs line 2712.
    ///
    /// Grammar: `.identifier`
    fn parse_pattern_variable(&mut self) -> ParseResult<CPat> {
        self.expect(&TokenKind::SymDot)?;
        let name = self.parse_identifier()?;
        Ok(CPat::Var(name))
    }

    /// Parse a tagged union pattern (tagged Constructor Pattern).
    ///
    /// Corresponds to the tagged branch in `pPattern` line 2672.
    fn parse_tagged_pattern(&mut self) -> ParseResult<CPat> {
        self.expect(&TokenKind::KwTagged)?;
        let constr = self.parse_qualified_constructor()?;
        self.parse_constructor_pattern_with(constr, true)
    }

    /// Parse a constructor or struct pattern.
    ///
    /// Corresponds to `pStructOrEnumPatternWith` in CVParser.lhs line 2694.
    fn parse_constructor_or_struct_pattern(&mut self) -> ParseResult<CPat> {
        let constr = self.parse_qualified_constructor()?;
        self.parse_struct_or_enum_pattern_with(constr)
    }

    /// Parse a constructor pattern with the given constructor name.
    ///
    /// Corresponds to `pConstrPatternWith` in CVParser.lhs line 2679.
    ///
    /// This handles multiple forms:
    /// - `Constructor { field: pattern, ... }`  -- struct-like
    /// - `Constructor pattern`                   -- single argument
    /// - `Constructor .var`                     -- variable binding
    /// - `Constructor`                          -- no arguments
    fn parse_constructor_pattern_with(&mut self, constr: Id, _tagged: bool) -> ParseResult<CPat> {
        let _pos = self.current_span().start;

        // Try: Constructor { ... } (braced patterns)
        if self.check(&TokenKind::SymLBrace) {
            return self.parse_constructor_fields_or_tuple_pattern_with(Position::unknown(), constr);
        }

        // Try: Constructor pattern (single pattern argument)
        if self.is_pattern_start() {
            let pat = if self.check(&TokenKind::SymDotStar) {
                self.parse_wildcard_pattern()?
            } else if self.is_literal_token() {
                self.parse_const_pattern()?
            } else if self.is_enum_pattern_start() {
                self.parse_enum_pattern()?
            } else if self.check(&TokenKind::SymLParen) {
                self.parse_parenthesized_pattern()?
            } else {
                return Err(self.error("pattern"));
            };

            return Ok(CPat::Con(constr, vec![pat], Span::DUMMY));
        }

        // Try: Constructor .variable
        if self.check(&TokenKind::SymDot) {
            self.advance(); // consume '.'
            let var = self.parse_identifier()?;
            return Ok(CPat::Con(constr, vec![CPat::Var(var)], Span::DUMMY));
        }

        // Constructor with no arguments
        Ok(CPat::Con(constr, vec![], Span::DUMMY))
    }

    /// Parse struct or enum pattern with the given constructor.
    ///
    /// Corresponds to `pStructOrEnumPatternWith` in CVParser.lhs line 2694.
    fn parse_struct_or_enum_pattern_with(&mut self, constr: Id) -> ParseResult<CPat> {
        // Try struct pattern: Constructor { field: pattern, ... }
        if self.check(&TokenKind::SymLBrace) {
            let fields = self.parse_braced_comma_separated(Self::parse_field_pattern)?;
            // Convert (Id, CPat) tuples to CPatField structs
            let field_structs: Vec<CPatField> = fields.into_iter().map(|(name, pattern)| {
                CPatField {
                    name,
                    pattern,
                    span: Span::DUMMY,
                }
            }).collect();
            // is_struct = Some(true) indicates this is a struct pattern
            Ok(CPat::Struct(Some(true), constr, field_structs, Span::DUMMY))
        } else {
            // Enum pattern: just the constructor name
            Ok(CPat::Con(constr, vec![], Span::DUMMY))
        }
    }

    /// Parse constructor fields or tuple pattern within braces.
    ///
    /// Corresponds to `pConstrFieldsOrTuplePatternWith` in CVParser.lhs line 2701.
    fn parse_constructor_fields_or_tuple_pattern_with(
        &mut self,
        pos: Position,
        constr: Id
    ) -> ParseResult<CPat> {
        self.expect(&TokenKind::SymLBrace)?;

        // Try tuple pattern first (comma-separated patterns)
        if self.is_tuple_pattern_content() {
            let pat = self.parse_tuple_pattern_with(pos)?;
            self.expect(&TokenKind::SymRBrace)?;
            return Ok(CPat::Con(constr, vec![pat], Span::DUMMY));
        }

        // Otherwise, parse as field patterns
        let fields = self.parse_comma_separated_until(
            &TokenKind::SymRBrace,
            Self::parse_field_pattern
        )?;
        self.expect(&TokenKind::SymRBrace)?;

        // Convert (Id, CPat) tuples to CPatField structs
        let field_structs: Vec<CPatField> = fields.into_iter().map(|(name, pattern)| {
            CPatField {
                name,
                pattern,
                span: Span::DUMMY,
            }
        }).collect();

        // is_struct = Some(false) for constructor with named fields
        Ok(CPat::Struct(Some(false), constr, field_structs, Span::DUMMY))
    }

    /// Parse a field pattern (field_name: pattern).
    ///
    /// Corresponds to `pFieldPattern` in CVParser.lhs line 2718.
    fn parse_field_pattern(&mut self) -> ParseResult<(Id, CPat)> {
        let name = self.parse_identifier()?;
        self.expect(&TokenKind::SymColon)?;
        let pattern = self.parse_pattern_impl()?;
        Ok((name, pattern))
    }

    /// Parse a parenthesized pattern.
    fn parse_parenthesized_pattern(&mut self) -> ParseResult<CPat> {
        self.expect(&TokenKind::SymLParen)?;
        let pattern = self.parse_pattern_impl()?;
        self.expect(&TokenKind::SymRParen)?;
        Ok(pattern)
    }

    /// Parse a tuple pattern.
    ///
    /// Corresponds to `pTuplePattern` in CVParser.lhs line 2794.
    ///
    /// Grammar: `{ pattern1, pattern2, ... }`
    fn parse_tuple_pattern(&mut self) -> ParseResult<CPat> {
        let pos = Position::unknown();
        self.parse_tuple_pattern_with(pos)
    }

    /// Parse tuple pattern content with the given position.
    ///
    /// Corresponds to `pTuplePatternWith` in CVParser.lhs line 2799.
    fn parse_tuple_pattern_with(&mut self, pos: Position) -> ParseResult<CPat> {
        let patterns = self.parse_braced_comma_separated_non_empty(Self::parse_pattern_impl)?;
        Ok(make_tuple_pattern(pos, patterns))
    }

    /// Parse a wildcard pattern (.* ).
    ///
    /// Corresponds to `pWildcardPattern` in CVParser.lhs line 2788.
    fn parse_wildcard_pattern(&mut self) -> ParseResult<CPat> {
        let pos = Position::line_col(-1, -1); // TODO: Convert from span properly
        self.expect(&TokenKind::SymDotStar)?;
        Ok(CPat::Wildcard(pos))
    }

    /// Parse a constant pattern (number or string literal).
    ///
    /// Corresponds to `pConstPattern` in CVParser.lhs line 2779.
    fn parse_const_pattern(&mut self) -> ParseResult<CPat> {
        if self.is_numeric_literal() {
            self.parse_numeric_literal_pattern()
        } else if self.is_string_literal() {
            self.parse_string_literal_pattern()
        } else {
            Err(self.error("constant pattern"))
        }
    }

    /// Parse a numeric literal pattern.
    ///
    /// Corresponds to `pNumericLiteralPattern` in CVParser.lhs line 2725.
    fn parse_numeric_literal_pattern(&mut self) -> ParseResult<CPat> {
        let token = self.advance();
        let token_span = token.span;
        match &token.kind {
            TokenKind::Number { value, bitwidth, base, .. } => {
                let pos = Position::unknown();

                match value {
                    bsc_lexer_bsv::SvNumber::Integer(num) => {
                        let width = bitwidth.as_ref().map(|w| w.try_into().unwrap_or(0));
                        let num_base = base.map(|b| b.value()).unwrap_or(10);

                        let int_lit = IntLiteral {
                            width,
                            base: match num_base {
                                2 => bsc_syntax::literal::IntBase::Binary,
                                8 => bsc_syntax::literal::IntBase::Octal,
                                10 => bsc_syntax::literal::IntBase::Decimal,
                                16 => bsc_syntax::literal::IntBase::Hexadecimal,
                                _ => bsc_syntax::literal::IntBase::Decimal,
                            },
                            value: num.try_into().unwrap_or(0),
                        };

                        Ok(CPat::Lit(Literal::Integer(int_lit), pos))
                    },
                    bsc_lexer_bsv::SvNumber::Mixed(bs) => {
                        // Handle mixed literal patterns (like 4'b10x1)
                        let num_base = base.map(|b| b.value() as i64).unwrap_or(10);

                        // Convert mixed digits to (length, value_or_dont_care) format
                        let pairs: Vec<(i64, Option<i64>)> = bs.iter().map(|(len, digit)| {
                            match digit {
                                bsc_lexer_bsv::MixedDigit::Value(val) => {
                                    // Convert BigInt to i64 for now
                                    let val_i64 = val.try_into().unwrap_or(0);
                                    (*len as i64, Some(val_i64))
                                },
                                bsc_lexer_bsv::MixedDigit::Bit(_) => {
                                    // Don't care values (X, Z)
                                    (*len as i64, None)
                                },
                            }
                        }).collect();

                        Ok(CPat::MixedLit {
                            position: pos,
                            base: num_base,
                            parts: pairs,
                            span: bsc_diagnostics::Span::DUMMY,
                        })
                    },
                    _ => Err(self.error_at_span(
                        "unsupported numeric literal in pattern",
                        token_span
                    )),
                }
            },
            TokenKind::Integer { size: _, base, value } => {
                let pos = Position::unknown();
                let int_lit = IntLiteral {
                    width: None,
                    base: match base {
                        2 => bsc_syntax::literal::IntBase::Binary,
                        8 => bsc_syntax::literal::IntBase::Octal,
                        10 => bsc_syntax::literal::IntBase::Decimal,
                        16 => bsc_syntax::literal::IntBase::Hexadecimal,
                        _ => bsc_syntax::literal::IntBase::Decimal,
                    },
                    value: value.try_into().unwrap_or(0),
                };
                Ok(CPat::Lit(Literal::Integer(int_lit), pos))
            },
            _ => Err(self.error_at_span("expected numeric literal", token_span)),
        }
    }

    /// Parse a string literal pattern.
    ///
    /// Corresponds to `pStringLiteralPattern` in CVParser.lhs line 2772.
    fn parse_string_literal_pattern(&mut self) -> ParseResult<CPat> {
        let token = self.advance();
        if let TokenKind::String(s) = &token.kind {
            let pos = Position::unknown();
            Ok(CPat::Lit(Literal::String(s.clone()), pos))
        } else {
            let span = token.span;
            Err(self.error_at_span("expected string literal", span))
        }
    }

    /// Parse an enum pattern (just a constructor with no arguments).
    ///
    /// Corresponds to `pEnumPattern` in CVParser.lhs line 2784.
    fn parse_enum_pattern(&mut self) -> ParseResult<CPat> {
        let constr = self.parse_qualified_constructor()?;
        Ok(CPat::Con(constr, vec![], Span::DUMMY))
    }

    // ========================================================================
    // Helper methods for pattern parsing
    // ========================================================================

    /// Check if the current token could start a pattern.
    fn is_pattern_start(&self) -> bool {
        matches!(
            self.current_kind(),
            TokenKind::SymDot |
            TokenKind::SymDotStar |
            TokenKind::SymLParen |
            TokenKind::SymLBrace |
            TokenKind::KwTagged |
            TokenKind::Number { .. } |
            TokenKind::Integer { .. } |
            TokenKind::String(_) |
            TokenKind::Id(_)
        )
    }

    /// Check if the current token could start an enum pattern.
    fn is_enum_pattern_start(&self) -> bool {
        if let TokenKind::Id(id) = &self.current_kind() {
            is_constructor_name(id)
        } else {
            false
        }
    }

    /// Check if the current token is a numeric literal.
    fn is_numeric_literal(&self) -> bool {
        matches!(
            self.current_kind(),
            TokenKind::Number { .. } | TokenKind::Integer { .. }
        )
    }

    /// Check if the current token is a string literal.
    fn is_string_literal(&self) -> bool {
        matches!(self.current_kind(), TokenKind::String(_))
    }

    /// Check if the current token is any literal.
    fn is_literal_token(&self) -> bool {
        self.is_numeric_literal() || self.is_string_literal()
    }

    /// Check if the content inside braces looks like a tuple pattern.
    ///
    /// This is a heuristic - tuple patterns contain patterns that don't start
    /// with identifiers (since identifiers would be field names).
    fn is_tuple_pattern_content(&self) -> bool {
        // Look ahead to see if we have patterns (not field patterns)
        // This is a simplified heuristic
        !self.check(&TokenKind::Id(smol_str::SmolStr::new_static(""))) ||
        self.check(&TokenKind::SymDot) ||
        self.check(&TokenKind::SymDotStar)
    }

    /// Parse an identifier (for patterns, fields, etc.).
    fn parse_identifier(&mut self) -> ParseResult<Id> {
        if let TokenKind::Id(name) = &self.current_kind() {
            let id = Id::unpositioned(name.clone());
            self.advance();
            Ok(id)
        } else {
            Err(self.error("identifier"))
        }
    }

    /// Parse a qualified constructor name.
    fn parse_qualified_constructor(&mut self) -> ParseResult<Id> {
        // For now, just parse a simple identifier
        // TODO: Handle qualified names like Module::Constructor
        self.parse_identifier()
    }

    /// Parse comma-separated items within braces.
    fn parse_braced_comma_separated<T>(
        &mut self,
        parse_item: fn(&mut Self) -> ParseResult<T>
    ) -> ParseResult<Vec<T>> {
        self.expect(&TokenKind::SymLBrace)?;
        let items = self.parse_comma_separated_until(&TokenKind::SymRBrace, parse_item)?;
        self.expect(&TokenKind::SymRBrace)?;
        Ok(items)
    }

    /// Parse comma-separated items within braces (requiring at least one item).
    fn parse_braced_comma_separated_non_empty<T>(
        &mut self,
        parse_item: fn(&mut Self) -> ParseResult<T>
    ) -> ParseResult<Vec<T>> {
        self.expect(&TokenKind::SymLBrace)?;
        let items = self.parse_comma_separated_until_non_empty(&TokenKind::SymRBrace, parse_item)?;
        self.expect(&TokenKind::SymRBrace)?;
        Ok(items)
    }

    /// Parse comma-separated items until a terminator token.
    fn parse_comma_separated_until<T>(
        &mut self,
        terminator: &TokenKind,
        parse_item: fn(&mut Self) -> ParseResult<T>
    ) -> ParseResult<Vec<T>> {
        let mut items = Vec::new();

        while !self.check(terminator) && !self.is_eof() {
            items.push(parse_item(self)?);

            if self.check(&TokenKind::SymComma) {
                self.advance();
                // Allow trailing comma
                if self.check(terminator) {
                    break;
                }
            } else {
                break;
            }
        }

        Ok(items)
    }

    /// Parse comma-separated items until a terminator token (requiring at least one).
    fn parse_comma_separated_until_non_empty<T>(
        &mut self,
        terminator: &TokenKind,
        parse_item: fn(&mut Self) -> ParseResult<T>
    ) -> ParseResult<Vec<T>> {
        let mut items = Vec::new();

        if self.check(terminator) {
            return Err(self.error("expected at least one item"));
        }

        loop {
            items.push(parse_item(self)?);

            if self.check(&TokenKind::SymComma) {
                self.advance();
                // Allow trailing comma
                if self.check(terminator) {
                    break;
                }
            } else {
                break;
            }
        }

        Ok(items)
    }

    /// Create an error message at the current location.
    fn error(&self, expected: &str) -> bsc_diagnostics::ParseError {
        bsc_diagnostics::ParseError::UnexpectedToken {
            expected: expected.to_string(),
            found: self.current_kind().name().to_string(),
            span: self.current_span().into(),
        }
    }

    /// Create an error message at a specific span.
    fn error_at_span(&self, message: &str, span: bsc_diagnostics::Span) -> bsc_diagnostics::ParseError {
        bsc_diagnostics::ParseError::InvalidSyntax {
            message: message.to_string(),
            span: span.into(),
        }
    }
}

/// Check if an identifier is a constructor name (starts with uppercase).
fn is_constructor_name(name: &str) -> bool {
    name.chars().next().map_or(false, |c| c.is_ascii_uppercase())
}

/// Create a tuple pattern from a list of patterns.
///
/// Mirrors `pMkTuple` from CSyntaxUtil.hs:
/// - `pMkTuple pos []` -> `CPstruct (Just True) idPrimUnit []` (unit type)
/// - `pMkTuple pos [p]` -> `p` (single element, no tuple)
/// - `pMkTuple pos (p:ps)` -> `CPCon idComma [p, pMkTuple pos ps]` (nested pairs)
fn make_tuple_pattern(_pos: Position, patterns: Vec<CPat>) -> CPat {
    match patterns.len() {
        0 => {
            // Empty tuple -> unit pattern
            let unit_id = Id::unpositioned("()"); // idPrimUnit equivalent
            CPat::Struct(Some(true), unit_id, vec![], bsc_diagnostics::Span::DUMMY)
        },
        1 => {
            // Single element -> just the pattern itself
            patterns.into_iter().next().unwrap()
        },
        _ => {
            // Multiple elements -> nested pairs using comma constructor
            let comma_id = Id::unpositioned(","); // idComma equivalent
            patterns.into_iter().reduce(|acc, pat| {
                CPat::Con(comma_id.clone(), vec![acc, pat], bsc_diagnostics::Span::DUMMY)
            }).unwrap()
        }
    }
}