//! Expression parsing for BSV.
//!
//! This module mirrors the expression parsing functions from `src/comp/Parser/BSV/CVParser.lhs`
//! (lines 3700-4000 approximately). It implements BSV's expression syntax including operator
//! precedence, primary expressions, and special expression forms.
//!
//! # BSV Expression Syntax
//!
//! BSV supports several forms of expressions:
//!
//! ## Primary Expressions
//! - Numeric literals: `42`, `'h3f`, `16'h1234`, `3.14`
//! - String literals: `"hello world"`
//! - Variables and function calls: `foo`, `bar(x, y)`
//! - Field access: `obj.field`, `obj.method`
//! - Array subscripting: `arr[index]`, `arr[high:low]`
//! - Constructor expressions: `Tuple2 { fst: x, snd: y }`
//! - Bit concatenation: `{a, b, c}`
//!
//! ## Special Expression Forms
//! - Action blocks: `action ... endaction`
//! - ActionValue blocks: `actionvalue ... endactionvalue`
//! - Sequence/Parallel blocks: `seq ... endseq`, `par ... endpar`
//! - Case expressions: `case (expr) ... endcase`
//! - Conditional expressions: `cond ? expr1 : expr2`
//! - Pattern matching: `expr matches pattern ? expr1 : expr2`
//!
//! ## Operator Precedence (from CVParser.lhs opTable)
//!
//! Level 1 (highest): Prefix operators (`+`, `-`, `!`, `~`, `&`, `|`, `^`, `~&`, `~|`, `~^`, `^~`)
//! Level 2: Power (`**`)
//! Level 3: Multiplicative (`*`, `/`, `%`)
//! Level 4: Additive (`+`, `-`)
//! Level 5: Shift (`<<`, `>>`)
//! Level 6: Relational (`<`, `<=`, `>`, `>=`)
//! Level 7: Equality (`==`, `!=`)
//! Level 8: Bitwise AND (`&`)
//! Level 9: Bitwise XOR (`^`, `~^`, `^~`)
//! Level 10: Bitwise OR (`|`)
//! Level 11: Logical AND (`&&`)
//! Level 12: Logical OR (`||`)
//!
//! # Grammar Rules (from CVParser.lhs)
//!
//! ```text
//! pExpression ::= pCondExpressions pExpressionWith
//! pExpressionSimple ::= buildExpressionParser opTable pPrimary
//! pPrimary ::= pNumericLiteral pPrimaryWithSuffix
//!           |  pStringLiteral
//!           |  pActionExpr
//!           |  pActionValueExpr
//!           |  pSequenceExpr
//!           |  pVariable pPrimaryWithSuffix
//!           |  pConstructorPrimary
//!           |  ...
//! pPrimaryWithSuffix ::= pPrimaryWithFields | pPrimaryWithArgs | pPrimaryWithBitSel
//! ```

use crate::BsvParser;
use bsc_diagnostics::{ParseError, Position, Span};
use bsc_lexer_bsv::{SvNumber, TokenKind};
use bsc_syntax::{
    csyntax::*,
    id::Id,
    literal::{IntBase, IntLiteral, Literal, OrderedFloat},
};
use num_bigint::BigInt;
use smol_str::SmolStr;

/// BSV operator precedence levels mirroring CVParser.lhs opTable.
///
/// Haskell uses Parsec's buildExpressionParser which takes the LOWEST precedence
/// operators first. So Level 1 is LOWEST (||), Level 12 is HIGHEST (prefix ops).
/// But for precedence climbing, higher numbers = tighter binding.
///
/// From CVParser.lhs opTable:
/// Level 1: Logical OR (||)        - lowest
/// Level 2: Logical AND (&&)
/// Level 3: Bitwise OR (|)
/// Level 4: Bitwise XOR (^, ~^, ^~)
/// Level 5: Bitwise AND (&)
/// Level 6: Equality (==, !=)
/// Level 7: Relational (<, <=, >, >=)
/// Level 8: Shift (<<, >>)
/// Level 9: Additive (+, -)
/// Level 10: Multiplicative (*, /, %)
/// Level 11: Power (**)
/// Level 12: Prefix operators      - highest
impl<'src> BsvParser<'src> {
    fn get_binary_op_info(&self, token: &TokenKind) -> Option<(u8, bool, &'static str)> {
        use TokenKind::*;
        match token {
            SymPipePipe => Some((1, true, "||")),
            SymAndAnd => Some((2, true, "&&")),
            SymPipe => Some((3, true, "|")),
            SymCaret | SymTildeCaret | SymCaretTilde => {
                let name = match token {
                    SymCaret => "^",
                    SymTildeCaret => "~^",
                    SymCaretTilde => "^~",
                    _ => unreachable!(),
                };
                Some((4, true, name))
            },
            SymAnd => Some((5, true, "&")),
            SymEqEq => Some((6, true, "==")),
            SymBangEq => Some((6, true, "!=")),
            SymLt => Some((7, false, "<")),
            SymLtEq => Some((7, false, "<=")),
            SymGt => Some((7, false, ">")),
            SymGtEq => Some((7, false, ">=")),
            SymLtLt => Some((8, true, "<<")),
            SymGtGt => Some((8, true, ">>")),
            SymPlus => Some((9, true, "+")),
            SymMinus => Some((9, true, "-")),
            SymStar => Some((10, true, "*")),
            SymSlash => Some((10, true, "/")),
            SymPercent => Some((10, true, "%")),
            SymStarStar => Some((11, false, "**")),
            _ => None,
        }
    }

    fn get_prefix_op_name(&self, token: &TokenKind) -> Option<&'static str> {
        use TokenKind::*;
        match token {
            SymPlus => Some("id"),
            SymMinus => Some("negate"),
            SymBang => Some("!"),
            SymTilde => Some("~"),
            SymAnd => Some("&"),
            SymPipe => Some("|"),
            SymCaret => Some("^"),
            SymTildeAnd => Some("~&"),
            SymTildePipe => Some("~|"),
            SymTildeCaret => Some("~^"),
            SymCaretTilde => Some("^~"),
            _ => None,
        }
    }
}

impl<'src> BsvParser<'src> {
    /// Parse a full expression including conditional (?:) operator.
    ///
    /// Mirrors Haskell's `pExpression :: SV_Parser CExpr` from CVParser.lhs.
    /// This handles the complete expression syntax including pattern matching
    /// with the `matches` keyword and conditional expressions.
    pub fn parse_expr(&mut self) -> Result<CExpr, ParseError> {
        let conditions = self.parse_cond_expressions()?;
        self.parse_expression_with(conditions)
    }

    /// Parse expression without conditional operator.
    ///
    /// Mirrors Haskell's `pExpressionSimple :: SV_Parser CExpr`.
    /// This uses the operator precedence table to handle binary and prefix operators.
    pub fn parse_expr_simple(&mut self) -> Result<CExpr, ParseError> {
        self.parse_expression_with_precedence()
    }

    /// Parse primary expressions with suffix handling.
    ///
    /// Mirrors Haskell's `pPrimary :: SV_Parser CExpr`.
    /// Primary expressions are the basic building blocks: literals, variables,
    /// constructors, action blocks, etc.
    pub fn parse_primary(&mut self) -> Result<CExpr, ParseError> {
        self.parse_primary_caring(true)
    }

    /// Parse primary expression with control over don't-care (`.*`) handling.
    ///
    /// Mirrors Haskell's `pPrimaryCaring :: Bool -> SV_Parser CExpr`.
    /// The boolean parameter controls whether wildcard patterns are allowed.
    fn parse_primary_caring(&mut self, allow_dont_care: bool) -> Result<CExpr, ParseError> {
        // Try each primary expression alternative in order
        // (following the pattern from CVParser.lhs pPrimaryCaring)

        // Numeric literals with suffix handling
        if let Ok(lit) = self.try_parse_numeric_literal() {
            return self.parse_primary_with_suffix(lit);
        }

        // String literals
        if let Ok(lit) = self.try_parse_string_literal() {
            return Ok(lit);
        }

        // Action expressions
        if self.check(&TokenKind::KwAction) {
            return self.parse_action_expr();
        }

        // ActionValue expressions
        if self.check(&TokenKind::KwActionvalue) {
            return self.parse_actionvalue_expr();
        }

        // Sequence/Parallel expressions
        if self.check(&TokenKind::KwSeq) || self.check(&TokenKind::KwPar) {
            return self.parse_seq_expr();
        }

        // Bit concatenation {a, b, c}
        if self.check(&TokenKind::SymLBrace) {
            return self.parse_bit_concat_primary();
        }

        // Parenthesized expressions
        if self.check(&TokenKind::SymLParen) {
            self.advance(); // consume '('
            let expr = self.parse_expr()?;
            self.expect(&TokenKind::SymRParen)?;
            return self.parse_primary_with_suffix(expr);
        }

        // Variables and function calls
        if let Ok(var) = self.try_parse_variable() {
            return self.parse_primary_with_suffix(var);
        }

        // Don't care pattern (.*) - only if allowed
        if allow_dont_care && self.check(&TokenKind::SymDotStar) {
            let span = self.current_span();
            self.advance();
            return Ok(CExpr::Any {
                position: Position::unknown(),
                kind: UndefKind::DontCare,
                span
            });
        }

        // Constructor expressions
        if let Ok(con) = self.try_parse_constructor_primary() {
            return Ok(con);
        }

        // If nothing matches, we have an unexpected token
        Err(ParseError::UnexpectedToken {
            expected: "expression".to_string(),
            found: self.current_kind().name().to_string(),
            span: self.current_span().into(),
        })
    }

    /// Parse numeric literal expressions.
    ///
    /// Mirrors Haskell's `pNumericLiteral :: SV_Parser CExpr` from CVParser.lhs.
    /// This handles integer literals, real literals, and sized literals with
    /// optional leading sign.
    fn try_parse_numeric_literal(&mut self) -> Result<CExpr, ParseError> {
        let pos = self.current().position.clone();

        // Handle optional leading sign
        let sign = if self.check(&TokenKind::SymMinus) {
            self.advance();
            -1
        } else if self.check(&TokenKind::SymPlus) {
            self.advance();
            1
        } else {
            1
        };

        let current = self.current().clone();
        match &current.kind {
            TokenKind::Number { value, bitwidth, base, .. } => {
                let span = self.current_span();
                self.advance();

                let literal = match value {
                    SvNumber::Integer(int_val) => {
                        let mut val = int_val.clone();
                        if sign == -1 {
                            val = -val;
                        }

                        let base_val = base.map(|b| b.value()).unwrap_or(10);
                        let width = bitwidth.clone();

                        let int_base = match base_val {
                            2 => IntBase::Binary,
                            8 => IntBase::Octal,
                            10 => IntBase::Decimal,
                            16 => IntBase::Hexadecimal,
                            _ => return Err(ParseError::InvalidSyntax {
                                message: format!("Invalid numeric base: {base_val}"),
                                span: span.into(),
                            }),
                        };
                        let width_u32 = width.map(|w| w.to_string().parse::<u32>().unwrap_or(0));
                        let value_i128 = val.to_string().parse::<i128>().unwrap_or(0);
                        Literal::Integer(IntLiteral {
                            width: width_u32,
                            base: int_base,
                            value: value_i128,
                        })
                    },
                    SvNumber::Real(real_val) => {
                        let mut val = *real_val;
                        if sign == -1 {
                            val = -val;
                        }
                        Literal::Float(OrderedFloat(val))
                    },
                    SvNumber::Repeated(bit) => {
                        // Handle repeated bit patterns like '0, '1, 'x, 'z
                        let val = match bit {
                            bsc_lexer_bsv::SvBit::Zero => BigInt::from(0),
                            bsc_lexer_bsv::SvBit::One => BigInt::from(1),
                            _ => return Err(ParseError::InvalidSyntax {
                                message: "Unsupported bit value in repeated literal".to_string(),
                                span: span.into(),
                            }),
                        };

                        Literal::Integer(IntLiteral {
                            width: Some(1),
                            base: IntBase::Decimal,
                            value: val.to_string().parse::<i128>().unwrap_or(0),
                        })
                    },
                    SvNumber::Mixed(_) => {
                        return Err(ParseError::InvalidSyntax {
                            message: "Mixed bit literals not yet supported".to_string(),
                            span: span.into(),
                        });
                    }
                };

                Ok(CExpr::Lit(literal, pos))
            },
            _ => Err(ParseError::UnexpectedToken {
                expected: "numeric literal".to_string(),
                found: self.current_kind().name().to_string(),
                span: self.current_span().into(),
            })
        }
    }

    /// Parse string literal expressions.
    ///
    /// Mirrors Haskell's `pStringLiteral :: SV_Parser CExpr`.
    fn try_parse_string_literal(&mut self) -> Result<CExpr, ParseError> {
        match &self.current().kind {
            TokenKind::String(s) => {
                let pos = self.current().position.clone();
                let _span = self.current_span();
                let string_val = s.clone();
                self.advance();

                let literal = Literal::String(string_val);
                Ok(CExpr::Lit(literal, pos))
            },
            _ => Err(ParseError::UnexpectedToken {
                expected: "string literal".to_string(),
                found: self.current_kind().name().to_string(),
                span: self.current_span().into(),
            })
        }
    }

    /// Parse variable references.
    fn try_parse_variable(&mut self) -> Result<CExpr, ParseError> {
        match &self.current().kind {
            TokenKind::Id(name) => {
                let pos = self.current().position.clone();
                let _span = self.current_span();
                let var_name = name.clone();
                self.advance();

                let id = Id::new(var_name, pos);
                Ok(CExpr::Var(id))
            },
            _ => Err(ParseError::UnexpectedToken {
                expected: "identifier".to_string(),
                found: self.current_kind().name().to_string(),
                span: self.current_span().into(),
            })
        }
    }

    /// Parse constructor primary expressions.
    fn try_parse_constructor_primary(&mut self) -> Result<CExpr, ParseError> {
        // This would handle tagged constructors and struct initializers
        // For now, return a placeholder error
        Err(ParseError::InvalidSyntax {
            message: "Constructor expressions not yet implemented".to_string(),
            span: self.current_span().into(),
        })
    }

    /// Parse bit concatenation expressions {a, b, c}.
    ///
    /// Mirrors Haskell's `pBitConcatPrimary :: SV_Parser CExpr`.
    fn parse_bit_concat_primary(&mut self) -> Result<CExpr, ParseError> {
        let start_span = self.current_span();
        self.expect(&TokenKind::SymLBrace)?;

        let mut elements = Vec::new();

        // Parse comma-separated expressions
        if !self.check(&TokenKind::SymRBrace) {
            loop {
                let expr = self.parse_expr()?;
                elements.push(expr);

                if self.check(&TokenKind::SymComma) {
                    self.advance();
                } else {
                    break;
                }
            }
        }

        self.expect(&TokenKind::SymRBrace)?;
        let end_span = self.current_span();
        let full_span = Span::new(start_span.start, end_span.end);

        // Create concatenation expression using primConcat
        // This matches the Haskell implementation in CVParser.lhs
        if elements.is_empty() {
            return Err(ParseError::InvalidSyntax {
                message: "Empty bit concatenation".to_string(),
                span: full_span.into(),
            });
        }

        // Fold the elements with concat operator (right-associative)
        let _first_pos = elements[0].span().start;
        let concat_id = Id::new(SmolStr::new("primConcat"), Position::unknown());
        let result = elements.into_iter().reduce(|acc, expr| {
            let span = Span::new(acc.span().start, expr.span().end);
            CExpr::Apply(
                Box::new(CExpr::Var(concat_id.clone())),
                vec![expr, acc],
                span,
            )
        }).unwrap();

        Ok(result)
    }

    /// Parse suffix operations on primary expressions.
    ///
    /// Mirrors Haskell's `pPrimaryWithSuffix :: CExpr -> SV_Parser CExpr`.
    /// This handles field access, function calls, and bit selection.
    fn parse_primary_with_suffix(&mut self, mut expr: CExpr) -> Result<CExpr, ParseError> {
        loop {
            if self.check(&TokenKind::SymDot) {
                expr = self.parse_primary_with_fields(expr)?;
            } else if self.check(&TokenKind::SymLParen) {
                expr = self.parse_primary_with_args(expr)?;
            } else if self.check(&TokenKind::SymLBracket) {
                expr = self.parse_primary_with_bit_sel(expr)?;
            } else {
                break;
            }
        }
        Ok(expr)
    }

    /// Parse field access (.field, .method).
    ///
    /// Mirrors Haskell's `pPrimaryWithFields :: CExpr -> SV_Parser CExpr`.
    fn parse_primary_with_fields(&mut self, mut expr: CExpr) -> Result<CExpr, ParseError> {
        while self.check(&TokenKind::SymDot) {
            self.advance(); // consume '.'

            match &self.current().kind {
                TokenKind::Id(field_name) => {
                    let pos = self.current().position.clone();
                    let field_id = Id::new(field_name.clone(), pos);
                    let span = Span::new(expr.span().start, self.current_span().end);
                    self.advance();

                    expr = CExpr::Select(Box::new(expr), field_id, span);
                },
                _ => return Err(ParseError::UnexpectedToken {
                    expected: "field name".to_string(),
                    found: self.current_kind().name().to_string(),
                    span: self.current_span().into(),
                })
            }
        }
        Ok(expr)
    }

    /// Parse function/method arguments.
    ///
    /// Mirrors Haskell's `pPrimaryWithArgs :: CExpr -> SV_Parser CExpr`.
    fn parse_primary_with_args(&mut self, func: CExpr) -> Result<CExpr, ParseError> {
        let start_span = func.span();
        self.expect(&TokenKind::SymLParen)?;

        let mut args = Vec::new();

        // Parse comma-separated arguments
        if !self.check(&TokenKind::SymRParen) {
            loop {
                let arg = self.parse_expr()?;
                args.push(arg);

                if self.check(&TokenKind::SymComma) {
                    self.advance();
                } else {
                    break;
                }
            }
        }

        self.expect(&TokenKind::SymRParen)?;
        let end_span = self.current_span();
        let full_span = Span::new(start_span.start, end_span.end);

        Ok(CExpr::Apply(Box::new(func), args, full_span))
    }

    /// Parse bit selection [n] and [n:m].
    ///
    /// Mirrors Haskell's `pPrimaryWithBitSel :: CExpr -> SV_Parser CExpr`.
    fn parse_primary_with_bit_sel(&mut self, mut expr: CExpr) -> Result<CExpr, ParseError> {
        while self.check(&TokenKind::SymLBracket) {
            let start_span = expr.span();
            self.advance(); // consume '['

            let index_expr = self.parse_expr()?;

            // Check for range selection [high:low]
            if self.check(&TokenKind::SymColon) {
                self.advance(); // consume ':'
                let low_expr = self.parse_expr()?;
                self.expect(&TokenKind::SymRBracket)?;

                let end_span = self.current_span();
                let full_span = Span::new(start_span.start, end_span.end);
                expr = CExpr::IndexRange {
                    expr: Box::new(expr),
                    hi: Box::new(index_expr),
                    lo: Box::new(low_expr),
                    span: full_span,
                };
            } else {
                // Single bit selection [n]
                self.expect(&TokenKind::SymRBracket)?;

                let end_span = self.current_span();
                let full_span = Span::new(start_span.start, end_span.end);
                expr = CExpr::Index {
                    expr: Box::new(expr),
                    index: Box::new(index_expr),
                    span: full_span,
                };
            }
        }
        Ok(expr)
    }

    /// Parse action expressions.
    ///
    /// Mirrors Haskell's `pActionExpr :: SV_Parser CExpr`.
    /// This parses `action ... endaction` blocks and converts them to CExpr::Action.
    fn parse_action_expr(&mut self) -> Result<CExpr, ParseError> {
        let start_span = self.current_span();
        let start_pos = Position::new(
            "unknown.bsv".to_string(),
            start_span.start as i32,
            1  // line (placeholder)
        );

        self.expect(&TokenKind::KwAction)?;

        // Parse action body (imperative statements)
        // This mirrors pImperativeNestedAction from CVParser.lhs
        let statements = self.parse_action_statements()?;

        self.expect_end_keyword("action")?;
        let end_span = self.current_span();
        let _full_span = Span::new(start_span.start, end_span.end);

        // Create Action ImperativeStatement and convert to CExpr
        use crate::imperative::{ImperativeStatement, convert_stmts_to_expr};
        let action_stmt = ImperativeStatement::Action {
            pos: start_pos,
            stmts: statements,
        };

        // Convert the action statement to CExpr using the imperative conversion
        Ok(convert_stmts_to_expr(vec![action_stmt]))
    }

    /// Parse actionvalue expressions.
    ///
    /// Mirrors Haskell's `pActionValueExpr :: SV_Parser CExpr`.
    /// This parses `actionvalue ... endactionvalue` blocks and converts them to CExpr::Do.
    fn parse_actionvalue_expr(&mut self) -> Result<CExpr, ParseError> {
        let start_span = self.current_span();
        let start_pos = Position::new(
            "unknown.bsv".to_string(),
            start_span.start as i32,
            1  // line (placeholder)
        );

        self.expect(&TokenKind::KwActionvalue)?;

        // Parse actionvalue body (imperative statements)
        // This mirrors pImperativeNestedActionValue from CVParser.lhs
        let statements = self.parse_actionvalue_statements()?;

        self.expect_end_keyword("actionvalue")?;
        let end_span = self.current_span();
        let _full_span = Span::new(start_span.start, end_span.end);

        // ActionValue is handled differently than Action in the conversion
        // It should result in a CExpr::Do (monadic do expression)
        // For now, we'll create a simple action and rely on the conversion to handle it properly
        use crate::imperative::{ImperativeStatement, convert_stmts_to_expr};

        // In Haskell, ActionValue creates ISActionValue which converts to Cdo
        // For now, create a simple expression that returns unit
        let return_stmt = ImperativeStatement::Return {
            pos: start_pos.clone(),
            expr: Some(CExpr::Var(
                Id::new(SmolStr::new("()"), Position::unknown())
            )),
        };

        let mut all_stmts = statements;
        all_stmts.push(return_stmt);

        // Convert using the imperative conversion
        Ok(convert_stmts_to_expr(all_stmts))
    }

    /// Parse sequence/parallel expressions.
    ///
    /// Mirrors Haskell's `pSequenceExpr :: SV_Parser CExpr`.
    /// This parses `seq ... endseq` and `par ... endpar` blocks for FSM sequences.
    fn parse_seq_expr(&mut self) -> Result<CExpr, ParseError> {
        let start_span = self.current_span();
        let start_pos = Position::new(
            "unknown.bsv".to_string(),
            start_span.start as i32,
            1  // line (placeholder)
        );

        let is_seq = if self.check(&TokenKind::KwSeq) {
            self.advance();
            true
        } else if self.check(&TokenKind::KwPar) {
            self.advance();
            false
        } else {
            return Err(ParseError::UnexpectedToken {
                expected: "seq or par".to_string(),
                found: self.current_kind().name().to_string(),
                span: self.current_span().into(),
            });
        };

        // Parse sequence body
        // This mirrors pSequenceExpr2 from CVParser.lhs
        let statements = self.parse_sequence_statements(is_seq)?;

        if is_seq {
            self.expect_end_keyword("seq")?;
        } else {
            self.expect_end_keyword("par")?;
        }

        let end_span = self.current_span();
        let _full_span = Span::new(start_span.start, end_span.end);

        // Create sequence/parallel expression
        // In Haskell, these are converted to special sequence expressions
        // For now, we'll create a simple sequence statement and convert
        use crate::imperative::{ImperativeStatement, convert_stmts_to_expr};

        // Create a BeginEnd block that represents the sequence
        let seq_stmt = ImperativeStatement::BeginEnd {
            pos: start_pos,
            stmts: statements,
        };

        // For now, convert using the imperative conversion
        // In the future, this should create proper FSM sequence expressions
        Ok(convert_stmts_to_expr(vec![seq_stmt]))
    }

    /// Parse conditional expressions and pattern matching.
    ///
    /// Mirrors Haskell's `pCondExpressions :: SV_Parser [CQual]`.
    fn parse_cond_expressions(&mut self) -> Result<Vec<CQual>, ParseError> {
        let mut conditions = Vec::new();

        loop {
            let expr = self.parse_expr_simple()?;

            // Check for 'matches' pattern
            if self.check(&TokenKind::KwMatches) {
                self.advance();
                let pattern = self.parse_pattern_stub()?;
                conditions.push(CQual::Gen(CType::NoType, pattern, expr));
            } else {
                conditions.push(CQual::Filter(expr));
            }

            // Check for &&& separator
            if self.check(&TokenKind::SymAndAndAnd) {
                self.advance();
            } else {
                break;
            }
        }

        Ok(conditions)
    }

    /// Temporary stub for pattern parsing until the patterns module is complete.
    fn parse_pattern_stub(&mut self) -> Result<CPat, ParseError> {
        // For now, return a wildcard pattern as a placeholder
        // This will be replaced with proper pattern parsing
        let _span = self.current_span();
        let pos = Position::unknown();
        Ok(CPat::Wildcard(pos))
    }

    /// Parse expression with conditional qualifiers.
    ///
    /// Mirrors Haskell's `pExpressionWith :: [CQual] -> SV_Parser CExpr`.
    fn parse_expression_with(&mut self, conditions: Vec<CQual>) -> Result<CExpr, ParseError> {
        if conditions.is_empty() {
            return Err(ParseError::InvalidSyntax {
                message: "Empty condition list in expression".to_string(),
                span: self.current_span().into(),
            });
        }

        // Check if this is a conditional expression (has ?)
        if self.check(&TokenKind::SymQuestion) {
            let question_pos = self.current_position();
            self.advance(); // consume '?'

            let then_expr = self.parse_expr()?;
            self.expect(&TokenKind::SymColon)?;
            let else_expr = self.parse_expr()?;

            // Create conditional expression (mirrors mkIf from Haskell)
            Ok(self.make_if(question_pos, conditions, then_expr, else_expr))
        } else {
            // No conditional, just join conditions with logical AND
            Ok(self.join_with_and(conditions))
        }
    }

    /// Create a conditional expression from conditions.
    ///
    /// Mirrors Haskell's `mkIf`.
    /// This handles multiple conditions, pattern matching, and guard expressions.
    fn make_if(&self, pos: Position, conditions: Vec<CQual>, then_expr: CExpr, else_expr: CExpr) -> CExpr {
        match conditions.len() {
            0 => {
                // No conditions - this shouldn't happen, but return then_expr as fallback
                then_expr
            },
            1 => {
                // Single condition - simple case
                match conditions.into_iter().next().unwrap() {
                    CQual::Filter(cond) => {
                        let _span = Span::new(cond.span().start, else_expr.span().end);
                        CExpr::If(pos, Box::new(cond), Box::new(then_expr), Box::new(else_expr))
                    },
                    CQual::Gen(_, pattern, expr) => {
                        // Pattern match with generator: expr matches pattern ? then_expr : else_expr
                        // This is converted to a case expression in BSV
                        let mut arms = vec![CCaseArm {
                            pattern,
                            qualifiers: Vec::new(),
                            body: then_expr,
                            span: Span::DUMMY,
                        }];

                        // Add default arm as a wildcard pattern
                        arms.push(CCaseArm {
                            pattern: CPat::Wildcard(Position::unknown()),
                            qualifiers: Vec::new(),
                            body: else_expr,
                            span: Span::DUMMY,
                        });

                        CExpr::Case(
                            Position::unknown(),
                            Box::new(expr),
                            arms,
                        )
                    },
                }
            },
            _ => {
                // Multiple conditions - join with logical AND for filters, handle patterns
                let mut filter_conditions = Vec::new();
                let mut pattern_matches = Vec::new();

                for qual in conditions {
                    match qual {
                        CQual::Filter(expr) => filter_conditions.push(expr),
                        CQual::Gen(_, pattern, expr) => pattern_matches.push((pattern, expr)),
                    }
                }

                // If we have pattern matches, create nested case expressions
                if !pattern_matches.is_empty() {
                    // Create nested case expressions for multiple pattern matches
                    // Start from the innermost (last pattern) and work outward
                    let mut result = then_expr;

                    // Process pattern matches in reverse order to build nested cases
                    for (pattern, subject_expr) in pattern_matches.into_iter().rev() {
                        let success_arm = CCaseArm {
                            pattern,
                            qualifiers: vec![], // Filters will be added to outermost case
                            body: result,
                            span: Span::DUMMY,
                        };

                        let fail_arm = CCaseArm {
                            pattern: CPat::Wildcard(Position::unknown()),
                            qualifiers: vec![],
                            body: else_expr.clone(),
                            span: Span::DUMMY,
                        };

                        result = CExpr::Case(
                            Position::unknown(),
                            Box::new(subject_expr),
                            vec![success_arm, fail_arm],
                        );
                    }

                    // If there are also filter conditions, wrap in an if
                    if !filter_conditions.is_empty() {
                        let combined_cond = self.join_conditions_with_and(filter_conditions);
                        CExpr::If(pos, Box::new(combined_cond), Box::new(result), Box::new(else_expr))
                    } else {
                        result
                    }
                } else {
                    // Only filter conditions - join with &&
                    let combined_cond = self.join_conditions_with_and(filter_conditions);
                    CExpr::If(pos, Box::new(combined_cond), Box::new(then_expr), Box::new(else_expr))
                }
            }
        }
    }

    /// Join multiple condition expressions with logical AND.
    fn join_conditions_with_and(&self, conditions: Vec<CExpr>) -> CExpr {
        match conditions.len() {
            0 => {
                // Return a placeholder true expression
                let true_id = Id::new(SmolStr::new("True"), Position::unknown());
                CExpr::Var(true_id)
            },
            1 => conditions.into_iter().next().unwrap(),
            _ => {
                // Join with && operator
                let and_id = Id::new(SmolStr::new("&&"), Position::unknown());
                conditions.into_iter().reduce(|acc, expr| {
                    let span = Span::new(acc.span().start, expr.span().end);
                    CExpr::Infix(Box::new(acc), and_id.clone(), Box::new(expr), span)
                }).unwrap()
            }
        }
    }

    /// Join condition expressions with logical AND.
    ///
    /// Mirrors Haskell's `joinWithAnd`.
    fn join_with_and(&self, conditions: Vec<CQual>) -> CExpr {
        let exprs: Vec<CExpr> = conditions.into_iter()
            .filter_map(|qual| match qual {
                CQual::Filter(expr) => Some(expr),
                _ => None, // Skip pattern qualifiers for now
            })
            .collect();

        match exprs.len() {
            0 => {
                // Return a placeholder true expression
                let true_id = Id::new(SmolStr::new("True"), Position::unknown());
                CExpr::Var(true_id)
            },
            1 => exprs.into_iter().next().unwrap(),
            _ => {
                // Join with && operator
                let and_id = Id::new(SmolStr::new("&&"), Position::unknown());
                exprs.into_iter().reduce(|acc, expr| {
                    let span = Span::new(acc.span().start, expr.span().end);
                    CExpr::Infix(Box::new(acc), and_id.clone(), Box::new(expr), span)
                }).unwrap()
            }
        }
    }

    /// Parse expression with operator precedence using precedence climbing.
    ///
    /// This implements the operator precedence table from CVParser.lhs using
    /// the precedence climbing algorithm to properly handle operator precedence
    /// and associativity.
    fn parse_expression_with_precedence(&mut self) -> Result<CExpr, ParseError> {
        self.parse_precedence_expr(0)
    }

    /// Parse expression with given minimum precedence.
    ///
    /// This implements the precedence climbing algorithm to handle operator
    /// precedence and associativity correctly.
    fn parse_precedence_expr(&mut self, min_prec: u8) -> Result<CExpr, ParseError> {
        let mut left = self.parse_prefix_expr()?;

        while let Some((prec, is_left_assoc, op_name)) = self.get_binary_op_info(self.current_kind()) {
            if prec < min_prec {
                break;
            }

            let op_pos = self.current().position.clone();
            let op_id = Id::new(op_name, op_pos);
            self.advance();

            let next_min_prec = if is_left_assoc { prec + 1 } else { prec };
            let right = self.parse_precedence_expr(next_min_prec)?;

            let span = Span::new(left.span().start, right.span().end);
            left = CExpr::Infix(Box::new(left), op_id, Box::new(right), span);
        }

        Ok(left)
    }

    /// Parse prefix expressions (unary operators).
    ///
    /// This handles prefix operators like +, -, !, ~, etc. using CApply
    /// to match Haskell's representation of prefix operators.
    fn parse_prefix_expr(&mut self) -> Result<CExpr, ParseError> {
        if let Some(op_name) = self.get_prefix_op_name(self.current_kind()) {
            let op_pos = self.current().position.clone();
            let op_id = Id::new(op_name, op_pos);
            self.advance();

            let operand = self.parse_prefix_expr()?;

            let span = operand.span();
            let op_var = CExpr::Var(op_id);
            Ok(CExpr::Apply(Box::new(op_var), vec![operand], span))
        } else {
            self.parse_primary()
        }
    }

    /// Parse imperative statements for action blocks.
    ///
    /// This mirrors the imperative statement parsing from CVParser.lhs for action contexts.
    /// Parses statements until 'endaction' is reached.
    fn parse_action_statements(&mut self) -> Result<Vec<crate::imperative::ImperativeStatement>, ParseError> {
        use crate::imperative::ImperativeStatement;
        let mut statements = Vec::new();

        // Parse imperative statements until endaction
        while !self.check(&TokenKind::Id("endaction".into())) && !self.is_eof() {
            // Skip empty statements (just semicolons)
            if self.check(&TokenKind::SymSemi) {
                self.advance();
                continue;
            }

            let stmt = self.parse_imperative_stmt_in_action_context()?;
            statements.push(stmt);
        }

        Ok(statements)
    }

    /// Parse imperative statements for actionvalue blocks.
    ///
    /// This mirrors the imperative statement parsing from CVParser.lhs for actionvalue contexts.
    /// ActionValue blocks must end with a return statement.
    fn parse_actionvalue_statements(&mut self) -> Result<Vec<crate::imperative::ImperativeStatement>, ParseError> {
        use crate::imperative::ImperativeStatement;
        let mut statements = Vec::new();

        // Parse imperative statements until endactionvalue
        while !self.check(&TokenKind::Id("endactionvalue".into())) && !self.is_eof() {
            // Skip empty statements (just semicolons)
            if self.check(&TokenKind::SymSemi) {
                self.advance();
                continue;
            }

            let stmt = self.parse_imperative_stmt_in_actionvalue_context()?;
            statements.push(stmt);
        }

        Ok(statements)
    }

    /// Parse imperative statements for sequence/parallel blocks.
    ///
    /// This mirrors the imperative statement parsing for sequence contexts in CVParser.lhs.
    /// Sequence blocks are used for FSM generation.
    fn parse_sequence_statements(&mut self, is_seq: bool) -> Result<Vec<crate::imperative::ImperativeStatement>, ParseError> {
        use crate::imperative::ImperativeStatement;
        let mut statements = Vec::new();

        let end_keyword = if is_seq { "endseq" } else { "endpar" };

        // Parse imperative statements until the end keyword
        while !self.check(&TokenKind::Id(end_keyword.into())) && !self.is_eof() {
            // Skip empty statements (just semicolons)
            if self.check(&TokenKind::SymSemi) {
                self.advance();
                continue;
            }

            let stmt = self.parse_imperative_stmt_in_sequence_context()?;
            statements.push(stmt);
        }

        Ok(statements)
    }

    /// Parse a single imperative statement in action context.
    ///
    /// This mirrors the individual statement parsing from pImperativeStmt in CVParser.lhs.
    /// Action contexts allow most imperative statements except return statements.
    fn parse_imperative_stmt_in_action_context(&mut self) -> Result<crate::imperative::ImperativeStatement, ParseError> {
        self.parse_imperative_stmt_core(false, false)
    }

    /// Parse a single imperative statement in actionvalue context.
    ///
    /// ActionValue contexts allow all statements including return statements.
    fn parse_imperative_stmt_in_actionvalue_context(&mut self) -> Result<crate::imperative::ImperativeStatement, ParseError> {
        self.parse_imperative_stmt_core(true, false)
    }

    /// Parse a single imperative statement in sequence context.
    ///
    /// Sequence contexts allow specialized FSM statements.
    fn parse_imperative_stmt_in_sequence_context(&mut self) -> Result<crate::imperative::ImperativeStatement, ParseError> {
        self.parse_imperative_stmt_core(true, true)
    }

    /// Core imperative statement parser.
    ///
    /// This implements the core parsing logic that's shared across different contexts.
    /// The flags control which statements are allowed in each context.
    fn parse_imperative_stmt_core(
        &mut self,
        allow_return: bool,
        _is_sequence: bool
    ) -> Result<crate::imperative::ImperativeStatement, ParseError> {
        use crate::imperative::ImperativeStatement;

        let pos = Position::new(
            "unknown.bsv".to_string(),
            self.current_span().start as i32,
            1
        );

        match &self.current().kind {
            // Return statement: return [expr];
            TokenKind::KwReturn if allow_return => {
                self.advance(); // consume 'return'

                let expr = if self.check(&TokenKind::SymSemi) {
                    None
                } else {
                    Some(self.parse_expr()?)
                };

                self.expect(&TokenKind::SymSemi)?;
                Ok(ImperativeStatement::Return { pos, expr })
            },

            // If statement: if (cond) stmt [else stmt]
            TokenKind::KwIf => {
                self.advance(); // consume 'if'
                self.expect(&TokenKind::SymLParen)?;
                let cond = self.parse_expr()?;
                self.expect(&TokenKind::SymRParen)?;

                let then_stmt = self.parse_imperative_stmt_core(allow_return, _is_sequence)?;
                let then_branch = vec![then_stmt];

                let else_branch = if self.check(&TokenKind::KwElse) {
                    self.advance(); // consume 'else'
                    let else_stmt = self.parse_imperative_stmt_core(allow_return, _is_sequence)?;
                    Some(vec![else_stmt])
                } else {
                    None
                };

                Ok(ImperativeStatement::If { pos, cond, then_branch, else_branch })
            },

            // Begin/end block: begin stmts end
            TokenKind::KwBegin => {
                self.advance(); // consume 'begin'
                let mut stmts = Vec::new();

                while !self.check(&TokenKind::KwEnd) && !self.is_eof() {
                    if self.check(&TokenKind::SymSemi) {
                        self.advance();
                        continue;
                    }
                    let stmt = self.parse_imperative_stmt_core(allow_return, _is_sequence)?;
                    stmts.push(stmt);
                }

                self.expect(&TokenKind::KwEnd)?;
                Ok(ImperativeStatement::BeginEnd { pos, stmts })
            },

            // For loop: for (init; cond; update) stmt
            TokenKind::KwFor => {
                self.advance(); // consume 'for'
                self.expect(&TokenKind::SymLParen)?;

                // Parse init statements (until first semicolon)
                let mut init = Vec::new();
                while !self.check(&TokenKind::SymSemi) && !self.is_eof() {
                    let init_stmt = self.parse_imperative_stmt_core(false, false)?;
                    init.push(init_stmt);
                    if self.check(&TokenKind::SymComma) {
                        self.advance(); // consume comma
                    }
                }
                self.expect(&TokenKind::SymSemi)?;

                // Parse condition expression
                let cond = self.parse_expr()?;
                self.expect(&TokenKind::SymSemi)?;

                // Parse update statements (until right paren)
                let mut update = Vec::new();
                while !self.check(&TokenKind::SymRParen) && !self.is_eof() {
                    let update_stmt = self.parse_imperative_stmt_core(false, false)?;
                    update.push(update_stmt);
                    if self.check(&TokenKind::SymComma) {
                        self.advance(); // consume comma
                    }
                }
                self.expect(&TokenKind::SymRParen)?;

                // Parse body statement
                let body_stmt = self.parse_imperative_stmt_core(allow_return, _is_sequence)?;
                let body = vec![body_stmt];

                Ok(ImperativeStatement::For { pos, init, cond, update, body })
            },

            // While loop: while (cond) stmt
            TokenKind::KwWhile => {
                self.advance(); // consume 'while'
                self.expect(&TokenKind::SymLParen)?;
                let cond = self.parse_expr()?;
                self.expect(&TokenKind::SymRParen)?;

                let body_stmt = self.parse_imperative_stmt_core(allow_return, _is_sequence)?;
                let body = vec![body_stmt];

                Ok(ImperativeStatement::While { pos, cond, body })
            },

            // Action block: action stmts endaction
            TokenKind::KwAction => {
                self.advance(); // consume 'action'
                let mut stmts = Vec::new();

                while !self.check(&TokenKind::Id("endaction".into())) && !self.is_eof() {
                    if self.check(&TokenKind::SymSemi) {
                        self.advance();
                        continue;
                    }
                    let stmt = self.parse_imperative_stmt_core(false, false)?;
                    stmts.push(stmt);
                }

                self.expect_end_keyword("action")?;
                Ok(ImperativeStatement::Action { pos, stmts })
            },

            // Let binding: let var = expr;
            TokenKind::KwLet => {
                self.advance(); // consume 'let'

                if let TokenKind::Id(name) = &self.current().kind {
                    let var_name = Id::new(name.clone(), self.current().position.clone());
                    self.advance(); // consume identifier

                    self.expect(&TokenKind::SymEq)?;
                    let expr = self.parse_expr()?;
                    self.expect(&TokenKind::SymSemi)?;

                    Ok(ImperativeStatement::Let { name: var_name, expr })
                } else {
                    Err(ParseError::UnexpectedToken {
                        expected: "identifier".to_string(),
                        found: self.current_kind().name().to_string(),
                        span: self.current_span().into(),
                    })
                }
            },

            // Variable assignment or method call
            TokenKind::Id(_) => {
                // Parse as an expression first to handle complex left-hand sides
                let expr = self.parse_expr()?;

                // Check what follows to determine statement type
                match &self.current().kind {
                    // Assignment: var = expr;
                    TokenKind::SymEq => {
                        self.advance(); // consume '='
                        let rhs = self.parse_expr()?;
                        self.expect(&TokenKind::SymSemi)?;

                        // Convert expression to assignment
                        if let CExpr::Var(var_id) = expr {
                            Ok(ImperativeStatement::Equal { name: var_id, expr: rhs })
                        } else {
                            Ok(ImperativeStatement::NakedExpr(expr))
                        }
                    },

                    // Bind statement: var <- expr;
                    TokenKind::SymLArrow => {
                        self.advance(); // consume '<-'
                        let rhs = self.parse_expr()?;
                        self.expect(&TokenKind::SymSemi)?;

                        // Convert expression to bind
                        if let CExpr::Var(var_id) = expr {
                            Ok(ImperativeStatement::Bind { name: var_id, ty: None, expr: rhs })
                        } else {
                            Ok(ImperativeStatement::NakedExpr(expr))
                        }
                    },

                    // Register write: var <= expr;
                    TokenKind::SymLtEq => {
                        self.advance(); // consume '<='
                        let rhs = self.parse_expr()?;
                        self.expect(&TokenKind::SymSemi)?;

                        Ok(ImperativeStatement::RegWrite { lhs: expr, rhs })
                    },

                    // Naked expression: expr;
                    TokenKind::SymSemi => {
                        self.advance(); // consume ';'
                        Ok(ImperativeStatement::NakedExpr(expr))
                    },

                    _ => {
                        Err(ParseError::UnexpectedToken {
                            expected: "=, <-, <=, or ;".to_string(),
                            found: self.current_kind().name().to_string(),
                            span: self.current_span().into(),
                        })
                    }
                }
            },

            _ => {
                Err(ParseError::UnexpectedToken {
                    expected: "imperative statement".to_string(),
                    found: self.current_kind().name().to_string(),
                    span: self.current_span().into(),
                })
            }
        }
    }

}