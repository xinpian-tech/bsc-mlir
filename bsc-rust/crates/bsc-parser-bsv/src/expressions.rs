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
                let _pos = Position::unknown(); // Placeholder position
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
    fn parse_action_expr(&mut self) -> Result<CExpr, ParseError> {
        let start_span = self.current_span();
        self.expect(&TokenKind::KwAction)?;

        // Parse action body (imperative statements)
        // For now, return a placeholder
        // TODO: Implement full action parsing when imperative module is ready

        self.expect_end_keyword("action")?;
        let end_span = self.current_span();
        let _full_span = Span::new(start_span.start, end_span.end);

        // Create a placeholder action expression
        Ok(CExpr::Var(Id::new(SmolStr::new("__action_placeholder"), Position::unknown())))
    }

    /// Parse actionvalue expressions.
    ///
    /// Mirrors Haskell's `pActionValueExpr :: SV_Parser CExpr`.
    fn parse_actionvalue_expr(&mut self) -> Result<CExpr, ParseError> {
        let start_span = self.current_span();
        self.expect(&TokenKind::KwActionvalue)?;

        // Parse actionvalue body
        // For now, return a placeholder
        // TODO: Implement full actionvalue parsing when imperative module is ready

        self.expect_end_keyword("actionvalue")?;
        let end_span = self.current_span();
        let _full_span = Span::new(start_span.start, end_span.end);

        // Create a placeholder actionvalue expression
        Ok(CExpr::Var(Id::new(SmolStr::new("__actionvalue_placeholder"), Position::unknown())))
    }

    /// Parse sequence/parallel expressions.
    ///
    /// Mirrors Haskell's `pSequenceExpr :: SV_Parser CExpr`.
    fn parse_seq_expr(&mut self) -> Result<CExpr, ParseError> {
        let start_span = self.current_span();

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
        // For now, return a placeholder
        // TODO: Implement full sequence parsing when imperative module is ready

        if is_seq {
            self.expect_end_keyword("seq")?;
        } else {
            self.expect_end_keyword("par")?;
        }

        let end_span = self.current_span();
        let _full_span = Span::new(start_span.start, end_span.end);

        // Create a placeholder sequence expression
        let placeholder_name = if is_seq { "__seq_placeholder" } else { "__par_placeholder" };
        Ok(CExpr::Var(Id::new(SmolStr::new(placeholder_name), Position::unknown())))
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
            let question_pos = Position::unknown();
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
    fn make_if(&self, _pos: Position, conditions: Vec<CQual>, then_expr: CExpr, else_expr: CExpr) -> CExpr {
        // For now, create a simple conditional based on the first condition
        // TODO: Handle multiple conditions and pattern matching properly
        match conditions.into_iter().next() {
            Some(CQual::Filter(cond)) => {
                let _span = Span::new(cond.span().start, else_expr.span().end);
                CExpr::If(Position::unknown(), Box::new(cond), Box::new(then_expr), Box::new(else_expr))
            },
            _ => {
                // Fallback for complex patterns
                then_expr
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

    /// Parse expression with operator precedence.
    ///
    /// This implements the operator precedence table from CVParser.lhs.
    /// Currently a simplified version - full precedence climbing would be implemented here.
    fn parse_expression_with_precedence(&mut self) -> Result<CExpr, ParseError> {
        // Start with a primary expression
        let mut left = self.parse_primary()?;

        // Parse binary operators with precedence
        while let Some((op_id, _precedence)) = self.try_parse_binary_operator() {
            let right = self.parse_primary()?;
            let span = Span::new(left.span().start, right.span().end);
            left = CExpr::Infix(Box::new(left), op_id, Box::new(right), span);
        }

        Ok(left)
    }

    /// Try to parse a binary operator and return its ID and precedence.
    fn try_parse_binary_operator(&mut self) -> Option<(Id, u8)> {
        let pos = self.current().position.clone();
        match self.current().kind {
            TokenKind::SymStarStar => {
                self.advance();
                Some((Id::new(SmolStr::new("**"), pos), 2))
            },
            TokenKind::SymStar => {
                self.advance();
                Some((Id::new(SmolStr::new("*"), pos), 3))
            },
            TokenKind::SymSlash => {
                self.advance();
                Some((Id::new(SmolStr::new("/"), pos), 3))
            },
            TokenKind::SymPercent => {
                self.advance();
                Some((Id::new(SmolStr::new("%"), pos), 3))
            },
            TokenKind::SymPlus => {
                self.advance();
                Some((Id::new(SmolStr::new("+"), pos), 4))
            },
            TokenKind::SymMinus => {
                self.advance();
                Some((Id::new(SmolStr::new("-"), pos), 4))
            },
            TokenKind::SymLtLt => {
                self.advance();
                Some((Id::new(SmolStr::new("<<"), pos), 5))
            },
            TokenKind::SymGtGt => {
                self.advance();
                Some((Id::new(SmolStr::new(">>"), pos), 5))
            },
            TokenKind::SymLt => {
                self.advance();
                Some((Id::new(SmolStr::new("<"), pos), 6))
            },
            TokenKind::SymLtEq => {
                self.advance();
                Some((Id::new(SmolStr::new("<="), pos), 6))
            },
            TokenKind::SymGt => {
                self.advance();
                Some((Id::new(SmolStr::new(">"), pos), 6))
            },
            TokenKind::SymGtEq => {
                self.advance();
                Some((Id::new(SmolStr::new(">="), pos), 6))
            },
            TokenKind::SymEqEq => {
                self.advance();
                Some((Id::new(SmolStr::new("=="), pos), 7))
            },
            TokenKind::SymBangEq => {
                self.advance();
                Some((Id::new(SmolStr::new("!="), pos), 7))
            },
            TokenKind::SymAnd => {
                self.advance();
                Some((Id::new(SmolStr::new("&"), pos), 8))
            },
            TokenKind::SymCaret => {
                self.advance();
                Some((Id::new(SmolStr::new("^"), pos), 9))
            },
            TokenKind::SymTildeCaret => {
                self.advance();
                Some((Id::new(SmolStr::new("~^"), pos), 9))
            },
            TokenKind::SymCaretTilde => {
                self.advance();
                Some((Id::new(SmolStr::new("^~"), pos), 9))
            },
            TokenKind::SymPipe => {
                self.advance();
                Some((Id::new(SmolStr::new("|"), pos), 10))
            },
            TokenKind::SymAndAnd => {
                self.advance();
                Some((Id::new(SmolStr::new("&&"), pos), 11))
            },
            TokenKind::SymPipePipe => {
                self.advance();
                Some((Id::new(SmolStr::new("||"), pos), 12))
            },
            _ => None,
        }
    }
}