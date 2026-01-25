//! BSV (SystemVerilog-like) syntax parser.
//!
//! Mirrors `src/comp/CVParser.lhs` from the Haskell implementation.
//!
//! BSV uses explicit end keywords (`endmodule`, `endinterface`, etc.)
//! instead of layout/indentation rules. This parser handles the BSV
//! syntax variant of Bluespec.
//!
//! # Design Principles
//!
//! - **Explicit errors**: All parse errors are returned via `ParseResult`,
//!   following the "no silent failures" principle.
//! - **Span tracking**: All AST nodes include source location information
//!   for error messages and IDE features.
//! - **No panics**: The parser never panics on invalid input; it returns
//!   structured error information instead.

pub mod definitions;
pub mod expressions;
pub mod imperative;
pub mod operators;
pub mod package;
pub mod patterns;
pub mod types;

use bsc_diagnostics::{ParseError, Span};
use bsc_lexer_bsv::{Lexer, Token, TokenKind};
use bsc_syntax::{CDefn, CExpr, CPackage, CPat, CType};

/// Result type for parser operations.
pub type ParseResult<T> = Result<T, ParseError>;

/// BSV parser state.
///
/// This parser handles BSV (SystemVerilog-like) syntax, which uses explicit
/// end keywords rather than layout-based scoping:
///
/// - `module ... endmodule`
/// - `interface ... endinterface`
/// - `function ... endfunction`
/// - `method ... endmethod`
/// - `rule ... endrule`
/// - `action ... endaction`
/// - `actionvalue ... endactionvalue`
/// - `begin ... end`
#[derive(Debug)]
pub struct BsvParser<'src> {
    /// Source text (for error messages and span extraction)
    source: &'src str,
    /// Pre-lexed tokens
    tokens: Vec<Token>,
    /// Current position in token stream
    pos: usize,
}

impl<'src> BsvParser<'src> {
    /// Create a new BSV parser for the given source text.
    ///
    /// This lexes the source using BSV mode and prepares for parsing.
    ///
    /// # Errors
    ///
    /// Returns an error if lexing fails (e.g., unterminated string,
    /// invalid character).
    pub fn new(source: &'src str) -> ParseResult<Self> {
        let lexer = Lexer::new(source);
        let tokens = lexer.tokenize().map_err(|e| ParseError::InvalidSyntax {
            message: format!("Lexer error: {e}"),
            span: Span::DUMMY.into(),
        })?;

        Ok(Self {
            source,
            tokens,
            pos: 0,
        })
    }

    /// Parse a complete BSV package.
    ///
    /// A BSV package has the form:
    /// ```text
    /// package PackageName;
    ///     import ...;
    ///     export ...;
    ///     <definitions>
    /// endpackage
    /// ```
    ///
    /// # Errors
    ///
    /// Returns an error if the source does not contain a valid package.
    pub fn parse_package(&mut self) -> ParseResult<CPackage> {
        self.parse_package_with_default("DefaultPackage".to_string())
    }

    /// Parse a BSV package with a default name.
    pub fn parse_package_with_default(&mut self, default_name: String) -> ParseResult<CPackage> {
        // Convert tokens to the format expected by the chumsky parser
        let token_spans: Vec<(bsc_lexer_bsv::TokenKind, chumsky::prelude::SimpleSpan<u32>)> =
            self.tokens
                .iter()
                .map(|token| {
                    use chumsky::span::Span as ChumskySpan;
                    let span = chumsky::prelude::SimpleSpan::new((), token.span.start..token.span.end);
                    (token.kind.clone(), span)
                })
                .collect();

        // Use the chumsky-based package parser
        package::parse_bsv_package(token_spans, default_name)
            .map_err(|errors| {
                // Convert chumsky errors to our ParseError format
                let message = if errors.is_empty() {
                    "Unknown parse error".to_string()
                } else {
                    format!("Parse error: {:?}", errors[0])
                };

                ParseError::InvalidSyntax {
                    message,
                    span: Span::DUMMY.into(),
                }
            })
    }

    /// Parse a top-level definition.
    ///
    /// BSV definitions include:
    /// - `module` definitions
    /// - `interface` declarations
    /// - `function` definitions
    /// - `typedef` declarations
    /// - `instance` declarations
    ///
    /// # Errors
    ///
    /// Returns an error if the current tokens do not form a valid definition.
    pub fn parse_definition(&mut self) -> ParseResult<CDefn> {
        match self.current_kind() {
            TokenKind::KwModule => {
                let _stmt = self.parse_module()?;
                // TODO: Convert ImperativeStatement to CDefn
                Err(ParseError::InvalidSyntax {
                    message: "Module definition conversion to CDefn not yet implemented".to_string(),
                    span: self.current_span().into(),
                })
            }
            TokenKind::KwFunction => {
                let _stmt = self.parse_function()?;
                // TODO: Convert ImperativeStatement to CDefn
                Err(ParseError::InvalidSyntax {
                    message: "Function definition conversion to CDefn not yet implemented".to_string(),
                    span: self.current_span().into(),
                })
            }
            TokenKind::KwInterface => {
                let _stmt = self.parse_interface_decl()?;
                // TODO: Convert ImperativeStatement to CDefn
                Err(ParseError::InvalidSyntax {
                    message: "Interface definition conversion to CDefn not yet implemented".to_string(),
                    span: self.current_span().into(),
                })
            }
            TokenKind::KwTypedef => {
                let _stmt = self.parse_typedef()?;
                // TODO: Convert ImperativeStatement to CDefn
                Err(ParseError::InvalidSyntax {
                    message: "Typedef definition conversion to CDefn not yet implemented".to_string(),
                    span: self.current_span().into(),
                })
            }
            TokenKind::KwRule => {
                let _stmt = self.parse_rule()?;
                // TODO: Convert ImperativeStatement to CDefn
                Err(ParseError::InvalidSyntax {
                    message: "Rule definition conversion to CDefn not yet implemented".to_string(),
                    span: self.current_span().into(),
                })
            }
            _ => Err(ParseError::InvalidSyntax {
                message: format!("Expected definition keyword, found: {}", self.current_kind().name()),
                span: self.current_span().into(),
            }),
        }
    }

    /// Parse an expression.
    ///
    /// # Errors
    ///
    /// Returns an error if the current tokens do not form a valid expression.
    pub fn parse_expression(&mut self) -> ParseResult<CExpr> {
        // Delegate to the expressions module implementation
        self.parse_expr()
    }

    /// Parse a pattern.
    ///
    /// # Errors
    ///
    /// Returns an error if the current tokens do not form a valid pattern.
    pub fn parse_pattern(&mut self) -> ParseResult<CPat> {
        patterns::parse_pattern(self)
    }

    /// Parse a type.
    ///
    /// # Errors
    ///
    /// Returns an error if the current tokens do not form a valid type.
    pub fn parse_type(&mut self) -> ParseResult<CType> {
        // Delegate to the types module implementation
        self.parse_type_expr()
    }

    // ========================================================================
    // Token stream navigation
    // ========================================================================

    /// Get the current token, or EOF if past the end.
    fn current(&self) -> &Token {
        self.tokens.get(self.pos).unwrap_or_else(|| {
            self.tokens
                .last()
                .expect("token stream should contain at least EOF")
        })
    }

    /// Get the kind of the current token.
    fn current_kind(&self) -> &TokenKind {
        &self.current().kind
    }

    /// Get the span of the current token.
    fn current_span(&self) -> Span {
        self.current().span
    }

    /// Check if we're at end of file.
    fn is_eof(&self) -> bool {
        matches!(self.current_kind(), TokenKind::Eof)
    }

    /// Advance to the next token and return the previous one.
    fn advance(&mut self) -> &Token {
        let token = self.current();
        if self.pos < self.tokens.len() {
            self.pos += 1;
        }
        // Return reference to the token we just passed
        &self.tokens[self.pos.saturating_sub(1)]
    }

    /// Check if the current token matches the expected kind.
    fn check(&self, expected: &TokenKind) -> bool {
        std::mem::discriminant(self.current_kind()) == std::mem::discriminant(expected)
    }

    /// Consume a token of the expected kind, or return an error.
    fn expect(&mut self, expected: &TokenKind) -> ParseResult<&Token> {
        if self.check(expected) {
            Ok(self.advance())
        } else {
            Err(ParseError::UnexpectedToken {
                expected: expected.name().to_string(),
                found: self.current_kind().name().to_string(),
                span: self.current_span().into(),
            })
        }
    }

    /// Consume a token if it matches the expected kind.
    fn eat(&mut self, expected: &TokenKind) -> bool {
        if self.check(expected) {
            self.advance();
            true
        } else {
            false
        }
    }

    /// Get the source text for a span.
    fn span_text(&self, span: Span) -> &'src str {
        &self.source[span.start as usize..span.end as usize]
    }

    // ========================================================================
    // BSV-specific helpers
    // ========================================================================

    /// Expect an `end*` keyword matching the given construct.
    ///
    /// BSV uses explicit end keywords like `endmodule`, `endinterface`, etc.
    fn expect_end_keyword(&mut self, construct: &str) -> ParseResult<Span> {
        let end_keyword = format!("end{construct}");
        match self.current_kind() {
            TokenKind::Id(id) if id.as_str() == end_keyword => {
                let span = self.current_span();
                self.advance();
                Ok(span)
            }
            _ => Err(ParseError::UnexpectedToken {
                expected: end_keyword,
                found: self.current_kind().name().to_string(),
                span: self.current_span().into(),
            }),
        }
    }
}

/// Parse BSV source code into a package AST.
///
/// This is the main entry point for BSV parsing.
///
/// # Errors
///
/// Returns an error if the source cannot be parsed as a valid BSV package.
///
/// # Examples
///
/// ```ignore
/// use bsc_parser_bsv::parse;
///
/// let source = r#"
///     package MyPackage;
///         module mkCounter(Counter);
///             // ...
///         endmodule
///     endpackage
/// "#;
///
/// let package = parse(source)?;
/// ```
pub fn parse(source: &str) -> ParseResult<CPackage> {
    let mut parser = BsvParser::new(source)?;
    parser.parse_package()
}

/// Parse BSV source code with a specific default package name.
pub fn parse_with_default_name(source: &str, default_name: String) -> ParseResult<CPackage> {
    let mut parser = BsvParser::new(source)?;
    parser.parse_package_with_default(default_name)
}

#[derive(Debug)]
pub struct ParseErrorInfo {
    pub message: String,
}

pub fn parse_package_with_file(source: &str, _filename: &str) -> Result<CPackage, Vec<ParseErrorInfo>> {
    parse(source).map_err(|e| vec![ParseErrorInfo { message: e.to_string() }])
}

#[cfg(test)]
mod tests {
    use super::*;
    use bsc_test_utils::{get_bsc_path, get_testsuite_dir, run_differential_test_fail_fast, SyntaxMode};

    #[test]
    fn test_differential_bsv_testsuite() {
        let bsc_path = match get_bsc_path() {
            Some(p) => p,
            None => {
                eprintln!("BSC_PATH not set, skipping differential test");
                return;
            }
        };

        let testsuite_dir = get_testsuite_dir();
        if !testsuite_dir.exists() {
            eprintln!("BSC_TESTSUITE_DIR not found at {}, skipping differential test", testsuite_dir.display());
            return;
        }

        run_differential_test_fail_fast(
            SyntaxMode::Bsv,
            &testsuite_dir,
            &bsc_path,
            |source, filename| {
                parse_package_with_file(source, filename)
                    .map_err(|errs| format!("{:?}", errs.first()))
            },
        );
    }
}
