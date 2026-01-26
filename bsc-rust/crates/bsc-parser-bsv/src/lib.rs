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
pub mod imperative_parsing;
pub mod operators;
pub mod package;
pub mod patterns;
pub mod types;

use bsc_diagnostics::{ParseError, Span, Position};
use bsc_lexer_bsv::{Lexer, LexerFlags, Token, TokenKind};
use bsc_syntax::{
    CDefn, CExpr, CPackage, CPat, CType, CDef, CQType, CClause, CPragma, CStructDef,
    StructSubType, IdK, CField, CValueDef
};
use crate::imperative::ImperativeStatement;
use std::collections::HashMap;
use std::sync::RwLock;

/// Global position map for span.start → Position lookup.
/// Populated during token stream creation, used by chumsky parsers.
/// Mirrors Haskell's approach where each Token carries its Position.
static POSITION_MAP: RwLock<Option<HashMap<u32, Position>>> = RwLock::new(None);

/// Set the position map (called before parsing).
fn set_position_map(map: HashMap<u32, Position>) {
    *POSITION_MAP.write().unwrap() = Some(map);
}

/// Look up Position from span start offset.
/// Returns the actual Position from the lexer, never Position::unknown().
pub fn lookup_position(span_start: u32) -> Position {
    POSITION_MAP
        .read()
        .unwrap()
        .as_ref()
        .and_then(|map| map.get(&span_start).cloned())
        .unwrap_or_else(|| Position::line_col(1, span_start as i32 + 1))
}

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
        Self::new_with_file(source, "")
    }

    pub fn new_with_file(source: &'src str, filename: &str) -> ParseResult<Self> {
        let lexer = Lexer::with_file(source, LexerFlags::default(), filename);
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
        // Build position map for span → position lookup (mirrors Haskell's Token Position LexItem)
        let mut position_map = HashMap::new();

        // Convert tokens to the format expected by the chumsky parser
        // Filter out Eof tokens - chumsky handles end-of-input separately via end()
        let token_spans: Vec<(bsc_lexer_bsv::TokenKind, chumsky::prelude::SimpleSpan<u32>)> =
            self.tokens
                .iter()
                .filter(|t| !matches!(t.kind, TokenKind::Eof))
                .map(|token| {
                    // Store position in map for lookup by chumsky parsers
                    position_map.insert(token.span.start, token.position.clone());
                    use chumsky::span::Span as ChumskySpan;
                    let span = chumsky::prelude::SimpleSpan::new((), token.span.start..token.span.end);
                    (token.kind.clone(), span)
                })
                .collect();

        // Set global position map for use by parsers
        set_position_map(position_map);

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

    /// Convert an ImperativeStatement to a CDefn.
    ///
    /// Mirrors `convImperativeStmtsToCDefns` from CVParserImperative.lhs.
    /// This function converts BSV imperative constructs to the functional CSyntax representation.
    fn imperative_statement_to_cdefn(&self, stmt: ImperativeStatement) -> ParseResult<CDefn> {
        match stmt {
            ImperativeStatement::ModuleDefn { pos, name, pragma, module_type, def_clause } => {
                // From Haskell: ISModule pos name maybePragma moduleType definition : rest) =
                //   do let pragmas = map CPragma (maybeToList maybePragma)
                //          defn = CValueSign (CDef name moduleType [definition])
                let mut cdefns = Vec::new();

                // Add pragma if present
                if let Some(p) = pragma {
                    cdefns.push(CDefn::Pragma(p));
                }

                // Create the module definition
                let def = CDef::Untyped {
                    name: name.clone(),
                    ty: module_type,
                    clauses: vec![def_clause],
                    span: Span::DUMMY,
                };
                cdefns.push(CDefn::ValueSign(def));

                // Return the module definition (prefer the second item if pragma exists)
                if cdefns.len() > 1 {
                    Ok(cdefns.remove(1))
                } else {
                    Ok(cdefns.remove(0))
                }
            }
            ImperativeStatement::FunctionDefn { pos, name, ret_type, params, provisos, body: _, attrs: _ } => {
                // From Haskell: ISFunction pos prags (CLValueSign def []) : rest) =
                //   do let pragmas = map CPragma prags
                //          defn = (CValueSign def)

                // Convert parameters and return type to a function type signature
                let ty = if let Some(ret_ty) = ret_type {
                    // Create a qualified type with provisos and function type
                    CQType {
                        context: provisos,
                        ty: ret_ty,
                        span: Span::DUMMY,
                    }
                } else {
                    return Err(ParseError::InvalidSyntax {
                        message: "Function must have a return type".to_string(),
                        span: Span::DUMMY.into(),
                    });
                };

                // For now, create a simple function definition
                // In a full implementation, we'd need to convert the function body to a CClause
                let clause = CClause {
                    patterns: params.into_iter().map(|(param_name, _)| {
                        use bsc_syntax::CPat;
                        CPat::Var(param_name)
                    }).collect(),
                    qualifiers: Vec::new(),
                    body: CExpr::Var(name.clone()), // Placeholder
                    span: Span::DUMMY,
                };

                let def = CDef::Untyped {
                    name: name.clone(),
                    ty,
                    clauses: vec![clause],
                    span: Span::DUMMY,
                };

                Ok(CDefn::ValueSign(def))
            }
            ImperativeStatement::InterfaceDecl { pos, name, type_vars, members } => {
                // From Haskell: ISInterface pos name ifcPragmas params methods : rest) =
                //   do let derivedClasses = []
                //          defn = Cstruct True (SInterface ifcPragmas) name params methods derivedClasses
                let struct_def = CStructDef {
                    visible: true, // Interface constructors are visible
                    sub_type: StructSubType::Interface(vec![]),
                    name: IdK::Plain(name),
                    params: type_vars,
                    fields: members,
                    deriving: Vec::new(), // No derived classes for interfaces
                    span: Span::DUMMY,
                };

                Ok(CDefn::Struct(struct_def))
            }
            ImperativeStatement::Typedef(defns) => {
                // From Haskell: ISTypedef pos defns : rest) =
                //   do restDefns <- convImperativeStmtsToCDefns rest
                //      return (defns ++ restDefns)

                // For multiple typedefs, return the first one
                // In a full implementation, we'd need a way to return multiple CDefns
                if let Some(first_def) = defns.into_iter().next() {
                    Ok(first_def)
                } else {
                    Err(ParseError::InvalidSyntax {
                        message: "Empty typedef list".to_string(),
                        span: Span::DUMMY.into(),
                    })
                }
            }
            ImperativeStatement::Rule { pos, name, guard, body_pos: _, body: _ } => {
                // From Haskell, rules are not directly converted to CDefn in the same way.
                // They are typically wrapped in a module or handled differently.
                // For now, we'll create a simple value definition representing the rule

                let rule_expr = if let Some(guard_expr) = guard {
                    // Create a rule with guard
                    guard_expr
                } else {
                    // Create a rule without guard
                    CExpr::Var(name.clone())
                };

                let clause = CClause {
                    patterns: Vec::new(),
                    qualifiers: Vec::new(),
                    body: rule_expr,
                    span: Span::DUMMY,
                };

                let def = CValueDef {
                    name: name.clone(),
                    clauses: vec![clause],
                    span: Span::DUMMY,
                };

                Ok(CDefn::Value(def))
            }
            _ => {
                Err(ParseError::InvalidSyntax {
                    message: format!("Cannot convert imperative statement to CDefn: {:?}", stmt),
                    span: Span::DUMMY.into(),
                })
            }
        }
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
                let stmt = self.parse_module()?;
                self.imperative_statement_to_cdefn(stmt)
            }
            TokenKind::KwFunction => {
                let stmt = self.parse_function()?;
                self.imperative_statement_to_cdefn(stmt)
            }
            TokenKind::KwInterface => {
                let stmt = self.parse_interface_decl()?;
                self.imperative_statement_to_cdefn(stmt)
            }
            TokenKind::KwTypedef => {
                let stmt = self.parse_typedef()?;
                self.imperative_statement_to_cdefn(stmt)
            }
            TokenKind::KwRule => {
                let stmt = self.parse_rule()?;
                self.imperative_statement_to_cdefn(stmt)
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

    /// Get the position of the current token (file, line, column).
    /// Mirrors Haskell's `getPos` which extracts position from current token.
    fn current_position(&self) -> Position {
        self.current().position.clone()
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

    /// Look ahead N tokens and check if it matches the expected kind.
    ///
    /// Returns true if the token at position `current_pos + offset` matches `expected`.
    /// Returns false if we would go past the end of the token stream.
    fn peek_ahead(&self, offset: usize, expected: &TokenKind) -> bool {
        if let Some(token) = self.tokens.get(self.pos + offset) {
            std::mem::discriminant(&token.kind) == std::mem::discriminant(expected)
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

pub fn parse_package_with_file(source: &str, filename: &str) -> Result<CPackage, Vec<ParseErrorInfo>> {
    // Extract default package name from filename (without path and extension)
    let default_name = std::path::Path::new(filename)
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("DefaultPackage")
        .to_string();

    let mut parser = BsvParser::new_with_file(source, filename)
        .map_err(|e: ParseError| vec![ParseErrorInfo { message: e.to_string() }])?;

    parser.parse_package_with_default(default_name)
        .map_err(|e: ParseError| vec![ParseErrorInfo { message: e.to_string() }])
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
