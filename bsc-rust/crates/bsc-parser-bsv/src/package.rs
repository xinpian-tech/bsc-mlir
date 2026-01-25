//! Package-level parsing for BSV.
//!
//! This module implements parsing for BSV packages, imports, exports, and attributes.
//! Mirrors the package parsing functions from `src/comp/Parser/BSV/CVParser.lhs`.

use crate::imperative::{ImperativeFlags, ImperativeStatement, ImperativeStmtContext};
use bsc_diagnostics::{Position, Span};
use bsc_lexer_bsv::TokenKind;
use bsc_syntax::csyntax::*;
use bsc_syntax::id::Id;
// use bsc_syntax::literal::{IntLiteral, Literal}; // Unused for now
use chumsky::input::{MappedInput, Input};
use chumsky::prelude::*;
use smol_str::SmolStr;
use num_bigint::BigInt;

/// Parser error type - uses SimpleSpan<u32> to match our Span type.
pub type PError<'a> = Rich<'a, TokenKind, SimpleSpan<u32>>;

/// Type alias for our token input with spans.
type TokenStream<'a> = MappedInput<'a, TokenKind, SimpleSpan<u32>, &'a [(TokenKind, SimpleSpan<u32>)]>;

/// Type alias for parser extra with our error type.
type ParserExtra<'a> = extra::Err<PError<'a>>;

// ============================================================================
// Helper Functions
// ============================================================================

/// Create an Id from a string and position (like Haskell's mkId).
fn make_id(name: SmolStr, pos: Position) -> Id {
    Id::new(name, pos)
}

/// Convert SimpleSpan to our Span type.
fn to_span(simple_span: SimpleSpan<u32>) -> Span {
    Span::new(simple_span.start, simple_span.end)
}

/// Convert SimpleSpan to Position (using start of span).
/// For now, we use Position::unknown() since we don't have file/line info in spans.
fn to_position(_simple_span: SimpleSpan<u32>) -> Position {
    Position::unknown()
}

/// Check if an ImperativeStatement is an import.
fn is_is_import(stmt: &ImperativeStatement) -> bool {
    matches!(stmt, ImperativeStatement::Import(_))
}

/// Check if an ImperativeStatement is an export.
fn is_is_export(stmt: &ImperativeStatement) -> bool {
    matches!(stmt, ImperativeStatement::Export(_))
}

// ============================================================================
// Token Parsers
// ============================================================================

/// Parse a keyword token.
fn keyword<'a>(
    expected: TokenKind,
) -> impl Parser<'a, TokenStream<'a>, (), ParserExtra<'a>> + Clone {
    let expected_clone = expected.clone();
    select! { token if std::mem::discriminant(&token) == std::mem::discriminant(&expected_clone) => () }
        .labelled(format!("keyword '{}'", expected.name()))
}

/// Parse a semicolon.
fn semicolon<'a>() -> impl Parser<'a, TokenStream<'a>, (), ParserExtra<'a>> + Clone {
    select! { TokenKind::SymSemi => () }.labelled("semicolon")
}

/// Parse a word (identifier).
fn word<'a>() -> impl Parser<'a, TokenStream<'a>, SmolStr, ParserExtra<'a>> + Clone {
    select! {
        TokenKind::Id(name) => name,
    }
    .labelled("identifier")
}

/// Parse a quoted string literal.
fn quoted_string<'a>() -> impl Parser<'a, TokenStream<'a>, String, ParserExtra<'a>> + Clone {
    select! {
        TokenKind::String(s) => s,
    }
    .labelled("quoted string")
}

/// Parse a decimal number.
fn decimal<'a>() -> impl Parser<'a, TokenStream<'a>, BigInt, ParserExtra<'a>> + Clone {
    select! {
        TokenKind::Integer { value, .. } => value,
    }
    .labelled("decimal number")
}

/// Parse a comma.
fn comma<'a>() -> impl Parser<'a, TokenStream<'a>, (), ParserExtra<'a>> + Clone {
    select! { TokenKind::SymComma => () }.labelled("comma")
}

/// Parse a symbol.
fn symbol<'a>(
    expected: TokenKind,
) -> impl Parser<'a, TokenStream<'a>, (), ParserExtra<'a>> + Clone {
    let expected_clone = expected.clone();
    select! { token if std::mem::discriminant(&token) == std::mem::discriminant(&expected_clone) => () }
        .labelled(format!("symbol '{}'", expected.name()))
}

// ============================================================================
// Attribute Parsing (mirrors pAttributes, pAttribute, pAttValue)
// ============================================================================

/// Attribute value - mirrors `AttValue` from CVParser.lhs.
#[derive(Debug, Clone, PartialEq)]
pub enum AttValue {
    Num(Position, BigInt),
    String(Position, String),
    List(Position, Vec<AttValue>),
}

/// An attribute - mirrors `Attribute` from CVParser.lhs.
#[derive(Debug, Clone, PartialEq)]
pub struct Attribute {
    pub name: Id,
    pub value: AttValue,
}

/// Parse an attribute value.
fn parse_att_value<'a>() -> impl Parser<'a, TokenStream<'a>, AttValue, ParserExtra<'a>> + Clone {
    recursive(|att_value| {
        choice((
            // Number
            decimal()
                .map_with(|num, e| AttValue::Num(to_position(e.span()), num)),
            // String
            quoted_string()
                .map_with(|s, e| AttValue::String(to_position(e.span()), s)),
            // List in braces: { value1, value2, ... }
            att_value
                .separated_by(comma())
                .allow_trailing()
                .collect::<Vec<_>>()
                .delimited_by(symbol(TokenKind::SymLBrace), symbol(TokenKind::SymRBrace))
                .map_with(|list, e| AttValue::List(to_position(e.span()), list)),
        ))
    })
    .labelled("attribute value")
}

/// Parse a single attribute.
fn parse_attribute<'a>() -> impl Parser<'a, TokenStream<'a>, Attribute, ParserExtra<'a>> + Clone {
    // Attribute name - can be regular word or special keywords
    let name = choice((
        word(),
        keyword(TokenKind::KwClockedBy).to(SmolStr::from("clocked_by")),
        keyword(TokenKind::KwResetBy).to(SmolStr::from("reset_by")),
    ));

    name.map_with(|name, e| make_id(name, to_position(e.span())))
        .then(
            // Optional value (defaults to 1 if not specified)
            symbol(TokenKind::SymEq)
                .ignore_then(parse_att_value())
                .or_not(),
        )
        .map_with(|(name, value): (Id, Option<AttValue>), e| {
            let value = value.unwrap_or_else(|| AttValue::Num(to_position(e.span()), BigInt::from(1)));
            Attribute { name, value }
        })
        .labelled("attribute")
}

/// Parse attributes: (* attr1 = value1, attr2, ... *)
fn parse_attributes<'a>() -> impl Parser<'a, TokenStream<'a>, Vec<Attribute>, ParserExtra<'a>> + Clone {
    // Each attribute block starts with (* and ends with *)
    let attr_block = parse_attribute()
        .separated_by(comma())
        .allow_trailing()
        .collect::<Vec<_>>()
        .delimited_by(
            symbol(TokenKind::SymLParenStar),
            symbol(TokenKind::SymStarRParen),
        )
        .labelled("attribute block");

    // Multiple attribute blocks can appear consecutively
    attr_block
        .repeated()
        .collect::<Vec<Vec<_>>>()
        .map(|blocks: Vec<Vec<Attribute>>| blocks.into_iter().flatten().collect())
        .labelled("attributes")
}

// ============================================================================
// Export Parsing (mirrors pExportItem, pExportConstructor, etc.)
// ============================================================================

/// Parse a single export item.
fn parse_export_item<'a>() -> impl Parser<'a, TokenStream<'a>, CExport, ParserExtra<'a>> + Clone {
    choice((
        // Try package export first: Pkg::*
        parse_export_package(),
        // Then constructor export: Con or Con(..)
        parse_export_constructor(),
        // Finally identifier export
        parse_export_identifier(),
    ))
    .labelled("export item")
}

/// Parse package export: Package::*
fn parse_export_package<'a>() -> impl Parser<'a, TokenStream<'a>, CExport, ParserExtra<'a>> + Clone {
    word()
        .map_with(|name, e| make_id(name, to_position(e.span())))
        .then_ignore(symbol(TokenKind::SymColonColon))
        .then_ignore(symbol(TokenKind::SymStar))
        .map(CExport::Package)
        .labelled("package export")
}

/// Parse constructor export: Con or Con(..)
fn parse_export_constructor<'a>() -> impl Parser<'a, TokenStream<'a>, CExport, ParserExtra<'a>> + Clone {
    // Constructor name (uppercase identifier)
    select! {
        TokenKind::Id(name) if name.chars().next().unwrap_or('a').is_ascii_uppercase() => name
    }
    .map_with(|name, e| make_id(name, to_position(e.span())))
    .then(
        // Optional (..) for all constructors
        symbol(TokenKind::SymLParen)
            .ignore_then(symbol(TokenKind::SymDotDot))
            .ignore_then(symbol(TokenKind::SymRParen))
            .to(true)
            .or_not(),
    )
    .map(|(name, all): (Id, Option<bool>)| {
        if all.unwrap_or(false) {
            CExport::ConAll(name)
        } else {
            CExport::Con(name)
        }
    })
    .labelled("constructor export")
}

/// Parse identifier export.
fn parse_export_identifier<'a>() -> impl Parser<'a, TokenStream<'a>, CExport, ParserExtra<'a>> + Clone {
    select! {
        TokenKind::Id(name) if name.chars().next().unwrap_or('A').is_ascii_lowercase() => name
    }
    .map_with(|name, e| make_id(name, to_position(e.span())))
    .map(CExport::Var)
    .labelled("identifier export")
}

/// Parse export statement: export item1, item2, ...;
fn parse_export<'a>() -> impl Parser<'a, TokenStream<'a>, Vec<CExport>, ParserExtra<'a>> + Clone {
    keyword(TokenKind::KwExport)
        .ignore_then(
            parse_export_item()
                .separated_by(comma())
                .at_least(1)
                .collect(),
        )
        .then_ignore(semicolon())
        .labelled("export statement")
}

// ============================================================================
// Import Parsing (mirrors pImportItem)
// ============================================================================

/// Parse a single import item: Package::*
fn parse_import_item<'a>() -> impl Parser<'a, TokenStream<'a>, Id, ParserExtra<'a>> + Clone {
    word()
        .map_with(|name, e| make_id(name, to_position(e.span())))
        .then_ignore(symbol(TokenKind::SymColonColon))
        .then_ignore(symbol(TokenKind::SymStar))
        .labelled("import item")
}

/// Parse import statement: import Package1::*, Package2::*, ...;
fn parse_import<'a>() -> impl Parser<'a, TokenStream<'a>, Vec<Id>, ParserExtra<'a>> + Clone {
    keyword(TokenKind::KwImport)
        .ignore_then(
            parse_import_item()
                .separated_by(comma())
                .at_least(1)
                .collect(),
        )
        .then_ignore(semicolon())
        .labelled("import statement")
}

// ============================================================================
// Package Declaration Parsing (mirrors pPackageDecl)
// ============================================================================

/// Parse package declaration: package Name;
fn parse_package_decl<'a>() -> impl Parser<'a, TokenStream<'a>, Id, ParserExtra<'a>> + Clone {
    keyword(TokenKind::KwPackage)
        .ignore_then(word().map_with(|name, e| make_id(name, to_position(e.span()))))
        .then_ignore(semicolon())
        .labelled("package declaration")
}

// ============================================================================
// Imperative Statement Conversion
// ============================================================================

/// Convert ImperativeStatement to CDefn (simplified for now).
/// This should call `imperativeToCDefns` from the Haskell implementation.
fn imperative_to_cdefns(_stmts: Vec<ImperativeStatement>) -> Vec<CDefn> {
    // TODO: Implement full conversion from ImperativeStatement to CDefn
    // For now, return empty list to allow compilation
    Vec::new()
}

/// Create default imperative flags for top-level parsing.
fn toplevel_flags() -> ImperativeFlags {
    ImperativeFlags {
        function_name_args: None,
        stmt_context: ImperativeStmtContext::ISCToplevel,
        filestr: None,
        ifc_type: None,
        end_keyword: None,
        allow_eq: true,
        allow_bind: false,
        allow_reg_write: false,
        allow_subscript_assign: false,
        allow_field_assign: false,
        allow_return: false,
        allow_naked_expr: false,
        allow_let: false,
        allow_function: true,
        allow_inst: false,
        allow_rule: false,
        allow_method: false,
        allow_subinterface: false,
        allow_conditionals: false,
        allow_loops: false,
        allow_module: true,
        allow_interface: true,
        allow_foreign: true,
        allow_typedef: true,
        allow_typeclass: true,
    }
}

// ============================================================================
// Main Package Parser (mirrors pPackage)
// ============================================================================

/// Parse a complete BSV package.
/// Mirrors `pPackage` from CVParser.lhs.
pub fn parse_package<'a>(
    default_pkg_name: String,
) -> impl Parser<'a, TokenStream<'a>, CPackage, ParserExtra<'a>> + Clone {
    // Optional package declaration
    parse_package_decl()
        .or_not()
        .then(
            // TODO: Parse imperative statements with toplevel flags
            // For now, parse basic import/export statements
            choice((
                parse_import().map(ImperativeStatement::Import),
                parse_export().map(ImperativeStatement::Export),
            ))
            .repeated()
            .collect::<Vec<_>>(),
        )
        .then_ignore(
            // Optional endpackage (only required if package was specified)
            keyword(TokenKind::KwEndpackage).or_not(),
        )
        .then_ignore(end())
        .map_with(move |(pkg_name, stmts): (Option<Id>, Vec<ImperativeStatement>), e| {
            let default_id = make_id(SmolStr::from(&default_pkg_name), to_position(e.span()));
            let name = pkg_name.unwrap_or(default_id);

            // Separate imports and exports
            let (import_stmts, non_import_stmts): (Vec<_>, Vec<_>) =
                stmts.into_iter().partition(is_is_import);
            let (export_stmts, remaining_stmts): (Vec<_>, Vec<_>) =
                non_import_stmts.into_iter().partition(is_is_export);

            // Extract import package names
            let import_pkgs: Vec<Id> = import_stmts
                .into_iter()
                .flat_map(|stmt| match stmt {
                    ImperativeStatement::Import(pkgs) => pkgs,
                    _ => Vec::new(),
                })
                .collect();

            // Check for self-imports (prohibited)
            let self_imports: Vec<_> = import_pkgs
                .iter()
                .filter(|pkg| pkg.name() == name.name())
                .collect();
            if !self_imports.is_empty() {
                // TODO: Report error for circular imports
                // For now, continue with parsing
            }

            // Create CImport list
            let imports: Vec<CImport> = import_pkgs
                .into_iter()
                .map(|pkg| CImport::Simple {
                    qualified: false,
                    module: pkg,
                    alias: None,
                    spec: None,
                    span: to_span(e.span()),
                })
                .collect();

            // Extract export items
            let exported_ids: Vec<CExport> = export_stmts
                .into_iter()
                .flat_map(|stmt| match stmt {
                    ImperativeStatement::Export(exports) => exports,
                    _ => Vec::new(),
                })
                .collect();

            // Create export spec
            let exports = if exported_ids.is_empty() {
                ExportSpec::Hiding(Vec::new()) // Export everything (Right [])
            } else {
                ExportSpec::Only(exported_ids) // Export only these (Left exports)
            };

            // Convert remaining statements to definitions
            let definitions = imperative_to_cdefns(remaining_stmts);

            CPackage {
                name,
                exports,
                imports,
                fixities: Vec::new(), // TODO: Parse fixity declarations
                definitions,
                includes: Vec::new(), // TODO: Parse include files
                span: to_span(e.span()),
            }
        })
        .labelled("package")
}

// ============================================================================
// Public API
// ============================================================================

/// Parse a BSV package from a token stream.
pub fn parse_bsv_package(
    tokens: Vec<(TokenKind, SimpleSpan<u32>)>,
    default_pkg_name: String,
) -> Result<CPackage, Vec<Rich<'static, TokenKind, SimpleSpan<u32>>>> {
    // For now, just return a simple empty package to resolve compilation
    // TODO: Implement proper parsing once the lifetime issues are resolved
    Ok(CPackage {
        name: Id::unpositioned(SmolStr::from(default_pkg_name)),
        exports: ExportSpec::Only(vec![]),
        imports: vec![],
        definitions: vec![],
        fixities: vec![],
        includes: vec![],
        span: Span::DUMMY,
    })
}

