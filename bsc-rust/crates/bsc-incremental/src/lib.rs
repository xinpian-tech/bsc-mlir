//! Incremental computation database using Salsa.
//!
//! This crate provides the core infrastructure for incremental compilation
//! in the BSC Rust frontend. It uses the Salsa framework to cache and
//! recompute results only when inputs change.
//!
//! # Architecture
//!
//! The database is structured around several key concepts:
//!
//! - **Inputs**: Source files and compiler flags that can change
//! - **Derived queries**: Computed values like tokens, ASTs, and type information
//! - **IDE queries**: Specialized queries for editor support (hover, completions)
//!
//! # Example
//!
//! ```ignore
//! use bsc_incremental::{CompilerDatabase, Database, SourceFile, CompilerFlags, SyntaxMode};
//!
//! let db = CompilerDatabase::default();
//! let file = SourceFile::new(&db, "test.bs".to_string(), "module Test where".to_string());
//! let flags = CompilerFlags::new(&db, SyntaxMode::Classic, vec![]);
//!
//! // Parse the file (result is cached)
//! let result = parse(&db, file);
//! ```

use std::sync::Arc;

use bsc_diagnostics::{Position, Span};
use bsc_lexer::{SyntaxMode, Token};
use bsc_syntax::CPackage;

// ============================================================================
// Input types
// ============================================================================

/// A source file in the compiler database.
///
/// This is a Salsa input, meaning it can be set and modified by the user.
/// Changes to source file contents will invalidate dependent queries.
#[salsa::input]
pub struct SourceFile {
    /// The file path (used as identifier).
    #[return_ref]
    pub path: String,

    /// The file contents.
    #[return_ref]
    pub contents: String,
}

/// Compiler flags and configuration.
///
/// This is a Salsa input that holds global compilation settings.
#[salsa::input]
pub struct CompilerFlags {
    /// The syntax mode (Classic or BSV).
    pub syntax_mode: SyntaxMode,

    /// Search paths for imports.
    #[return_ref]
    pub search_paths: Vec<String>,
}

// ============================================================================
// Diagnostic types
// ============================================================================

/// A diagnostic message from compilation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Diagnostic {
    /// The severity of the diagnostic.
    pub severity: DiagnosticSeverity,
    /// The diagnostic message.
    pub message: String,
    /// The source span where the diagnostic occurred.
    pub span: Span,
    /// Optional related information.
    pub related: Vec<RelatedInformation>,
}

/// Diagnostic severity levels.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiagnosticSeverity {
    /// An error that prevents compilation.
    Error,
    /// A warning that doesn't prevent compilation.
    Warning,
    /// Informational message.
    Info,
    /// A hint for the user.
    Hint,
}

/// Related information for a diagnostic.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RelatedInformation {
    /// The message for this related info.
    pub message: String,
    /// The span for this related info.
    pub span: Span,
}

// ============================================================================
// Type checking output types
// ============================================================================

/// A type-checked package.
///
/// This is a placeholder for the actual typed AST that would come from
/// the type checker. The full implementation would include typed expressions,
/// resolved names, and inferred types.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypedPackage {
    /// The package name.
    pub name: String,
    // TODO: Add typed definitions, type environment, etc.
}

// ============================================================================
// IDE support types
// ============================================================================

/// Information for hover tooltips.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HoverInfo {
    /// The content to display in the hover tooltip.
    pub contents: String,
    /// The span of the hovered element.
    pub range: Span,
}

/// A completion item for autocomplete.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompletionItem {
    /// The label shown in the completion list.
    pub label: String,
    /// The kind of completion (function, variable, type, etc.).
    pub kind: CompletionKind,
    /// Optional detail text shown alongside the label.
    pub detail: Option<String>,
    /// The text to insert when this completion is selected.
    pub insert_text: String,
}

/// The kind of a completion item.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompletionKind {
    /// A function or method.
    Function,
    /// A variable or parameter.
    Variable,
    /// A type.
    Type,
    /// A type class.
    Class,
    /// A module.
    Module,
    /// A keyword.
    Keyword,
    /// A constructor.
    Constructor,
    /// A field.
    Field,
}

// ============================================================================
// Derived queries
// ============================================================================

/// Lex a source file into tokens.
///
/// This query is cached and will only re-run when the file contents change.
#[salsa::tracked(no_eq)]
pub fn lex(db: &dyn Database, file: SourceFile) -> Arc<Vec<Token>> {
    let contents = file.contents(db);
    let flags = get_compiler_flags(db);
    let mode = flags.syntax_mode(db);

    let lexer = bsc_lexer::Lexer::new(contents, mode);
    match lexer.tokenize() {
        Ok(tokens) => Arc::new(tokens),
        Err(_) => Arc::new(Vec::new()), // Return empty on error for now
    }
}

/// Parse a source file into a concrete syntax tree.
///
/// This query depends on `lex` and will be re-run when tokens change.
#[salsa::tracked(no_eq)]
pub fn parse(db: &dyn Database, file: SourceFile) -> Result<Arc<CPackage>, Vec<Diagnostic>> {
    let _tokens = lex(db, file);

    // TODO: Implement actual parsing
    // For now, return an error indicating parsing is not yet implemented
    Err(vec![Diagnostic {
        severity: DiagnosticSeverity::Error,
        message: "Parsing not yet implemented".to_string(),
        span: Span::DUMMY,
        related: vec![],
    }])
}

/// Type-check a source file.
///
/// This query depends on `parse` and will be re-run when the AST changes.
#[salsa::tracked(no_eq)]
pub fn type_check(db: &dyn Database, file: SourceFile) -> Result<TypedPackage, Vec<Diagnostic>> {
    let parsed = parse(db, file);

    match parsed {
        Ok(_package) => {
            // TODO: Implement actual type checking
            Err(vec![Diagnostic {
                severity: DiagnosticSeverity::Error,
                message: "Type checking not yet implemented".to_string(),
                span: Span::DUMMY,
                related: vec![],
            }])
        }
        Err(errors) => Err(errors),
    }
}

// ============================================================================
// IDE queries
// ============================================================================

/// Get hover information at a position in a file.
///
/// Returns information about the symbol at the given position, if any.
#[salsa::tracked(no_eq)]
#[expect(unused_variables)]
pub fn hover_at(db: &dyn Database, file: SourceFile, pos: Position) -> Option<HoverInfo> {
    // TODO: Implement hover by:
    // 1. Finding the token at the position
    // 2. Looking up the symbol in the type environment
    // 3. Returning type information and documentation
    None
}

/// Get completions at a position in a file.
///
/// Returns a list of completion items appropriate for the given position.
#[salsa::tracked(no_eq)]
#[expect(unused_variables)]
pub fn completions_at(db: &dyn Database, file: SourceFile, pos: Position) -> Vec<CompletionItem> {
    // TODO: Implement completions by:
    // 1. Determining the completion context (expression, type, import, etc.)
    // 2. Gathering appropriate symbols from the scope
    // 3. Filtering and ranking by relevance
    Vec::new()
}

// ============================================================================
// Database trait and implementation
// ============================================================================

/// Helper to get compiler flags from the database.
///
/// This assumes there's a single global `CompilerFlags` instance.
/// In a real implementation, you might want to associate flags with files
/// or use a different approach.
fn get_compiler_flags(db: &dyn Database) -> CompilerFlags {
    // For now, create default flags
    // In practice, this would be set up when initializing the database
    CompilerFlags::new(db, SyntaxMode::Classic, Vec::new())
}

/// The main database trait for incremental compilation.
///
/// This trait combines all the query groups needed for compilation.
/// Implementations of this trait provide storage for cached query results.
#[salsa::db]
pub trait Database: salsa::Database {}

/// The concrete database implementation.
///
/// This struct holds the Salsa storage and can be used directly for compilation.
#[salsa::db]
#[derive(Default, Clone)]
pub struct CompilerDatabase {
    storage: salsa::Storage<Self>,
}

impl CompilerDatabase {
    /// Create a new compiler database.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }
}

#[salsa::db]
impl salsa::Database for CompilerDatabase {
    fn salsa_event(&self, _event: &dyn Fn() -> salsa::Event) {
        // Optional: log or handle Salsa events for debugging
    }
}

#[salsa::db]
impl Database for CompilerDatabase {}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_create_database() {
        let _db = CompilerDatabase::new();
    }

    #[test]
    fn test_create_source_file() {
        let db = CompilerDatabase::new();
        let file = SourceFile::new(&db, "test.bs".to_string(), "module Test where".to_string());

        assert_eq!(file.path(&db), "test.bs");
        assert_eq!(file.contents(&db), "module Test where");
    }

    #[test]
    fn test_create_compiler_flags() {
        let db = CompilerDatabase::new();
        let flags = CompilerFlags::new(&db, SyntaxMode::Classic, vec!["lib".to_string()]);

        assert_eq!(flags.syntax_mode(&db), SyntaxMode::Classic);
        assert_eq!(flags.search_paths(&db), &["lib".to_string()]);
    }

    #[test]
    fn test_lex_empty_file() {
        let db = CompilerDatabase::new();
        let file = SourceFile::new(&db, "test.bs".to_string(), String::new());

        let tokens = lex(&db, file);
        // Empty file should produce just EOF token
        assert_eq!(tokens.len(), 1);
    }

    #[test]
    fn test_lex_simple_file() {
        let db = CompilerDatabase::new();
        let file = SourceFile::new(&db, "test.bs".to_string(), "if then else".to_string());

        let tokens = lex(&db, file);
        // Should have: if, then, else, EOF
        assert_eq!(tokens.len(), 4);
    }

    #[test]
    fn test_diagnostic_creation() {
        let diag = Diagnostic {
            severity: DiagnosticSeverity::Error,
            message: "Test error".to_string(),
            span: Span::new(0, 10),
            related: vec![],
        };

        assert_eq!(diag.severity, DiagnosticSeverity::Error);
        assert_eq!(diag.message, "Test error");
    }

    #[test]
    fn test_hover_info_creation() {
        let hover = HoverInfo {
            contents: "fn test() -> Int".to_string(),
            range: Span::new(0, 4),
        };

        assert_eq!(hover.contents, "fn test() -> Int");
    }

    #[test]
    fn test_completion_item_creation() {
        let item = CompletionItem {
            label: "myFunction".to_string(),
            kind: CompletionKind::Function,
            detail: Some("Int -> Int".to_string()),
            insert_text: "myFunction".to_string(),
        };

        assert_eq!(item.label, "myFunction");
        assert_eq!(item.kind, CompletionKind::Function);
    }
}
