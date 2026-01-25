//! Error handling and diagnostics for the BSC Rust frontend.
//!
//! This crate provides:
//! - Source location tracking (`Span`, `Position`)
//! - Diagnostic types for errors and warnings
//! - Rich error context following the "no silent failures" principle

use miette::{Diagnostic, SourceSpan};
use std::fmt;
use std::sync::Arc;
use thiserror::Error;

/// A file identifier for tracking source files.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct FileId(pub u32);

impl FileId {
    /// The dummy/unknown file ID.
    pub const DUMMY: Self = Self(0);

    /// Check if this is a valid (non-dummy) file ID.
    #[must_use]
    pub const fn is_valid(&self) -> bool {
        self.0 > 0
    }
}

/// A position in source code (file, line, column, stdlib flag).
///
/// Mirrors the Haskell Position type from BSC exactly:
/// ```haskell
/// data Position = Position {
///     pos_file :: !FString,
///     pos_line :: !Int,
///     pos_column :: !Int,
///     pos_is_stdlib :: !Bool
/// }
/// ```
///
/// The filename is stored directly (as Arc<str>) rather than using FileId lookup,
/// following rule 8 in CLAUDE.md: "FOLLOW HASKELL'S DATA STRUCTURES EXACTLY".
#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Position {
    /// Filename (stored directly like Haskell's FString)
    #[cfg_attr(feature = "serde", serde(with = "arc_str_serde"))]
    pub file: Arc<str>,
    /// Line number (1-indexed, -1 for unknown, -2 for command line)
    pub line: i32,
    /// Column number (1-indexed, -1 for unknown)
    pub column: i32,
    /// Whether this position is from the standard library (Prelude)
    pub is_stdlib: bool,
}

#[cfg(feature = "serde")]
mod arc_str_serde {
    use serde::{Deserialize, Deserializer, Serialize, Serializer};
    use std::sync::Arc;

    pub fn serialize<S: Serializer>(value: &Arc<str>, serializer: S) -> Result<S::Ok, S::Error> {
        value.as_ref().serialize(serializer)
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(deserializer: D) -> Result<Arc<str>, D::Error> {
        let s = String::deserialize(deserializer)?;
        Ok(Arc::from(s))
    }
}

impl Position {
    /// Create a new position with file, line, and column.
    #[must_use]
    pub fn new(file: impl Into<Arc<str>>, line: i32, column: i32) -> Self {
        Self {
            file: file.into(),
            line,
            column,
            is_stdlib: false,
        }
    }

    /// Create a position with just line and column (empty filename).
    #[must_use]
    pub fn line_col(line: i32, column: i32) -> Self {
        Self {
            file: Arc::from(""),
            line,
            column,
            is_stdlib: false,
        }
    }

    /// Create a full position with all fields (mirrors Haskell's mkPositionFull).
    #[must_use]
    pub fn full(file: impl Into<Arc<str>>, line: i32, column: i32, is_stdlib: bool) -> Self {
        Self {
            file: file.into(),
            line,
            column,
            is_stdlib,
        }
    }

    /// The unknown/invalid position.
    pub fn unknown() -> Self {
        Self {
            file: Arc::from(""),
            line: -1,
            column: -1,
            is_stdlib: false,
        }
    }

    /// Command line position (special case in Haskell).
    pub fn command_line() -> Self {
        Self {
            file: Arc::from(""),
            line: -2,
            column: -1,
            is_stdlib: false,
        }
    }

    /// Check if this is a valid position.
    #[must_use]
    pub fn is_valid(&self) -> bool {
        self.line > 0 && self.column > 0
    }

    /// Check if this position is from the standard library (Prelude).
    #[must_use]
    pub fn is_prelude(&self) -> bool {
        self.is_stdlib
    }

    /// Set the stdlib flag.
    #[must_use]
    pub fn with_stdlib(mut self, is_stdlib: bool) -> Self {
        self.is_stdlib = is_stdlib;
        self
    }

    /// Choose the best position between two (prefer valid positions).
    #[must_use]
    pub fn best(self, other: Self) -> Self {
        if self.is_valid() {
            self
        } else {
            other
        }
    }
}

/// Trait for types that have an associated source position.
///
/// This mirrors the Haskell HasPosition class.
pub trait HasPosition {
    /// Get the position of this value.
    fn get_position(&self) -> Position;
}

impl HasPosition for Position {
    fn get_position(&self) -> Position {
        self.clone()
    }
}

impl<T: HasPosition> HasPosition for Option<T> {
    fn get_position(&self) -> Position {
        match self {
            Some(x) => x.get_position(),
            None => Position::unknown(),
        }
    }
}

impl<T: HasPosition> HasPosition for Vec<T> {
    fn get_position(&self) -> Position {
        self.iter().fold(Position::unknown(), |acc, x| {
            acc.best(x.get_position())
        })
    }
}

impl<T: HasPosition> HasPosition for Box<T> {
    fn get_position(&self) -> Position {
        (**self).get_position()
    }
}

impl<A: HasPosition, B: HasPosition> HasPosition for (A, B) {
    fn get_position(&self) -> Position {
        self.0.get_position().best(self.1.get_position())
    }
}

impl<A: HasPosition, B: HasPosition, C: HasPosition> HasPosition for (A, B, C) {
    fn get_position(&self) -> Position {
        self.0
            .get_position()
            .best(self.1.get_position())
            .best(self.2.get_position())
    }
}

/// Display for Position exactly matches Haskell's prPosition:
/// ```haskell
/// prPosition :: Position -> String
/// prPosition (Position fs l c pred) =
///     let f = getFString fs
///         f' = getRelativeFilePath f
///     in
///     if l==(-2) && c<0 && f=="" then "Command line" else
///     if l<0 && c<0 && f=="" then "Unknown position" else
///     let lc = if l<0 then "" else "line " ++ show3 l ++ (if c < 0 then "" else ", column "++show3 c)
///         show3 = show
///     in case f of
///         "" -> lc
///         _ -> show f' ++ (if null lc then "" else ", "++lc)
/// ```
impl fmt::Display for Position {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let file = &*self.file;
        let line = self.line;
        let col = self.column;

        if line == -2 && col < 0 && file.is_empty() {
            write!(f, "Command line")
        } else if line < 0 && col < 0 && file.is_empty() {
            write!(f, "Unknown position")
        } else {
            let lc = if line < 0 {
                String::new()
            } else if col < 0 {
                format!("line {}", line)
            } else {
                format!("line {}, column {}", line, col)
            };

            if file.is_empty() {
                write!(f, "{}", lc)
            } else if lc.is_empty() {
                write!(f, "{:?}", file)
            } else {
                write!(f, "{:?}, {}", file, lc)
            }
        }
    }
}

/// A span in source code (start and end byte offsets).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Span {
    /// Start byte offset (inclusive)
    pub start: u32,
    /// End byte offset (exclusive)
    pub end: u32,
}

impl Span {
    /// Create a new span.
    #[must_use]
    pub const fn new(start: u32, end: u32) -> Self {
        Self { start, end }
    }

    /// The empty/unknown span.
    pub const DUMMY: Self = Self { start: 0, end: 0 };

    /// Check if this span is empty.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.start == self.end
    }

    /// Get the length of this span in bytes.
    #[must_use]
    pub const fn len(&self) -> u32 {
        self.end.saturating_sub(self.start)
    }

    /// Combine two spans into one that covers both.
    #[must_use]
    pub const fn merge(self, other: Self) -> Self {
        let start = if self.start < other.start {
            self.start
        } else {
            other.start
        };
        let end = if self.end > other.end {
            self.end
        } else {
            other.end
        };
        Self { start, end }
    }

    /// Convert to miette's `SourceSpan`.
    #[must_use]
    pub fn to_source_span(self) -> SourceSpan {
        SourceSpan::new(
            miette::SourceOffset::from(self.start as usize),
            self.len() as usize,
        )
    }

    /// Convert a byte offset span to Position using source text.
    /// This computes line/column from byte offset.
    #[must_use]
    pub fn to_position(&self, source: &str, filename: &Arc<str>) -> Position {
        let mut line = 1i32;
        let mut col = 1i32;
        let mut current_offset = 0usize;

        for ch in source.chars() {
            if current_offset >= self.start as usize {
                break;
            }
            if ch == '\n' {
                line += 1;
                col = 1;
            } else {
                col += 1;
            }
            current_offset += ch.len_utf8();
        }

        Position::new(filename.clone(), line, col)
    }
}

impl From<Span> for SourceSpan {
    fn from(span: Span) -> Self {
        span.to_source_span()
    }
}

/// A located value - pairs a value with its source span.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Spanned<T> {
    pub node: T,
    pub span: Span,
}

impl<T> Spanned<T> {
    /// Create a new spanned value.
    pub const fn new(node: T, span: Span) -> Self {
        Self { node, span }
    }

    /// Map over the inner value.
    pub fn map<U, F: FnOnce(T) -> U>(self, f: F) -> Spanned<U> {
        Spanned {
            node: f(self.node),
            span: self.span,
        }
    }
}

/// Severity level for diagnostics.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Severity {
    Error,
    Warning,
    Info,
    Hint,
}

/// Base error type for lexer errors.
#[derive(Debug, Error, Diagnostic)]
pub enum LexError {
    #[error("unexpected character '{char}' at position {position}")]
    UnexpectedChar {
        char: char,
        position: Position,
        #[label("unexpected character here")]
        span: SourceSpan,
    },

    #[error("unterminated string literal starting at {position}")]
    UnterminatedString {
        position: Position,
        #[label("string starts here")]
        span: SourceSpan,
    },

    #[error("unterminated block comment starting at {position}")]
    UnterminatedBlockComment {
        position: Position,
        #[label("comment starts here")]
        span: SourceSpan,
    },

    #[error("invalid escape sequence '\\{sequence}' in string at {position}")]
    InvalidEscape {
        sequence: String,
        position: Position,
        #[label("invalid escape here")]
        span: SourceSpan,
    },

    #[error("invalid integer literal '{literal}' at {position}: {reason}")]
    InvalidInteger {
        literal: String,
        position: Position,
        reason: String,
        #[label("invalid integer here")]
        span: SourceSpan,
    },

    #[error("invalid sized literal '{literal}' at {position}: {reason}")]
    InvalidSizedLiteral {
        literal: String,
        position: Position,
        reason: String,
        #[label("invalid literal here")]
        span: SourceSpan,
    },

    #[error("C preprocessor directive at {position} - should be preprocessed first")]
    CppDirective {
        directive: String,
        position: Position,
        #[label("CPP directive here")]
        span: SourceSpan,
    },
}

/// Base error type for parser errors.
#[derive(Debug, Error, Diagnostic)]
pub enum ParseError {
    #[error("unexpected token: expected {expected}, found {found}")]
    UnexpectedToken {
        expected: String,
        found: String,
        #[label("unexpected token here")]
        span: SourceSpan,
    },

    #[error("unexpected end of file: expected {expected}")]
    UnexpectedEof {
        expected: String,
        #[label("file ends here")]
        span: SourceSpan,
    },

    #[error("invalid syntax: {message}")]
    InvalidSyntax {
        message: String,
        #[label("{message}")]
        span: SourceSpan,
    },

    #[error("duplicate definition of '{name}'")]
    DuplicateDefinition {
        name: String,
        #[label("duplicate definition here")]
        span: SourceSpan,
        #[label("first defined here")]
        first_span: SourceSpan,
    },
}

/// Base error type for type checking errors.
#[derive(Debug, Error, Diagnostic)]
pub enum TypeError {
    #[error("type mismatch: expected {expected}, found {found}")]
    TypeMismatch {
        expected: String,
        found: String,
        #[label("expected {expected}")]
        span: SourceSpan,
    },

    #[error("undefined variable '{name}'")]
    UndefinedVar {
        name: String,
        #[label("undefined variable")]
        span: SourceSpan,
    },

    #[error("undefined type '{name}'")]
    UndefinedType {
        name: String,
        #[label("undefined type")]
        span: SourceSpan,
    },

    #[error("undefined type class '{name}'")]
    UndefinedClass {
        name: String,
        #[label("undefined type class")]
        span: SourceSpan,
    },

    #[error("kind mismatch: expected {expected}, found {found}")]
    KindMismatch {
        expected: String,
        found: String,
        #[label("kind mismatch")]
        span: SourceSpan,
    },

    #[error("occurs check failed: cannot construct infinite type {var} ~ {ty}")]
    OccursCheck {
        var: String,
        ty: String,
        #[label("recursive type here")]
        span: SourceSpan,
    },

    #[error("ambiguous type variable '{var}' in context")]
    AmbiguousType {
        var: String,
        #[label("ambiguous type")]
        span: SourceSpan,
    },

    #[error("no instance of class '{class}' for type '{ty}'")]
    NoInstance {
        class: String,
        ty: String,
        #[label("no instance")]
        span: SourceSpan,
    },

    #[error("cannot unify numeric types: {t1} and {t2}")]
    NumericUnification {
        t1: String,
        t2: String,
        #[label("numeric type mismatch")]
        span: SourceSpan,
    },
}

/// Collector for diagnostics during compilation.
#[derive(Debug, Default)]
pub struct DiagnosticCollector {
    errors: Vec<Box<dyn Diagnostic + Send + Sync>>,
    warnings: Vec<Box<dyn Diagnostic + Send + Sync>>,
}

impl DiagnosticCollector {
    /// Create a new empty collector.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Add an error diagnostic.
    pub fn error(&mut self, diagnostic: impl Diagnostic + Send + Sync + 'static) {
        self.errors.push(Box::new(diagnostic));
    }

    /// Add a warning diagnostic.
    pub fn warning(&mut self, diagnostic: impl Diagnostic + Send + Sync + 'static) {
        self.warnings.push(Box::new(diagnostic));
    }

    /// Check if there are any errors.
    #[must_use]
    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }

    /// Get the number of errors.
    #[must_use]
    pub fn error_count(&self) -> usize {
        self.errors.len()
    }

    /// Get the number of warnings.
    #[must_use]
    pub fn warning_count(&self) -> usize {
        self.warnings.len()
    }

    /// Consume and return all errors.
    pub fn take_errors(&mut self) -> Vec<Box<dyn Diagnostic + Send + Sync>> {
        std::mem::take(&mut self.errors)
    }

    /// Consume and return all warnings.
    pub fn take_warnings(&mut self) -> Vec<Box<dyn Diagnostic + Send + Sync>> {
        std::mem::take(&mut self.warnings)
    }
}
