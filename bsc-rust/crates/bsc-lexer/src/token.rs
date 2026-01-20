//! Token types for the BSC lexer.
//!
//! Mirrors `LexItem` from `src/comp/Lex.hs` in the Haskell implementation.
//!
//! In Haskell: `data Token = Token Position LexItem`

use bsc_diagnostics::{Position, Span};
use bsc_syntax::literal::OrderedFloat;
use num_bigint::BigInt;
use smol_str::SmolStr;

/// A token with its kind and position.
///
/// Mirrors Haskell's `Token Position LexItem`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    /// The kind of token (LexItem)
    pub kind: TokenKind,
    /// Source span (byte offsets)
    pub span: Span,
    /// Position (file, line, column) - matches Haskell's Token Position
    pub position: Position,
}

impl Token {
    /// Create a new token with full position.
    #[must_use]
    pub fn new(kind: TokenKind, span: Span, position: Position) -> Self {
        Self { kind, span, position }
    }

    /// Check if this is an end-of-file token.
    #[must_use]
    pub fn is_eof(&self) -> bool {
        matches!(self.kind, TokenKind::Eof)
    }
}

impl std::hash::Hash for Token {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.kind.hash(state);
        self.span.hash(state);
    }
}

/// The kind of a token.
///
/// Mirrors `LexItem` from Haskell BSC's `src/comp/Lex.hs`.
/// Each variant is documented with its Haskell equivalent.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokenKind {
    // ========================================================================
    // Identifiers (L_varid, L_conid, L_varsym, L_consym)
    // ========================================================================

    /// Lowercase identifier (variable): `L_varid FString`
    VarId(SmolStr),
    /// Uppercase identifier (constructor/type): `L_conid FString`
    ConId(SmolStr),
    /// Lowercase symbol operator: `L_varsym FString`
    VarSym(SmolStr),
    /// Uppercase symbol operator (starting with :): `L_consym FString`
    ConSym(SmolStr),

    // ========================================================================
    // Literals (L_integer, L_float, L_char, L_string)
    // ========================================================================

    /// Integer literal: `L_integer (Maybe Integer) Integer Integer`
    /// Fields: (bit size if specified, base, value)
    /// Uses BigInt to match Haskell's arbitrary precision Integer.
    Integer {
        /// Bit size if specified (e.g., 8 for 8'hFF), None for unsized
        size: Option<BigInt>,
        /// Base (2, 8, 10, or 16)
        base: u32,
        /// Value
        value: BigInt,
    },
    /// Floating point literal: `L_float Rational`
    Float(OrderedFloat),
    /// Character literal: `L_char Char`
    Char(char),
    /// String literal: `L_string String`
    String(String),

    // ========================================================================
    // Delimiters (L_lpar, L_rpar, L_semi, L_uscore, L_bquote, etc.)
    // ========================================================================

    /// `(` : `L_lpar`
    LParen,
    /// `)` : `L_rpar`
    RParen,
    /// `;` : `L_semi`
    Semi,
    /// `_` : `L_uscore`
    Underscore,
    /// ``` ` ``` : `L_bquote`
    Backtick,
    /// `{` : `L_lcurl`
    LBrace,
    /// `}` : `L_rcurl`
    RBrace,
    /// `[` : `L_lbra`
    LBracket,
    /// `]` : `L_rbra`
    RBracket,
    /// `.` : `L_dot`
    Dot,
    /// `,` : `L_comma`
    Comma,

    // ========================================================================
    // Reserved words (from Haskell BSC Lex.hs lines 54-61)
    // ========================================================================

    /// `action` : `L_action`
    KwAction,
    /// `case` : `L_case`
    KwCase,
    /// `class` : `L_class`
    KwClass,
    /// `data` : `L_data`
    KwData,
    /// `deriving` : `L_deriving`
    KwDeriving,
    /// `do` : `L_do`
    KwDo,
    /// `else` : `L_else`
    KwElse,
    /// `foreign` : `L_foreign`
    KwForeign,
    /// `if` : `L_if`
    KwIf,
    /// `import` : `L_import`
    KwImport,
    /// `in` : `L_in`
    KwIn,
    /// `infix` : `L_infix`
    KwInfix,
    /// `infixl` : `L_infixl`
    KwInfixL,
    /// `infixr` : `L_infixr`
    KwInfixR,
    /// `interface` : `L_interface`
    KwInterface,
    /// `instance` : `L_instance`
    KwInstance,
    /// `let` : `L_let`
    KwLet,
    /// `letseq` : `L_letseq`
    KwLetSeq,
    /// `package` : `L_package`
    KwPackage,
    /// `of` : `L_of`
    KwOf,
    /// `primitive` : `L_primitive`
    KwPrimitive,
    /// `qualified` : `L_qualified`
    KwQualified,
    /// `rules` : `L_rules`
    KwRules,
    /// `signature` : `L_signature`
    KwSignature,
    /// `struct` : `L_struct`
    KwStruct,
    /// `then` : `L_then`
    KwThen,
    /// `module` : `L_module`
    KwModule,
    /// `type` : `L_type`
    KwType,
    /// `valueOf` : `L_valueOf`
    KwValueOf,
    /// `stringOf` : `L_stringOf`
    KwStringOf,
    /// `verilog` : `L_verilog`
    KwVerilog,
    /// `synthesize` : `L_synthesize`
    KwSynthesize,
    /// `when` : `L_when`
    KwWhen,
    /// `where` : `L_where`
    KwWhere,
    /// `coherent` : `L_coherent`
    KwCoherent,
    /// `incoherent` : `L_incoherent`
    KwIncoherent,

    // ========================================================================
    // BSV-specific keywords (not in Classic, but in BSV syntax mode)
    // ========================================================================

    /// `actionvalue` (BSV)
    KwActionValue,
    /// `export` (BSV)
    KwExport,
    /// `for` (BSV)
    KwFor,
    /// `function` (BSV)
    KwFunction,
    /// `match` (BSV)
    KwMatch,
    /// `matches` (BSV)
    KwMatches,
    /// `method` (BSV)
    KwMethod,
    /// `return` (BSV)
    KwReturn,
    /// `rule` (BSV)
    KwRule,
    /// `while` (BSV)
    KwWhile,

    // ========================================================================
    // Reserved operators (L_dcolon, L_colon, L_eq, etc.)
    // ========================================================================

    /// `::` : `L_dcolon`
    ColonColon,
    /// `:` : `L_colon`
    Colon,
    /// `=` : `L_eq`
    Equals,
    /// `@` : `L_at`
    At,
    /// `\` : `L_lam`
    Backslash,
    /// `|` : `L_bar`
    Bar,
    /// `->` : `L_rarrow`
    Arrow,
    /// `<-` : `L_larrow`
    LArrow,
    /// `==>` : `L_drarrow`
    DArrow,
    /// `=>` : `L_irarrow`
    FatArrow,

    // ========================================================================
    // Additional operators/punctuation
    // ========================================================================

    /// `..`
    DotDot,
    /// `#`
    Hash,
    /// `$`
    Dollar,
    /// `?`
    Question,

    // ========================================================================
    // Layout tokens (L_lcurl_o, L_rcurl_o, L_semi_o)
    // ========================================================================

    /// Implicit opening brace from layout: `L_lcurl_o`
    LayoutLBrace,
    /// Implicit closing brace from layout: `L_rcurl_o`
    LayoutRBrace,
    /// Implicit semicolon from layout: `L_semi_o`
    LayoutSemi,

    // ========================================================================
    // Pragmas (L_lpragma, L_rpragma)
    // ========================================================================

    /// `{-#` : `L_lpragma`
    LPragma,
    /// `#-}` : `L_rpragma`
    RPragma,

    // ========================================================================
    // Special (L_eof)
    // ========================================================================

    /// End of file: `L_eof`
    Eof,
}

impl TokenKind {
    /// Get a human-readable name for this token kind.
    #[must_use]
    pub fn name(&self) -> &'static str {
        match self {
            // Identifiers
            TokenKind::VarId(_) => "identifier",
            TokenKind::ConId(_) => "constructor",
            TokenKind::VarSym(_) => "operator",
            TokenKind::ConSym(_) => "constructor operator",

            // Literals
            TokenKind::Integer { .. } => "integer",
            TokenKind::Float(_) => "float",
            TokenKind::Char(_) => "character",
            TokenKind::String(_) => "string",

            // Delimiters
            TokenKind::LParen => "(",
            TokenKind::RParen => ")",
            TokenKind::Semi => ";",
            TokenKind::Underscore => "_",
            TokenKind::Backtick => "`",
            TokenKind::LBrace => "{",
            TokenKind::RBrace => "}",
            TokenKind::LBracket => "[",
            TokenKind::RBracket => "]",
            TokenKind::Dot => ".",
            TokenKind::Comma => ",",

            // Reserved words
            TokenKind::KwAction => "action",
            TokenKind::KwCase => "case",
            TokenKind::KwClass => "class",
            TokenKind::KwData => "data",
            TokenKind::KwDeriving => "deriving",
            TokenKind::KwDo => "do",
            TokenKind::KwElse => "else",
            TokenKind::KwForeign => "foreign",
            TokenKind::KwIf => "if",
            TokenKind::KwImport => "import",
            TokenKind::KwIn => "in",
            TokenKind::KwInfix => "infix",
            TokenKind::KwInfixL => "infixl",
            TokenKind::KwInfixR => "infixr",
            TokenKind::KwInterface => "interface",
            TokenKind::KwInstance => "instance",
            TokenKind::KwLet => "let",
            TokenKind::KwLetSeq => "letseq",
            TokenKind::KwPackage => "package",
            TokenKind::KwOf => "of",
            TokenKind::KwPrimitive => "primitive",
            TokenKind::KwQualified => "qualified",
            TokenKind::KwRules => "rules",
            TokenKind::KwSignature => "signature",
            TokenKind::KwStruct => "struct",
            TokenKind::KwThen => "then",
            TokenKind::KwModule => "module",
            TokenKind::KwType => "type",
            TokenKind::KwValueOf => "valueOf",
            TokenKind::KwStringOf => "stringOf",
            TokenKind::KwVerilog => "verilog",
            TokenKind::KwSynthesize => "synthesize",
            TokenKind::KwWhen => "when",
            TokenKind::KwWhere => "where",
            TokenKind::KwCoherent => "coherent",
            TokenKind::KwIncoherent => "incoherent",

            // BSV keywords
            TokenKind::KwActionValue => "actionvalue",
            TokenKind::KwExport => "export",
            TokenKind::KwFor => "for",
            TokenKind::KwFunction => "function",
            TokenKind::KwMatch => "match",
            TokenKind::KwMatches => "matches",
            TokenKind::KwMethod => "method",
            TokenKind::KwReturn => "return",
            TokenKind::KwRule => "rule",
            TokenKind::KwWhile => "while",

            // Reserved operators
            TokenKind::ColonColon => "::",
            TokenKind::Colon => ":",
            TokenKind::Equals => "=",
            TokenKind::At => "@",
            TokenKind::Backslash => "\\",
            TokenKind::Bar => "|",
            TokenKind::Arrow => "->",
            TokenKind::LArrow => "<-",
            TokenKind::DArrow => "==>",
            TokenKind::FatArrow => "=>",

            // Additional operators
            TokenKind::DotDot => "..",
            TokenKind::Hash => "#",
            TokenKind::Dollar => "$",
            TokenKind::Question => "?",

            // Layout tokens
            TokenKind::LayoutLBrace => "{ (layout)",
            TokenKind::LayoutRBrace => "} (layout)",
            TokenKind::LayoutSemi => "; (layout)",

            // Pragmas
            TokenKind::LPragma => "{-#",
            TokenKind::RPragma => "#-}",

            // Special
            TokenKind::Eof => "end of file",
        }
    }

    /// Check if this token is a keyword.
    #[must_use]
    pub fn is_keyword(&self) -> bool {
        matches!(
            self,
            TokenKind::KwAction
                | TokenKind::KwCase
                | TokenKind::KwClass
                | TokenKind::KwData
                | TokenKind::KwDeriving
                | TokenKind::KwDo
                | TokenKind::KwElse
                | TokenKind::KwForeign
                | TokenKind::KwIf
                | TokenKind::KwImport
                | TokenKind::KwIn
                | TokenKind::KwInfix
                | TokenKind::KwInfixL
                | TokenKind::KwInfixR
                | TokenKind::KwInterface
                | TokenKind::KwInstance
                | TokenKind::KwLet
                | TokenKind::KwLetSeq
                | TokenKind::KwPackage
                | TokenKind::KwOf
                | TokenKind::KwPrimitive
                | TokenKind::KwQualified
                | TokenKind::KwRules
                | TokenKind::KwSignature
                | TokenKind::KwStruct
                | TokenKind::KwThen
                | TokenKind::KwModule
                | TokenKind::KwType
                | TokenKind::KwValueOf
                | TokenKind::KwStringOf
                | TokenKind::KwVerilog
                | TokenKind::KwSynthesize
                | TokenKind::KwWhen
                | TokenKind::KwWhere
                | TokenKind::KwCoherent
                | TokenKind::KwIncoherent
                | TokenKind::KwActionValue
                | TokenKind::KwExport
                | TokenKind::KwFor
                | TokenKind::KwFunction
                | TokenKind::KwMatch
                | TokenKind::KwMatches
                | TokenKind::KwMethod
                | TokenKind::KwReturn
                | TokenKind::KwRule
                | TokenKind::KwWhile
        )
    }

    /// Check if this token is a layout token.
    #[must_use]
    pub fn is_layout(&self) -> bool {
        matches!(
            self,
            TokenKind::LayoutLBrace | TokenKind::LayoutRBrace | TokenKind::LayoutSemi
        )
    }

    /// Check if this token is a delimiter that can start a block.
    #[must_use]
    pub fn is_block_starter(&self) -> bool {
        matches!(
            self,
            TokenKind::KwLet
                | TokenKind::KwLetSeq
                | TokenKind::KwWhere
                | TokenKind::KwOf
                | TokenKind::KwDo
        )
    }
}

/// Manual Hash implementation for TokenKind.
/// BigInt doesn't implement Hash, so we use its signed bytes representation.
impl std::hash::Hash for TokenKind {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        // Hash a discriminant for each variant
        std::mem::discriminant(self).hash(state);

        match self {
            TokenKind::VarId(s) => s.hash(state),
            TokenKind::ConId(s) => s.hash(state),
            TokenKind::VarSym(s) => s.hash(state),
            TokenKind::ConSym(s) => s.hash(state),
            TokenKind::Integer { size, base, value } => {
                // Hash size if present
                if let Some(sz) = size {
                    true.hash(state);
                    sz.to_signed_bytes_le().hash(state);
                } else {
                    false.hash(state);
                }
                base.hash(state);
                value.to_signed_bytes_le().hash(state);
            }
            TokenKind::Float(f) => f.hash(state),
            TokenKind::Char(c) => c.hash(state),
            TokenKind::String(s) => s.hash(state),
            // Unit variants don't need additional hashing beyond discriminant
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_token_name() {
        assert_eq!(TokenKind::KwIf.name(), "if");
        assert_eq!(TokenKind::Arrow.name(), "->");
        assert_eq!(TokenKind::LPragma.name(), "{-#");
    }

    #[test]
    fn test_is_keyword() {
        assert!(TokenKind::KwIf.is_keyword());
        assert!(TokenKind::KwSignature.is_keyword());
        assert!(TokenKind::KwCoherent.is_keyword());
        assert!(!TokenKind::Arrow.is_keyword());
    }

    #[test]
    fn test_is_layout() {
        assert!(TokenKind::LayoutLBrace.is_layout());
        assert!(TokenKind::LayoutSemi.is_layout());
        assert!(!TokenKind::LBrace.is_layout());
    }
}
