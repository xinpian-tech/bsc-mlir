//! Token types for the Classic Bluespec lexer.
//!
//! Mirrors `LexItem` from `src/comp/Lex.hs` in the Haskell implementation.
//!
//! In Haskell: `data Token = Token Position LexItem`

use bsc_diagnostics::{Position, Span};
use bsc_syntax::literal::OrderedFloat;
use num_bigint::BigInt;
use smol_str::SmolStr;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
    pub position: Position,
}

impl Token {
    #[must_use]
    pub fn new(kind: TokenKind, span: Span, position: Position) -> Self {
        Self { kind, span, position }
    }

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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokenKind {
    VarId(SmolStr),
    ConId(SmolStr),
    VarSym(SmolStr),
    ConSym(SmolStr),

    Integer {
        size: Option<BigInt>,
        base: u32,
        value: BigInt,
    },
    Float(OrderedFloat),
    Char(char),
    String(String),

    LParen,
    RParen,
    Semi,
    Underscore,
    Backtick,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    Dot,
    Comma,

    KwAction,
    KwCase,
    KwClass,
    KwData,
    KwDeriving,
    KwDo,
    KwElse,
    KwForeign,
    KwIf,
    KwImport,
    KwIn,
    KwInfix,
    KwInfixL,
    KwInfixR,
    KwInterface,
    KwInstance,
    KwLet,
    KwLetSeq,
    KwPackage,
    KwOf,
    KwPrimitive,
    KwQualified,
    KwRules,
    KwSignature,
    KwStruct,
    KwThen,
    KwModule,
    KwType,
    KwValueOf,
    KwStringOf,
    KwVerilog,
    KwSynthesize,
    KwWhen,
    KwWhere,
    KwCoherent,
    KwIncoherent,

    ColonColon,
    Colon,
    Equals,
    At,
    Backslash,
    Arrow,
    LArrow,
    DArrow,
    FatArrow,

    LayoutLBrace,
    LayoutRBrace,
    LayoutSemi,

    LPragma,
    RPragma,

    Eof,
}

impl TokenKind {
    #[must_use]
    pub fn name(&self) -> &'static str {
        match self {
            TokenKind::VarId(_) => "identifier",
            TokenKind::ConId(_) => "constructor",
            TokenKind::VarSym(_) => "operator",
            TokenKind::ConSym(_) => "constructor operator",

            TokenKind::Integer { .. } => "integer",
            TokenKind::Float(_) => "float",
            TokenKind::Char(_) => "character",
            TokenKind::String(_) => "string",

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

            TokenKind::ColonColon => "::",
            TokenKind::Colon => ":",
            TokenKind::Equals => "=",
            TokenKind::At => "@",
            TokenKind::Backslash => "\\",
            TokenKind::Arrow => "->",
            TokenKind::LArrow => "<-",
            TokenKind::DArrow => "==>",
            TokenKind::FatArrow => "=>",

            TokenKind::LayoutLBrace => "{ (layout)",
            TokenKind::LayoutRBrace => "} (layout)",
            TokenKind::LayoutSemi => "; (layout)",

            TokenKind::LPragma => "{-#",
            TokenKind::RPragma => "#-}",

            TokenKind::Eof => "end of file",
        }
    }

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
        )
    }

    #[must_use]
    pub fn is_layout(&self) -> bool {
        matches!(
            self,
            TokenKind::LayoutLBrace | TokenKind::LayoutRBrace | TokenKind::LayoutSemi
        )
    }

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

impl std::hash::Hash for TokenKind {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::mem::discriminant(self).hash(state);

        match self {
            TokenKind::VarId(s) => s.hash(state),
            TokenKind::ConId(s) => s.hash(state),
            TokenKind::VarSym(s) => s.hash(state),
            TokenKind::ConSym(s) => s.hash(state),
            TokenKind::Integer { size, base, value } => {
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
            _ => {}
        }
    }
}
