//! Hand-written lexer for BSC.
//!
//! Mirrors `src/comp/Lex.hs` from the Haskell implementation.
//! Supports both Classic and BSV syntax with layout rules.
//!
//! # Architecture
//!
//! The lexer is designed to closely match the Haskell BSC lexer for behavioral
//! compatibility. Key features:
//!
//! - Hand-written character-by-character processing (not regex-based)
//! - Layout rules for indentation-sensitive parsing
//! - CPP directive handling (`# <line> "<file>"`)
//! - Support for both Classic and BSV syntax modes
//! - Sized bit literals (`8'hFF`, `16'b1010`)
//! - Arbitrary precision integers (using `BigInt`)

mod token;

pub use token::{Token, TokenKind};

use bsc_diagnostics::{LexError, Position, Span};
use bsc_syntax::literal::OrderedFloat;
use num_bigint::BigInt;
use num_traits::Num;
use std::str::Chars;

/// Result type for lexer operations.
pub type LexResult<T> = Result<T, LexError>;

/// Tab stop width (matches Haskell BSC).
const TAB_STOP: u32 = 8;

/// Configuration flags for the lexer.
///
/// Mirrors `LFlags` from Haskell BSC's Lex.hs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LexerFlags {
    /// Whether parsing a stdlib file (positions get annotated)
    pub is_stdlib: bool,
    /// Whether to allow SystemVerilog keywords as identifiers
    pub allow_sv_keywords: bool,
}

impl Default for LexerFlags {
    fn default() -> Self {
        Self {
            is_stdlib: false,
            allow_sv_keywords: true,
        }
    }
}

/// Syntax mode for the lexer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum SyntaxMode {
    /// Classic Bluespec syntax
    #[default]
    Classic,
    /// BSV (SystemVerilog-like) syntax
    Bsv,
}

/// The lexer state.
#[derive(Debug)]
pub struct Lexer<'src> {
    /// Source text
    source: &'src str,
    /// Characters iterator
    chars: Chars<'src>,
    /// Current position in source (byte offset)
    pos: usize,
    /// Current line (1-indexed, matches Haskell)
    line: u32,
    /// Current column (0-indexed, matches Haskell)
    column: u32,
    /// Lookahead character
    current: Option<char>,
    /// Layout stack (column numbers for implicit braces)
    layout_stack: Vec<u32>,
    /// Pending tokens from layout processing
    pending: Vec<Token>,
    /// Syntax mode
    mode: SyntaxMode,
    /// Lexer flags
    flags: LexerFlags,
    /// Current file name (for CPP directive handling)
    file_name: String,
}

impl<'src> Lexer<'src> {
    /// Create a new lexer for the given source.
    #[must_use]
    pub fn new(source: &'src str, mode: SyntaxMode) -> Self {
        Self::with_file(source, mode, LexerFlags::default(), "")
    }

    /// Create a new lexer with a filename.
    #[must_use]
    pub fn with_file(source: &'src str, mode: SyntaxMode, flags: LexerFlags, file_name: &str) -> Self {
        let mut chars = source.chars();
        let current = chars.next();
        Self {
            source,
            chars,
            pos: 0,
            line: 1,
            column: 0, // 0-indexed to match Haskell
            current,
            layout_stack: Vec::new(),
            pending: Vec::new(),
            mode,
            flags,
            file_name: file_name.to_string(),
        }
    }

    /// Create a new lexer with specific flags (no filename).
    #[must_use]
    pub fn with_flags(source: &'src str, mode: SyntaxMode, flags: LexerFlags) -> Self {
        Self::with_file(source, mode, flags, "")
    }

    /// Get the current position.
    #[must_use]
    pub fn position(&self) -> Position {
        Position::full(
            self.file_name.as_str(),
            self.line as i32,
            self.column as i32, // Column is 0-indexed like Haskell
            self.flags.is_stdlib,
        )
    }

    /// Peek at the current character without consuming.
    #[must_use]
    fn peek(&self) -> Option<char> {
        self.current
    }

    /// Peek at the next character (one ahead).
    #[must_use]
    fn peek_next(&self) -> Option<char> {
        self.chars.clone().next()
    }

    /// Peek at the character two ahead.
    #[must_use]
    fn peek_next_next(&self) -> Option<char> {
        let mut iter = self.chars.clone();
        iter.next();
        iter.next()
    }

    /// Advance to the next character.
    fn advance(&mut self) -> Option<char> {
        let c = self.current;
        if let Some(ch) = c {
            self.pos += ch.len_utf8();
            if ch == '\n' {
                self.line += 1;
                self.column = 0;
            } else if ch == '\t' {
                // Tab handling: advance to next tab stop (matches Haskell: nextTab)
                self.column = ((self.column + TAB_STOP) / TAB_STOP) * TAB_STOP;
            } else {
                self.column += 1;
            }
        }
        self.current = self.chars.next();
        c
    }

    /// Calculate next tab stop position.
    fn next_tab(col: u32) -> u32 {
        ((col + TAB_STOP) / TAB_STOP) * TAB_STOP
    }

    /// Make a token at the given span with position info.
    fn make_token(&self, kind: TokenKind, start: u32, end: u32, start_line: u32, start_col: u32) -> Token {
        let pos = Position::full(
            self.file_name.as_str(),
            start_line as i32,
            start_col as i32,
            self.flags.is_stdlib,
        );
        Token::new(kind, Span::new(start, end), pos)
    }

    /// Make a token using current position as start (for simple tokens).
    fn make_simple_token(&self, kind: TokenKind, start: u32, end: u32) -> Token {
        let pos = Position::full(
            self.file_name.as_str(),
            self.line as i32,
            self.column as i32, // Column is 0-indexed like Haskell
            self.flags.is_stdlib,
        );
        Token::new(kind, Span::new(start, end), pos)
    }

    /// Skip whitespace and comments, returning whether we crossed a newline.
    fn skip_whitespace_and_comments(&mut self) -> LexResult<bool> {
        let mut crossed_newline = false;
        loop {
            match self.peek() {
                Some(' ') => {
                    self.advance();
                }
                Some('\t') => {
                    self.advance();
                }
                Some('\r') | Some('\x0B') | Some('\x0C') => {
                    // Carriage return, vertical tab (\x0B), form feed (\x0C): reset column (matches Haskell)
                    self.column = 0;
                    self.advance();
                }
                Some('\n') => {
                    self.advance();
                    crossed_newline = true;
                }
                // Line comment: --
                Some('-') if self.peek_next() == Some('-') && self.is_comment_start() => {
                    self.skip_line_comment()?;
                    crossed_newline = true;
                }
                // Pragma: {-#
                Some('{') if self.peek_next() == Some('-') && self.peek_next_next() == Some('#') => {
                    // Don't skip pragmas - they are tokens
                    break;
                }
                // Block comment: {-
                Some('{') if self.peek_next() == Some('-') => {
                    self.skip_block_comment()?;
                }
                // BSV line comment: //
                Some('/') if self.mode == SyntaxMode::Bsv && self.peek_next() == Some('/') => {
                    self.skip_bsv_line_comment()?;
                    crossed_newline = true;
                }
                // BSV block comment: /* */
                Some('/') if self.mode == SyntaxMode::Bsv && self.peek_next() == Some('*') => {
                    self.skip_bsv_block_comment()?;
                }
                _ => break,
            }
        }
        Ok(crossed_newline)
    }

    /// Check if this is a valid comment start (-- followed by appropriate char).
    /// Matches Haskell: isComm function.
    fn is_comment_start(&self) -> bool {
        let mut iter = self.chars.clone();
        iter.next(); // skip first -
        match iter.next() {
            Some('-') => true,  // ---
            Some('@') => true,  // --@
            Some(c) if !is_symbol_char(c) => true,
            None => true,
            _ => false,
        }
    }

    /// Skip a line comment (-- or //).
    fn skip_line_comment(&mut self) -> LexResult<()> {
        while let Some(c) = self.peek() {
            if c == '\n' {
                self.advance(); // consume the newline
                return Ok(());
            }
            self.advance();
        }
        // EOF without newline - this is an error in Haskell BSC
        // But we'll be lenient here and just return Ok
        Ok(())
    }

    /// Skip a BSV-style line comment (//).
    fn skip_bsv_line_comment(&mut self) -> LexResult<()> {
        self.skip_line_comment()
    }

    /// Skip a block comment ({- -}).
    fn skip_block_comment(&mut self) -> LexResult<()> {
        let start_pos = self.position();
        let start_offset = self.pos as u32;

        // Skip {-
        self.advance();
        self.advance();

        let mut depth = 1;
        while depth > 0 {
            match self.peek() {
                None => {
                    return Err(LexError::UnterminatedBlockComment {
                        position: start_pos.clone(),
                        span: Span::new(start_offset, self.pos as u32).into(),
                    });
                }
                Some('{') if self.peek_next() == Some('-') => {
                    self.advance();
                    self.advance();
                    depth += 1;
                }
                Some('-') if self.peek_next() == Some('}') => {
                    self.advance();
                    self.advance();
                    depth -= 1;
                }
                _ => {
                    self.advance();
                }
            }
        }
        Ok(())
    }

    /// Skip a BSV block comment (/* */).
    fn skip_bsv_block_comment(&mut self) -> LexResult<()> {
        let start_pos = self.position();
        let start_offset = self.pos as u32;

        // Skip /*
        self.advance();
        self.advance();

        loop {
            match self.peek() {
                None => {
                    return Err(LexError::UnterminatedBlockComment {
                        position: start_pos.clone(),
                        span: Span::new(start_offset, self.pos as u32).into(),
                    });
                }
                Some('*') if self.peek_next() == Some('/') => {
                    self.advance();
                    self.advance();
                    break;
                }
                _ => {
                    self.advance();
                }
            }
        }
        Ok(())
    }

    /// Handle CPP directive at column 0: # <line> "<file>"
    fn try_cpp_directive(&mut self) -> bool {
        if self.column != 0 || self.peek() != Some('#') {
            return false;
        }

        // Check for: # <space> <digit>
        let mut iter = self.chars.clone();
        if iter.next() != Some(' ') {
            return false;
        }
        match iter.next() {
            Some(c) if c.is_ascii_digit() => {}
            _ => return false,
        }

        // This is a CPP directive, consume it
        self.advance(); // skip #
        self.advance(); // skip space

        // Parse line number
        let mut line_str = String::new();
        while let Some(c) = self.peek() {
            if c.is_ascii_digit() {
                line_str.push(c);
                self.advance();
            } else {
                break;
            }
        }

        // Skip space(s)
        while self.peek() == Some(' ') {
            self.advance();
        }

        // Parse filename (in quotes)
        let mut file_name = String::new();
        if self.peek() == Some('"') {
            self.advance(); // skip opening quote
            while let Some(c) = self.peek() {
                if c == '"' {
                    self.advance();
                    break;
                }
                if c == '\n' {
                    break;
                }
                file_name.push(c);
                self.advance();
            }
        }

        // Skip rest of line (flags, etc.)
        while let Some(c) = self.peek() {
            if c == '\n' {
                self.advance(); // consume newline
                break;
            }
            self.advance();
        }

        // Update position
        if let Ok(new_line) = line_str.parse::<u32>() {
            self.line = new_line;
            self.column = 0;
        }
        if !file_name.is_empty() {
            self.file_name = file_name;
        }

        true
    }

    /// Get the next token.
    pub fn next_token(&mut self) -> LexResult<Token> {
        // Return pending tokens first (from layout processing)
        if let Some(tok) = self.pending.pop() {
            return Ok(tok);
        }

        // Handle CPP directives at column 0
        while self.try_cpp_directive() {
            // Keep processing directives
        }

        let _crossed_newline = self.skip_whitespace_and_comments()?;

        let start_pos = self.position();
        let start_offset = self.pos as u32;

        let kind = match self.peek() {
            None => TokenKind::Eof,
            Some(c) => match c {
                // Pragma: {-#
                '{' if self.peek_next() == Some('-') && self.peek_next_next() == Some('#') => {
                    self.advance();
                    self.advance();
                    self.advance();
                    TokenKind::LPragma
                }
                // Close pragma: #-}
                '#' if self.peek_next() == Some('-') && self.peek_next_next() == Some('}') => {
                    self.advance();
                    self.advance();
                    self.advance();
                    TokenKind::RPragma
                }
                // Delimiters
                '(' => { self.advance(); TokenKind::LParen }
                ')' => { self.advance(); TokenKind::RParen }
                ',' => { self.advance(); TokenKind::Comma }
                ';' => { self.advance(); TokenKind::Semi }
                '`' => { self.advance(); TokenKind::Backtick }
                '{' => { self.advance(); TokenKind::LBrace }
                '}' => { self.advance(); TokenKind::RBrace }
                '[' => { self.advance(); TokenKind::LBracket }
                ']' => { self.advance(); TokenKind::RBracket }
                // Dot is special: could be . or ..
                '.' if self.peek_next() == Some('.') => {
                    self.advance();
                    self.advance();
                    TokenKind::DotDot
                }
                '.' => { self.advance(); TokenKind::Dot }
                // Character literal
                '\'' => self.lex_char()?,
                // String literal
                '"' => self.lex_string()?,
                // Numbers (and sized literals like 8'hFF)
                c if c.is_ascii_digit() => self.lex_number()?,
                // $ identifier or $ symbol
                '$' => self.lex_dollar()?,
                // Symbol/operator
                c if is_symbol_char(c) => self.lex_symbol()?,
                // Identifiers and keywords
                c if c.is_ascii_alphabetic() || c == '_' => self.lex_identifier()?,
                // Unknown character
                _ => {
                    let pos = self.position();
                    self.advance();
                    return Err(LexError::UnexpectedChar {
                        char: c,
                        position: pos,
                        span: Span::new(start_offset, self.pos as u32).into(),
                    });
                }
            }
        };

        let end_offset = self.pos as u32;
        Ok(self.make_token(kind, start_offset, end_offset, start_pos.line as u32, start_pos.column as u32))
    }

    /// Lex a lowercase identifier or keyword.
    fn lex_identifier(&mut self) -> LexResult<TokenKind> {
        let start = self.pos;
        while let Some(c) = self.peek() {
            if is_id_char(c) {
                self.advance();
            } else {
                break;
            }
        }
        let text = &self.source[start..self.pos];

        // Check for underscore (special token)
        if text == "_" {
            return Ok(TokenKind::Underscore);
        }

        // Check for keywords
        let kind = match text {
            // Reserved words (Classic)
            "action" => TokenKind::KwAction,
            "case" => TokenKind::KwCase,
            "class" => TokenKind::KwClass,
            "data" => TokenKind::KwData,
            "deriving" => TokenKind::KwDeriving,
            "do" => TokenKind::KwDo,
            "else" => TokenKind::KwElse,
            "foreign" => TokenKind::KwForeign,
            "if" => TokenKind::KwIf,
            "import" => TokenKind::KwImport,
            "in" => TokenKind::KwIn,
            "infix" => TokenKind::KwInfix,
            "infixl" => TokenKind::KwInfixL,
            "infixr" => TokenKind::KwInfixR,
            "interface" => TokenKind::KwInterface,
            "instance" => TokenKind::KwInstance,
            "let" => TokenKind::KwLet,
            "letseq" => TokenKind::KwLetSeq,
            "module" => TokenKind::KwModule,
            "of" => TokenKind::KwOf,
            "package" => TokenKind::KwPackage,
            "primitive" => TokenKind::KwPrimitive,
            "qualified" => TokenKind::KwQualified,
            "rules" => TokenKind::KwRules,
            "signature" => TokenKind::KwSignature,
            "struct" => TokenKind::KwStruct,
            "then" => TokenKind::KwThen,
            "type" => TokenKind::KwType,
            "valueOf" => TokenKind::KwValueOf,
            "stringOf" => TokenKind::KwStringOf,
            "verilog" => TokenKind::KwVerilog,
            "synthesize" => TokenKind::KwSynthesize,
            "when" => TokenKind::KwWhen,
            "where" => TokenKind::KwWhere,
            "coherent" => TokenKind::KwCoherent,
            "incoherent" => TokenKind::KwIncoherent,
            // BSV-specific keywords (only recognized in BSV mode)
            "actionvalue" if self.mode == SyntaxMode::Bsv => TokenKind::KwActionValue,
            "export" if self.mode == SyntaxMode::Bsv => TokenKind::KwExport,
            "for" if self.mode == SyntaxMode::Bsv => TokenKind::KwFor,
            "function" if self.mode == SyntaxMode::Bsv => TokenKind::KwFunction,
            "match" if self.mode == SyntaxMode::Bsv => TokenKind::KwMatch,
            "matches" if self.mode == SyntaxMode::Bsv => TokenKind::KwMatches,
            "method" if self.mode == SyntaxMode::Bsv => TokenKind::KwMethod,
            "return" if self.mode == SyntaxMode::Bsv => TokenKind::KwReturn,
            "rule" if self.mode == SyntaxMode::Bsv => TokenKind::KwRule,
            "while" if self.mode == SyntaxMode::Bsv => TokenKind::KwWhile,
            // Not a keyword - check if constructor or variable
            _ => {
                let first_char = text.chars().next().unwrap_or('a');
                if first_char.is_ascii_uppercase() {
                    TokenKind::ConId(text.into())
                } else {
                    TokenKind::VarId(text.into())
                }
            }
        };

        Ok(kind)
    }

    /// Lex a $ identifier or symbol.
    fn lex_dollar(&mut self) -> LexResult<TokenKind> {
        let start = self.pos;
        self.advance(); // consume $

        // Check what follows
        match self.peek() {
            // $identifier
            Some(c) if is_id_char(c) => {
                while let Some(c) = self.peek() {
                    if is_id_char(c) || c == '$' {
                        self.advance();
                    } else {
                        break;
                    }
                }
                let text = &self.source[start..self.pos];
                Ok(TokenKind::VarId(text.into()))
            }
            // Just $ by itself
            _ => Ok(TokenKind::VarSym("$".into())),
        }
    }

    /// Lex a symbol/operator.
    fn lex_symbol(&mut self) -> LexResult<TokenKind> {
        let start = self.pos;

        // Collect all symbol characters
        while let Some(c) = self.peek() {
            if is_symbol_char(c) {
                self.advance();
            } else {
                break;
            }
        }

        let text = &self.source[start..self.pos];

        // Check for reserved operators
        // Note: "|" is NOT a reserved operator - it's a regular VarSym so it can be used
        // in fixity declarations like "infixr 4 |"
        let kind = match text {
            "::" => TokenKind::ColonColon,
            ":" => TokenKind::Colon,
            "=" => TokenKind::Equals,
            "@" => TokenKind::At,
            "\\" => TokenKind::Backslash,
            "->" => TokenKind::Arrow,
            "<=>" => TokenKind::VarSym(text.into()), // Not a reserved operator
            "==>" => TokenKind::DArrow,
            "=>" => TokenKind::FatArrow,
            "<-" => TokenKind::LArrow,
            "#" => TokenKind::Hash,
            "?" => TokenKind::Question,
            // Not a reserved operator - check if consym or varsym
            _ => {
                if text.starts_with(':') {
                    TokenKind::ConSym(text.into())
                } else {
                    TokenKind::VarSym(text.into())
                }
            }
        };

        Ok(kind)
    }

    /// Lex a number (integer or float, including sized literals).
    fn lex_number(&mut self) -> LexResult<TokenKind> {
        let start = self.pos;
        let start_pos = self.position();

        // Check for 0x, 0o, 0b prefix
        if self.peek() == Some('0') {
            let next = self.peek_next();
            match next {
                Some('x') | Some('X') => {
                    self.advance(); // 0
                    self.advance(); // x
                    return self.lex_integer_with_base(16, start, start_pos, None);
                }
                Some('o') | Some('O') => {
                    self.advance(); // 0
                    self.advance(); // o
                    return self.lex_integer_with_base(8, start, start_pos, None);
                }
                Some('b') | Some('B') => {
                    self.advance(); // 0
                    self.advance(); // b
                    return self.lex_integer_with_base(2, start, start_pos, None);
                }
                _ => {}
            }
        }

        // Collect decimal digits
        let mut int_part = String::new();
        while let Some(c) = self.peek() {
            if c.is_ascii_digit() {
                int_part.push(c);
                self.advance();
            } else if c == '_' {
                self.advance(); // skip underscores
            } else {
                break;
            }
        }

        // Check for sized literal: N'bXXX, N'oXXX, N'dXXX, N'hXXX
        if self.peek() == Some('\'') {
            let size = BigInt::from_str_radix(&int_part, 10)
                .map_err(|_| LexError::InvalidInteger {
                    literal: int_part.clone(),
                    position: start_pos.clone(),
                    reason: "invalid size".to_string(),
                    span: Span::new(start as u32, self.pos as u32).into(),
                })?;

            self.advance(); // consume '
            let format_char = self.peek();
            self.advance(); // consume format character

            let base = match format_char {
                Some('h') | Some('H') => 16,
                Some('d') | Some('D') => 10,
                Some('b') | Some('B') => 2,
                Some('o') | Some('O') => 8,
                _ => {
                    return Err(LexError::InvalidSizedLiteral {
                        literal: self.source[start..self.pos].to_string(),
                        position: start_pos.clone(),
                        reason: "expected h, d, b, or o after '".to_string(),
                        span: Span::new(start as u32, self.pos as u32).into(),
                    });
                }
            };

            return self.lex_integer_with_base(base, start, start_pos, Some(size));
        }

        // Check for decimal point (float)
        if self.peek() == Some('.') && self.peek_next().is_some_and(|c| c.is_ascii_digit()) {
            self.advance(); // consume .

            let mut frac_part = String::new();
            while let Some(c) = self.peek() {
                if c.is_ascii_digit() {
                    frac_part.push(c);
                    self.advance();
                } else {
                    break;
                }
            }

            // Check for exponent
            let mut exp_part = String::new();
            if matches!(self.peek(), Some('e') | Some('E')) {
                exp_part.push(self.advance().unwrap_or('e'));
                if matches!(self.peek(), Some('+') | Some('-')) {
                    exp_part.push(self.advance().unwrap_or('+'));
                }
                while let Some(c) = self.peek() {
                    if c.is_ascii_digit() {
                        exp_part.push(c);
                        self.advance();
                    } else {
                        break;
                    }
                }
            }

            let full_str = format!("{int_part}.{frac_part}{exp_part}");
            let value: f64 = full_str.parse().map_err(|_| LexError::InvalidInteger {
                literal: full_str.clone(),
                position: start_pos.clone(),
                reason: "invalid float literal".to_string(),
                span: Span::new(start as u32, self.pos as u32).into(),
            })?;

            return Ok(TokenKind::Float(OrderedFloat::new(value)));
        }

        // Check for exponent without decimal (still a float in some languages, but in BSC it's an error)
        // Actually in BSC, this becomes an integer followed by identifier 'e...'
        // So we just return the integer

        // Plain integer
        let value = BigInt::from_str_radix(&int_part, 10).map_err(|_| LexError::InvalidInteger {
            literal: int_part.clone(),
            position: start_pos.clone(),
            reason: "invalid integer literal".to_string(),
            span: Span::new(start as u32, self.pos as u32).into(),
        })?;

        Ok(TokenKind::Integer {
            size: None,
            base: 10,
            value,
        })
    }

    /// Lex an integer with a specific base.
    fn lex_integer_with_base(
        &mut self,
        base: u32,
        start: usize,
        start_pos: Position,
        size: Option<BigInt>,
    ) -> LexResult<TokenKind> {
        let digit_start = self.pos;

        while let Some(c) = self.peek() {
            if c == '_' {
                self.advance();
            } else if is_digit_for_base(c, base) {
                self.advance();
            } else {
                break;
            }
        }

        let digits: String = self.source[digit_start..self.pos]
            .chars()
            .filter(|&c| c != '_')
            .collect();

        if digits.is_empty() {
            return Err(LexError::InvalidInteger {
                literal: self.source[start..self.pos].to_string(),
                position: start_pos.clone(),
                reason: format!("expected base-{base} digits"),
                span: Span::new(start as u32, self.pos as u32).into(),
            });
        }

        let value = BigInt::from_str_radix(&digits, base).map_err(|_| LexError::InvalidInteger {
            literal: self.source[start..self.pos].to_string(),
            position: start_pos.clone(),
            reason: format!("invalid base-{base} integer literal"),
            span: Span::new(start as u32, self.pos as u32).into(),
        })?;

        Ok(TokenKind::Integer { size, base, value })
    }

    /// Lex a string literal.
    fn lex_string(&mut self) -> LexResult<TokenKind> {
        let start_pos = self.position();
        let start = self.pos as u32;

        self.advance(); // consume opening "

        let mut value = String::new();
        loop {
            match self.peek() {
                None | Some('\n') => {
                    return Err(LexError::UnterminatedString {
                        position: start_pos.clone(),
                        span: Span::new(start, self.pos as u32).into(),
                    });
                }
                Some('"') => {
                    self.advance();
                    break;
                }
                Some('\\') => {
                    self.advance();
                    let escaped = self.lex_escape_sequence(start_pos.clone(), start)?;
                    value.push(escaped);
                    if self.column > 0 {
                        self.column -= 1;
                    }
                }
                Some(c) => {
                    value.push(c);
                    self.advance();
                }
            }
        }

        Ok(TokenKind::String(value))
    }

    /// Lex a character literal.
    fn lex_char(&mut self) -> LexResult<TokenKind> {
        let start_pos = self.position();
        let start = self.pos as u32;

        self.advance(); // consume opening '

        let c = match self.peek() {
            None | Some('\n') | Some('\'') => {
                return Err(LexError::UnterminatedString {
                    position: start_pos.clone(),
                    span: Span::new(start, self.pos as u32).into(),
                });
            }
            Some('\\') => {
                self.advance();
                let escaped = self.lex_escape_sequence(start_pos.clone(), start)?;
                if self.column > 0 {
                    self.column -= 1;
                }
                escaped
            }
            Some(c) => {
                self.advance();
                c
            }
        };

        if self.peek() != Some('\'') {
            return Err(LexError::UnterminatedString {
                position: start_pos.clone(),
                span: Span::new(start, self.pos as u32).into(),
            });
        }
        self.advance(); // consume closing '

        Ok(TokenKind::Char(c))
    }

    /// Lex an escape sequence (after the backslash).
    fn lex_escape_sequence(&mut self, start_pos: Position, start: u32) -> LexResult<char> {
        match self.peek() {
            Some('n') => { self.advance(); Ok('\n') }
            Some('t') => { self.advance(); Ok('\t') }
            Some('r') => { self.advance(); Ok('\r') }
            Some('v') => { self.advance(); Ok('\x0B') }  // vertical tab
            Some('f') => { self.advance(); Ok('\x0C') }  // form feed
            Some('\\') => { self.advance(); Ok('\\') }
            Some('"') => { self.advance(); Ok('"') }
            Some('\'') => { self.advance(); Ok('\'') }
            Some('0') => { self.advance(); Ok('\0') }
            Some('x') => {
                self.advance();
                let mut hex = String::new();
                while let Some(c) = self.peek() {
                    if c.is_ascii_hexdigit() {
                        hex.push(c);
                        self.advance();
                    } else {
                        break;
                    }
                }
                if hex.is_empty() {
                    return Err(LexError::InvalidEscape {
                        sequence: "x".to_string(),
                        position: start_pos.clone(),
                        span: Span::new(start, self.pos as u32).into(),
                    });
                }
                let code = u32::from_str_radix(&hex, 16).map_err(|_| LexError::InvalidEscape {
                    sequence: format!("x{hex}"),
                    position: start_pos.clone(),
                    span: Span::new(start, self.pos as u32).into(),
                })?;
                char::from_u32(code).ok_or_else(|| LexError::InvalidEscape {
                    sequence: format!("x{hex}"),
                    position: start_pos.clone(),
                    span: Span::new(start, self.pos as u32).into(),
                })
            }
            Some(c) => Err(LexError::InvalidEscape {
                sequence: c.to_string(),
                position: start_pos.clone(),
                span: Span::new(start, self.pos as u32).into(),
            }),
            None => Err(LexError::InvalidEscape {
                sequence: String::new(),
                position: start_pos.clone(),
                span: Span::new(start, self.pos as u32).into(),
            }),
        }
    }

    /// Tokenize the entire source.
    pub fn tokenize(mut self) -> LexResult<Vec<Token>> {
        let mut tokens = Vec::new();
        loop {
            let token = self.next_token()?;
            let is_eof = token.kind == TokenKind::Eof;
            tokens.push(token);
            if is_eof {
                break;
            }
        }
        Ok(tokens)
    }
}

/// Check if a character can be part of an identifier.
/// Matches Haskell BSC's `isIdChar`.
#[inline]
fn is_id_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_' || c == '\''
}

/// Check if a character is a valid digit for the given base.
#[inline]
fn is_digit_for_base(c: char, base: u32) -> bool {
    match base {
        2 => matches!(c, '0' | '1'),
        8 => matches!(c, '0'..='7'),
        10 => c.is_ascii_digit(),
        16 => c.is_ascii_hexdigit(),
        _ => false,
    }
}

/// Check if a character can be part of a symbol/operator.
/// Matches Haskell BSC's `isSym`.
#[inline]
fn is_symbol_char(c: char) -> bool {
    matches!(c,
        '!' | '@' | '#' | '$' | '%' | '&' | '*' | '+' | '.' | '/' |
        '<' | '=' | '>' | '?' | '\\' | '^' | '|' | ':' | '-' | '~' | ','
    ) || (c >= '\u{80}' && is_unicode_symbol(c))
}

/// Check if a Unicode character is a symbol (mirrors Haskell's handling).
/// Haskell's `isSymbol` returns True for Unicode categories:
/// - MathSymbol, CurrencySymbol, ModifierSymbol, OtherSymbol
fn is_unicode_symbol(c: char) -> bool {
    // Common symbol ranges used in Bluespec
    matches!(c,
        '\u{00A2}'..='\u{00BF}' | // Currency and special symbols (Latin-1 Supplement)
        '\u{00D7}' | '\u{00F7}' | // Multiplication and division signs
        '\u{2200}'..='\u{22FF}' | // Mathematical Operators (includes ∘ at U+2218)
        '\u{2300}'..='\u{23FF}' | // Miscellaneous Technical
        '\u{25A0}'..='\u{25FF}' | // Geometric Shapes
        '\u{2600}'..='\u{26FF}' | // Miscellaneous Symbols
        '\u{2700}'..='\u{27BF}' | // Dingbats
        '\u{27C0}'..='\u{27EF}' | // Miscellaneous Mathematical Symbols-A
        '\u{27F0}'..='\u{27FF}' | // Supplemental Arrows-A
        '\u{2900}'..='\u{297F}' | // Supplemental Arrows-B
        '\u{2980}'..='\u{29FF}' | // Miscellaneous Mathematical Symbols-B
        '\u{2A00}'..='\u{2AFF}'   // Supplemental Mathematical Operators
    ) || (c.is_ascii_punctuation() && !is_id_char(c))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lex_keywords() {
        let lexer = Lexer::new("if then else signature coherent incoherent", SyntaxMode::Classic);
        let tokens = lexer.tokenize().expect("lexing failed");

        assert!(matches!(tokens[0].kind, TokenKind::KwIf));
        assert!(matches!(tokens[1].kind, TokenKind::KwThen));
        assert!(matches!(tokens[2].kind, TokenKind::KwElse));
        assert!(matches!(tokens[3].kind, TokenKind::KwSignature));
        assert!(matches!(tokens[4].kind, TokenKind::KwCoherent));
        assert!(matches!(tokens[5].kind, TokenKind::KwIncoherent));
    }

    #[test]
    fn test_lex_identifiers() {
        let lexer = Lexer::new("foo Bar x' _test", SyntaxMode::Classic);
        let tokens = lexer.tokenize().expect("lexing failed");

        assert!(matches!(&tokens[0].kind, TokenKind::VarId(s) if s == "foo"));
        assert!(matches!(&tokens[1].kind, TokenKind::ConId(s) if s == "Bar"));
        assert!(matches!(&tokens[2].kind, TokenKind::VarId(s) if s == "x'"));
        assert!(matches!(&tokens[3].kind, TokenKind::VarId(s) if s == "_test"));
    }

    #[test]
    fn test_lex_underscore() {
        let lexer = Lexer::new("_", SyntaxMode::Classic);
        let tokens = lexer.tokenize().expect("lexing failed");

        assert!(matches!(tokens[0].kind, TokenKind::Underscore));
    }

    #[test]
    fn test_lex_dollar_identifier() {
        let lexer = Lexer::new("$foo $x$y", SyntaxMode::Classic);
        let tokens = lexer.tokenize().expect("lexing failed");

        assert!(matches!(&tokens[0].kind, TokenKind::VarId(s) if s == "$foo"));
        assert!(matches!(&tokens[1].kind, TokenKind::VarId(s) if s == "$x$y"));
    }

    #[test]
    fn test_lex_sized_literal() {
        let lexer = Lexer::new("8'hFF 16'b1010 32'd42 4'o7", SyntaxMode::Classic);
        let tokens = lexer.tokenize().expect("lexing failed");

        if let TokenKind::Integer { size, base, value } = &tokens[0].kind {
            assert_eq!(*size, Some(BigInt::from(8)));
            assert_eq!(*base, 16);
            assert_eq!(*value, BigInt::from(255));
        } else {
            panic!("Expected Integer token");
        }

        if let TokenKind::Integer { size, base, value } = &tokens[1].kind {
            assert_eq!(*size, Some(BigInt::from(16)));
            assert_eq!(*base, 2);
            assert_eq!(*value, BigInt::from(10));
        } else {
            panic!("Expected Integer token");
        }
    }

    #[test]
    fn test_lex_operators() {
        let lexer = Lexer::new("-> <- :: => ==>", SyntaxMode::Classic);
        let tokens = lexer.tokenize().expect("lexing failed");

        assert!(matches!(tokens[0].kind, TokenKind::Arrow));
        assert!(matches!(tokens[1].kind, TokenKind::LArrow));
        assert!(matches!(tokens[2].kind, TokenKind::ColonColon));
        assert!(matches!(tokens[3].kind, TokenKind::FatArrow));
        assert!(matches!(tokens[4].kind, TokenKind::DArrow));
    }

    #[test]
    fn test_lex_pragmas() {
        let lexer = Lexer::new("{-# NOINLINE foo #-}", SyntaxMode::Classic);
        let tokens = lexer.tokenize().expect("lexing failed");

        assert!(matches!(tokens[0].kind, TokenKind::LPragma));
        assert!(matches!(&tokens[1].kind, TokenKind::ConId(s) if s == "NOINLINE"));
        assert!(matches!(&tokens[2].kind, TokenKind::VarId(s) if s == "foo"));
        assert!(matches!(tokens[3].kind, TokenKind::RPragma));
    }

    #[test]
    fn test_lex_escape_sequences() {
        let lexer = Lexer::new(r#""\n\t\r\v\f\\\"\'""#, SyntaxMode::Classic);
        let tokens = lexer.tokenize().expect("lexing failed");

        if let TokenKind::String(s) = &tokens[0].kind {
            assert_eq!(s, "\n\t\r\x0B\x0C\\\"'");
        } else {
            panic!("Expected String token");
        }
    }

    #[test]
    fn test_lex_hex_escape() {
        let lexer = Lexer::new(r#""\x41\x42\x43""#, SyntaxMode::Classic);
        let tokens = lexer.tokenize().expect("lexing failed");

        if let TokenKind::String(s) = &tokens[0].kind {
            assert_eq!(s, "ABC");
        } else {
            panic!("Expected String token");
        }
    }

    #[test]
    fn test_lex_block_comment() {
        let lexer = Lexer::new("foo {- comment -} bar", SyntaxMode::Classic);
        let tokens = lexer.tokenize().expect("lexing failed");

        assert!(matches!(&tokens[0].kind, TokenKind::VarId(s) if s == "foo"));
        assert!(matches!(&tokens[1].kind, TokenKind::VarId(s) if s == "bar"));
    }

    #[test]
    fn test_lex_nested_block_comment() {
        let lexer = Lexer::new("foo {- outer {- inner -} -} bar", SyntaxMode::Classic);
        let tokens = lexer.tokenize().expect("lexing failed");

        assert!(matches!(&tokens[0].kind, TokenKind::VarId(s) if s == "foo"));
        assert!(matches!(&tokens[1].kind, TokenKind::VarId(s) if s == "bar"));
    }

    #[test]
    fn test_lex_line_comment() {
        let lexer = Lexer::new("foo -- comment\nbar", SyntaxMode::Classic);
        let tokens = lexer.tokenize().expect("lexing failed");

        assert!(matches!(&tokens[0].kind, TokenKind::VarId(s) if s == "foo"));
        assert!(matches!(&tokens[1].kind, TokenKind::VarId(s) if s == "bar"));
    }

    #[test]
    fn test_lex_bsv_comments() {
        let lexer = Lexer::new("foo // comment\nbar /* block */ baz", SyntaxMode::Bsv);
        let tokens = lexer.tokenize().expect("lexing failed");

        assert!(matches!(&tokens[0].kind, TokenKind::VarId(s) if s == "foo"));
        assert!(matches!(&tokens[1].kind, TokenKind::VarId(s) if s == "bar"));
        assert!(matches!(&tokens[2].kind, TokenKind::VarId(s) if s == "baz"));
    }

    #[test]
    fn test_lex_float() {
        let lexer = Lexer::new("3.14 1.0e10 2.5e-3", SyntaxMode::Classic);
        let tokens = lexer.tokenize().expect("lexing failed");

        if let TokenKind::Float(f) = &tokens[0].kind {
            assert!((f.0 - 3.14).abs() < 0.001);
        } else {
            panic!("Expected Float token");
        }
    }

    #[test]
    fn test_lex_consym() {
        let lexer = Lexer::new(":+ :++ :.", SyntaxMode::Classic);
        let tokens = lexer.tokenize().expect("lexing failed");

        assert!(matches!(&tokens[0].kind, TokenKind::ConSym(s) if s == ":+"));
        assert!(matches!(&tokens[1].kind, TokenKind::ConSym(s) if s == ":++"));
        assert!(matches!(&tokens[2].kind, TokenKind::ConSym(s) if s == ":."));
    }
}
