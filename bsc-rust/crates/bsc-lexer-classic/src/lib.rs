//! Hand-written lexer for Classic Bluespec syntax.
//!
//! Mirrors `src/comp/Lex.hs` from the Haskell implementation.
//! Supports layout rules for indentation-sensitive parsing.
//!
//! # Architecture
//!
//! The lexer is designed to closely match the Haskell BSC lexer for behavioral
//! compatibility. Key features:
//!
//! - Hand-written character-by-character processing (not regex-based)
//! - Layout rules for indentation-sensitive parsing
//! - CPP directive handling (`# <line> "<file>"`)
//! - Sized bit literals (`8'hFF`, `16'b1010`)
//! - Arbitrary precision integers (using `BigInt`)

mod token;

pub use token::{Token, TokenKind};

use bsc_diagnostics::{LexError, Position, Span};
use bsc_syntax::literal::OrderedFloat;
use num_bigint::BigInt;
use num_traits::Num;
use std::str::Chars;

pub type LexResult<T> = Result<T, LexError>;

const TAB_STOP: u32 = 8;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LexerFlags {
    pub is_stdlib: bool,
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

#[derive(Debug)]
pub struct Lexer<'src> {
    source: &'src str,
    chars: Chars<'src>,
    pos: usize,
    line: u32,
    column: u32,
    current: Option<char>,
    layout_stack: Vec<u32>,
    pending: Vec<Token>,
    flags: LexerFlags,
    file_name: String,
}

impl<'src> Lexer<'src> {
    #[must_use]
    pub fn new(source: &'src str) -> Self {
        Self::with_file(source, LexerFlags::default(), "")
    }

    #[must_use]
    pub fn with_file(source: &'src str, flags: LexerFlags, file_name: &str) -> Self {
        let mut chars = source.chars();
        let current = chars.next();
        Self {
            source,
            chars,
            pos: 0,
            line: 1,
            column: 0,
            current,
            layout_stack: Vec::new(),
            pending: Vec::new(),
            flags,
            file_name: file_name.to_string(),
        }
    }

    #[must_use]
    pub fn with_flags(source: &'src str, flags: LexerFlags) -> Self {
        Self::with_file(source, flags, "")
    }

    #[must_use]
    pub fn position(&self) -> Position {
        Position::full(
            self.file_name.as_str(),
            self.line as i32,
            self.column as i32,
            self.flags.is_stdlib,
        )
    }

    #[must_use]
    fn peek(&self) -> Option<char> {
        self.current
    }

    #[must_use]
    fn peek_next(&self) -> Option<char> {
        self.chars.clone().next()
    }

    #[must_use]
    fn peek_next_next(&self) -> Option<char> {
        let mut iter = self.chars.clone();
        iter.next();
        iter.next()
    }

    fn advance(&mut self) -> Option<char> {
        let c = self.current;
        if let Some(ch) = c {
            self.pos += ch.len_utf8();
            if ch == '\n' {
                self.line += 1;
                self.column = 0;
            } else if ch == '\t' {
                self.column = ((self.column + TAB_STOP) / TAB_STOP) * TAB_STOP;
            } else {
                self.column += 1;
            }
        }
        self.current = self.chars.next();
        c
    }

    fn make_token(&self, kind: TokenKind, start: u32, end: u32, start_line: u32, start_col: u32) -> Token {
        let pos = Position::full(
            self.file_name.as_str(),
            start_line as i32,
            start_col as i32,
            self.flags.is_stdlib,
        );
        Token::new(kind, Span::new(start, end), pos)
    }

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
                    self.column = 0;
                    self.advance();
                }
                Some('\n') => {
                    self.advance();
                    crossed_newline = true;
                }
                Some('-') if self.peek_next() == Some('-') && self.is_comment_start() => {
                    self.skip_line_comment()?;
                    crossed_newline = true;
                }
                Some('{') if self.peek_next() == Some('-') && self.peek_next_next() == Some('#') => {
                    break;
                }
                Some('{') if self.peek_next() == Some('-') => {
                    self.skip_block_comment()?;
                }
                _ => break,
            }
        }
        Ok(crossed_newline)
    }

    fn is_comment_start(&self) -> bool {
        let mut iter = self.chars.clone();
        iter.next();
        match iter.next() {
            Some('-') => true,
            Some('@') => true,
            Some(c) if !is_symbol_char(c) => true,
            None => true,
            _ => false,
        }
    }

    fn skip_line_comment(&mut self) -> LexResult<()> {
        while let Some(c) = self.peek() {
            if c == '\n' {
                self.advance();
                return Ok(());
            }
            self.advance();
        }
        Ok(())
    }

    fn skip_block_comment(&mut self) -> LexResult<()> {
        let start_pos = self.position();
        let start_offset = self.pos as u32;

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

    fn try_cpp_directive(&mut self) -> bool {
        if self.column != 0 || self.peek() != Some('#') {
            return false;
        }

        let mut iter = self.chars.clone();
        if iter.next() != Some(' ') {
            return false;
        }
        match iter.next() {
            Some(c) if c.is_ascii_digit() => {}
            _ => return false,
        }

        self.advance();
        self.advance();

        let mut line_str = String::new();
        while let Some(c) = self.peek() {
            if c.is_ascii_digit() {
                line_str.push(c);
                self.advance();
            } else {
                break;
            }
        }

        while self.peek() == Some(' ') {
            self.advance();
        }

        let mut file_name = String::new();
        if self.peek() == Some('"') {
            self.advance();
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

        while let Some(c) = self.peek() {
            if c == '\n' {
                self.advance();
                break;
            }
            self.advance();
        }

        if let Ok(new_line) = line_str.parse::<u32>() {
            self.line = new_line;
            self.column = 1;
        }
        if !file_name.is_empty() {
            self.file_name = file_name;
        }

        true
    }

    pub fn next_token(&mut self) -> LexResult<Token> {
        if let Some(tok) = self.pending.pop() {
            return Ok(tok);
        }

        while self.try_cpp_directive() {
        }

        let _crossed_newline = self.skip_whitespace_and_comments()?;

        let start_pos = self.position();
        let start_offset = self.pos as u32;

        let kind = match self.peek() {
            None => {
                let eof_pos = Position::full(
                    self.file_name.as_str(),
                    (self.line + 1) as i32,
                    -1,
                    self.flags.is_stdlib,
                );
                let tok = Token::new(TokenKind::Eof, Span::new(start_offset, start_offset), eof_pos);
                return Ok(tok);
            }
            Some(c) => match c {
                '{' if self.peek_next() == Some('-') && self.peek_next_next() == Some('#') => {
                    self.advance();
                    self.advance();
                    self.advance();
                    TokenKind::LPragma
                }
                '#' if self.peek_next() == Some('-') && self.peek_next_next() == Some('}') => {
                    self.advance();
                    self.advance();
                    self.advance();
                    TokenKind::RPragma
                }
                '(' => { self.advance(); TokenKind::LParen }
                ')' => { self.advance(); TokenKind::RParen }
                ',' => { self.advance(); TokenKind::Comma }
                ';' => { self.advance(); TokenKind::Semi }
                '`' => { self.advance(); TokenKind::Backtick }
                '{' => { self.advance(); TokenKind::LBrace }
                '}' => { self.advance(); TokenKind::RBrace }
                '[' => { self.advance(); TokenKind::LBracket }
                ']' => { self.advance(); TokenKind::RBracket }
                '.' => { self.advance(); TokenKind::Dot }
                '\'' => self.lex_char()?,
                '"' => self.lex_string()?,
                c if c.is_ascii_digit() => self.lex_number()?,
                '$' => self.lex_dollar()?,
                c if is_symbol_char(c) => self.lex_symbol()?,
                c if c.is_ascii_alphabetic() || c == '_' => {
                    let kind = self.lex_identifier()?;
                    let end_offset = self.pos as u32;
                    let col = if kind == TokenKind::KwPackage {
                        start_pos.column as i32 - 1
                    } else {
                        start_pos.column as i32
                    };
                    let pos = Position::full(
                        self.file_name.as_str(),
                        start_pos.line as i32,
                        col,
                        self.flags.is_stdlib,
                    );
                    return Ok(Token::new(kind, Span::new(start_offset, end_offset), pos));
                }
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

        if text == "_" {
            return Ok(TokenKind::Underscore);
        }

        let kind = match text {
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

    fn lex_dollar(&mut self) -> LexResult<TokenKind> {
        let start = self.pos;
        self.advance();

        match self.peek() {
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
            _ => {
                Ok(TokenKind::VarSym("$".into()))
            }
        }
    }

    fn lex_symbol(&mut self) -> LexResult<TokenKind> {
        let start = self.pos;

        while let Some(c) = self.peek() {
            if is_symbol_char(c) {
                self.advance();
            } else {
                break;
            }
        }

        let text = &self.source[start..self.pos];

        let kind = match text {
            "::" => TokenKind::ColonColon,
            ":" => TokenKind::Colon,
            "=" => TokenKind::Equals,
            "@" => TokenKind::At,
            "\\" => TokenKind::Backslash,
            "->" => TokenKind::Arrow,
            "==>" => TokenKind::DArrow,
            "=>" => TokenKind::FatArrow,
            "<-" => TokenKind::LArrow,
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

    fn lex_number(&mut self) -> LexResult<TokenKind> {
        let start = self.pos;
        let start_pos = self.position();

        if self.peek() == Some('0') {
            let next = self.peek_next();
            match next {
                Some('x') | Some('X') => {
                    self.advance();
                    self.advance();
                    return self.lex_integer_with_base(16, start, start_pos, None);
                }
                Some('o') | Some('O') => {
                    self.advance();
                    self.advance();
                    return self.lex_integer_with_base(8, start, start_pos, None);
                }
                Some('b') | Some('B') => {
                    self.advance();
                    self.advance();
                    return self.lex_integer_with_base(2, start, start_pos, None);
                }
                _ => {}
            }
        }

        let mut int_part = String::new();
        while let Some(c) = self.peek() {
            if c.is_ascii_digit() {
                int_part.push(c);
                self.advance();
            } else if c == '_' {
                self.advance();
            } else {
                break;
            }
        }

        if self.peek() == Some('\'') {
            let size = BigInt::from_str_radix(&int_part, 10)
                .map_err(|_| LexError::InvalidInteger {
                    literal: int_part.clone(),
                    position: start_pos.clone(),
                    reason: "invalid size".to_string(),
                    span: Span::new(start as u32, self.pos as u32).into(),
                })?;

            self.advance();
            let format_char = self.peek();
            self.advance();

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

        if self.peek() == Some('.') && self.peek_next().is_some_and(|c| c.is_ascii_digit()) {
            self.advance();

            let mut frac_part = String::new();
            while let Some(c) = self.peek() {
                if c.is_ascii_digit() {
                    frac_part.push(c);
                    self.advance();
                } else {
                    break;
                }
            }

            let exp_part = self.lex_exponent_part();
            let full_str = format!("{int_part}.{frac_part}{exp_part}");
            let value: f64 = full_str.parse().map_err(|_| LexError::InvalidInteger {
                literal: full_str.clone(),
                position: start_pos.clone(),
                reason: "invalid float literal".to_string(),
                span: Span::new(start as u32, self.pos as u32).into(),
            })?;

            return Ok(TokenKind::Float(OrderedFloat::new(value)));
        }

        if matches!(self.peek(), Some('e') | Some('E')) {
            let next = self.peek_next();
            let is_exponent = match next {
                Some(c) if c.is_ascii_digit() => true,
                Some('+') | Some('-') => self.peek_next_next().is_some_and(|c| c.is_ascii_digit()),
                _ => false,
            };
            if is_exponent {
                let exp_part = self.lex_exponent_part();
                let full_str = format!("{int_part}{exp_part}");
                let value: f64 = full_str.parse().map_err(|_| LexError::InvalidInteger {
                    literal: full_str.clone(),
                    position: start_pos.clone(),
                    reason: "invalid float literal".to_string(),
                    span: Span::new(start as u32, self.pos as u32).into(),
                })?;

                return Ok(TokenKind::Float(OrderedFloat::new(value)));
            }
        }

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

    fn lex_exponent_part(&mut self) -> String {
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
        exp_part
    }

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

    fn lex_string(&mut self) -> LexResult<TokenKind> {
        let start_pos = self.position();
        let start = self.pos as u32;

        self.advance();

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

    fn lex_char(&mut self) -> LexResult<TokenKind> {
        let start_pos = self.position();
        let start = self.pos as u32;

        self.advance();

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
        self.advance();

        Ok(TokenKind::Char(c))
    }

    fn lex_escape_sequence(&mut self, start_pos: Position, start: u32) -> LexResult<char> {
        match self.peek() {
            Some('n') => { self.advance(); Ok('\n') }
            Some('t') => { self.advance(); Ok('\t') }
            Some('r') => { self.advance(); Ok('\r') }
            Some('v') => { self.advance(); Ok('\x0B') }
            Some('f') => { self.advance(); Ok('\x0C') }
            Some('\\') => { self.advance(); Ok('\\') }
            Some('"') => { self.advance(); Ok('"') }
            Some('\'') => { self.advance(); Ok('\'') }
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

#[inline]
fn is_id_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_' || c == '\''
}

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

#[inline]
fn is_symbol_char(c: char) -> bool {
    matches!(c,
        '!' | '@' | '#' | '$' | '%' | '&' | '*' | '+' | '.' | '/' |
        '<' | '=' | '>' | '?' | '\\' | '^' | '|' | ':' | '-' | '~' | ','
    ) || (c >= '\u{80}' && is_unicode_symbol(c))
}

fn is_unicode_symbol(c: char) -> bool {
    matches!(c,
        '\u{00A2}'..='\u{00B5}' |
        '\u{00B7}'..='\u{00BF}' |
        '\u{00D7}' | '\u{00F7}'
    ) || (c.is_alphabetic() == false && c.is_alphanumeric() == false && !is_id_char(c))
}
