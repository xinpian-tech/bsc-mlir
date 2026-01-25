//! Lexer for BSV (SystemVerilog-like) syntax.
//!
//! Mirrors `src/comp/SystemVerilogScanner.lhs` from the Haskell implementation.
//! No layout rules - uses explicit begin/end and semicolons.
//!
//! # Architecture
//!
//! Key features:
//! - SystemVerilog-style comments (// and /* */)
//! - SystemVerilog keywords and operators
//! - System identifiers ($display, $finish, etc.)
//! - Bit fill patterns ('0, '1, 'x, 'z)
//! - No layout/indentation rules

mod token;

pub use token::{MixedDigit, SvBit, SvNumber, SvNumericBase, Token, TokenKind};

use bsc_diagnostics::{LexError, Position, Span};
use bsc_syntax::literal::OrderedFloat;
use num_bigint::BigInt;
use num_traits::Num;
use std::str::Chars;

pub type LexResult<T> = Result<T, LexError>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LexerFlags {
    pub is_stdlib: bool,
}

impl Default for LexerFlags {
    fn default() -> Self {
        Self { is_stdlib: false }
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
            column: 1,
            current,
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
                self.column = 1;
            } else if ch == '\t' {
                self.column = ((self.column - 1 + 8) / 8) * 8 + 1;
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

    fn skip_whitespace_and_comments(&mut self) -> LexResult<()> {
        loop {
            match self.peek() {
                Some(' ') | Some('\t') | Some('\r') | Some('\n') | Some('\x0B') | Some('\x0C') => {
                    self.advance();
                }
                Some('/') if self.peek_next() == Some('/') => {
                    self.skip_line_comment();
                }
                Some('/') if self.peek_next() == Some('*') => {
                    self.skip_block_comment()?;
                }
                Some('#') if self.column == 1 && self.peek_next().is_some_and(|c| c == ' ' || c.is_ascii_digit()) => {
                    self.handle_cpp_line_directive();
                }
                Some('`') if self.is_line_directive() => {
                    self.handle_sv_line_directive();
                }
                _ => break,
            }
        }
        Ok(())
    }

    fn is_line_directive(&self) -> bool {
        let rest = &self.source[self.pos..];
        rest.starts_with("`line(") || rest.starts_with("`line ")
    }

    fn handle_sv_line_directive(&mut self) {
        for _ in 0..5 {
            self.advance();
        }

        if self.peek() == Some('(') {
            self.advance();
            let mut file = String::new();
            while let Some(c) = self.peek() {
                if c == ',' {
                    self.advance();
                    break;
                }
                file.push(c);
                self.advance();
            }

            let mut line_str = String::new();
            while let Some(c) = self.peek() {
                if c == ',' {
                    self.advance();
                    break;
                }
                if !c.is_whitespace() {
                    line_str.push(c);
                }
                self.advance();
            }

            let mut col_str = String::new();
            while let Some(c) = self.peek() {
                if c == ',' {
                    self.advance();
                    break;
                }
                if !c.is_whitespace() {
                    col_str.push(c);
                }
                self.advance();
            }

            while let Some(c) = self.peek() {
                if c == ')' {
                    self.advance();
                    break;
                }
                self.advance();
            }

            self.file_name = file;
            if let Ok(n) = line_str.parse::<u32>() {
                self.line = n;
            }
            if let Ok(n) = col_str.parse::<u32>() {
                self.column = n;
            }
        } else {
            while self.peek() == Some(' ') || self.peek() == Some('\t') {
                self.advance();
            }

            let mut line_str = String::new();
            while let Some(c) = self.peek() {
                if c.is_ascii_digit() {
                    line_str.push(c);
                    self.advance();
                } else {
                    break;
                }
            }

            while self.peek() == Some(' ') || self.peek() == Some('\t') {
                self.advance();
            }

            if self.peek() == Some('"') {
                self.advance();
                let mut filename = String::new();
                while let Some(c) = self.peek() {
                    if c == '"' {
                        self.advance();
                        break;
                    }
                    filename.push(c);
                    self.advance();
                }
                self.file_name = filename;
            }

            while let Some(c) = self.peek() {
                if c == '\n' {
                    self.advance();
                    break;
                }
                self.advance();
            }

            if let Ok(n) = line_str.parse::<u32>() {
                self.line = n;
                self.column = 1;
            }
        }
    }

    fn handle_cpp_line_directive(&mut self) {
        self.advance();
        while self.peek() == Some(' ') {
            self.advance();
        }

        let mut line_num_str = String::new();
        while let Some(c) = self.peek() {
            if c.is_ascii_digit() {
                line_num_str.push(c);
                self.advance();
            } else {
                break;
            }
        }

        while self.peek() == Some(' ') {
            self.advance();
        }

        if self.peek() == Some('"') {
            self.advance();
            let mut filename = String::new();
            while let Some(c) = self.peek() {
                if c == '"' {
                    self.advance();
                    break;
                }
                filename.push(c);
                self.advance();
            }
            self.file_name = filename;
        }

        while let Some(c) = self.peek() {
            if c == '\n' {
                self.advance();
                break;
            }
            self.advance();
        }

        if let Ok(n) = line_num_str.parse::<u32>() {
            self.line = n;
            self.column = 1;
        }
    }

    fn skip_line_comment(&mut self) {
        while let Some(c) = self.peek() {
            if c == '\n' {
                self.advance();
                return;
            }
            self.advance();
        }
    }

    fn skip_block_comment(&mut self) -> LexResult<()> {
        let start_pos = self.position();
        let start_offset = self.pos as u32;

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

    fn is_cpp_directive(&self) -> Option<&str> {
        if self.column != 1 {
            return None;
        }
        let rest = &self.source[self.pos..];
        if !rest.starts_with('#') {
            return None;
        }
        let after_hash = &rest[1..];
        const CPP_DIRECTIVES: &[&str] = &[
            "define", "undef", "include", "line", "pragma",
            "endif", "ifdef", "ifndef", "if", "elif", "else",
        ];
        for &dir in CPP_DIRECTIVES {
            if after_hash.starts_with(dir) {
                let after = after_hash.get(dir.len()..).and_then(|s| s.chars().next());
                if after.is_none() || after.unwrap().is_ascii_whitespace() {
                    return Some(dir);
                }
            }
        }
        None
    }

    pub fn next_token(&mut self) -> LexResult<Token> {
        self.skip_whitespace_and_comments()?;

        let start_pos = self.position();
        let start_offset = self.pos as u32;

        if let Some(directive) = self.is_cpp_directive() {
            let dir_string = directive.to_string();
            let dir_len = 1 + dir_string.len();
            for _ in 0..dir_len {
                self.advance();
            }
            return Err(LexError::CppDirective {
                directive: format!("#{dir_string}"),
                position: start_pos,
                span: Span::new(start_offset, self.pos as u32).into(),
            });
        }

        let kind = match self.peek() {
            None => TokenKind::Eof,
            Some(c) => match c {
                '(' if self.peek_next() == Some('*') => {
                    self.advance();
                    self.advance();
                    TokenKind::SymLParenStar
                }
                '*' if self.peek_next() == Some(')') => {
                    self.advance();
                    self.advance();
                    TokenKind::SymStarRParen
                }
                '(' => { self.advance(); TokenKind::SymLParen }
                ')' => { self.advance(); TokenKind::SymRParen }
                ',' => { self.advance(); TokenKind::SymComma }
                ';' => { self.advance(); TokenKind::SymSemi }
                '`' => self.lex_backtick_or_directive()?,
                '{' => { self.advance(); TokenKind::SymLBrace }
                '}' => { self.advance(); TokenKind::SymRBrace }
                '[' if self.peek_next() == Some('*') => {
                    self.advance();
                    self.advance();
                    TokenKind::SymLBracketStar
                }
                '[' if self.peek_next() == Some('-') && self.peek_next_next() == Some('>') => {
                    self.advance();
                    self.advance();
                    self.advance();
                    TokenKind::SymLBracketArrow
                }
                '[' if self.peek_next() == Some('=') => {
                    self.advance();
                    self.advance();
                    TokenKind::SymLBracketEq
                }
                '[' => { self.advance(); TokenKind::SymLBracket }
                ']' => { self.advance(); TokenKind::SymRBracket }
                '.' if self.peek_next() == Some('*') => {
                    self.advance();
                    self.advance();
                    TokenKind::SymDotStar
                }
                '.' if self.peek_next() == Some('.') => {
                    self.advance();
                    self.advance();
                    TokenKind::SymDotDot
                }
                '.' => { self.advance(); TokenKind::SymDot }
                '\'' => self.lex_tick_or_unbased()?,
                '"' => self.lex_string()?,
                c if c.is_ascii_digit() => self.lex_number()?,
                '$' => self.lex_system_id()?,
                c if is_symbol_char(c) => self.lex_symbol()?,
                '\\' => self.lex_escaped_identifier()?,
                c if is_id_start(c) => self.lex_identifier()?,
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

    fn lex_backtick_or_directive(&mut self) -> LexResult<TokenKind> {
        self.advance();

        match self.peek() {
            Some(c) if is_id_start(c) => {
                let start = self.pos;
                while let Some(ch) = self.peek() {
                    if is_id_char(ch) {
                        self.advance();
                    } else {
                        break;
                    }
                }
                let text = &self.source[start..self.pos];
                let directive = format!("`{text}");
                Ok(TokenKind::Directive(directive.into()))
            }
            _ => Ok(TokenKind::SymBacktick),
        }
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

        Ok(match text {
            "alias" => TokenKind::KwAlias,
            "always" => TokenKind::KwAlways,
            "always_comb" => TokenKind::KwAlwaysComb,
            "always_ff" => TokenKind::KwAlwaysFf,
            "always_latch" => TokenKind::KwAlwaysLatch,
            "and" => TokenKind::KwAnd,
            "assert" => TokenKind::KwAssert,
            "assert_strobe" => TokenKind::KwAssertStrobe,
            "assign" => TokenKind::KwAssign,
            "assume" => TokenKind::KwAssume,
            "automatic" => TokenKind::KwAutomatic,
            "before" => TokenKind::KwBefore,
            "begin" => TokenKind::KwBegin,
            "bind" => TokenKind::KwBind,
            "bins" => TokenKind::KwBins,
            "binsof" => TokenKind::KwBinsof,
            "bit" => TokenKind::KwBit,
            "break" => TokenKind::KwBreak,
            "buf" => TokenKind::KwBuf,
            "bufif0" => TokenKind::KwBufif0,
            "bufif1" => TokenKind::KwBufif1,
            "byte" => TokenKind::KwByte,
            "case" => TokenKind::KwCase,
            "casex" => TokenKind::KwCasex,
            "casez" => TokenKind::KwCasez,
            "cell" => TokenKind::KwCell,
            "chandle" => TokenKind::KwChandle,
            "class" => TokenKind::KwClass,
            "clocking" => TokenKind::KwClocking,
            "cmos" => TokenKind::KwCmos,
            "config" => TokenKind::KwConfig,
            "const" => TokenKind::KwConst,
            "constraint" => TokenKind::KwConstraint,
            "context" => TokenKind::KwContext,
            "continue" => TokenKind::KwContinue,
            "cover" => TokenKind::KwCover,
            "covergroup" => TokenKind::KwCovergroup,
            "coverpoint" => TokenKind::KwCoverpoint,
            "cross" => TokenKind::KwCross,
            "deassign" => TokenKind::KwDeassign,
            "default" => TokenKind::KwDefault,
            "defparam" => TokenKind::KwDefparam,
            "design" => TokenKind::KwDesign,
            "disable" => TokenKind::KwDisable,
            "dist" => TokenKind::KwDist,
            "do" => TokenKind::KwDo,
            "edge" => TokenKind::KwEdge,
            "else" => TokenKind::KwElse,
            "end" => TokenKind::KwEnd,
            "endcase" => TokenKind::KwEndcase,
            "endclass" => TokenKind::KwEndclass,
            "endclocking" => TokenKind::KwEndclocking,
            "endconfig" => TokenKind::KwEndconfig,
            "endfunction" => TokenKind::KwEndfunction,
            "endgenerate" => TokenKind::KwEndgenerate,
            "endgroup" => TokenKind::KwEndgroup,
            "endinterface" => TokenKind::KwEndinterface,
            "endmodule" => TokenKind::KwEndmodule,
            "endpackage" => TokenKind::KwEndpackage,
            "endprimitive" => TokenKind::KwEndprimitive,
            "endprogram" => TokenKind::KwEndprogram,
            "endproperty" => TokenKind::KwEndproperty,
            "endspecify" => TokenKind::KwEndspecify,
            "endsequence" => TokenKind::KwEndsequence,
            "endtable" => TokenKind::KwEndtable,
            "endtask" => TokenKind::KwEndtask,
            "enum" => TokenKind::KwEnum,
            "event" => TokenKind::KwEvent,
            "expect" => TokenKind::KwExpect,
            "export" => TokenKind::KwExport,
            "extends" => TokenKind::KwExtends,
            "extern" => TokenKind::KwExtern,
            "final" => TokenKind::KwFinal,
            "first_match" => TokenKind::KwFirstMatch,
            "for" => TokenKind::KwFor,
            "force" => TokenKind::KwForce,
            "foreach" => TokenKind::KwForeach,
            "forever" => TokenKind::KwForever,
            "fork" => TokenKind::KwFork,
            "forkjoin" => TokenKind::KwForkjoin,
            "function" => TokenKind::KwFunction,
            "generate" => TokenKind::KwGenerate,
            "genvar" => TokenKind::KwGenvar,
            "highz0" => TokenKind::KwHighz0,
            "highz1" => TokenKind::KwHighz1,
            "if" => TokenKind::KwIf,
            "iff" => TokenKind::KwIff,
            "ifnone" => TokenKind::KwIfnone,
            "ignore_bins" => TokenKind::KwIgnoreBins,
            "illegal_bins" => TokenKind::KwIllegalBins,
            "import" => TokenKind::KwImport,
            "incdir" => TokenKind::KwIncdir,
            "include" => TokenKind::KwInclude,
            "initial" => TokenKind::KwInitial,
            "inout" => TokenKind::KwInout,
            "input" => TokenKind::KwInput,
            "inside" => TokenKind::KwInside,
            "instance" => TokenKind::KwInstance,
            "int" => TokenKind::KwInt,
            "integer" => TokenKind::KwInteger,
            "interface" => TokenKind::KwInterface,
            "intersect" => TokenKind::KwIntersect,
            "join" => TokenKind::KwJoin,
            "join_any" => TokenKind::KwJoinAny,
            "join_none" => TokenKind::KwJoinNone,
            "large" => TokenKind::KwLarge,
            "liblist" => TokenKind::KwLiblist,
            "library" => TokenKind::KwLibrary,
            "local" => TokenKind::KwLocal,
            "localparam" => TokenKind::KwLocalparam,
            "logic" => TokenKind::KwLogic,
            "longint" => TokenKind::KwLongint,
            "macromodule" => TokenKind::KwMacromodule,
            "match" => TokenKind::KwMatch,
            "matches" => TokenKind::KwMatches,
            "medium" => TokenKind::KwMedium,
            "modport" => TokenKind::KwModport,
            "module" => TokenKind::KwModule,
            "nand" => TokenKind::KwNand,
            "negedge" => TokenKind::KwNegedge,
            "new" => TokenKind::KwNew,
            "nmos" => TokenKind::KwNmos,
            "nor" => TokenKind::KwNor,
            "noshowcancelled" => TokenKind::KwNoshowcancelled,
            "not" => TokenKind::KwNot,
            "notif0" => TokenKind::KwNotif0,
            "notif1" => TokenKind::KwNotif1,
            "null" => TokenKind::KwNull,
            "or" => TokenKind::KwOr,
            "output" => TokenKind::KwOutput,
            "package" => TokenKind::KwPackage,
            "packed" => TokenKind::KwPacked,
            "parameter" => TokenKind::KwParameter,
            "pmos" => TokenKind::KwPmos,
            "posedge" => TokenKind::KwPosedge,
            "primitive" => TokenKind::KwPrimitive,
            "priority" => TokenKind::KwPriority,
            "program" => TokenKind::KwProgram,
            "property" => TokenKind::KwProperty,
            "protected" => TokenKind::KwProtected,
            "pull0" => TokenKind::KwPull0,
            "pull1" => TokenKind::KwPull1,
            "pulldown" => TokenKind::KwPulldown,
            "pullup" => TokenKind::KwPullup,
            "pulsestyle_onevent" => TokenKind::KwPulsestyleOnevent,
            "pulsestyle_ondetect" => TokenKind::KwPulsestyleOndetect,
            "pure" => TokenKind::KwPure,
            "rand" => TokenKind::KwRand,
            "randc" => TokenKind::KwRandc,
            "randcase" => TokenKind::KwRandcase,
            "randsequence" => TokenKind::KwRandsequence,
            "rcmos" => TokenKind::KwRcmos,
            "real" => TokenKind::KwReal,
            "realtime" => TokenKind::KwRealtime,
            "ref" => TokenKind::KwRef,
            "reg" => TokenKind::KwReg,
            "release" => TokenKind::KwRelease,
            "repeat" => TokenKind::KwRepeat,
            "return" => TokenKind::KwReturn,
            "rnmos" => TokenKind::KwRnmos,
            "rpmos" => TokenKind::KwRpmos,
            "rtran" => TokenKind::KwRtran,
            "rtranif0" => TokenKind::KwRtranif0,
            "rtranif1" => TokenKind::KwRtranif1,
            "scalared" => TokenKind::KwScalared,
            "sequence" => TokenKind::KwSequence,
            "shortint" => TokenKind::KwShortint,
            "shortreal" => TokenKind::KwShortreal,
            "showcancelled" => TokenKind::KwShowcancelled,
            "signed" => TokenKind::KwSigned,
            "small" => TokenKind::KwSmall,
            "solve" => TokenKind::KwSolve,
            "specify" => TokenKind::KwSpecify,
            "specparam" => TokenKind::KwSpecparam,
            "static" => TokenKind::KwStatic,
            "string" => TokenKind::KwString,
            "strong0" => TokenKind::KwStrong0,
            "strong1" => TokenKind::KwStrong1,
            "struct" => TokenKind::KwStruct,
            "super" => TokenKind::KwSuper,
            "supply0" => TokenKind::KwSupply0,
            "supply1" => TokenKind::KwSupply1,
            "table" => TokenKind::KwTable,
            "tagged" => TokenKind::KwTagged,
            "task" => TokenKind::KwTask,
            "this" => TokenKind::KwThis,
            "throughout" => TokenKind::KwThroughout,
            "time" => TokenKind::KwTime,
            "timeprecision" => TokenKind::KwTimeprecision,
            "timeunit" => TokenKind::KwTimeunit,
            "tran" => TokenKind::KwTran,
            "tranif0" => TokenKind::KwTranif0,
            "tranif1" => TokenKind::KwTranif1,
            "tri" => TokenKind::KwTri,
            "tri0" => TokenKind::KwTri0,
            "tri1" => TokenKind::KwTri1,
            "triand" => TokenKind::KwTriand,
            "trior" => TokenKind::KwTrior,
            "trireg" => TokenKind::KwTrireg,
            "type" => TokenKind::KwType,
            "typedef" => TokenKind::KwTypedef,
            "union" => TokenKind::KwUnion,
            "unique" => TokenKind::KwUnique,
            "unsigned" => TokenKind::KwUnsigned,
            "use" => TokenKind::KwUse,
            "var" => TokenKind::KwVar,
            "vectored" => TokenKind::KwVectored,
            "virtual" => TokenKind::KwVirtual,
            "void" => TokenKind::KwVoid,
            "wait" => TokenKind::KwWait,
            "wait_order" => TokenKind::KwWaitOrder,
            "wand" => TokenKind::KwWand,
            "weak0" => TokenKind::KwWeak0,
            "weak1" => TokenKind::KwWeak1,
            "while" => TokenKind::KwWhile,
            "wildcard" => TokenKind::KwWildcard,
            "wire" => TokenKind::KwWire,
            "with" => TokenKind::KwWith,
            "within" => TokenKind::KwWithin,
            "wor" => TokenKind::KwWor,
            "xnor" => TokenKind::KwXnor,
            "xor" => TokenKind::KwXor,
            "action" => TokenKind::KwAction,
            "endaction" => TokenKind::KwEndaction,
            "actionvalue" => TokenKind::KwActionvalue,
            "endactionvalue" => TokenKind::KwEndactionvalue,
            "deriving" => TokenKind::KwDeriving,
            "endinstance" => TokenKind::KwEndinstance,
            "let" => TokenKind::KwLet,
            "method" => TokenKind::KwMethod,
            "endmethod" => TokenKind::KwEndmethod,
            "par" => TokenKind::KwPar,
            "endpar" => TokenKind::KwEndpar,
            "abortif" => TokenKind::KwAbortif,
            "provisos" => TokenKind::KwProvisos,
            "rule" => TokenKind::KwRule,
            "endrule" => TokenKind::KwEndrule,
            "rules" => TokenKind::KwRules,
            "endrules" => TokenKind::KwEndrules,
            "seq" => TokenKind::KwSeq,
            "endseq" => TokenKind::KwEndseq,
            "goto" => TokenKind::KwGoto,
            "typeclass" => TokenKind::KwTypeclass,
            "endtypeclass" => TokenKind::KwEndtypeclass,
            "valueof" => TokenKind::KwValueof,
            "valueOf" => TokenKind::KwValueOf,
            "stringof" => TokenKind::KwStringof,
            "stringOf" => TokenKind::KwStringOf,
            "clocked_by" => TokenKind::KwClockedBy,
            "reset_by" => TokenKind::KwResetBy,
            "powered_by" => TokenKind::KwPoweredBy,
            "Action" => TokenKind::KwActionType,
            "ActionValue" => TokenKind::KwActionValueType,
            _ => TokenKind::Id(text.into()),
        })
    }

    fn lex_escaped_identifier(&mut self) -> LexResult<TokenKind> {
        self.advance();
        let start = self.pos;
        while let Some(c) = self.peek() {
            if c.is_whitespace() {
                break;
            }
            self.advance();
        }
        let text = &self.source[start..self.pos];
        Ok(TokenKind::Id(text.into()))
    }

    fn lex_system_id(&mut self) -> LexResult<TokenKind> {
        let start = self.pos;
        self.advance();

        match self.peek() {
            Some(c) if is_id_char(c) => {
                while let Some(c) = self.peek() {
                    if is_id_char(c) {
                        self.advance();
                    } else {
                        break;
                    }
                }
                let text = &self.source[start..self.pos];
                Ok(TokenKind::SystemId(text.into()))
            }
            _ => Ok(TokenKind::SymDollar),
        }
    }

    fn lex_symbol(&mut self) -> LexResult<TokenKind> {
        let c1 = self.peek();
        let c2 = self.peek_next();
        let c3 = self.peek_next_next();

        fn peek4(lexer: &Lexer) -> Option<char> {
            let mut iter = lexer.chars.clone();
            iter.next();
            iter.next();
            iter.next()
        }

        if c1 == Some('&') && c2 == Some('&') && c3 == Some('&') {
            self.advance(); self.advance(); self.advance();
            return Ok(TokenKind::SymAndAndAnd);
        }
        if c1 == Some('>') && c2 == Some('>') && c3 == Some('>') {
            if peek4(self) == Some('=') {
                self.advance(); self.advance(); self.advance(); self.advance();
                return Ok(TokenKind::SymGtGtGtEq);
            }
            self.advance(); self.advance(); self.advance();
            return Ok(TokenKind::SymGtGtGt);
        }
        if c1 == Some('<') && c2 == Some('<') && c3 == Some('<') {
            if peek4(self) == Some('=') {
                self.advance(); self.advance(); self.advance(); self.advance();
                return Ok(TokenKind::SymLtLtLtEq);
            }
            self.advance(); self.advance(); self.advance();
            return Ok(TokenKind::SymLtLtLt);
        }
        if c1 == Some('=') && c2 == Some('=') && c3 == Some('=') {
            self.advance(); self.advance(); self.advance();
            return Ok(TokenKind::SymEqEqEq);
        }
        if c1 == Some('!') && c2 == Some('=') && c3 == Some('=') {
            self.advance(); self.advance(); self.advance();
            return Ok(TokenKind::SymBangEqEq);
        }
        if c1 == Some('=') && c2 == Some('?') && c3 == Some('=') {
            self.advance(); self.advance(); self.advance();
            return Ok(TokenKind::SymEqQuestionEq);
        }
        if c1 == Some('!') && c2 == Some('?') && c3 == Some('=') {
            self.advance(); self.advance(); self.advance();
            return Ok(TokenKind::SymBangQuestionEq);
        }
        if c1 == Some('|') && c2 == Some('=') && c3 == Some('>') {
            self.advance(); self.advance(); self.advance();
            return Ok(TokenKind::SymPipeFatArrow);
        }
        if c1 == Some('|') && c2 == Some('-') && c3 == Some('>') {
            self.advance(); self.advance(); self.advance();
            return Ok(TokenKind::SymPipeArrow);
        }
        if c1 == Some('<') && c2 == Some('<') && c3 == Some('=') {
            self.advance(); self.advance(); self.advance();
            return Ok(TokenKind::SymLtLtEq);
        }
        if c1 == Some('>') && c2 == Some('>') && c3 == Some('=') {
            self.advance(); self.advance(); self.advance();
            return Ok(TokenKind::SymGtGtEq);
        }

        let kind = match (c1, c2) {
            (Some(':'), Some(':')) => { self.advance(); self.advance(); TokenKind::SymColonColon }
            (Some('='), Some('=')) => { self.advance(); self.advance(); TokenKind::SymEqEq }
            (Some('!'), Some('=')) => { self.advance(); self.advance(); TokenKind::SymBangEq }
            (Some('&'), Some('&')) => { self.advance(); self.advance(); TokenKind::SymAndAnd }
            (Some('|'), Some('|')) => { self.advance(); self.advance(); TokenKind::SymPipePipe }
            (Some('*'), Some('*')) => { self.advance(); self.advance(); TokenKind::SymStarStar }
            (Some('<'), Some('=')) => { self.advance(); self.advance(); TokenKind::SymLtEq }
            (Some('>'), Some('=')) => { self.advance(); self.advance(); TokenKind::SymGtEq }
            (Some('<'), Some('<')) => { self.advance(); self.advance(); TokenKind::SymLtLt }
            (Some('>'), Some('>')) => { self.advance(); self.advance(); TokenKind::SymGtGt }
            (Some('+'), Some('+')) => { self.advance(); self.advance(); TokenKind::SymPlusPlus }
            (Some('-'), Some('-')) => { self.advance(); self.advance(); TokenKind::SymMinusMinus }
            (Some('+'), Some('=')) => { self.advance(); self.advance(); TokenKind::SymPlusEq }
            (Some('-'), Some('=')) => { self.advance(); self.advance(); TokenKind::SymMinusEq }
            (Some('/'), Some('=')) => { self.advance(); self.advance(); TokenKind::SymSlashEq }
            (Some('%'), Some('=')) => { self.advance(); self.advance(); TokenKind::SymPercentEq }
            (Some('&'), Some('=')) => { self.advance(); self.advance(); TokenKind::SymAndEq }
            (Some('|'), Some('=')) => { self.advance(); self.advance(); TokenKind::SymPipeEq }
            (Some('^'), Some('=')) => { self.advance(); self.advance(); TokenKind::SymCaretEq }
            (Some('#'), Some('#')) => { self.advance(); self.advance(); TokenKind::SymHashHash }
            (Some('-'), Some('>')) => { self.advance(); self.advance(); TokenKind::SymArrow }
            (Some('<'), Some('-')) => { self.advance(); self.advance(); TokenKind::SymLArrow }
            (Some('<'), Some('>')) => { self.advance(); self.advance(); TokenKind::SymLtGt }
            (Some('~'), Some('&')) => { self.advance(); self.advance(); TokenKind::SymTildeAnd }
            (Some('~'), Some('|')) => { self.advance(); self.advance(); TokenKind::SymTildePipe }
            (Some('~'), Some('^')) => { self.advance(); self.advance(); TokenKind::SymTildeCaret }
            (Some('^'), Some('~')) => { self.advance(); self.advance(); TokenKind::SymCaretTilde }
            (Some('+'), _) => { self.advance(); TokenKind::SymPlus }
            (Some('-'), _) => { self.advance(); TokenKind::SymMinus }
            (Some('!'), _) => { self.advance(); TokenKind::SymBang }
            (Some('~'), _) => { self.advance(); TokenKind::SymTilde }
            (Some('&'), _) => { self.advance(); TokenKind::SymAnd }
            (Some('|'), _) => { self.advance(); TokenKind::SymPipe }
            (Some('^'), _) => { self.advance(); TokenKind::SymCaret }
            (Some('*'), _) => { self.advance(); TokenKind::SymStar }
            (Some('/'), _) => { self.advance(); TokenKind::SymSlash }
            (Some('%'), _) => { self.advance(); TokenKind::SymPercent }
            (Some('<'), _) => { self.advance(); TokenKind::SymLt }
            (Some('>'), _) => { self.advance(); TokenKind::SymGt }
            (Some(':'), _) => { self.advance(); TokenKind::SymColon }
            (Some('='), _) => { self.advance(); TokenKind::SymEq }
            (Some('?'), _) => { self.advance(); TokenKind::SymQuestion }
            (Some('#'), _) => { self.advance(); TokenKind::SymHash }
            (Some('@'), _) => { self.advance(); TokenKind::Id("@".into()) }
            _ => {
                self.advance();
                TokenKind::Id(self.source[self.pos - 1..self.pos].into())
            }
        };

        Ok(kind)
    }

    fn lex_tick_or_unbased(&mut self) -> LexResult<TokenKind> {
        self.advance();

        match self.peek() {
            Some(c) if c != '_' && is_bin_xz_underscore(c) => {
                self.advance();
                while self.peek() == Some('_') {
                    self.advance();
                }
                Ok(TokenKind::Number {
                    value: SvNumber::Repeated(char_to_sv_bit(c)),
                    bitwidth: None,
                    base: None,
                    signed: false,
                })
            }
            Some(c1) => {
                let signed = c1 == 's' || c1 == 'S';
                let base_char = if signed { self.peek_next() } else { Some(c1) };
                let base = base_char.and_then(|c| match c.to_ascii_lowercase() {
                    'd' => Some(10),
                    'b' => Some(2),
                    'o' => Some(8),
                    'h' => Some(16),
                    _ => None,
                });
                if base.is_some() {
                    Ok(TokenKind::SymTick)
                } else {
                    Ok(TokenKind::SymTick)
                }
            }
            None => Ok(TokenKind::SymTick),
        }
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
                    return self.lex_unsized_based_number(16, start, start_pos);
                }
                Some('o') | Some('O') => {
                    self.advance();
                    self.advance();
                    return self.lex_unsized_based_number(8, start, start_pos);
                }
                Some('b') | Some('B') => {
                    self.advance();
                    self.advance();
                    return self.lex_unsized_based_number(2, start, start_pos);
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
            let next = self.peek_next();
            let signed = next == Some('s') || next == Some('S');
            let format_char = if signed { self.peek_next_next() } else { next };

            let base = match format_char {
                Some('h') | Some('H') => Some(16),
                Some('d') | Some('D') => Some(10),
                Some('b') | Some('B') => Some(2),
                Some('o') | Some('O') => Some(8),
                _ => None,
            };

            if let Some(base) = base {
                let size = BigInt::from_str_radix(&int_part, 10)
                    .map_err(|_| LexError::InvalidInteger {
                        literal: int_part.clone(),
                        position: start_pos.clone(),
                        reason: "invalid size".to_string(),
                        span: Span::new(start as u32, self.pos as u32).into(),
                    })?;

                self.advance();
                if signed {
                    self.advance();
                }
                self.advance();

                while matches!(self.peek(), Some(' ') | Some('\t')) {
                    self.advance();
                }

                return self.lex_sized_based_number(base, start, start_pos, Some(size));
            }
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

    fn lex_sized_based_number(
        &mut self,
        base: u32,
        start: usize,
        start_pos: Position,
        size: Option<BigInt>,
    ) -> LexResult<TokenKind> {
        let sv_base = match base {
            2 => SvNumericBase::Bin,
            8 => SvNumericBase::Oct,
            10 => SvNumericBase::Dec,
            16 => SvNumericBase::Hex,
            _ => SvNumericBase::Dec,
        };

        if base == 10 {
            if let Some(c) = self.peek() {
                if is_xz_digit(c) {
                    self.advance();
                    while self.peek() == Some('_') {
                        self.advance();
                    }
                    return Ok(TokenKind::Number {
                        value: SvNumber::Repeated(char_to_sv_bit(c)),
                        bitwidth: size,
                        base: Some(sv_base),
                        signed: false,
                    });
                }
            }
        }

        let accept_xz = base != 10;

        let is_ok_digit = |c: char| -> bool {
            c == '_' || is_digit_for_base(c, base) || (accept_xz && is_xz_digit(c))
        };

        let digit_start = self.pos;

        while let Some(c) = self.peek() {
            if is_ok_digit(c) {
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

        let has_special = digits.chars().any(is_xz_digit);

        let sv_number = if has_special {
            let grouped = group_digits(&digits);
            let pairs: Vec<(u64, MixedDigit)> = grouped
                .into_iter()
                .map(|group| {
                    let count = group.len() as u64;
                    let first = group.chars().next().unwrap();
                    if is_xz_digit(first) {
                        (count, MixedDigit::Bit(char_to_sv_bit(first)))
                    } else {
                        let val = BigInt::from_str_radix(&group, base).unwrap_or_default();
                        (count, MixedDigit::Value(val))
                    }
                })
                .collect();
            SvNumber::Mixed(pairs)
        } else {
            let value = BigInt::from_str_radix(&digits, base).map_err(|_| LexError::InvalidInteger {
                literal: self.source[start..self.pos].to_string(),
                position: start_pos.clone(),
                reason: format!("invalid base-{base} integer literal"),
                span: Span::new(start as u32, self.pos as u32).into(),
            })?;
            SvNumber::Integer(value)
        };

        Ok(TokenKind::Number {
            value: sv_number,
            bitwidth: size,
            base: Some(sv_base),
            signed: false,
        })
    }

    fn lex_unsized_based_number(
        &mut self,
        base: u32,
        start: usize,
        start_pos: Position,
    ) -> LexResult<TokenKind> {
        let sv_base = match base {
            2 => SvNumericBase::Bin,
            8 => SvNumericBase::Oct,
            10 => SvNumericBase::Dec,
            16 => SvNumericBase::Hex,
            _ => SvNumericBase::Dec,
        };

        let is_ok_digit = |c: char| -> bool {
            c == '_' || is_digit_for_base(c, base) || is_xz_digit(c)
        };

        let digit_start = self.pos;

        while let Some(c) = self.peek() {
            if is_ok_digit(c) {
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

        let has_special = digits.chars().any(is_xz_digit);

        let sv_number = if has_special {
            let grouped = group_digits(&digits);
            let pairs: Vec<(u64, MixedDigit)> = grouped
                .into_iter()
                .map(|group| {
                    let count = group.len() as u64;
                    let first = group.chars().next().unwrap();
                    if is_xz_digit(first) {
                        (count, MixedDigit::Bit(char_to_sv_bit(first)))
                    } else {
                        let val = BigInt::from_str_radix(&group, base).unwrap_or_default();
                        (count, MixedDigit::Value(val))
                    }
                })
                .collect();
            SvNumber::Mixed(pairs)
        } else {
            let value = BigInt::from_str_radix(&digits, base).map_err(|_| LexError::InvalidInteger {
                literal: self.source[start..self.pos].to_string(),
                position: start_pos.clone(),
                reason: format!("invalid base-{base} integer literal"),
                span: Span::new(start as u32, self.pos as u32).into(),
            })?;
            SvNumber::Integer(value)
        };

        Ok(TokenKind::Number {
            value: sv_number,
            bitwidth: None,
            base: Some(sv_base),
            signed: false,
        })
    }

    fn lex_string(&mut self) -> LexResult<TokenKind> {
        let start_pos = self.position();
        let start = self.pos as u32;

        self.advance();

        let mut value = String::new();
        loop {
            match self.peek() {
                None => {
                    return Err(LexError::UnterminatedString {
                        position: start_pos.clone(),
                        span: Span::new(start, self.pos as u32).into(),
                    });
                }
                Some('\n') => {
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
                    if self.peek() == Some('\n') {
                        self.advance();
                        continue;
                    }
                    let escaped = self.lex_escape_sequence(start_pos.clone(), start)?;
                    value.push(escaped);
                }
                Some(c) => {
                    value.push(c);
                    self.advance();
                }
            }
        }

        Ok(TokenKind::String(value))
    }

    fn lex_escape_sequence(&mut self, start_pos: Position, start: u32) -> LexResult<char> {
        match self.peek() {
            Some('n') => { self.advance(); Ok('\n') }
            Some('t') => { self.advance(); Ok('\t') }
            Some('\\') => { self.advance(); Ok('\\') }
            Some('"') => { self.advance(); Ok('"') }
            Some('v') => { self.advance(); Ok('\x0B') }
            Some('f') => { self.advance(); Ok('\x0C') }
            Some('a') => { self.advance(); Ok('\x07') }
            Some('x') => {
                self.advance();
                let d1 = self.peek();
                let d2 = self.peek_next();
                match (d1, d2) {
                    (Some(c1), Some(c2)) if c1.is_ascii_hexdigit() && c2.is_ascii_hexdigit() => {
                        self.advance();
                        self.advance();
                        let code = c1.to_digit(16).unwrap() * 16 + c2.to_digit(16).unwrap();
                        Ok(char::from_u32(code).unwrap_or('\0'))
                    }
                    _ => Err(LexError::InvalidEscape {
                        sequence: "x".to_string(),
                        position: start_pos.clone(),
                        span: Span::new(start, self.pos as u32).into(),
                    }),
                }
            }
            Some(d1) if d1.is_ascii_digit() && d1 < '8' => {
                let d2 = self.peek_next();
                let d3 = self.peek_next_next();
                match (d2, d3) {
                    (Some(c2), Some(c3)) if c2.is_ascii_digit() && c2 < '8' && c3.is_ascii_digit() && c3 < '8' => {
                        self.advance();
                        self.advance();
                        self.advance();
                        let code = d1.to_digit(8).unwrap() * 64 + c2.to_digit(8).unwrap() * 8 + c3.to_digit(8).unwrap();
                        Ok(char::from_u32(code).unwrap_or('\0'))
                    }
                    _ => Err(LexError::InvalidEscape {
                        sequence: d1.to_string(),
                        position: start_pos.clone(),
                        span: Span::new(start, self.pos as u32).into(),
                    }),
                }
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
fn is_id_start(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_'
}

#[inline]
fn is_id_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_' || c == '$'
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
        '!' | '#' | '%' | '&' | '*' | '+' | '/' |
        '<' | '=' | '>' | '?' | '^' | '|' | ':' | '-' | '~'
    )
}

#[inline]
fn is_xz_digit(c: char) -> bool {
    matches!(c, 'x' | 'X' | 'z' | 'Z' | '?')
}

#[inline]
fn is_bin_xz_underscore(c: char) -> bool {
    matches!(c, '0' | '1' | 'X' | 'x' | 'Z' | 'z' | '?' | '_')
}

fn char_to_sv_bit(c: char) -> SvBit {
    match c {
        '0' => SvBit::Zero,
        '1' => SvBit::One,
        'x' | 'X' => SvBit::X,
        'z' | 'Z' => SvBit::Z,
        '?' => SvBit::DontCare,
        _ => SvBit::Zero,
    }
}

fn group_digits(digits: &str) -> Vec<String> {
    let mut groups = Vec::new();
    let mut current_group = String::new();
    let mut in_special = false;

    for c in digits.chars() {
        let is_special = is_xz_digit(c);

        if current_group.is_empty() {
            in_special = is_special;
            current_group.push(c);
        } else if is_special == in_special && (!is_special || current_group.chars().next() == Some(c) || (matches!(c, 'x' | 'X') && matches!(current_group.chars().next(), Some('x') | Some('X'))) || (matches!(c, 'z' | 'Z' | '?') && matches!(current_group.chars().next(), Some('z') | Some('Z') | Some('?')))) {
            current_group.push(c);
        } else {
            groups.push(current_group);
            current_group = c.to_string();
            in_special = is_special;
        }
    }

    if !current_group.is_empty() {
        groups.push(current_group);
    }

    groups
}
