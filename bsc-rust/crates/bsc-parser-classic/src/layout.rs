//! Layout rule processing for Classic Bluespec.
//!
//! This module implements layout rules (indentation-sensitive parsing) that are used
//! in Classic Bluespec syntax. The layout rules mirror those in `src/comp/Parser/Classic/CParser.hs`.
//!
//! # How Layout Works
//!
//! Layout rules insert implicit braces (`{_`, `}_`) and semicolons (`;_`) based on
//! indentation. This allows writing:
//!
//! ```text
//! package Foo where
//!   import Bar
//!   x = 1
//! ```
//!
//! instead of:
//!
//! ```text
//! package Foo where {
//!   import Bar;
//!   x = 1
//! }
//! ```
//!
//! # Layout Triggers
//!
//! Layout is triggered after these keywords:
//! - `where` (in packages, classes, instances)
//! - `let`, `letseq` (in expressions)
//! - `of` (in case expressions)
//! - `do` (in do notation)
//! - `rules` (in modules)
//! - `action` (for action blocks)
//!
//! When a layout trigger is encountered:
//! 1. If the next token is `{`, use explicit braces (no layout)
//! 2. Otherwise, insert an implicit `{_`
//! 3. Track the column of the first token in the block
//! 4. At the same column, insert `;_`
//! 5. At a lesser column, insert `}_`

use bsc_diagnostics::{Position, Span};
use bsc_lexer_classic::{Token, TokenKind};

/// Create a layout token inheriting position from another token.
fn make_layout_token(kind: TokenKind, from: &Token) -> Token {
    Token::new(kind, from.span, from.position.clone())
}

/// Create a layout token with span and position.
fn make_layout_token_at(kind: TokenKind, span: Span, pos: &Position) -> Token {
    Token::new(kind, span, pos.clone())
}

/// Keywords that trigger layout unconditionally.
/// These keywords start a block and layout processing inserts implicit braces.
fn is_layout_trigger(kind: &TokenKind) -> bool {
    matches!(
        kind,
        TokenKind::KwWhere
            | TokenKind::KwLet
            | TokenKind::KwLetSeq
            | TokenKind::KwOf
            | TokenKind::KwDo
            | TokenKind::KwRules
            | TokenKind::KwAction
    )
}

/// Check if this is a module keyword (conditional layout - skip if followed by verilog)
fn is_module_layout_trigger(kind: &TokenKind) -> bool {
    matches!(kind, TokenKind::KwModule)
}

/// Check if this is an interface keyword (special delayed layout)
/// Interface uses delayed layout insertion - the brace is inserted AFTER the optional
/// type name on the same line, not immediately after the interface keyword.
fn is_interface_layout_trigger(kind: &TokenKind) -> bool {
    matches!(kind, TokenKind::KwInterface)
}


/// Check if tokens at idx look like interface body fields.
/// Body fields must be:
/// 1. Indented more than the interface keyword (column > trigger_col)
/// 2. Look like a field definition:
///    - Type signature: identifier ::
///    - Method impl: identifier = or identifier identifier (args) or identifier _ (pattern)
fn looks_like_body_field(tokens: &[Token], idx: usize, trigger_col: i32) -> bool {
    if idx + 1 >= tokens.len() {
        return false;
    }

    let tok = &tokens[idx];
    let next = &tokens[idx + 1];

    // Body fields must be indented relative to interface keyword position
    if tok.position.column <= trigger_col {
        return false;
    }

    // Check if it's a VarId followed by ::, =, another identifier, underscore (pattern), or ( (pattern arg)
    if matches!(tok.kind, TokenKind::VarId(_)) {
        if matches!(
            next.kind,
            TokenKind::ColonColon | TokenKind::Equals | TokenKind::VarId(_) | TokenKind::Underscore | TokenKind::LParen
        ) {
            return true;
        }
    }

    false
}


/// Get the column of a token's start position.
fn get_column(token: &Token) -> i32 {
    token.position.column
}

/// Get the line of a token.
fn get_line(token: &Token) -> i32 {
    token.position.line
}

/// Tracks whether layout expectation is unconditional or conditional.
#[derive(Clone, Copy, PartialEq, Debug)]
enum LayoutExpect {
    None,
    /// Unconditional layout trigger (where, let, do, etc.)
    /// trigger_col is the column of the trigger keyword (used for empty block detection per Haskell BSC)
    Unconditional { trigger_line: i32, trigger_col: i32 },
    /// Module layout trigger - does NOT trigger if next token is 'verilog'
    Module { trigger_line: i32, trigger_col: i32 },
    /// Interface delayed - waiting for tokens on same line to pass, then insert layout
    /// when we see a body field on a new indented line. Set after seeing 'interface'.
    InterfaceDelayed { trigger_line: i32, trigger_col: i32 },
}

/// Process layout rules on a token stream.
///
/// This function takes a raw token stream and returns a new token stream with
/// layout tokens (`LBraceLayout`, `RBraceLayout`, `SemiLayout`) inserted
/// according to the layout rules.
pub fn process_layout(tokens: Vec<Token>) -> Vec<Token> {
    let mut result = Vec::new();
    let mut layout_stack: Vec<i32> = Vec::new(); // Stack of column positions
    let mut explicit_brace_depth = 0; // Track explicit braces
    let mut expect_layout = LayoutExpect::None;
    let mut last_line = 0i32;
    let mut in_struct_def = false; // Track if we're in a struct/data/interface type definition

    let mut i = 0;
    while i < tokens.len() {
        let token = &tokens[i];
        let current_column = get_column(&token);
        let current_line = get_line(&token);


        // Handle InterfaceDelayed specially - we're waiting for tokens on the same line
        // to pass, then insert layout brace when we see body content on a new line
        if let LayoutExpect::InterfaceDelayed { trigger_line, trigger_col } = expect_layout {
            if token.kind == TokenKind::LBrace {
                // Explicit brace - cancel delayed layout
                expect_layout = LayoutExpect::None;
                explicit_brace_depth += 1;
                result.push(token.clone());
                i += 1;
                continue;
            }

            if current_line == trigger_line {
                // Still on same line as interface keyword
                if token.kind == TokenKind::Equals {
                    // It's an interface type definition (interface Foo n = ...),
                    // add the = token first, then trigger layout for the next token
                    result.push(token.clone());
                    last_line = current_line;
                    i += 1;
                    expect_layout = LayoutExpect::Unconditional {
                        trigger_line: current_line,
                        trigger_col: 0,
                    };
                    continue;
                } else {
                    // Keep waiting - output token and continue
                    result.push(token.clone());
                    last_line = current_line;
                    i += 1;
                    continue;
                }
            } else {
                // New line - check if this looks like a body field
                if looks_like_body_field(&tokens, i, trigger_col) {
                    // Insert layout brace now, then process this token
                    result.push(make_layout_token(TokenKind::LayoutLBrace, token));
                    layout_stack.push(current_column);
                    last_line = current_line; // Prevent semicolon before first token
                    expect_layout = LayoutExpect::None;
                    // Fall through to normal processing of this token
                } else {
                    // Not a body field, cancel layout
                    expect_layout = LayoutExpect::None;
                    // Fall through to normal processing
                }
            }
        }

        // Check if we're expecting a layout block (non-interface cases)
        if expect_layout != LayoutExpect::None {
            let saved_expect = expect_layout;
            expect_layout = LayoutExpect::None;

            // If next token is explicit brace, no layout
            if token.kind == TokenKind::LBrace {
                explicit_brace_depth += 1;
                result.push(token.clone());
                i += 1;
                continue;
            }

            // Determine if we should start layout based on the trigger type
            let should_start_layout = match saved_expect {
                LayoutExpect::None | LayoutExpect::InterfaceDelayed { .. } => false,
                LayoutExpect::Unconditional { .. } => true,
                LayoutExpect::Module { .. } => {
                    // Don't start layout if followed by 'verilog'
                    token.kind != TokenKind::KwVerilog
                }
            };

            if should_start_layout {
                let trigger_col = match saved_expect {
                    LayoutExpect::Unconditional { trigger_col, .. } => trigger_col,
                    LayoutExpect::Module { trigger_col, .. } => trigger_col,
                    LayoutExpect::InterfaceDelayed { .. } | LayoutExpect::None => 0,
                };

                if token.kind == TokenKind::Eof {
                    result.push(make_layout_token(TokenKind::LayoutLBrace, token));
                    result.push(make_layout_token(TokenKind::LayoutRBrace, token));
                    continue;
                }

                result.push(make_layout_token(TokenKind::LayoutLBrace, token));

                if current_column > trigger_col {
                    layout_stack.push(current_column);
                    last_line = current_line;
                } else {
                    // Empty block - immediately close it
                    result.push(make_layout_token(TokenKind::LayoutRBrace, token));
                    continue;
                }
            }
            // If should_start_layout is false, fall through to normal token processing
        }

        // Handle explicit braces
        if token.kind == TokenKind::LBrace {
            explicit_brace_depth += 1;
            result.push(token.clone());
            i += 1;
            continue;
        }

        if token.kind == TokenKind::RBrace {
            if explicit_brace_depth > 0 {
                explicit_brace_depth -= 1;
            }
            result.push(token.clone());
            i += 1;
            continue;
        }

        // Only apply layout rules when not inside explicit braces
        if explicit_brace_depth == 0 && !layout_stack.is_empty() {
            let layout_col = *layout_stack.last().unwrap();

            // New line started
            if current_line > last_line {
                // Close layouts for columns greater than current
                while let Some(&col) = layout_stack.last() {
                    if current_column < col {
                        result.push(make_layout_token(TokenKind::LayoutRBrace, token));
                        layout_stack.pop();
                    } else {
                        break;
                    }
                }

                // At the same column, insert semicolon (but not if we just had an explicit semicolon)
                if let Some(&col) = layout_stack.last() {
                    if current_column == col && token.kind != TokenKind::Eof {
                        let last_was_semi = result.last().map_or(false, |t| t.kind == TokenKind::Semi);
                        if !last_was_semi {
                            result.push(make_layout_token(TokenKind::LayoutSemi, token));
                        }
                    }
                }
            }
        }

        last_line = current_line;

        // Handle EOF specially - close all layout blocks before adding EOF
        if token.kind == TokenKind::Eof {
            while !layout_stack.is_empty() {
                result.push(make_layout_token(TokenKind::LayoutRBrace, token));
                layout_stack.pop();
            }
            result.push(token.clone());
            i += 1;
            continue;
        }

        // Track struct type definition context (NOT data - data uses different syntax after =)
        if matches!(token.kind, TokenKind::KwStruct) {
            in_struct_def = true;
        }

        // Check for layout triggers
        if is_layout_trigger(&token.kind) {
            // Use column -1 as trigger (matches Haskell's noTrig = mkPosition fsEmpty 0 (-1)).
            // This allows layout block contents to start at any column >= 0.
            // Haskell BSC uses noTrig for: where, of, do, action, module bodies.
            // For let/letseq/rules, Haskell uses blockKwOf which uses actual column,
            // but our parser handles empty blocks via explicit braces or parse failure,
            // so using noTrig for all is simpler and works for the library files.
            expect_layout = LayoutExpect::Unconditional {
                trigger_line: current_line,
                trigger_col: -1, // noTrig - any column >= 0 starts a non-empty block
            };
        } else if is_module_layout_trigger(&token.kind) {
            // Module triggers layout unless followed by 'verilog'
            expect_layout = LayoutExpect::Module {
                trigger_line: current_line,
                trigger_col: -1, // noTrig - any column >= 0 starts a non-empty block
            };
        } else if is_interface_layout_trigger(&token.kind) {
            // Interface uses delayed layout - skip tokens on same line, then check for body
            expect_layout = LayoutExpect::InterfaceDelayed {
                trigger_line: current_line,
                trigger_col: current_column,
            };
        } else if in_struct_def && token.kind == TokenKind::Equals {
            // In struct/data definition, `=` triggers layout for field definitions
            expect_layout = LayoutExpect::Unconditional {
                trigger_line: current_line,
                trigger_col: -1, // noTrig - any column >= 0 starts a non-empty block
            };
            in_struct_def = false; // Reset after seeing `=`
        }

        // Add the token
        result.push(token.clone());
        i += 1;
    }

    // Close any remaining layout blocks
    while !layout_stack.is_empty() {
        if let Some(last_tok) = result.last().cloned() {
            result.push(make_layout_token(TokenKind::LayoutRBrace, &last_tok));
        }
        layout_stack.pop();
    }

    result
}
