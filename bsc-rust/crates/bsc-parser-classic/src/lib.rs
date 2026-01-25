//! Parser for Classic Bluespec syntax.
//!
//! Mirrors `src/comp/Parser/Classic/CParser.hs` from the Haskell implementation.
//! Uses the chumsky parser combinator library for parsing.
//!
//! # Architecture
//!
//! The parser operates on a stream of tokens from `bsc-lexer` and produces
//! a CSyntax AST. Key features:
//!
//! - Parser combinators matching the Haskell monadic parser style
//! - Layout rule processing (indentation-sensitive)
//! - Full grammar coverage for Classic Bluespec syntax
//! - Rich error messages with source locations

mod layout;

use bsc_diagnostics::{Position, Span};
use bsc_lexer_classic::{Lexer, LexerFlags, Token, TokenKind};
use bsc_syntax::csyntax::*;
use bsc_syntax::id::{Id, IdProp};
use bsc_syntax::literal::{IntBase, IntLiteral, Literal, OrderedFloat};
use bsc_syntax::vmodinfo::{
    VArgInfo, VClockInfo, VFieldInfo, VName, VPathInfo, VPort, VResetInfo, VeriPortProp,
    MethodConflictInfo, SchedInfo, Either,
};
use chumsky::input::{MappedInput, Input, ValueInput};
use chumsky::prelude::*;
use num_bigint::BigInt;
use smol_str::SmolStr;

pub use layout::process_layout;

/// Parser error type - uses SimpleSpan<u32> to match our Span type.
pub type PError<'a> = Rich<'a, Token, SimpleSpan<u32>>;

/// Parser result type.
pub type ParseResult<T> = Result<T, Vec<ParseError>>;

/// A simplified parse error for external use.
#[derive(Debug, Clone)]
pub struct ParseError {
    pub message: String,
    pub span: Span,
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} at {:?}", self.message, self.span)
    }
}

impl std::error::Error for ParseError {}

/// Type alias for our token input with spans.
/// This uses MappedInput to split (Token, SimpleSpan<u32>) pairs into token and span components.
type TokenStream<'a> = MappedInput<'a, Token, SimpleSpan<u32>, &'a [(Token, SimpleSpan<u32>)]>;

/// Type alias for parser extra with our error type.
type ParserExtra<'a> = extra::Err<PError<'a>>;

// ============================================================================
// Helper functions for creating parsers
// ============================================================================

/// Create an Id from a string and position (like Haskell's mkId).
fn make_id(name: SmolStr, pos: Position) -> Id {
    Id::new(name, pos)
}

/// Create a qualified Id from qualifier, name and position.
fn make_qualified_id(qualifier: SmolStr, name: SmolStr, pos: Position) -> Id {
    Id::qualified(qualifier.as_str(), name, pos)
}

/// Check if an Id is a task name (starts with $ followed by an alphabetic char).
/// Mirrors Haskell's `isTaskName :: String -> Bool`.
fn is_task_name(id: &Id) -> bool {
    let name = id.name();
    let mut chars = name.chars();
    matches!(chars.next(), Some('$')) && matches!(chars.next(), Some(c) if c.is_alphabetic())
}

/// Construct an application expression, matching Haskell's cApply function from CSyntax.hs.
/// Flattens nested applications:
/// - cApply n e [] = e
/// - cApply n (CCon i es) es' = CCon i (es ++ es')
/// - cApply n (CConT t i es) es' = CConT t i (es ++ es')
/// - cApply n (CApply e es) es' = CApply e (es ++ es')
/// - cApply n (CTaskApply e es) es' = CTaskApply e (es ++ es')
/// - cApply n e as = CApply e as
fn c_apply(func: CExpr, mut args: Vec<CExpr>) -> CExpr {
    if args.is_empty() {
        return func;
    }
    match func {
        CExpr::Con(id, mut es, span) => {
            es.append(&mut args);
            CExpr::Con(id, es, span)
        }
        CExpr::ConTyped { type_name, con_name, args: mut es, span } => {
            es.append(&mut args);
            CExpr::ConTyped { type_name, con_name, args: es, span }
        }
        CExpr::Apply(f, mut es, span) => {
            es.append(&mut args);
            CExpr::Apply(f, es, span)
        }
        CExpr::TaskApply(f, mut es, span) => {
            es.append(&mut args);
            CExpr::TaskApply(f, es, span)
        }
        _ => {
            if let CExpr::Var(ref id) = func {
                if is_task_name(id) {
                    CExpr::TaskApply(Box::new(func), args, Span::DUMMY)
                } else {
                    CExpr::Apply(Box::new(func), args, Span::DUMMY)
                }
            } else {
                CExpr::Apply(Box::new(func), args, Span::DUMMY)
            }
        }
    }
}

/// Construct a lambda expression, matching Haskell's cLam function from CParser.hs.
/// Special cases:
/// - cLam _ [] e = e  (no patterns, just return expr)
/// - cLam pos (CPVar i : ps) e = CLam (Right i) $ cLam pos ps e  (simple var, use CLam)
/// - cLam pos (CPAny pos' : ps) e = CLam (Left pos') $ cLam pos ps e  (wildcard, use CLam with position)
/// - cLam pos ps e = Cletseq [CLValue _lam [CClause ps [] e]] (CVar _lam)  (complex patterns)
fn c_lam(pos: Position, mut pats: Vec<CPat>, body: CExpr) -> CExpr {
    if pats.is_empty() {
        return body;
    }

    let first_pat = pats.remove(0);

    match first_pat {
        CPat::Var(id) => {
            let inner = c_lam(pos, pats, body);
            CExpr::Lambda(vec![CPat::Var(id)], Box::new(inner), Span::DUMMY)
        }
        CPat::Wildcard(any_pos) => {
            let inner = c_lam(pos, pats, body);
            CExpr::Lambda(vec![CPat::Wildcard(any_pos)], Box::new(inner), Span::DUMMY)
        }
        other => {
            pats.insert(0, other);
            let id_lam = Id::new(SmolStr::new_static("_lam"), pos);
            CExpr::LetSeq(
                vec![CDefl::Value(
                    id_lam.clone(),
                    vec![CClause {
                        patterns: pats,
                        qualifiers: vec![],
                        body,
                        span: Span::DUMMY,
                    }],
                    vec![],
                    Span::DUMMY,
                )],
                Box::new(CExpr::Var(id_lam)),
                Span::DUMMY,
            )
        }
    }
}

/// Match any VarId token and extract the identifier string and position.
fn var_id<'a>() -> impl Parser<'a, TokenStream<'a>, (SmolStr, Position), ParserExtra<'a>> + Clone {
    any()
        .try_map(|t: Token, span| {
            if let TokenKind::VarId(s) = t.kind {
                Ok((s, t.position))
            } else {
                Err(Rich::custom(span, "expected variable identifier"))
            }
        })
        .labelled("variable identifier")
}

/// Match any ConId token and extract the identifier string and position.
fn con_id<'a>() -> impl Parser<'a, TokenStream<'a>, (SmolStr, Position), ParserExtra<'a>> + Clone {
    any()
        .try_map(|t: Token, span| {
            if let TokenKind::ConId(s) = t.kind {
                Ok((s, t.position))
            } else {
                Err(Rich::custom(span, "expected constructor identifier"))
            }
        })
        .labelled("constructor identifier")
}

/// Match any VarSym token and extract the operator string and position.
fn var_sym<'a>() -> impl Parser<'a, TokenStream<'a>, (SmolStr, Position), ParserExtra<'a>> + Clone {
    any()
        .try_map(|t: Token, span| {
            if let TokenKind::VarSym(s) = t.kind {
                Ok((s, t.position))
            } else {
                Err(Rich::custom(span, "expected operator"))
            }
        })
        .labelled("operator")
}

/// Match any ConSym token and extract the operator string and position.
fn con_sym<'a>() -> impl Parser<'a, TokenStream<'a>, (SmolStr, Position), ParserExtra<'a>> + Clone {
    any()
        .try_map(|t: Token, span| {
            if let TokenKind::ConSym(s) = t.kind {
                Ok((s, t.position))
            } else {
                Err(Rich::custom(span, "expected constructor operator"))
            }
        })
        .labelled("constructor operator")
}

/// Match any integer literal.
fn integer<'a>(
) -> impl Parser<'a, TokenStream<'a>, (Option<BigInt>, u32, BigInt, Span, Position), ParserExtra<'a>> + Clone
{
    any()
        .try_map(|t: Token, span| {
            if let TokenKind::Integer { size, base, value } = t.kind {
                Ok((size, base, value, t.span, t.position))
            } else {
                Err(Rich::custom(span, "expected integer literal"))
            }
        })
        .labelled("integer literal")
}

/// Match any string literal.
fn string_lit<'a>() -> impl Parser<'a, TokenStream<'a>, (String, Span, Position), ParserExtra<'a>> + Clone {
    any()
        .try_map(|t: Token, span| {
            if let TokenKind::String(s) = t.kind {
                Ok((s, t.span, t.position))
            } else {
                Err(Rich::custom(span, "expected string literal"))
            }
        })
        .labelled("string literal")
}

/// Match any char literal.
fn char_lit<'a>() -> impl Parser<'a, TokenStream<'a>, (char, Position), ParserExtra<'a>> + Clone {
    any()
        .try_map(|t: Token, span| {
            if let TokenKind::Char(c) = t.kind {
                Ok((c, t.position))
            } else {
                Err(Rich::custom(span, "expected character literal"))
            }
        })
        .labelled("character literal")
}

/// Match any float literal.
fn float_lit<'a>(
) -> impl Parser<'a, TokenStream<'a>, (OrderedFloat, Position), ParserExtra<'a>> + Clone {
    any()
        .try_map(|t: Token, span| {
            if let TokenKind::Float(f) = t.kind {
                Ok((f, t.position))
            } else {
                Err(Rich::custom(span, "expected float literal"))
            }
        })
        .labelled("float literal")
}

// ============================================================================
// Keyword and punctuation parsers using macros
// ============================================================================

macro_rules! token_parser {
    ($name:ident, $variant:ident, $label:expr) => {
        fn $name<'a>() -> impl Parser<'a, TokenStream<'a>, Span, ParserExtra<'a>> + Clone {
            any()
                .try_map(|t: Token, span| {
                    if t.kind == TokenKind::$variant {
                        Ok(t.span)
                    } else {
                        Err(Rich::custom(span, concat!("expected ", $label)))
                    }
                })
                .labelled($label)
        }
    };
}

// Keywords
token_parser!(kw_action, KwAction, "action");

fn kw_action_pos<'a>() -> impl Parser<'a, TokenStream<'a>, Position, ParserExtra<'a>> + Clone {
    any()
        .try_map(|t: Token, span| {
            if t.kind == TokenKind::KwAction {
                Ok(t.position)
            } else {
                Err(Rich::custom(span, "expected action"))
            }
        })
        .labelled("action")
}
token_parser!(kw_case, KwCase, "case");

fn kw_case_pos<'a>() -> impl Parser<'a, TokenStream<'a>, Position, ParserExtra<'a>> + Clone {
    any()
        .try_map(|t: Token, span| {
            if t.kind == TokenKind::KwCase {
                Ok(t.position)
            } else {
                Err(Rich::custom(span, "expected case"))
            }
        })
        .labelled("case")
}

token_parser!(kw_class, KwClass, "class");
token_parser!(kw_data, KwData, "data");
token_parser!(kw_deriving, KwDeriving, "deriving");
token_parser!(kw_do, KwDo, "do");
token_parser!(kw_else, KwElse, "else");
token_parser!(kw_foreign, KwForeign, "foreign");
token_parser!(kw_if, KwIf, "if");

fn kw_if_pos<'a>() -> impl Parser<'a, TokenStream<'a>, Position, ParserExtra<'a>> + Clone {
    any()
        .try_map(|t: Token, span| {
            if t.kind == TokenKind::KwIf {
                Ok(t.position)
            } else {
                Err(Rich::custom(span, "expected if"))
            }
        })
        .labelled("if")
}

token_parser!(kw_import, KwImport, "import");
token_parser!(kw_in, KwIn, "in");
token_parser!(kw_infix, KwInfix, "infix");
token_parser!(kw_infixl, KwInfixL, "infixl");
token_parser!(kw_infixr, KwInfixR, "infixr");
token_parser!(kw_interface, KwInterface, "interface");

fn kw_interface_pos<'a>() -> impl Parser<'a, TokenStream<'a>, Position, ParserExtra<'a>> + Clone {
    any()
        .try_map(|t: Token, span| {
            if t.kind == TokenKind::KwInterface {
                Ok(t.position)
            } else {
                Err(Rich::custom(span, "expected interface"))
            }
        })
        .labelled("interface")
}

token_parser!(kw_instance, KwInstance, "instance");
token_parser!(kw_let, KwLet, "let");
token_parser!(kw_letseq, KwLetSeq, "letseq");
token_parser!(kw_module, KwModule, "module");

fn kw_module_pos<'a>() -> impl Parser<'a, TokenStream<'a>, Position, ParserExtra<'a>> + Clone {
    any()
        .try_map(|t: Token, span| {
            if t.kind == TokenKind::KwModule {
                Ok(t.position)
            } else {
                Err(Rich::custom(span, "expected module"))
            }
        })
        .labelled("module")
}

token_parser!(kw_of, KwOf, "of");
token_parser!(kw_package, KwPackage, "package");
token_parser!(kw_primitive, KwPrimitive, "primitive");
token_parser!(kw_qualified, KwQualified, "qualified");
token_parser!(kw_rules, KwRules, "rules");
token_parser!(kw_signature, KwSignature, "signature");
token_parser!(kw_struct, KwStruct, "struct");
token_parser!(kw_then, KwThen, "then");
token_parser!(kw_type, KwType, "type");
token_parser!(kw_valueof, KwValueOf, "valueOf");
token_parser!(kw_stringof, KwStringOf, "stringOf");
token_parser!(kw_verilog, KwVerilog, "verilog");

/// Parse valueOf keyword and return Position
fn kw_valueof_pos<'a>() -> impl Parser<'a, TokenStream<'a>, Position, ParserExtra<'a>> + Clone {
    any()
        .try_map(|t: Token, span| {
            if t.kind == TokenKind::KwValueOf {
                Ok(t.position)
            } else {
                Err(Rich::custom(span, "expected valueOf"))
            }
        })
        .labelled("valueOf")
}

/// Parse stringOf keyword and return Position
fn kw_stringof_pos<'a>() -> impl Parser<'a, TokenStream<'a>, Position, ParserExtra<'a>> + Clone {
    any()
        .try_map(|t: Token, span| {
            if t.kind == TokenKind::KwStringOf {
                Ok(t.position)
            } else {
                Err(Rich::custom(span, "expected stringOf"))
            }
        })
        .labelled("stringOf")
}
token_parser!(kw_synthesize, KwSynthesize, "synthesize");
token_parser!(kw_when, KwWhen, "when");
token_parser!(kw_where, KwWhere, "where");
token_parser!(kw_coherent, KwCoherent, "coherent");
token_parser!(kw_incoherent, KwIncoherent, "incoherent");

// Punctuation
token_parser!(lparen, LParen, "(");
token_parser!(rparen, RParen, ")");
token_parser!(lbrace, LBrace, "{");
token_parser!(rbrace, RBrace, "}");
token_parser!(lbracket, LBracket, "[");
token_parser!(rbracket, RBracket, "]");
token_parser!(semi, Semi, ";");
token_parser!(comma, Comma, ",");
token_parser!(dot, Dot, ".");
fn dotdot<'a>() -> impl Parser<'a, TokenStream<'a>, (), ParserExtra<'a>> + Clone {
    dot().then(dot()).to(()).labelled("..")
}
token_parser!(dcolon, ColonColon, "::");
token_parser!(colon, Colon, ":");
token_parser!(equals, Equals, "=");
token_parser!(at, At, "@");
token_parser!(backslash, Backslash, "\\");

fn backslash_pos<'a>() -> impl Parser<'a, TokenStream<'a>, Position, ParserExtra<'a>> + Clone {
    any()
        .try_map(|t: Token, span| {
            if t.kind == TokenKind::Backslash {
                Ok(t.position)
            } else {
                Err(Rich::custom(span, "expected \\"))
            }
        })
        .labelled("\\")
}

token_parser!(arrow, Arrow, "->");

/// Match the `|` operator (lexed as VarSym)
fn bar<'a>() -> impl Parser<'a, TokenStream<'a>, (), ParserExtra<'a>> + Clone {
    any()
        .try_map(|t: Token, span| {
            if let TokenKind::VarSym(s) = &t.kind {
                if s == "|" {
                    return Ok(());
                }
            }
            Err(Rich::custom(span, "expected |"))
        })
        .labelled("|")
}
token_parser!(larrow, LArrow, "<-");
token_parser!(fat_arrow, FatArrow, "=>");
token_parser!(darrow, DArrow, "==>");
token_parser!(underscore, Underscore, "_");

/// Parse underscore and return Position (for CPat::Wildcard)
fn underscore_pos<'a>() -> impl Parser<'a, TokenStream<'a>, Position, ParserExtra<'a>> + Clone {
    any()
        .try_map(|t: Token, span| {
            if t.kind == TokenKind::Underscore {
                Ok(t.position)
            } else {
                Err(Rich::custom(span, "expected _"))
            }
        })
        .labelled("_")
}

fn hash<'a>() -> impl Parser<'a, TokenStream<'a>, (), ParserExtra<'a>> + Clone {
    any()
        .try_map(|t: Token, span| {
            if let TokenKind::VarSym(s) = &t.kind {
                if s == "#" {
                    return Ok(());
                }
            }
            Err(Rich::custom(span, "expected #"))
        })
        .labelled("#")
}

fn question<'a>() -> impl Parser<'a, TokenStream<'a>, (), ParserExtra<'a>> + Clone {
    any()
        .try_map(|t: Token, span| {
            if let TokenKind::VarSym(s) = &t.kind {
                if s == "?" {
                    return Ok(());
                }
            }
            Err(Rich::custom(span, "expected ?"))
        })
        .labelled("?")
}
token_parser!(lpragma, LPragma, "{-#");
token_parser!(rpragma, RPragma, "#-}");
token_parser!(backtick, Backtick, "`");

// Layout tokens
token_parser!(lbrace_layout, LayoutLBrace, "layout {");
token_parser!(rbrace_layout, LayoutRBrace, "layout }");
token_parser!(semi_layout, LayoutSemi, "layout ;");

/// Left curly brace (explicit or layout)
fn lc<'a>() -> impl Parser<'a, TokenStream<'a>, Span, ParserExtra<'a>> + Clone {
    lbrace().or(lbrace_layout())
}

/// Right curly brace (explicit or layout)
fn rc<'a>() -> impl Parser<'a, TokenStream<'a>, Span, ParserExtra<'a>> + Clone {
    rbrace().or(rbrace_layout())
}

/// Semicolon (explicit or layout)
fn sm<'a>() -> impl Parser<'a, TokenStream<'a>, Span, ParserExtra<'a>> + Clone {
    semi().or(semi_layout())
}

/// Definition separator (semicolon)
fn dsm<'a>() -> impl Parser<'a, TokenStream<'a>, Span, ParserExtra<'a>> + Clone {
    sm()
}

/// Optional semicolon
fn osm<'a>() -> impl Parser<'a, TokenStream<'a>, (), ParserExtra<'a>> + Clone {
    sm().or_not().ignored()
}

// ============================================================================
// Qualified identifier parsing
// ============================================================================

/// Parse a qualified variable: Con.varSym (e.g., Prelude.map)
/// Matches Haskell: qvar = con +.+ dot ..+ varSym >>> qualId
fn qvar<'a>() -> impl Parser<'a, TokenStream<'a>, Id, ParserExtra<'a>> + Clone {
    con_id()
        .then_ignore(dot())
        .then(var_id())
        .map(|((qual, pos), (name, _))| make_qualified_id(qual, name, pos))
        .labelled("qualified variable")
}

/// Parse a qualified constructor: Con.con (e.g., List.Nil)
/// Matches Haskell: qcon = con +.+ dot ..+ con >>> qualId
fn qcon<'a>() -> impl Parser<'a, TokenStream<'a>, Id, ParserExtra<'a>> + Clone {
    con_id()
        .then_ignore(dot())
        .then(con_id())
        .map(|((qual, pos), (name, _))| make_qualified_id(qual, name, pos))
        .labelled("qualified constructor")
}

/// Parse a qualified variable operator: Con.varop (e.g., Prelude.+)
/// Matches Haskell: qvarop = con +.+ dot ..+ varop >>> qualId
fn qvarop<'a>() -> impl Parser<'a, TokenStream<'a>, Id, ParserExtra<'a>> + Clone {
    con_id()
        .then_ignore(dot())
        .then(var_sym())
        .map(|((qual, pos), (name, _))| make_qualified_id(qual, name, pos))
        .labelled("qualified variable operator")
}

/// Parse a qualified constructor operator: Con.conop (e.g., List.:>)
/// Matches Haskell: qconop = con +.+ dot ..+ conop >>> qualId
fn qconop<'a>() -> impl Parser<'a, TokenStream<'a>, Id, ParserExtra<'a>> + Clone {
    con_id()
        .then_ignore(dot())
        .then(con_sym())
        .map(|((qual, pos), (name, _))| make_qualified_id(qual, name, pos))
        .labelled("qualified constructor operator")
}

// ============================================================================
// Identifier parsing
// ============================================================================

/// Parse a variable identifier (lowercase), possibly qualified.
/// Matches Haskell: pVarId = varSym ||! qvar
fn p_var_id<'a>() -> impl Parser<'a, TokenStream<'a>, Id, ParserExtra<'a>> + Clone {
    let simple_var = var_id().map(|(s, pos)| make_id(s, pos));
    let paren_op = lparen()
        .ignore_then(var_sym().or(con_sym()))
        .then_ignore(rparen())
        .map(|(s, pos)| make_id(s, pos));
    simple_var
        .or(paren_op)
        .or(qvar())
        .labelled("variable identifier")
}

/// Parse a variable identifier with optional preceding hide pragma.
/// Matches Haskell: pHVarId = (pHidePragma ||! pHideAllPragma) ..+ sm ..+ pVarId >>- setHideId ||! pVarId
fn p_h_var_id<'a>() -> impl Parser<'a, TokenStream<'a>, Id, ParserExtra<'a>> + Clone {
    // Parse optional hide/hideall pragma
    let hide_pragma = lpragma()
        .ignore_then(
            any().try_map(|t: Token, span| {
                if let TokenKind::VarId(s) = &t.kind {
                    if s == "hide" {
                        return Ok(IdProp::Hide);
                    }
                    if s == "hideall" {
                        return Ok(IdProp::HideAll);
                    }
                }
                Err(Rich::custom(span, "expected hide or hideall"))
            }),
        )
        .then_ignore(rpragma())
        .then_ignore(dsm().repeated()) // Skip semicolons after pragma
        .then(p_var_id())
        .map(|(prop, mut id)| {
            id.add_prop(prop);
            id
        });

    // Either with pragma or without
    hide_pragma.or(p_var_id())
}

/// Parse a constructor identifier (uppercase), possibly qualified.
/// Matches Haskell: pConId = qcon ||! con
fn p_con_id<'a>() -> impl Parser<'a, TokenStream<'a>, Id, ParserExtra<'a>> + Clone {
    // Try qualified first (Haskell order: qcon ||! con)
    qcon()
        .or(con_id().map(|(s, pos)| make_id(s, pos)))
        .labelled("constructor identifier")
}

/// Parse a type variable identifier.
fn p_tyvar_id<'a>() -> impl Parser<'a, TokenStream<'a>, Id, ParserExtra<'a>> + Clone {
    var_id().map(|(s, pos)| make_id(s, pos))
}

/// Parse a type constructor identifier, possibly qualified.
/// Matches Haskell: pTyConId = qcon ||! con
fn p_tycon_id<'a>() -> impl Parser<'a, TokenStream<'a>, Id, ParserExtra<'a>> + Clone {
    // Try qualified first (Haskell order: qcon ||! con)
    qcon()
        .or(con_id().map(|(s, pos)| make_id(s, pos)))
        .labelled("type constructor identifier")
}

/// Parse a module identifier.
fn p_mod_id<'a>() -> impl Parser<'a, TokenStream<'a>, Id, ParserExtra<'a>> + Clone {
    con_id().map(|(s, pos)| make_id(s, pos))
}

/// Parse a field identifier.
/// Accepts qualified variables, simple variables, or operators in parentheses like (==).
/// Matches Haskell: pFieldId = qvar ||! var ||! lp ..+ pAnySym +.. rp
fn p_field_id<'a>() -> impl Parser<'a, TokenStream<'a>, Id, ParserExtra<'a>> + Clone {
    // Qualified variable (e.g., Prelude.map)
    let qualified_var = qvar();

    // Simple variable identifier
    let simple_var = var_id().map(|(s, pos)| make_id(s, pos));

    // Operator in parentheses like (==) or (:>)
    // Uses p_any_sym_inner to avoid recursion issues
    let paren_op = lparen()
        .ignore_then(p_any_sym_inner())
        .then_ignore(rparen());

    // Try in Haskell order: qvar ||! var ||! (pAnySym)
    qualified_var
        .or(simple_var)
        .or(paren_op)
        .labelled("field identifier")
}

/// Parse an operator (varsym or consym), possibly qualified.
fn p_operator<'a>() -> impl Parser<'a, TokenStream<'a>, Id, ParserExtra<'a>> + Clone {
    p_any_sym_inner()
}

/// Parse a constructor operator, possibly qualified.
/// Matches Haskell: pConOp = qconop ||! conop
fn p_con_oper<'a>() -> impl Parser<'a, TokenStream<'a>, Id, ParserExtra<'a>> + Clone {
    qconop()
        .or(con_sym().map(|(s, pos)| make_id(s, pos)))
        .labelled("constructor operator")
}

/// Parse a variable or underscore.
fn p_var_id_or_underscore<'a>(
) -> impl Parser<'a, TokenStream<'a>, Option<Id>, ParserExtra<'a>> + Clone {
    var_id()
        .map(|(s, pos)| Some(make_id(s, pos)))
        .or(underscore().map(|_| None))
}

/// Parse any symbol operator (qualified or unqualified).
/// This is the inner version that doesn't include backtick-quoted identifiers.
/// Matches Haskell: pAnySym = qvarop ||! qconop ||! varop ||! conop
fn p_any_sym_inner<'a>() -> impl Parser<'a, TokenStream<'a>, Id, ParserExtra<'a>> + Clone {
    // Try qualified operators first, then simple operators
    // Haskell order: qvarop ||! qconop ||! varop ||! conop
    qvarop()
        .or(qconop())
        .or(var_sym().map(|(s, pos)| make_id(s, pos)))
        .or(con_sym().map(|(s, pos)| make_id(s, pos)))
        .labelled("symbol operator")
}

/// Parse an operator: symbol (possibly qualified) or identifier in backticks.
/// Matches Haskell: pOper = pAnySym ||! l L_bquote ..+ pAnyId +.. l L_bquote
fn p_any_sym<'a>() -> impl Parser<'a, TokenStream<'a>, Id, ParserExtra<'a>> + Clone {
    p_any_sym_inner()
        .or(backtick()
            .ignore_then(p_var_id().or(p_con_id()))
            .then_ignore(backtick()))
        .labelled("operator")
}

// ============================================================================
// Kind parsing
// ============================================================================

/// Parse a kind.
fn p_kind<'a>() -> impl Parser<'a, TokenStream<'a>, CKind, ParserExtra<'a>> + Clone {
    recursive(|kind| {
        let star = any()
            .try_map(|t: Token, span: SimpleSpan<u32>| {
                if let TokenKind::VarSym(s) = t.kind {
                    if s == "*" {
                        Ok(CKind::Star(Span::new(span.start, span.end)))
                    } else {
                        Err(Rich::custom(span, "expected *"))
                    }
                } else {
                    Err(Rich::custom(span, "expected *"))
                }
            });

        let num = any()
            .try_map(|t: Token, span: SimpleSpan<u32>| {
                if let TokenKind::VarSym(s) = t.kind {
                    if s == "#" {
                        Ok(CKind::Num(Span::new(span.start, span.end)))
                    } else {
                        Err(Rich::custom(span, "expected #"))
                    }
                } else {
                    Err(Rich::custom(span, "expected #"))
                }
            });

        // $ for string kind
        let str_kind = any()
            .try_map(|t: Token, span: SimpleSpan<u32>| {
                if let TokenKind::VarSym(s) = t.kind {
                    if s == "$" {
                        Ok(CKind::Str(Span::new(span.start, span.end)))
                    } else {
                        Err(Rich::custom(span, "expected $"))
                    }
                } else {
                    Err(Rich::custom(span, "expected $"))
                }
            });

        let paren = kind.clone().delimited_by(lparen(), rparen()).map(|k| {
            let span = match &k {
                CKind::Star(s)
                | CKind::Num(s)
                | CKind::Str(s)
                | CKind::Fun(_, _, s)
                | CKind::Paren(_, s) => *s,
            };
            CKind::Paren(Box::new(k), span)
        });

        // Use .boxed() to reduce compile time
        let atom = star.or(num).or(str_kind).or(paren).boxed();

        atom.clone().foldl(arrow().ignore_then(kind).repeated(), |l, r| {
            let span = Span::new(
                match &l {
                    CKind::Star(s)
                    | CKind::Num(s)
                    | CKind::Str(s)
                    | CKind::Fun(_, _, s)
                    | CKind::Paren(_, s) => s.start,
                },
                match &r {
                    CKind::Star(s)
                    | CKind::Num(s)
                    | CKind::Str(s)
                    | CKind::Fun(_, _, s)
                    | CKind::Paren(_, s) => s.end,
                },
            );
            CKind::Fun(Box::new(l), Box::new(r), span)
        })
    })
}

// ============================================================================
// Type parsing
// ============================================================================

/// Parse a type.
fn p_type<'a>() -> impl Parser<'a, TokenStream<'a>, CType, ParserExtra<'a>> + Clone {
    recursive(|ty| {
        let tyvar = p_tyvar_id().map(CType::Var);
        let tycon = p_tycon_id().map(CType::Con);

        let num_type = integer().map(|(_, _, value, _span, pos)| {
            let v: i128 = value.to_string().parse().unwrap_or(0);
            CType::Num(v, pos)
        });

        let str_type = string_lit().map(|(s, _span, pos)| CType::Str(s, pos));

        // Tuple or parenthesized type
        let paren_or_tuple = ty
            .clone()
            .separated_by(comma())
            .collect::<Vec<_>>()
            .delimited_by(lparen(), rparen())
            .map(|ts| {
                if ts.is_empty() {
                    CType::Con(Id::qualified("Prelude", "PrimUnit", Position::unknown()))
                } else if ts.len() == 1 {
                    CType::Paren(Box::new(ts.into_iter().next().unwrap()), Span::DUMMY)
                } else {
                    CType::Tuple(ts, Span::DUMMY)
                }
            });

        let list_type = ty
            .clone()
            .delimited_by(lbracket(), rbracket())
            .map(|t| CType::List(Box::new(t), Span::DUMMY));

        // Use .boxed() on type alternatives to reduce compile time
        let atype = choice((paren_or_tuple, list_type, tyvar, tycon, num_type, str_type)).boxed();

        // Type application
        let app_type = atype
            .clone()
            .foldl(atype.clone().repeated(), |acc, arg| {
                CType::Apply(Box::new(acc), Box::new(arg), Span::DUMMY)
            });

        // Function type
        app_type
            .clone()
            .foldl(arrow().ignore_then(ty.clone()).repeated(), |l, r| {
                CType::Fun(Box::new(l), Box::new(r), Span::DUMMY)
            })
    })
}

/// Parse a type predicate.
fn p_pred<'a>() -> impl Parser<'a, TokenStream<'a>, CPred, ParserExtra<'a>> + Clone {
    p_tycon_id()
        .then(p_atype().repeated().collect::<Vec<_>>())
        .map(|(class, args)| CPred {
            class,
            args,
            span: Span::DUMMY,
        })
}

/// Parse predicates (context).
fn p_preds<'a>() -> impl Parser<'a, TokenStream<'a>, Vec<CPred>, ParserExtra<'a>> + Clone {
    p_pred()
        .separated_by(comma())
        .at_least(1)
        .collect::<Vec<_>>()
        .delimited_by(lparen(), rparen())
        .then_ignore(fat_arrow())
        .or_not()
        .map(|opt| opt.unwrap_or_default())
}

/// Parse a qualified type (with context).
fn p_qtype<'a>() -> impl Parser<'a, TokenStream<'a>, CQType, ParserExtra<'a>> + Clone {
    p_preds().then(p_type()).map(|(context, ty)| CQType {
        context,
        ty,
        span: Span::DUMMY,
    })
}

/// Parse an atomic type (for type applications).
fn p_atype<'a>() -> impl Parser<'a, TokenStream<'a>, CType, ParserExtra<'a>> + Clone {
    recursive(|_| {
        let tyvar = p_tyvar_id().map(CType::Var);
        let tycon = p_tycon_id().map(CType::Con);

        let num_type = integer().map(|(_, _, value, _span, pos)| {
            let v: i128 = value.to_string().parse().unwrap_or(0);
            CType::Num(v, pos)
        });

        let str_type = string_lit().map(|(s, _span, pos)| CType::Str(s, pos));

        let paren_or_tuple = p_type()
            .separated_by(comma())
            .collect::<Vec<_>>()
            .delimited_by(lparen(), rparen())
            .map(|ts| {
                if ts.is_empty() {
                    CType::Con(Id::qualified("Prelude", "PrimUnit", Position::unknown()))
                } else if ts.len() == 1 {
                    CType::Paren(Box::new(ts.into_iter().next().unwrap()), Span::DUMMY)
                } else {
                    CType::Tuple(ts, Span::DUMMY)
                }
            });

        let list_type = p_type()
            .delimited_by(lbracket(), rbracket())
            .map(|t| CType::List(Box::new(t), Span::DUMMY));

        // Use .boxed() to reduce compile time
        choice((paren_or_tuple, list_type, tyvar, tycon, num_type, str_type)).boxed()
    })
}

// ============================================================================
// Literal parsing
// ============================================================================

/// Parse a literal.
fn p_literal<'a>() -> impl Parser<'a, TokenStream<'a>, Literal, ParserExtra<'a>> + Clone {
    p_literal_with_pos().map(|(lit, _pos)| lit)
}

fn p_literal_with_pos<'a>(
) -> impl Parser<'a, TokenStream<'a>, (Literal, Position), ParserExtra<'a>> + Clone {
    let int_lit = integer().map(|(size, base, value, _span, pos)| {
        (
            Literal::Integer(IntLiteral {
                width: size.map(|s| s.to_string().parse().unwrap_or(0)),
                base: match base {
                    2 => IntBase::Binary,
                    8 => IntBase::Octal,
                    16 => IntBase::Hexadecimal,
                    _ => IntBase::Decimal,
                },
                value: value.to_string().parse().unwrap_or(0),
            }),
            pos,
        )
    });

    let float_lit_p = float_lit().map(|(f, pos)| (Literal::Float(f), pos));
    let char_lit_p = char_lit().map(|(c, pos)| (Literal::Char(c), pos));
    let string_lit_p = string_lit().map(|(s, _span, pos)| (Literal::String(s), pos));

    choice((int_lit, float_lit_p, char_lit_p, string_lit_p)).boxed()
}

// ============================================================================
// Pattern parsing
// ============================================================================

/// Parse a pattern.
/// Matches Haskell: pPat = pPatApply ||! pPatOp ||! pAPat
fn p_pattern<'a>() -> impl Parser<'a, TokenStream<'a>, CPat, ParserExtra<'a>> + Clone {
    recursive(|pat| {
        let var_pat = p_var_id().map(CPat::Var);
        let wildcard = underscore_pos().map(|pos| CPat::Wildcard(pos));
        let lit_pat = p_literal_with_pos().map(|(lit, pos)| CPat::Lit(lit, pos));

        let paren_or_tuple = pat
            .clone()
            .separated_by(comma())
            .collect::<Vec<_>>()
            .delimited_by(lparen(), rparen())
            .map(|pats| {
                if pats.is_empty() {
                    CPat::Struct(Some(true), Id::qualified("Prelude", "PrimUnit", Position::unknown()), vec![], Span::DUMMY)
                } else if pats.len() == 1 {
                    CPat::Paren(Box::new(pats.into_iter().next().unwrap()), Span::DUMMY)
                } else {
                    CPat::Tuple(pats, Span::DUMMY)
                }
            })
            .boxed();

        let list_pat = pat
            .clone()
            .separated_by(comma())
            .collect::<Vec<_>>()
            .delimited_by(lbracket(), rbracket())
            .map(|pats| CPat::List(pats, Span::DUMMY));

        // pPatApply: Struct pattern or constructor application
        // Haskell: pPatApply = pConId `into` (\ c -> blockBrOf pPField >>- CPstruct Nothing c
        //                                       ||! many1 pAPat >>- CPCon c)
        let struct_pat = p_con_id()
            .then(
                p_pfield(pat.clone())
                    .separated_by(sm())
                    .collect::<Vec<_>>()
                    .delimited_by(lc(), rc()),
            )
            .map(|(con, fields)| CPat::Struct(None, con, fields, Span::DUMMY));

        // Constructor application with at least one argument: Cons x xs
        let con_app_pat = p_con_id()
            .then(p_apat(pat.clone()).repeated().at_least(1).collect::<Vec<_>>())
            .map(|(con, args)| CPat::Con(con, args, Span::DUMMY));

        // Nullary constructor (no args)
        let con_nullary = p_con_id().map(|con| CPat::Con(con, vec![], Span::DUMMY));

        let as_pat = p_var_id()
            .then_ignore(at())
            .then(pat.clone())
            .map(|(name, p)| CPat::As(name, Box::new(p), Span::DUMMY));

        // Atomic patterns (pAPat) - for use in infix patterns
        // Does NOT include constructor application with args (that's pPatApply)
        let apat_inner = choice((
            wildcard.clone(),
            lit_pat.clone(),
            paren_or_tuple.clone(),
            list_pat.clone(),
            con_nullary.clone(),
            var_pat.clone(),
        ))
        .boxed();

        // pPatOp: Infix pattern operators like `x :> xs`
        // Uses pConOper (constructor operators) between atomic patterns.
        // Haskell: pPatOp = binop getFixity mkBinP pConOper pAPat
        //   where mkBinP p1 op p2 = CPCon op [p1, p2]
        // We build left-associatively here; proper fixity resolution happens later.
        let pat_op = apat_inner
            .clone()
            .then(
                p_con_oper()
                    .then(apat_inner.clone())
                    .repeated()
                    .collect::<Vec<_>>(),
            )
            .map(|(first, rest)| {
                if rest.is_empty() {
                    first
                } else {
                    // Build left-associative chain: CPCon op [left, right]
                    rest.into_iter().fold(first, |left, (op, right)| {
                        CPat::Con(op, vec![left, right], Span::DUMMY)
                    })
                }
            });

        // Try in Haskell order: pPatApply ||! pPatOp ||! pAPat
        // 1. as_pat - as patterns like x@(...)
        // 2. struct_pat - struct patterns like Foo { x = 1 }
        // 3. con_app_pat - constructor with args like Cons x xs
        // 4. pat_op - infix patterns like x :> xs (includes atomic patterns)
        choice((as_pat, struct_pat, con_app_pat, pat_op)).boxed()
    })
}

/// Parse an atomic pattern.
/// Haskell: pAPat = pVarIdOrU `into` (\ mi -> l L_at ..+ pAPat >>- CPAs ||! succeed CPVar)
///       ||! pConId >>- CPCon [] ||! lp +.+ sepBy pPat cm +.. rp ||! numericLit
fn p_apat<'a>(
    pat: impl Parser<'a, TokenStream<'a>, CPat, ParserExtra<'a>> + Clone + 'a,
) -> impl Parser<'a, TokenStream<'a>, CPat, ParserExtra<'a>> + Clone {
    recursive(move |apat| {
        let lit_pat = p_literal_with_pos().map(|(lit, pos)| CPat::Lit(lit, pos));

        let paren_or_tuple = pat
            .clone()
            .separated_by(comma())
            .collect::<Vec<_>>()
            .delimited_by(lparen(), rparen())
            .map(|pats| {
                if pats.is_empty() {
                    CPat::Struct(Some(true), Id::qualified("Prelude", "PrimUnit", Position::unknown()), vec![], Span::DUMMY)
                } else if pats.len() == 1 {
                    CPat::Paren(Box::new(pats.into_iter().next().unwrap()), Span::DUMMY)
                } else {
                    CPat::Tuple(pats, Span::DUMMY)
                }
            });

        let list_pat = pat
            .clone()
            .separated_by(comma())
            .collect::<Vec<_>>()
            .delimited_by(lbracket(), rbracket())
            .map(|pats| CPat::List(pats, Span::DUMMY));

        let con_nullary = p_con_id().map(|con| CPat::Con(con, vec![], Span::DUMMY));

        // Variable with optional as-pattern: x or x@pat
        // Haskell: pVarIdOrU `into` (l L_at ..+ pAPat >>- CPAs ||! succeed CPVar)
        let var_or_as = p_var_id()
            .then(at().ignore_then(apat.clone()).or_not())
            .map(|(name, opt_pat)| {
                if let Some(inner) = opt_pat {
                    CPat::As(name, Box::new(inner), Span::DUMMY)
                } else {
                    CPat::Var(name)
                }
            });

        // Wildcard with optional as-pattern: _ or _@pat (though _@pat doesn't make sense, handle it)
        let wildcard = underscore_pos()
            .then(at().ignore_then(apat.clone()).or_not())
            .map(|(pos, opt_pat)| {
                if let Some(inner) = opt_pat {
                    inner // discard the wildcard binding
                } else {
                    CPat::Wildcard(pos)
                }
            });

        // Use .boxed() to reduce compile time
        choice((wildcard, lit_pat, paren_or_tuple, list_pat, con_nullary, var_or_as)).boxed()
    })
}

/// Parse a pattern field.
fn p_pfield<'a>(
    pat: impl Parser<'a, TokenStream<'a>, CPat, ParserExtra<'a>> + Clone,
) -> impl Parser<'a, TokenStream<'a>, CPatField, ParserExtra<'a>> + Clone {
    p_field_id()
        .then_ignore(equals())
        .then(pat)
        .map(|(name, pattern)| CPatField {
            name,
            pattern,
            span: Span::DUMMY,
        })
}

// ============================================================================
// Expression parsing
// ============================================================================

/// Suffix operation for expression parsing.
#[derive(Clone)]
enum SuffixOp {
    Select(Id),
    Index(CExpr),
    Range(CExpr, CExpr),
    TypeAsc(CQType),
    Update(Vec<CFieldInit>),
    App(CExpr),
}

/// Parse an expression.
fn p_expr<'a>() -> impl Parser<'a, TokenStream<'a>, CExpr, ParserExtra<'a>> + Clone {
    recursive(|expr| {
        let lit_expr = p_literal_with_pos().map(|(lit, pos)| CExpr::Lit(lit, pos));
        let var_expr = p_var_id().map(CExpr::Var);
        // Underscore as expression means undefined/don't care
        // Haskell: anyExprAt pos = CAny pos UDontCare
        let underscore_expr = underscore_pos().map(|pos| CExpr::Any {
            position: pos,
            kind: UndefKind::DontCare,
            span: Span::DUMMY,
        });

        // Parenthesized operator as expression, like (^) or (==) or (:<-)
        // This must be tried BEFORE paren_or_tuple since operators aren't valid expressions
        let paren_op_expr = lparen()
            .ignore_then(p_any_sym())
            .then_ignore(rparen())
            .map(CExpr::Var);

        // Field accessor as expression: (.field) creates lambda \x -> x.field
        // Mirrors Haskell: lp ..+ dot ..+ pFieldId +.. rp >>- CLam (Right id_x) . CSelect (cVar id_x)
        let field_accessor = lparen()
            .ignore_then(dot())
            .ignore_then(p_field_id())
            .then_ignore(rparen())
            .map(|field| {
                let mut x = Id::new("_x", Position::unknown());
                x.add_prop(bsc_syntax::id::IdProp::BadName);
                CExpr::Lambda(
                    vec![CPat::Var(x.clone())],
                    Box::new(CExpr::Select(Box::new(CExpr::Var(x)), field, Span::DUMMY)),
                    Span::DUMMY,
                )
            });

        let paren_or_tuple = expr
            .clone()
            .separated_by(comma())
            .collect::<Vec<_>>()
            .delimited_by(lparen(), rparen())
            .map(|exprs| {
                if exprs.is_empty() {
                    CExpr::Struct(Some(true), Id::qualified("Prelude", "PrimUnit", Position::unknown()), vec![], Span::DUMMY)
                } else if exprs.len() == 1 {
                    exprs.into_iter().next().unwrap()
                } else {
                    CExpr::Tuple(exprs, Span::DUMMY)
                }
            });

        let list_expr = expr
            .clone()
            .separated_by(comma())
            .collect::<Vec<_>>()
            .delimited_by(lbracket(), rbracket())
            .map(|exprs| CExpr::List(exprs, Span::DUMMY));

        let if_expr = kw_if_pos()
            .then(expr.clone())
            .then(osm().ignore_then(kw_then()).ignore_then(expr.clone()))
            .then(osm().ignore_then(kw_else()).ignore_then(expr.clone()))
            .map(|(((pos, cond), then_e), else_e)| {
                CExpr::If(pos, Box::new(cond), Box::new(then_e), Box::new(else_e))
            });

        // Lambda: \ patterns -> body
        // Haskell's cLam function (CParser.hs) handles this with special cases:
        // - \x -> e becomes CLam (Right x) e
        // - \_ -> e becomes CLam (Left pos) e
        // - \(Pat x) -> e becomes Cletseq [CLValue _lam [CClause [Pat x] [] e]] (CVar _lam)
        // - \x y -> e becomes CLam (Right x) (CLam (Right y) e)
        let lambda = backslash_pos()
            .then(p_pattern().repeated().at_least(1).collect::<Vec<_>>())
            .then_ignore(arrow())
            .then(expr.clone())
            .map(|((pos, pats), body)| c_lam(pos, pats, body));

        let let_expr = kw_let()
            .ignore_then(p_defl_block(expr.clone()))
            .then_ignore(kw_in())
            .then(expr.clone())
            .map(|(defls, body)| CExpr::LetRec(defls, Box::new(body), Span::DUMMY));

        let letseq_expr = kw_letseq()
            .ignore_then(p_defl_block(expr.clone()))
            .then_ignore(kw_in())
            .then(expr.clone())
            .map(|(defls, body)| CExpr::LetSeq(defls, Box::new(body), Span::DUMMY));

        let case_expr = kw_case_pos()
            .then(expr.clone())
            .then_ignore(kw_of())
            .then(p_case_arm_block(expr.clone()))
            .map(|((pos, scrutinee), arms)| CExpr::Case(pos, Box::new(scrutinee), arms));

        let do_expr = kw_do()
            .ignore_then(p_stmt_block(expr.clone()))
            .map(|stmts| CExpr::Do {
                recursive: true,
                stmts,
                span: Span::DUMMY,
            });

        let action_expr = kw_action_pos()
            .then(p_stmt_block(expr.clone()))
            .map(|(pos, stmts)| CExpr::Action(pos, stmts));

        let con_or_struct = p_con_id()
            .then(p_field_block(expr.clone()).or_not())
            .map(|(name, opt_fields)| {
                if let Some(fields) = opt_fields {
                    CExpr::Struct(None, name, fields, Span::DUMMY)
                } else {
                    CExpr::Con(name, Vec::new(), Span::DUMMY)
                }
            });

        let valueof_expr = kw_valueof_pos()
            .then(p_atype())
            .map(|(pos, ty)| {
                let valueof_id = Id::qualified("Prelude", "primValueOf", pos.clone());
                // Haskell: idBit = prelude_id_no fsBit (uses noPosition)
                let bit_tycon = CType::Con(Id::qualified("Prelude", "Bit", Position::unknown()));
                let bit_ty = CType::Apply(Box::new(bit_tycon), Box::new(ty), Span::DUMMY);
                let qtype = CQType { context: vec![], ty: bit_ty, span: Span::DUMMY };
                // Haskell: anyExprAt pos = CAny pos UDontCare
                let any_expr = CExpr::Any { position: pos, kind: UndefKind::DontCare, span: Span::DUMMY };
                let hastype_expr = CExpr::TypeAscription(Box::new(any_expr), qtype, Span::DUMMY);
                CExpr::Apply(Box::new(CExpr::Var(valueof_id)), vec![hastype_expr], Span::DUMMY)
            });

        let stringof_expr = kw_stringof_pos()
            .then(p_atype())
            .map(|(pos, ty)| {
                let stringof_id = Id::qualified("Prelude", "primStringOf", pos.clone());
                // Haskell: idStringProxy = prelude_id_no fsStringProxy (uses noPosition)
                let proxy_tycon = CType::Con(Id::qualified("Prelude", "StringProxy", Position::unknown()));
                let proxy_ty = CType::Apply(Box::new(proxy_tycon), Box::new(ty), Span::DUMMY);
                let qtype = CQType { context: vec![], ty: proxy_ty, span: Span::DUMMY };
                // Haskell: anyExprAt pos = CAny pos UDontCare
                let any_expr = CExpr::Any { position: pos, kind: UndefKind::DontCare, span: Span::DUMMY };
                let hastype_expr = CExpr::TypeAscription(Box::new(any_expr), qtype, Span::DUMMY);
                CExpr::Apply(Box::new(CExpr::Var(stringof_id)), vec![hastype_expr], Span::DUMMY)
            });

        let rules_expr = kw_rules()
            .ignore_then(p_rule_block(expr.clone()))
            .map(|rules| CExpr::Rules(vec![], rules, Span::DUMMY));

        // Interface expression: interface [ConId] [{ definitions }]
        // The block is optional - `interface Empty` is valid with no definitions
        // Haskell: Cinterface Position (Maybe Id) [CDefl]
        let interface_expr = kw_interface_pos()
            .then(p_con_id().or_not())
            .then(p_tdefl_block(expr.clone()).or_not())
            .map(|((pos, opt_id), opt_defls)| CExpr::Interface(pos, opt_id, opt_defls.unwrap_or_default()));

        // Module verilog expression: module verilog "Name" (params) clocks resets { ports } [sched]
        // The expr parameter is threaded through to handle parameter expressions
        let verilog_param = lparen()
            .ignore_then(string_lit())
            .then_ignore(comma())
            .then(expr.clone())
            .then_ignore(rparen())
            .map(|((name, _, _), value)| (SmolStr::new(&name), value));

        let verilog_params = verilog_param
            .separated_by(comma())
            .collect::<Vec<_>>()
            .delimited_by(lparen(), rparen())
            .or_not()
            .map(|opt| opt.unwrap_or_default());

        let verilog_clocks = string_lit()
            .map(|(s, _, _)| SmolStr::new(&s))
            .separated_by(comma())
            .at_least(1)
            .collect::<Vec<_>>();

        let verilog_resets = string_lit()
            .map(|(s, _, _)| SmolStr::new(&s))
            .separated_by(comma())
            .collect::<Vec<_>>();

        let verilog_port_props = lbrace()
            .ignore_then(p_var_id().separated_by(comma()).collect::<Vec<_>>())
            .then_ignore(rbrace())
            .or_not()
            .map(|opt| opt.unwrap_or_default());

        let verilog_port_name = string_lit()
            .map(|(s, _, _)| SmolStr::new(&s))
            .then(verilog_port_props.clone());

        let verilog_mult = lbracket()
            .ignore_then(integer())
            .then_ignore(rbracket())
            .map(|(_, _, val, _, _)| val.to_string().parse::<i64>().unwrap_or(1))
            .or_not()
            .map(|opt| opt.unwrap_or(1));

        let verilog_field = p_field_id()
            .then(verilog_mult)
            .then_ignore(equals())
            .then(verilog_port_name.clone().repeated().collect::<Vec<_>>())
            .then(
                comma()
                    .ignore_then(any().try_map(|t: Token, span| {
                        if let TokenKind::VarId(s) = &t.kind {
                            if s.as_str() == "output" { return Ok(()); }
                        }
                        Err(Rich::custom(span, "expected output"))
                    }))
                    .ignore_then(verilog_port_name.clone())
                    .or_not(),
            )
            .then(
                comma()
                    .ignore_then(any().try_map(|t: Token, span| {
                        if let TokenKind::VarId(s) = &t.kind {
                            if s.as_str() == "enable" { return Ok(()); }
                        }
                        Err(Rich::custom(span, "expected enable"))
                    }))
                    .ignore_then(verilog_port_name.clone())
                    .or_not(),
            );

        let verilog_fields = verilog_field
            .separated_by(dsm())
            .allow_trailing()
            .collect::<Vec<_>>()
            .delimited_by(lc(), rc());

        let verilog_sched_elem = lbracket()
            .ignore_then(p_var_id().separated_by(comma()).collect::<Vec<_>>())
            .then_ignore(rbracket())
            .or(p_var_id().map(|id| vec![id]));

        let verilog_sched_op = any().try_map(|t: Token, span| {
            if let TokenKind::VarSym(s) | TokenKind::ConSym(s) = &t.kind {
                let s_str = s.as_str();
                match s_str {
                    "<>" => return Ok(SchedConflictOp::CF),
                    "<" => return Ok(SchedConflictOp::SB),
                    "<<" => return Ok(SchedConflictOp::SBR),
                    "><" => return Ok(SchedConflictOp::C),
                    _ => {}
                }
            }
            Err(Rich::custom(span, "expected scheduling operator (<, <<, <>, or ><)"))
        });

        let verilog_sched_item = verilog_sched_elem
            .clone()
            .then(verilog_sched_op)
            .then(verilog_sched_elem)
            .map(|((lhs, op), rhs)| (lhs, op, rhs));

        let verilog_schedule = lbracket()
            .ignore_then(verilog_sched_item.separated_by(comma()).collect::<Vec<_>>())
            .then_ignore(rbracket())
            .or_not();

        // For verilog module name: can be string literal or expression (variable)
        // Haskell: l L_verilog ..+ aexp
        let verilog_name_expr = choice((
            string_lit().map(|(s, _, pos)| CExpr::Lit(Literal::String(s.to_string()), pos)),
            var_expr.clone(),
            p_con_id().map(|id| CExpr::Con(id, vec![], Span::DUMMY)),
        ));

        let verilog_body = kw_verilog()
            .ignore_then(verilog_name_expr)
            .then(verilog_params)
            .then(verilog_clocks)
            .then(verilog_resets)
            .then(verilog_fields)
            .then(verilog_schedule)
            .map(|(((((name_expr, params), clocks), resets), fields), schedule)| {
                x_classic_module_verilog(name_expr, params, clocks, resets, fields, schedule)
            });

        let module_body = p_mstmt_block(expr.clone())
            .or_not()
            .map(|opt_items| opt_items.unwrap_or_default());

        let module_expr = choice((
            kw_module().ignore_then(verilog_body),
            kw_module_pos().then(module_body).map(|(pos, items)| CExpr::Module(pos, items)),
        ));

        // RESTRUCTURED TO MATCH HASKELL BSC PARSER:
        //
        // Haskell structure (from CParser.hs):
        //   aexp' = pAny ||! pVarId ||! pConId ||! paren_tuple ||! literals ||! blkexp
        //   blkexp = do ||! action  (only these two are "atomic block expressions")
        //   aexp = aexp' +.+ many suff  (suffixes: .field, [index])
        //   expX = let/letseq/case/lambda/if-then-else/struct/valueOf/stringOf
        //        ||! aexp `into` (where/type-ascription/struct-update/many-aexp-for-application)
        //        ||! rules ||! interface ||! module
        //
        // Key insight: rules, interface, module are at expX level, NOT aexp level.
        // This is critical for avoiding excessive backtracking and stack usage.
        //
        // blkexp: block expressions that can be atomic (do, action)
        let blkexp = choice((
            do_expr,
            action_expr,
        ));

        // aexp': truly atomic expressions (Haskell: pAny ||! pVarId ||! pConId ||! paren ||! lit ||! blkexp)
        let aexp_prime = choice((
            blkexp,
            lit_expr,
            paren_op_expr,   // Must come before paren_or_tuple - operators aren't expressions
            field_accessor,  // (.field) must come before paren_or_tuple
            paren_or_tuple,
            list_expr,
            underscore_expr,
            var_expr,        // Qualified vars like Prelude.map - must come before con_or_struct!
            con_or_struct,   // Qualified cons like List.Nil
        ))
        .boxed();

        // aexp: atomic expression with suffixes (.field, [index])
        // Haskell: aexp = aexp' +.+ many suff
        let aexp_suffix = choice((
            dot().ignore_then(p_field_id()).map(SuffixOp::Select),
            lbracket()
                .ignore_then(expr.clone())
                .then(colon().ignore_then(expr.clone()).or_not())
                .then_ignore(rbracket())
                .map(|(idx, hi_opt)| {
                    if let Some(hi) = hi_opt {
                        SuffixOp::Range(idx, hi)
                    } else {
                        SuffixOp::Index(idx)
                    }
                }),
        ));

        let aexp = aexp_prime.clone().foldl(
            aexp_suffix.repeated(),
            |acc, op| match op {
                SuffixOp::Select(field) => CExpr::Select(Box::new(acc), field, Span::DUMMY),
                SuffixOp::Index(idx) => CExpr::Index {
                    expr: Box::new(acc),
                    index: Box::new(idx),
                    span: Span::DUMMY,
                },
                SuffixOp::Range(hi, lo) => CExpr::IndexRange {
                    expr: Box::new(acc),
                    hi: Box::new(hi),
                    lo: Box::new(lo),
                    span: Span::DUMMY,
                },
                _ => unreachable!(),
            },
        ).boxed();

        // expX: main expression parser
        // Haskell: expX = let/letseq/case/lambda/if ||! aexp `into` (suffixes) ||! rules ||! interface ||! module
        //
        // The key pattern from Haskell is:
        //   aexp `into` (\e -> ... ||! many aexp >>- cmtApply 9 e)
        // This means: parse an aexp, then parse MORE aexps for function application
        //
        // Non-aexp expressions that are at expX level (not atomic):
        let expX_non_aexp = choice((
            if_expr,
            lambda,
            let_expr,
            letseq_expr,
            case_expr,
            valueof_expr,
            stringof_expr,
            rules_expr,
            interface_expr,
            module_expr,
        ));

        // expX with aexp and its continuations
        // Haskell: aexp `into` (\e -> where-block ||! subscript ||! type-asc ||! struct-update ||! many aexp)
        //
        // Suffix operations that can follow an aexp (type ascription, struct update, application)
        // Note: .field and [index] are already handled in aexp above
        let aexp_continuation = choice((
            dcolon().ignore_then(p_qtype()).map(SuffixOp::TypeAsc),
            p_field_block(expr.clone()).map(SuffixOp::Update),
            aexp.clone().map(SuffixOp::App),
        ));

        // aexp with application/type-ascription/struct-update
        // This matches Haskell's: aexp `into` (\e -> ... ||! many aexp >>- cmtApply 9 e)
        let aexp_with_continuation = aexp.clone().foldl(
            aexp_continuation.repeated(),
            |acc, op| match op {
                SuffixOp::TypeAsc(ty) => CExpr::TypeAscription(Box::new(acc), ty, Span::DUMMY),
                SuffixOp::Update(fields) => CExpr::Update(Box::new(acc), fields, Span::DUMMY),
                SuffixOp::App(arg) => c_apply(acc, vec![arg]),
                _ => unreachable!(),
            },
        );

        // expX: the main expression form (not including operators)
        // Haskell: expX = let/letseq/case/lambda/if ||! aexp-with-stuff ||! rules ||! interface ||! module
        let app = choice((
            expX_non_aexp,
            aexp_with_continuation,
        ))
        .boxed();

        // Parse operator expressions: exp0 = exp00 >>- (\x->case x of [CRand e] -> e; _ -> COper x)
        // This builds a flat list of operands and operators for later fixity resolution.
        // Use p_any_sym to handle both symbol operators (like +) and backtick-quoted identifiers (like `bind`)
        //
        // Haskell structure:
        //   exp00 = expX +.+ exp01 >>- (\ (e, es) -> CRand e : es)
        //   exp01 = pOper +.+ exp00 >>- (\ (o, es) -> CRator 2 o : es) ||! succeed []
        //
        // Result: [CRand e1, CRator 2 op1, CRand e2, CRator 2 op2, CRand e3, ...]
        // If only one operand, return the expression directly; otherwise wrap in OperChain.
        app.clone()
            .then(p_any_sym().then(app.clone()).repeated().collect::<Vec<_>>())
            .map(|(first, rest)| {
                if rest.is_empty() {
                    // Single expression, no operators - return as is
                    first
                } else {
                    // Build OperChain with alternating operands and operators
                    // Pattern: [Expr(e1), Operator(op1), Expr(e2), Operator(op2), Expr(e3), ...]
                    let mut operands = Vec::with_capacity(1 + rest.len() * 2);
                    operands.push(COperand::Expr(first));
                    for (op, expr) in rest {
                        operands.push(COperand::Operator { arity: 2, name: op });
                        operands.push(COperand::Expr(expr));
                    }
                    CExpr::OperChain(operands, Span::DUMMY)
                }
            })
            .boxed()
    })
}

/// Parse a block of field initializations.
fn p_field_block<'a>(
    expr: impl Parser<'a, TokenStream<'a>, CExpr, ParserExtra<'a>> + Clone,
) -> impl Parser<'a, TokenStream<'a>, Vec<CFieldInit>, ParserExtra<'a>> + Clone {
    p_field_id()
        .then_ignore(equals())
        .then(expr)
        .map(|(name, value)| CFieldInit {
            name,
            value,
            span: Span::DUMMY,
        })
        .separated_by(sm())
        .allow_trailing()
        .collect::<Vec<_>>()
        .delimited_by(lc(), rc())
}

fn merge_clauses(defls: Vec<CDefl>) -> Vec<CDefl> {
    let mut result: Vec<CDefl> = Vec::new();
    for defl in defls {
        match &defl {
            CDefl::Value(id, clauses, quals, _span) => {
                // Try to merge with a preceding Value with the same name
                if let Some(CDefl::Value(prev_id, prev_clauses, prev_quals, _prev_span)) = result.last_mut() {
                    if prev_id.name() == id.name() && prev_quals.is_empty() && quals.is_empty() {
                        prev_clauses.extend(clauses.clone());
                        continue;
                    }
                }
                // Try to merge with a preceding ValueSign with the same name
                // This handles: "name :: Type" followed by "name = expr [when cond]" on separate lines
                // The qualifiers from the Value definition are moved to the ValueSign's existing_quals
                if let Some(CDefl::ValueSign(def, existing_quals, _)) = result.last_mut() {
                    if let CDef::Untyped { name: prev_name, clauses: prev_clauses, .. } = def {
                        if prev_name.name() == id.name() && existing_quals.is_empty() {
                            prev_clauses.extend(clauses.clone());
                            existing_quals.extend(quals.clone());
                            continue;
                        }
                    }
                }
                result.push(defl);
            }
            _ => result.push(defl),
        }
    }
    result
}

/// Parse a block of local definitions.
fn p_defl_block<'a>(
    expr: impl Parser<'a, TokenStream<'a>, CExpr, ParserExtra<'a>> + Clone,
) -> impl Parser<'a, TokenStream<'a>, Vec<CDefl>, ParserExtra<'a>> + Clone {
    p_defl(expr)
        .separated_by(dsm())
        .allow_trailing()
        .collect::<Vec<_>>()
        .delimited_by(lc(), rc())
        .map(merge_clauses)
}

/// Parse a local definition.
/// Uses p_field_id to handle both regular identifiers and parenthesized operators like (==).
fn p_defl<'a>(
    expr: impl Parser<'a, TokenStream<'a>, CExpr, ParserExtra<'a>> + Clone,
) -> impl Parser<'a, TokenStream<'a>, CDefl, ParserExtra<'a>> + Clone {
    // For typed definitions, Haskell supports two forms:
    //   1. name :: Type = expr   (inline assignment)
    //   2. name :: Type          (type signature only, followed later by name = expr)
    //
    // The merge_clauses function handles combining a type signature with subsequent
    // value bindings of the same name.

    // Type signature with inline assignment: name :: Type = expr
    let with_sig_inline = p_field_id()
        .then_ignore(dcolon())
        .then(p_qtype())
        .then(equals().ignore_then(expr.clone()).map(|e| {
            vec![CClause {
                patterns: vec![],
                qualifiers: vec![],
                body: e,
                span: Span::DUMMY,
            }]
        }))
        .map(|((name, ty), clauses)| {
            CDefl::ValueSign(
                CDef::Untyped {
                    name,
                    ty,
                    clauses,
                    span: Span::DUMMY,
                },
                vec![],
                Span::DUMMY,
            )
        });

    // Standalone type signature: name :: Type (no assignment)
    // This will be merged with a subsequent name = expr by merge_clauses
    let type_sig_only = p_field_id()
        .then_ignore(dcolon())
        .then(p_qtype())
        .map(|(name, ty)| {
            CDefl::ValueSign(
                CDef::Untyped {
                    name,
                    ty,
                    clauses: vec![],  // Empty clauses - will be filled by merge_clauses
                    span: Span::DUMMY,
                },
                vec![],
                Span::DUMMY,
            )
        });

    let pattern_bind = p_pattern()
        .then_ignore(equals())
        .then(expr.clone())
        .map(|(pat, e)| CDefl::Match(pat, e, Span::DUMMY));

    let without_sig = p_field_id()
        .then(p_apat(p_pattern()).repeated().collect::<Vec<_>>())
        .then_ignore(equals())
        .then(expr.clone())
        .map(|((name, pats), body)| {
            CDefl::Value(
                name,
                vec![CClause {
                    patterns: pats,
                    qualifiers: vec![],
                    body,
                    span: Span::DUMMY,
                }],
                vec![],
                Span::DUMMY,
            )
        });

    // Try in order: with_sig_inline first (most specific), then type_sig_only, then without_sig, then pattern_bind
    with_sig_inline.or(type_sig_only).or(without_sig).or(pattern_bind)
}

/// Parse a clause (pattern matching line).
/// Matches Haskell: pClause i = piEq i ..+ many pAPat +.+ pOQuals +.+ eq ..+ exp0
///                          ||! pAPat +.+ psEq i ..+ pAPat +.+ pOQuals +.+ eq ..+ exp0
/// Uses p_field_id to accept both regular identifiers and parenthesized operators like (:<-).
fn p_clause<'a>(
    expr: impl Parser<'a, TokenStream<'a>, CExpr, ParserExtra<'a>> + Clone,
) -> impl Parser<'a, TokenStream<'a>, CClause, ParserExtra<'a>> + Clone {
    let prefix_form = p_field_id()
        .ignore_then(p_apat(p_pattern()).repeated().collect::<Vec<_>>())
        .then(p_oquals(expr.clone()))
        .then_ignore(equals())
        .then(expr.clone())
        .map(|((pats, quals), body)| CClause {
            patterns: pats,
            qualifiers: quals,
            body,
            span: Span::DUMMY,
        });

    let infix_form = p_apat(p_pattern())
        .then_ignore(p_any_sym())
        .then(p_apat(p_pattern()))
        .then(p_oquals(expr.clone()))
        .then_ignore(equals())
        .then(expr)
        .map(|(((pat1, pat2), quals), body)| CClause {
            patterns: vec![pat1, pat2],
            qualifiers: quals,
            body,
            span: Span::DUMMY,
        });

    choice((infix_form, prefix_form))
}

/// Parse optional qualifiers (guards).
fn p_oquals<'a>(
    expr: impl Parser<'a, TokenStream<'a>, CExpr, ParserExtra<'a>> + Clone,
) -> impl Parser<'a, TokenStream<'a>, Vec<CQual>, ParserExtra<'a>> + Clone {
    kw_when()
        .ignore_then(
            p_qual(expr)
                .separated_by(comma())
                .at_least(1)
                .collect::<Vec<_>>(),
        )
        .or_not()
        .map(|opt| opt.unwrap_or_default())
}

/// Parse a qualifier.
/// Matches Haskell: pQual = pPat +.+ l L_larrow ..+ pExpr >>> CQGen noType
fn p_qual<'a>(
    expr: impl Parser<'a, TokenStream<'a>, CExpr, ParserExtra<'a>> + Clone,
) -> impl Parser<'a, TokenStream<'a>, CQual, ParserExtra<'a>> + Clone {
    let generator = p_pattern()
        .then_ignore(larrow())
        .then(expr.clone())
        .map(|(p, e)| {
            // Use CType::NoType to match Haskell's noType = TGen noPosition (-1)
            CQual::Gen(CType::NoType, p, e)
        });

    let filter = expr.map(CQual::Filter);

    generator.or(filter)
}

/// Parse a block of case arms.
fn p_case_arm_block<'a>(
    expr: impl Parser<'a, TokenStream<'a>, CExpr, ParserExtra<'a>> + Clone,
) -> impl Parser<'a, TokenStream<'a>, Vec<CCaseArm>, ParserExtra<'a>> + Clone {
    p_case_arm(expr)
        .separated_by(dsm())
        .allow_trailing()
        .collect::<Vec<_>>()
        .delimited_by(lc(), rc())
}

/// Parse a case arm.
fn p_case_arm<'a>(
    expr: impl Parser<'a, TokenStream<'a>, CExpr, ParserExtra<'a>> + Clone,
) -> impl Parser<'a, TokenStream<'a>, CCaseArm, ParserExtra<'a>> + Clone {
    p_pattern()
        .then(p_oquals(expr.clone()))
        .then_ignore(arrow())
        .then(expr)
        .map(|((pattern, qualifiers), body)| CCaseArm {
            pattern,
            qualifiers,
            body,
            span: Span::DUMMY,
        })
}

/// Parse a block of statements.
fn p_stmt_block<'a>(
    expr: impl Parser<'a, TokenStream<'a>, CExpr, ParserExtra<'a>> + Clone + 'a,
) -> impl Parser<'a, TokenStream<'a>, Vec<CStmt>, ParserExtra<'a>> + Clone {
    p_stmt(expr)
        .separated_by(dsm())
        .allow_trailing()
        .collect::<Vec<_>>()
        .delimited_by(lc(), rc())
}

/// Parse a statement.
/// Matches Haskell pStmt which handles hide pragmas via pHVarId
fn p_stmt<'a>(
    expr: impl Parser<'a, TokenStream<'a>, CExpr, ParserExtra<'a>> + Clone + 'a,
) -> impl Parser<'a, TokenStream<'a>, CStmt, ParserExtra<'a>> + Clone {
    // Bind with variable identifier (possibly with hide pragma)
    // Matches Haskell: pHVarId `into` \i -> dc ..+ pQType `into` \t ->
    //     sm ..+ piHEq i ..+ larrow ..+ pExpr  (separate type sig and binding)
    //     ||! larrow ..+ pExpr  (combined type sig and binding)
    let var_typed_bind = p_h_var_id()
        .then_ignore(dcolon())
        .then(p_qtype())
        .then(
            dsm()  // semicolon separator
                .ignore_then(p_h_var_id())  // same var id repeated (possibly with hide pragma)
                .then_ignore(larrow())
                .then(expr.clone())
                .map(|(id, e)| (Some(id), e))
                .or(larrow().ignore_then(expr.clone()).map(|e| (None, e))),  // direct arrow form
        )
        .map(|((id, ty), (opt_id, e))| {
            let mut keep_id = match opt_id {
                Some(j) => {
                    let mut final_id = id.clone();
                    if j.has_prop(&IdProp::Hide) {
                        final_id.add_prop(IdProp::Hide);
                    }
                    if j.has_prop(&IdProp::HideAll) {
                        final_id.add_prop(IdProp::HideAll);
                    }
                    final_id
                }
                None => id,
            };
            keep_id.add_prop(IdProp::Keep);
            CStmt::BindT {
                pattern: CPat::Var(keep_id),
                instance_name: None,
                pragmas: Vec::new(),
                ty,
                expr: e,
                span: Span::DUMMY,
            }
        });

    let var_bind = p_h_var_id()
        .then_ignore(larrow())
        .then(expr.clone())
        .map(|(id, e)| {
            let mut keep_id = id;
            keep_id.add_prop(IdProp::Keep);
            CStmt::Bind {
                pattern: CPat::Var(keep_id),
                instance_name: None,
                pragmas: Vec::new(),
                expr: e,
                span: Span::DUMMY,
            }
        });

    // Bind with general pattern (no hide pragma possible)
    let pat_typed_bind = p_pattern()
        .then_ignore(dcolon())
        .then(p_qtype())
        .then_ignore(larrow())
        .then(expr.clone())
        .map(|((pattern, ty), e)| CStmt::BindT {
            pattern,
            instance_name: None,
            pragmas: Vec::new(),
            ty,
            expr: e,
            span: Span::DUMMY,
        });

    let pat_bind = p_pattern()
        .then_ignore(larrow())
        .then(expr.clone())
        .map(|(pattern, e)| CStmt::Bind {
            pattern,
            instance_name: None,
            pragmas: Vec::new(),
            expr: e,
            span: Span::DUMMY,
        });

    let let_stmt = kw_let()
        .ignore_then(p_defl_block(expr.clone()))
        .map(|defls| CStmt::LetRec(defls, Span::DUMMY));

    let letseq_stmt = kw_letseq()
        .ignore_then(p_defl_block(expr.clone()))
        .map(|defls| CStmt::LetSeq(defls, Span::DUMMY));

    let expr_stmt = expr.map(|e| CStmt::Expr {
        instance_name: None,
        expr: e,
        span: Span::DUMMY,
    });

    // Use .boxed() to reduce compile time
    // Try var binds first (more specific due to hide pragma handling), then pattern binds
    choice((var_typed_bind, var_bind, pat_typed_bind, pat_bind, let_stmt, letseq_stmt, expr_stmt)).boxed()
}

/// Parse a definition with optional `when` guards.
/// Mirrors Haskell pTDefl:
///   pTDefl = pDefl `into` \ d ->
///       l L_when ..+ sepBy1 pQual cm >>- updWhen d
///       ||! succeed d
fn p_tdefl<'a>(
    expr: impl Parser<'a, TokenStream<'a>, CExpr, ParserExtra<'a>> + Clone,
) -> impl Parser<'a, TokenStream<'a>, CDefl, ParserExtra<'a>> + Clone {
    p_defl(expr.clone())
        .then(
            kw_when()
                .ignore_then(
                    p_qual(expr)
                        .separated_by(comma())
                        .at_least(1)
                        .collect::<Vec<_>>()
                )
                .or_not()
        )
        .map(|(mut defl, opt_quals)| {
            if let Some(quals) = opt_quals {
                match &mut defl {
                    CDefl::ValueSign(def, existing_quals, _) => {
                        existing_quals.extend(quals);
                    }
                    CDefl::Value(_, _, existing_quals, _) => {
                        existing_quals.extend(quals);
                    }
                    CDefl::Match(_, _, _) => {}
                }
            }
            defl
        })
}

/// Parse a block of interface definitions.
/// Handles empty interface blocks (like `interface` with no definitions).
/// Mirrors Haskell: blockOf tp pTDefl = startBlock tp ..+ hBlock (sepBy pTDefl dsm +.. osm)
fn p_tdefl_block<'a>(
    expr: impl Parser<'a, TokenStream<'a>, CExpr, ParserExtra<'a>> + Clone,
) -> impl Parser<'a, TokenStream<'a>, Vec<CDefl>, ParserExtra<'a>> + Clone {
    // Block with layout or explicit braces - allows empty blocks
    // Layout processing inserts { } even for empty blocks
    lc().ignore_then(
        p_tdefl(expr)
            .separated_by(dsm())
            .allow_trailing()
            .collect::<Vec<_>>()
            .then_ignore(osm())
    ).then_ignore(rc())
        .map(merge_clauses)
}

/// Parse a block of module statements.
fn p_mstmt_block<'a>(
    expr: impl Parser<'a, TokenStream<'a>, CExpr, ParserExtra<'a>> + Clone + 'a,
) -> impl Parser<'a, TokenStream<'a>, Vec<CModuleItem>, ParserExtra<'a>> + Clone {
    p_mstmt(expr)
        .separated_by(dsm())
        .allow_trailing()
        .collect::<Vec<_>>()
        .delimited_by(lc(), rc())
}

/// Parse a module statement (mirrors Haskell's pMstmt).
fn p_mstmt<'a>(
    expr: impl Parser<'a, TokenStream<'a>, CExpr, ParserExtra<'a>> + Clone + 'a,
) -> impl Parser<'a, TokenStream<'a>, CModuleItem, ParserExtra<'a>> + Clone {
    let tuple_interface = kw_interface_pos()
        .then(
            lparen()
                .ignore_then(expr.clone().separated_by(comma()).collect::<Vec<_>>())
                .then_ignore(rparen()),
        )
        .map(|(pos, exprs)| CModuleItem::TupleInterface(pos, exprs));

    let regular_interface = kw_interface_pos()
        .then(p_con_id().or_not())
        .then(p_tdefl_block(expr.clone()).or_not())
        .map(|((pos, opt_con_id), opt_defls)| {
            CModuleItem::Interface(CExpr::Interface(pos, opt_con_id, opt_defls.unwrap_or_default()))
        });

    let interface_item = choice((tuple_interface, regular_interface));

    let rules = kw_rules()
        .ignore_then(p_rule_block(expr.clone()).or_not())
        .map(|opt_rules| {
            CModuleItem::Rules(CExpr::Rules(vec![], opt_rules.unwrap_or_default(), Span::DUMMY))
        });

    let stmt = p_stmt(expr.clone()).map(CModuleItem::Stmt);

    choice((interface_item, rules, stmt)).boxed()
}

/// Parse a block of rules.
fn p_rule_block<'a>(
    expr: impl Parser<'a, TokenStream<'a>, CExpr, ParserExtra<'a>> + Clone + 'a,
) -> impl Parser<'a, TokenStream<'a>, Vec<CRule>, ParserExtra<'a>> + Clone {
    p_rule(expr)
        .separated_by(dsm())
        .allow_trailing()
        .collect::<Vec<_>>()
        .delimited_by(lc(), rc())
}

/// Helper to match a pragma keyword (case-insensitive for ASSERT, case-sensitive for others).
fn pragma_keyword<'a>(
    kw: &'static str,
    case_insensitive: bool,
) -> impl Parser<'a, TokenStream<'a>, (), ParserExtra<'a>> + Clone {
    any().try_map(move |t: Token, span| {
        if let TokenKind::VarId(s) | TokenKind::ConId(s) = &t.kind {
            let matches = if case_insensitive {
                s.eq_ignore_ascii_case(kw)
            } else {
                s.as_str() == kw
            };
            if matches {
                return Ok(());
            }
        }
        Err(Rich::custom(span, format!("expected {}", kw)))
    })
}

/// Parse a rule pragma.
fn p_rule_pragma<'a>() -> impl Parser<'a, TokenStream<'a>, RulePragma, ParserExtra<'a>> + Clone {
    use bsc_syntax::RulePragma;

    let fire_when_enabled = pragma_keyword("ASSERT", true)
        .ignore_then(pragma_keyword("fire", false))
        .ignore_then(kw_when())
        .ignore_then(pragma_keyword("enabled", false))
        .to(RulePragma::FireWhenEnabled);

    let no_implicit_conditions = pragma_keyword("ASSERT", true)
        .ignore_then(pragma_keyword("no", false))
        .ignore_then(pragma_keyword("implicit", false))
        .ignore_then(pragma_keyword("conditions", false))
        .to(RulePragma::NoImplicitConditions);

    let can_schedule_first = pragma_keyword("ASSERT", true)
        .ignore_then(pragma_keyword("can", false))
        .ignore_then(pragma_keyword("schedule", false))
        .ignore_then(pragma_keyword("first", false))
        .to(RulePragma::CanFire);

    let aggressive_implicit_conditions = pragma_keyword("aggressive_implicit_conditions", false)
        .to(RulePragma::AggressiveConditions);

    let conservative_implicit_conditions = pragma_keyword("conservative_implicit_conditions", false)
        .to(RulePragma::ConservativeConditions);

    let hide = pragma_keyword("hide", false).to(RulePragma::Hide);

    let no_warn = pragma_keyword("no_warn", false).to(RulePragma::NoWarn);

    let warn_all_conflicts = pragma_keyword("warn_all_conflicts", false).to(RulePragma::WarnAllConflicts);

    let clock_crossing_rule = pragma_keyword("clock_crossing", false)
        .ignore_then(pragma_keyword("rule", false))
        .to(RulePragma::ClockCrossingRule);

    lpragma()
        .ignore_then(choice((
            fire_when_enabled,
            no_implicit_conditions,
            can_schedule_first,
            aggressive_implicit_conditions,
            conservative_implicit_conditions,
            hide,
            no_warn,
            warn_all_conflicts,
            clock_crossing_rule,
        )))
        .then_ignore(rpragma())
}

/// Parse a rule.
fn p_rule<'a>(
    expr: impl Parser<'a, TokenStream<'a>, CExpr, ParserExtra<'a>> + Clone + 'a,
) -> impl Parser<'a, TokenStream<'a>, CRule, ParserExtra<'a>> + Clone {
    recursive(move |rule| {
        let pragmas = p_rule_pragma()
            .then_ignore(osm())
            .repeated()
            .collect::<Vec<_>>();

        let label = p_aexpr(expr.clone()).then_ignore(colon()).or_not();
        let quals = p_oquals(expr.clone());

        let body = darrow().ignore_then(expr.clone()).map(|e| CRule::Rule {
            pragmas: vec![],
            name: None,
            qualifiers: vec![],
            body: e,
            span: Span::DUMMY,
        });

        let nested = kw_rules()
            .ignore_then(
                rule.separated_by(dsm())
                    .allow_trailing()
                    .collect::<Vec<_>>()
                    .delimited_by(lc(), rc()),
            )
            .map(|rules| CRule::Nested {
                pragmas: vec![],
                name: None,
                qualifiers: vec![],
                rules,
                span: Span::DUMMY,
            });

        pragmas
            .then(label)
            .then(quals)
            .then(body.or(nested))
            .map(|(((rule_pragmas, opt_name), quals), mut rule)| {
                match &mut rule {
                    CRule::Rule {
                        pragmas,
                        name,
                        qualifiers,
                        ..
                    } => {
                        *pragmas = rule_pragmas;
                        *name = opt_name;
                        *qualifiers = quals;
                    }
                    CRule::Nested {
                        pragmas,
                        name,
                        qualifiers,
                        ..
                    } => {
                        *pragmas = rule_pragmas;
                        *name = opt_name;
                        *qualifiers = quals;
                    }
                }
                rule
            })
    })
}

/// Parse an atomic expression (for rule labels).
/// This includes parenthesized expressions which can contain full expressions.
fn p_aexpr<'a>(
    expr: impl Parser<'a, TokenStream<'a>, CExpr, ParserExtra<'a>> + Clone + 'a,
) -> impl Parser<'a, TokenStream<'a>, CExpr, ParserExtra<'a>> + Clone {
    let lit = p_literal_with_pos().map(|(lit, pos)| CExpr::Lit(lit, pos));
    let var = p_var_id().map(CExpr::Var);
    let con = p_con_id().map(|con| CExpr::Con(con, Vec::new(), Span::DUMMY));
    let paren = expr
        .delimited_by(lparen(), rparen());

    choice((paren, lit, var, con))
}

// ============================================================================
// Top-level definition parsing
// ============================================================================

/// Parse a top-level definition.
fn p_defn<'a>() -> impl Parser<'a, TokenStream<'a>, Vec<CDefn>, ParserExtra<'a>> + Clone {
    // Use .boxed() on definition alternatives to reduce compile time
    choice((
        p_data_defn(),
        p_type_defn().map(|d| vec![d]),
        p_struct_defn().map(|d| vec![d]),
        p_interface_defn().map(|d| vec![d]),
        p_class_defn().map(|d| vec![d]),
        p_instance_defn().map(|d| vec![d]),
        p_foreign_defn().map(|d| vec![d]),
        p_primitive_defn().map(|d| vec![d]),
        p_pragma_defn().map(|d| vec![d]),
        p_var_defn().map(|d| vec![d]),
        empty().to(vec![]),
    ))
    .boxed()
}

/// Compute internal summands and struct definitions from original summands.
///
/// Mirrors the logic in CParser.hs `doCon` function:
/// - For constructors with no fields: arg_type = PrimUnit, no struct
/// - For constructors with single positional field (no context): arg_type = that field's type, no struct
/// - For constructors with multiple or named fields: creates a struct type AND a Cstruct definition
///
/// Returns: (struct_definitions, internal_summands)
fn compute_data_summands(
    type_name: &IdK,
    type_params: &[Id],
    original_summands: &[COriginalSummand],
    deriving: &[CTypeclass],
) -> (Vec<CDefn>, Vec<CInternalSummand>) {
    let mut struct_defs = Vec::new();
    let mut internal_summands = Vec::new();

    for (tag, summand) in original_summands.iter().enumerate() {
        let is_positional = summand.field_names.is_none();
        let first_con_name = summand.names.first().expect("summand must have at least one name");

        let arg_type = match &summand.arg_types[..] {
            [] => {
                CType::Con(Id::qualified("Prelude", "PrimUnit", Position::unknown()))
            }
            [single_qtype] if is_positional && single_qtype.context.is_empty() => {
                single_qtype.ty.clone()
            }
            _ => {
                let struct_type_name = make_struct_type_name(type_name, first_con_name);

                let fields = make_struct_fields(summand, is_positional);

                let struct_def = CDefn::Struct(CStructDef {
                    visible: true,
                    sub_type: StructSubType::DataCon {
                        type_id: idk_name(type_name).clone(),
                        named_fields: !is_positional,
                    },
                    name: IdK::Plain(struct_type_name.clone()),
                    params: type_params.to_vec(),
                    fields,
                    deriving: deriving.to_vec(),
                    span: Span::DUMMY,
                });
                struct_defs.push(struct_def);

                let base_type = CType::Con(struct_type_name);
                type_params.iter().fold(base_type, |acc, param| {
                    CType::Apply(
                        Box::new(acc),
                        Box::new(CType::Var(param.clone())),
                        Span::DUMMY,
                    )
                })
            }
        };

        internal_summands.push(CInternalSummand {
            names: summand.names.clone(),
            arg_type,
            tag_encoding: tag as i64,
        });
    }

    (struct_defs, internal_summands)
}

/// Extract the name Id from IdK
fn idk_name(idk: &IdK) -> &Id {
    match idk {
        IdK::Plain(id) => id,
        IdK::WithKind(id, _) => id,
        IdK::WithPartialKind(id, _) => id,
    }
}

/// Create struct fields from a summand's arg_types.
///
/// For positional fields, generates tuple field names (1, 2, 3, ...).
/// For named fields, uses the field names from the summand.
fn make_struct_fields(summand: &COriginalSummand, is_positional: bool) -> Vec<CField> {
    if is_positional {
        summand
            .arg_types
            .iter()
            .enumerate()
            .map(|(i, qtype)| {
                let field_name = Id::new(&format!("_{}", i + 1), Position::unknown());
                CField {
                    name: field_name,
                    pragmas: None,
                    ty: qtype.clone(),
                    default: vec![],
                    orig_type: None,
                    span: Span::DUMMY,
                }
            })
            .collect()
    } else {
        let field_names = summand.field_names.as_ref().unwrap();
        summand
            .arg_types
            .iter()
            .zip(field_names.iter())
            .map(|(qtype, name)| CField {
                name: name.clone(),
                pragmas: None,
                ty: qtype.clone(),
                default: vec![],
                orig_type: None,
                span: Span::DUMMY,
            })
            .collect()
    }
}

/// Create the struct type name for a data constructor.
///
/// Mirrors `mkTCId` from Haskell: creates a qualified name like "TypeName_$ConName"
/// with IdP_TypeJoin property storing the original type and constructor ids.
fn make_struct_type_name(type_name: &IdK, con_name: &Id) -> Id {
    let type_id = match type_name {
        IdK::Plain(id) => id,
        IdK::WithKind(id, _) => id,
        IdK::WithPartialKind(id, _) => id,
    };
    let combined_name = format!("{}_${}", type_id.name(), con_name.name());
    let mut result = Id::new(&combined_name, type_id.position().clone());
    result.set_qualifier(type_id.qualifier().clone());
    result.add_prop(IdProp::TypeJoin {
        original_type: Box::new(type_id.clone()),
        constructor: Box::new(con_name.clone()),
    });
    result
}

/// Parse a data type definition.
///
/// Returns a Vec<CDefn> because data types with multiple fields or named fields
/// also generate auxiliary struct definitions.
fn p_data_defn<'a>() -> impl Parser<'a, TokenStream<'a>, Vec<CDefn>, ParserExtra<'a>> + Clone {
    kw_data()
        .ignore_then(p_tycon_id_k())
        .then(p_tyvar_id().repeated().collect::<Vec<_>>())
        .then_ignore(equals())
        .then(
            p_summand()
                .separated_by(bar())
                .at_least(1)
                .collect::<Vec<_>>(),
        )
        .then(p_deriving())
        .map(|(((name, params), summands), deriving)| {
            let (struct_defs, internal_summands) =
                compute_data_summands(&name, &params, &summands, &deriving);
            let data_def = CDefn::Data(CDataDef {
                visible: true,
                name,
                params,
                original_summands: summands,
                internal_summands,
                deriving,
                span: Span::DUMMY,
            });
            let mut result = vec![data_def];
            result.extend(struct_defs);
            result
        })
}

/// Parse a type constructor with optional kind.
fn p_tycon_id_k<'a>() -> impl Parser<'a, TokenStream<'a>, IdK, ParserExtra<'a>> + Clone {
    let plain = p_tycon_id().map(IdK::Plain);

    let with_kind = lparen()
        .ignore_then(p_tycon_id())
        .then_ignore(dcolon())
        .then(p_kind())
        .then_ignore(rparen())
        .map(|(id, kind)| IdK::WithKind(id, kind));

    with_kind.or(plain)
}

/// Parse a data summand (constructor).
fn p_summand<'a>() -> impl Parser<'a, TokenStream<'a>, COriginalSummand, ParserExtra<'a>> + Clone {
    let names = p_con_id()
        .map(|id| vec![id])
        .or(lparen()
            .ignore_then(p_con_id().separated_by(comma()).collect::<Vec<_>>())
            .then_ignore(rparen()));

    let record_fields = p_qfield()
        .separated_by(sm())
        .allow_trailing()
        .collect::<Vec<_>>()
        .delimited_by(lc(), rc())
        .map(|fields| {
            let (names, types): (Vec<_>, Vec<_>) = fields.into_iter().unzip();
            (Some(names), types)
        });

    let positional_args = p_atype().repeated().collect::<Vec<_>>().map(|types| {
        let qtypes: Vec<CQType> = types
            .into_iter()
            .map(|ty| CQType {
                context: vec![],
                ty,
                span: Span::DUMMY,
            })
            .collect();
        (None, qtypes)
    });

    names
        .then(record_fields.or(positional_args))
        .map(|(names, (field_names, arg_types))| COriginalSummand {
            names,
            arg_types,
            field_names,
            tag_encoding: None,
        })
}

/// Parse a qualified field.
fn p_qfield<'a>() -> impl Parser<'a, TokenStream<'a>, (Id, CQType), ParserExtra<'a>> + Clone {
    p_field_id().then_ignore(dcolon()).then(p_qtype())
}

/// Parse deriving clause.
fn p_deriving<'a>() -> impl Parser<'a, TokenStream<'a>, Vec<CTypeclass>, ParserExtra<'a>> + Clone {
    kw_deriving()
        .ignore_then(
            p_tycon_id()
                .map(|name| CTypeclass { name })
                .separated_by(comma())
                .collect::<Vec<_>>()
                .delimited_by(lparen(), rparen()),
        )
        .or_not()
        .map(|opt| opt.unwrap_or_default())
}

/// Parse a type synonym definition.
fn p_type_defn<'a>() -> impl Parser<'a, TokenStream<'a>, CDefn, ParserExtra<'a>> + Clone {
    kw_type()
        .ignore_then(p_tycon_id_k())
        .then(p_tyvar_id().repeated().collect::<Vec<_>>())
        .then_ignore(equals())
        .then(p_type())
        .map(|((name, params), body)| {
            CDefn::Type(CTypeDef {
                name,
                params,
                body,
                span: Span::DUMMY,
            })
        })
}

/// Parse a struct definition.
fn p_struct_defn<'a>() -> impl Parser<'a, TokenStream<'a>, CDefn, ParserExtra<'a>> + Clone {
    kw_struct()
        .ignore_then(p_tycon_id_k())
        .then(p_tyvar_id().repeated().collect::<Vec<_>>())
        .then_ignore(equals())
        .then(p_struct_field_block())
        .then(p_deriving())
        .map(|(((name, params), fields), deriving)| {
            CDefn::Struct(CStructDef {
                visible: true,
                sub_type: StructSubType::Struct,
                name,
                params,
                fields,
                deriving,
                span: Span::DUMMY,
            })
        })
}

/// Parse a struct field block (with explicit or layout braces).
fn p_struct_field_block<'a>(
) -> impl Parser<'a, TokenStream<'a>, Vec<CField>, ParserExtra<'a>> + Clone {
    p_struct_field()
        .separated_by(dsm())
        .allow_trailing()
        .collect::<Vec<_>>()
        .delimited_by(lc(), rc())
}

/// Parse a struct field.
fn p_struct_field<'a>() -> impl Parser<'a, TokenStream<'a>, CField, ParserExtra<'a>> + Clone {
    p_field_id()
        .then_ignore(dcolon())
        .then(p_qtype())
        .then(p_ifc_prags())
        .then(p_field_clauses())
        .map(|(((name, ty), pragmas), default)| CField {
            name,
            pragmas: if pragmas.is_empty() { None } else { Some(pragmas) },
            ty,
            default,
            orig_type: None,
            span: Span::DUMMY,
        })
}


/// Parse optional field clauses (for default method implementations).
/// This handles both simple `= expr` defaults and function clauses with patterns.
fn p_field_clauses<'a>() -> impl Parser<'a, TokenStream<'a>, Vec<CClause>, ParserExtra<'a>> + Clone
{
    // Simple `= expr` default
    let simple_default = equals()
        .ignore_then(p_expr())
        .map(|e| {
            vec![CClause {
                patterns: vec![],
                qualifiers: vec![],
                body: e,
                span: Span::DUMMY,
            }]
        });

    simple_default.or_not().map(|opt| opt.unwrap_or_default())
}

/// Item in a class body - either a method signature or a default clause.
#[derive(Debug, Clone)]
enum ClassBodyItem {
    /// Method signature: (==) :: a -> a -> Bool
    Signature { name: Id, ty: CQType },
    /// Default clause: x == y = not (x /= y)
    Clause { name: Id, clause: CClause },
}

/// Parse a method signature: name :: type
fn p_method_signature<'a>() -> impl Parser<'a, TokenStream<'a>, ClassBodyItem, ParserExtra<'a>> + Clone {
    p_field_id()
        .then_ignore(dcolon())
        .then(p_qtype())
        .map(|(name, ty)| ClassBodyItem::Signature { name, ty })
}

/// Parse a default implementation clause (prefix or infix form).
fn p_method_default_clause<'a>() -> impl Parser<'a, TokenStream<'a>, ClassBodyItem, ParserExtra<'a>> + Clone {
    // Infix form: pat op pat = expr (e.g., "x == y = not (x /= y)")
    let infix = p_apat(p_pattern())
        .then(p_operator())
        .then(p_apat(p_pattern()))
        .then_ignore(equals())
        .then(p_expr())
        .map(|(((p1, op), p2), body)| {
            ClassBodyItem::Clause {
                name: op,
                clause: CClause {
                    patterns: vec![p1, p2],
                    qualifiers: vec![],
                    body,
                    span: Span::DUMMY,
                },
            }
        });

    // Prefix form: name patterns = expr (e.g., "foo x y = x + y" or "cshowP = cshow")
    // Use p_field_id to handle both plain names and parenthesized operators
    // Note: zero or more patterns (not at_least(1)) to handle nullary defaults like "cshowP = cshow"
    let prefix = p_field_id()
        .then(p_apat(p_pattern()).repeated().collect::<Vec<_>>())
        .then_ignore(equals())
        .then(p_expr())
        .map(|((name, pats), body)| {
            ClassBodyItem::Clause {
                name,
                clause: CClause {
                    patterns: pats,
                    qualifiers: vec![],
                    body,
                    span: Span::DUMMY,
                },
            }
        });

    // Try infix first (has operator in middle), then prefix
    infix.or(prefix)
}

/// Parse a class body item (either signature or default clause).
fn p_class_body_item<'a>() -> impl Parser<'a, TokenStream<'a>, ClassBodyItem, ParserExtra<'a>> + Clone {
    // Try method signature first (has ::), then default clause
    p_method_signature().or(p_method_default_clause())
}

/// Group class body items into CField structures.
/// Signatures define methods, clauses are attached to the preceding signature with matching name.
fn group_class_body_items(items: Vec<ClassBodyItem>) -> Vec<CField> {
    let mut fields: Vec<CField> = Vec::new();

    for item in items {
        match item {
            ClassBodyItem::Signature { name, ty } => {
                fields.push(CField {
                    name,
                    pragmas: None,
                    ty,
                    default: vec![],
                    orig_type: None,
                    span: Span::DUMMY,
                });
            }
            ClassBodyItem::Clause { name, clause } => {
                // Find the field with matching name and add the clause
                if let Some(field) = fields.iter_mut().rev().find(|f| f.name.name() == name.name()) {
                    field.default.push(clause);
                }
                // If no matching field found, the clause is orphaned (ignore for now)
            }
        }
    }

    fields
}

/// Parse a class body with type signatures and optional default implementations.
fn p_class_body<'a>() -> impl Parser<'a, TokenStream<'a>, Vec<CField>, ParserExtra<'a>> + Clone {
    p_class_body_item()
        .separated_by(dsm())
        .allow_trailing()
        .collect::<Vec<_>>()
        .delimited_by(lc(), rc())
        .map(group_class_body_items)
}

/// Parse an interface definition.
fn p_interface_defn<'a>() -> impl Parser<'a, TokenStream<'a>, CDefn, ParserExtra<'a>> + Clone {
    kw_interface()
        .ignore_then(p_tycon_id_k())
        .then(p_tyvar_id().repeated().collect::<Vec<_>>())
        .then(p_ifc_prags())
        .then_ignore(equals())
        .then(p_struct_field_block())
        .then(p_deriving())
        .map(|((((name, params), prags), fields), deriving)| {
            CDefn::Struct(CStructDef {
                visible: true,
                sub_type: StructSubType::Interface(prags),
                name,
                params,
                fields,
                deriving,
                span: Span::DUMMY,
            })
        })
}

/// Parse interface pragmas.
/// Format: {-# pragma = value, pragma2 = value2 #-}
/// Pragmas: prefix, ready, enable, result, always_ready, always_enabled, arg_names
fn p_ifc_prags<'a>() -> impl Parser<'a, TokenStream<'a>, Vec<IfcPragma>, ParserExtra<'a>> + Clone {
    let string_val = string_lit().map(|(s, _, _)| s);

    let prefix_pragma = select! { Token { kind: TokenKind::VarId(s), .. } if s.as_str() == "prefix" || s.as_str() == "prefixs" => () }
        .ignore_then(equals())
        .ignore_then(string_val.clone())
        .map(|s| IfcPragma::Prefix(s));

    let result_pragma = select! { Token { kind: TokenKind::VarId(s), .. } if s.as_str() == "result" => () }
        .ignore_then(equals())
        .ignore_then(string_val.clone())
        .map(|s| IfcPragma::Result(s));

    let ready_pragma = select! { Token { kind: TokenKind::VarId(s), .. } if s.as_str() == "ready" => () }
        .ignore_then(equals())
        .ignore_then(string_val.clone())
        .map(|s| IfcPragma::Ready(s));

    let enable_pragma = select! { Token { kind: TokenKind::VarId(s), .. } if s.as_str() == "enable" => () }
        .ignore_then(equals())
        .ignore_then(string_val.clone())
        .map(|s| IfcPragma::Enable(s));

    let arg_names_pragma = select! { Token { kind: TokenKind::VarId(s), .. } if s.as_str() == "arg_names" => () }
        .ignore_then(equals())
        .ignore_then(
            p_var_id().or(p_con_id())
                .separated_by(comma())
                .collect::<Vec<_>>()
                .delimited_by(lbracket(), rbracket())
        )
        .map(|ids| IfcPragma::ArgNames(ids));

    let always_ready_pragma = select! { Token { kind: TokenKind::VarId(s), .. } if s.as_str() == "always_ready" => () }
        .map(|_| IfcPragma::AlwaysReady);
    let always_enabled_pragma = select! { Token { kind: TokenKind::VarId(s), .. } if s.as_str() == "always_enabled" => () }
        .map(|_| IfcPragma::AlwaysEnabled);

    let single_pragma = choice((
        arg_names_pragma,
        prefix_pragma,
        result_pragma,
        ready_pragma,
        enable_pragma,
        always_ready_pragma,
        always_enabled_pragma,
    ));

    lpragma()
        .ignore_then(single_pragma.separated_by(comma()).collect::<Vec<_>>())
        .then_ignore(rpragma())
        .or_not()
        .map(|opt| opt.unwrap_or_default())
}

/// Parse a class definition.
fn p_class_defn<'a>() -> impl Parser<'a, TokenStream<'a>, CDefn, ParserExtra<'a>> + Clone {
    kw_class()
        .ignore_then(p_opt_coherence())
        .then(p_preds())
        .then(p_tycon_id_k())
        .then(p_tyvar_id().repeated().collect::<Vec<_>>())
        .then(p_fundeps())
        .then_ignore(kw_where())
        .then(p_class_body())
        .map(
            |(((((coherence, supers), name), params), fundeps), methods)| {
                CDefn::Class(CClassDef {
                    incoherent_matches: coherence,
                    supers,
                    name,
                    params,
                    fundeps,
                    methods,
                    span: Span::DUMMY,
                })
            },
        )
}

/// Parse optional coherence annotation.
fn p_opt_coherence<'a>() -> impl Parser<'a, TokenStream<'a>, Option<bool>, ParserExtra<'a>> + Clone
{
    kw_incoherent()
        .to(Some(true))
        .or(kw_coherent().to(Some(false)))
        .or_not()
        .map(|opt| opt.flatten())
}

/// Parse functional dependencies.
fn p_fundeps<'a>() -> impl Parser<'a, TokenStream<'a>, Vec<CFunDep>, ParserExtra<'a>> + Clone {
    bar()
        .ignore_then(
            p_fundep()
                .separated_by(comma())
                .at_least(1)
                .collect::<Vec<_>>(),
        )
        .or_not()
        .map(|opt| opt.unwrap_or_default())
}

/// Parse a single functional dependency.
fn p_fundep<'a>() -> impl Parser<'a, TokenStream<'a>, CFunDep, ParserExtra<'a>> + Clone {
    p_tyvar_id()
        .repeated()
        .collect::<Vec<_>>()
        .then_ignore(arrow())
        .then(p_tyvar_id().repeated().collect::<Vec<_>>())
        .map(|(from, to)| CFunDep { from, to })
}

/// Parse an instance definition.
fn p_instance_defn<'a>() -> impl Parser<'a, TokenStream<'a>, CDefn, ParserExtra<'a>> + Clone {
    kw_instance()
        .ignore_then(p_qtype())
        .then_ignore(kw_where())
        .then(p_defl_block(p_expr()))
        .map(|(ty, methods)| {
            CDefn::Instance(CInstanceDef {
                ty,
                methods,
                span: Span::DUMMY,
            })
        })
}

/// Parse a foreign declaration.
fn p_foreign_defn<'a>() -> impl Parser<'a, TokenStream<'a>, CDefn, ParserExtra<'a>> + Clone {
    // Haskell: l L_foreign ..+ pVarId +.+ dc ..+ pQType +.+ opt (eq ..+ pString)
    //          +.+ opt (cm ..+ lp ..+ many pString +.+ pForeignRes +.. rp)
    // Example: foreign vfork :: Bit n -> Bit m = "Fork",("i","o")
    // pForeignRes = cm ..+ (pString >>- (: []) ||! lp ..+ sepBy1 pString cm +.. rp)
    // So outputs can be: ,"single" or ,("a","b","c")
    //
    // Structure: ,( inputs... , outputs )
    // where inputs = zero or more strings
    // and outputs = single string OR parenthesized list of strings
    let foreign_res = comma().ignore_then(choice((
        string_lit().map(|(s, _, _)| vec![s]),
        string_lit()
            .map(|(s, _, _)| s)
            .separated_by(comma())
            .at_least(1)
            .collect::<Vec<_>>()
            .delimited_by(lparen(), rparen()),
    )));

    // Parse input strings (strings before the comma that starts foreign_res)
    // Use a different approach: parse all comma-separated strings, then the last one or parens is outputs
    // Actually simpler: parse ,( then strings separated by comma, where the LAST comma starts foreign_res
    // This is tricky because we need to know which comma starts foreign_res...
    //
    // For now, use a simpler approach that covers common cases:
    // ,("in","out") or ,("in1","in2",("out1","out2"))
    let ports_parser = comma()
        .ignore_then(lparen())
        .ignore_then(
            // Collect all strings (some are inputs, then comma, then outputs)
            string_lit()
                .map(|(s, _, _)| s)
                .separated_by(comma())
                .collect::<Vec<_>>(),
        )
        .then(
            // Optional nested parens for outputs
            comma()
                .ignore_then(
                    string_lit()
                        .map(|(s, _, _)| s)
                        .separated_by(comma())
                        .at_least(1)
                        .collect::<Vec<_>>()
                        .delimited_by(lparen(), rparen()),
                )
                .or_not(),
        )
        .then_ignore(rparen())
        .map(|(strings, nested_outputs)| {
            if let Some(outputs) = nested_outputs {
                // Inputs are `strings`, outputs are `outputs`
                (strings, outputs)
            } else if strings.len() >= 2 {
                // Last string is output, rest are inputs
                let mut inputs = strings;
                let output = inputs.pop().unwrap();
                (inputs, vec![output])
            } else if strings.len() == 1 {
                // Single string, assume it's the output with no inputs
                (vec![], strings)
            } else {
                (vec![], vec![])
            }
        })
        .or_not();

    kw_foreign()
        .ignore_then(p_var_id())
        .then_ignore(dcolon())
        .then(p_qtype())
        .then(
            equals()
                .ignore_then(string_lit())
                .map(|(s, _, _)| Some(s))
                .or_not()
                .map(|opt| opt.flatten()),
        )
        .then(ports_parser)
        .map(|(((name, ty), foreign_name), ports)| {
            CDefn::Foreign(CForeignDef {
                name,
                ty,
                foreign_name,
                ports,
                span: Span::DUMMY,
            })
        })
}

/// Parse a primitive declaration.
fn p_primitive_defn<'a>() -> impl Parser<'a, TokenStream<'a>, CDefn, ParserExtra<'a>> + Clone {
    let prim_val = kw_primitive()
        .ignore_then(p_var_id())
        .then_ignore(dcolon())
        .then(p_qtype())
        .map(|(name, ty)| {
            CDefn::Primitive(CPrimitiveDef {
                name,
                ty,
                span: Span::DUMMY,
            })
        });

    let prim_type = kw_primitive()
        .ignore_then(kw_type())
        .ignore_then(p_tycon_id())
        .then_ignore(dcolon())
        .then(p_kind())
        .map(|(name, kind)| {
            CDefn::PrimitiveType(CPrimitiveTypeDef {
                name,
                kind,
                span: Span::DUMMY,
            })
        });

    prim_type.or(prim_val)
}

/// Parse a pragma keyword (NOINLINE, etc.)
/// Note: hide/hideall are handled at identifier level by p_h_var_id
fn p_pragma_keyword<'a>() -> impl Parser<'a, TokenStream<'a>, (), ParserExtra<'a>> + Clone {
    any()
        .try_map(|t: Token, span| {
            match &t.kind {
                TokenKind::ConId(s) if s == "NOINLINE" => Ok(()),
                _ => Err(Rich::custom(span, "expected pragma keyword"))
            }
        })
}

/// Parse a pragma definition at the top level.
/// Handles: {-# noinline id #-}, {-# properties id = {...} #-}
/// Note: {-# hide #-} and {-# hideall #-} are handled at identifier level by p_h_var_id
fn p_pragma_defn<'a>() -> impl Parser<'a, TokenStream<'a>, CDefn, ParserExtra<'a>> + Clone {
    // noinline pragma: {-# noinline id1 id2 ... #-} (can also accept NOINLINE for compatibility)
    // Returns multiple CDefn::Pragma for multiple identifiers
    let noinline = lpragma()
        .ignore_then(
            any().try_map(|t: Token, span| {
                if let TokenKind::VarId(s) | TokenKind::ConId(s) = &t.kind {
                    if s.eq_ignore_ascii_case("noinline") {
                        return Ok(());
                    }
                }
                Err(Rich::custom(span, "expected noinline"))
            }),
        )
        .ignore_then(
            p_var_id()
                .separated_by(osm())
                .at_least(1)
                .collect::<Vec<_>>(),
        )
        .then_ignore(osm())
        .then_ignore(rpragma())
        .map(|ids| CDefn::Pragma(CPragma::NoInline(ids.into_iter().next().unwrap())));

    // Properties pragma: {-# properties id = { name = "value", ... } #-}
    // Parse a single property: name = "value"
    let prop = var_id()
        .then_ignore(equals())
        .then(string_lit())
        .map(|((name, _), (value, _, _))| CPragmaProperty {
            name: name.to_string(),
            value: Some(value),
        });

    // Parse property list: { name = "value", name2 = "value2" }
    let prop_list = prop
        .separated_by(comma())
        .allow_trailing()
        .collect::<Vec<_>>()
        .delimited_by(lc(), rc());

    let properties = lpragma()
        .ignore_then(
            any().try_map(|t: Token, span| {
                if let TokenKind::VarId(s) = &t.kind {
                    if s == "properties" {
                        return Ok(());
                    }
                }
                Err(Rich::custom(span, "expected properties"))
            }),
        )
        .ignore_then(p_var_id())
        .then_ignore(equals())
        .then(prop_list)
        .then_ignore(rpragma())
        .map(|(id, props)| CDefn::Pragma(CPragma::Properties(id, props)));

    noinline.or(properties)
}

/// Parse a variable definition.
/// Handles both regular variable identifiers and parenthesized operators like (:<-).
fn p_var_defn<'a>() -> impl Parser<'a, TokenStream<'a>, CDefn, ParserExtra<'a>> + Clone {
    // Use p_field_id to accept both variable identifiers and parenthesized operators
    let with_sig = p_field_id()
        .then_ignore(dcolon())
        .then(p_qtype())
        .then(
            dsm()
                .ignore_then(p_clause(p_expr()))
                .repeated()
                .at_least(1)
                .collect::<Vec<_>>()
                .or(equals().ignore_then(p_expr()).map(|e| {
                    vec![CClause {
                        patterns: vec![],
                        qualifiers: vec![],
                        body: e,
                        span: Span::DUMMY,
                    }]
                })),
        )
        .map(|((name, ty), clauses)| {
            CDefn::ValueSign(CDef::Untyped {
                name,
                ty,
                clauses,
                span: Span::DUMMY,
            })
        });

    let without_sig = p_field_id()
        .then(p_apat(p_pattern()).repeated().collect::<Vec<_>>())
        .then_ignore(equals())
        .then(p_expr())
        .map(|((name, pats), body)| {
            CDefn::Value(CValueDef {
                name,
                clauses: vec![CClause {
                    patterns: pats,
                    qualifiers: vec![],
                    body,
                    span: Span::DUMMY,
                }],
                span: Span::DUMMY,
            })
        });

    with_sig.or(without_sig)
}

// ============================================================================
// Verilog Module Transformation
// ============================================================================

type VerilogFieldParsed = (
    (
        ((Id, i64), Vec<(SmolStr, Vec<Id>)>),
        Option<(SmolStr, Vec<Id>)>,
    ),
    Option<(SmolStr, Vec<Id>)>,
);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SchedConflictOp {
    CF,
    SB,
    SBR,
    C,
}

type VerilogSchedItem = (Vec<Id>, SchedConflictOp, Vec<Id>);

fn get_position(expr: &CExpr) -> Position {
    match expr {
        CExpr::Lambda(_, _, _) => Position::unknown(),
        CExpr::LetRec(_, _, _) | CExpr::LetSeq(_, _, _) => Position::unknown(),
        CExpr::If(pos, _, _, _) => pos.clone(),
        CExpr::Case(pos, _, _) => pos.clone(),
        CExpr::Rules(_, _, _) => Position::unknown(),
        CExpr::Var(id) | CExpr::Con(id, _, _) => id.position().clone(),
        CExpr::ConTyped { con_name, .. } => con_name.position().clone(),
        CExpr::Select(e, _, _) => get_position(e),
        CExpr::Index { expr, .. } => get_position(expr),
        CExpr::Apply(f, _, _) | CExpr::TaskApply(f, _, _) => get_position(f),
        CExpr::Lit(_, pos) => pos.clone(),
        CExpr::Any { position, .. } => position.clone(),
        CExpr::AnyTyped { position, .. } => position.clone(),
        CExpr::Do { stmts, .. } => {
            if let Some(first) = stmts.first() {
                match first {
                    CStmt::Bind { pattern, .. } => match pattern {
                        CPat::Var(id) => id.position().clone(),
                        _ => Position::unknown(),
                    },
                    _ => Position::unknown(),
                }
            } else {
                Position::unknown()
            }
        }
        CExpr::Module(pos, _) => pos.clone(),
        CExpr::Interface(pos, _, _) => pos.clone(),
        CExpr::Struct(_, id, _, _) => id.position().clone(),
        CExpr::Update(e, _, _) => get_position(e),
        CExpr::TypeAscription(e, _, _) => get_position(e),
        CExpr::OperChain(ops, _) => {
            if let Some(COperand::Expr(e)) = ops.first() {
                get_position(e)
            } else {
                Position::unknown()
            }
        }
        CExpr::Tuple(exprs, _) => {
            if let Some(first) = exprs.first() {
                get_position(first)
            } else {
                Position::unknown()
            }
        }
        CExpr::List(_, _) => Position::unknown(),
        CExpr::ModuleVerilog { name_expr, .. } => get_position(name_expr),
        CExpr::Paren(e, _) => get_position(e),
        _ => Position::unknown(),
    }
}

fn x_classic_module_verilog(
    name_expr: CExpr,
    params: Vec<(SmolStr, CExpr)>,
    clocks: Vec<SmolStr>,
    resets: Vec<SmolStr>,
    fields: Vec<VerilogFieldParsed>,
    schedule: Option<Vec<VerilogSchedItem>>,
) -> CExpr {
    let pos = get_position(&name_expr);
    let id_clk = Id::new("_clk__", Position::unknown());
    let id_rst = Id::new("_rst__", Position::unknown());
    let id_expose_current_clock = Id::qualified("Prelude", "exposeCurrentClock", Position::unknown());
    let id_expose_current_reset = Id::qualified("Prelude", "exposeCurrentReset", Position::unknown());
    let id_clock_type = Id::qualified("Prelude", "Clock", Position::unknown());
    let id_reset_type = Id::qualified("Prelude", "Reset", Position::unknown());
    let t_clock = CType::Con(id_clock_type);
    let t_reset = CType::Con(id_reset_type);
    let clock_names: Vec<Id> = (1..=clocks.len())
        .map(|i| Id::new(&format!("_clk__{}", i), Position::unknown()))
        .collect();
    let reset_names: Vec<Id> = (1..=resets.len())
        .map(|i| Id::new(&format!("_rst__{}", i), Position::unknown()))
        .collect();
    let default_clk = clock_names.first().cloned();
    let default_rst = reset_names.first().cloned();
    let clock_stmt: Vec<CModuleItem> = if clocks.is_empty() {
        vec![]
    } else {
        vec![CModuleItem::Stmt(CStmt::BindT {
            pattern: CPat::Var(id_clk.clone()),
            instance_name: None,
            pragmas: vec![],
            ty: CQType {
                context: vec![],
                ty: t_clock.clone(),
                span: Span::DUMMY,
            },
            expr: CExpr::Var(id_expose_current_clock),
            span: Span::DUMMY,
        })]
    };
    let reset_stmt: Vec<CModuleItem> = if resets.is_empty() {
        vec![]
    } else {
        vec![CModuleItem::Stmt(CStmt::BindT {
            pattern: CPat::Var(id_rst.clone()),
            instance_name: None,
            pragmas: vec![],
            ty: CQType {
                context: vec![],
                ty: t_reset.clone(),
                span: Span::DUMMY,
            },
            expr: CExpr::Var(id_expose_current_reset),
            span: Span::DUMMY,
        })]
    };
    let clock_info = VClockInfo {
        input_clocks: clock_names
            .iter()
            .zip(clocks.iter())
            .map(|(id, name)| {
                (
                    id.clone(),
                    Some((VName::new(name.to_string()), Either::Left(false))),
                )
            })
            .collect(),
        output_clocks: vec![],
        ancestor_clocks: vec![],
        sibling_clocks: vec![],
    };
    let reset_info = VResetInfo {
        input_resets: reset_names
            .iter()
            .zip(resets.iter())
            .map(|(id, name)| {
                (
                    id.clone(),
                    (Some(VName::new(name.to_string())), default_clk.clone()),
                )
            })
            .collect(),
        output_resets: vec![],
    };
    let clock_args: Vec<(VArgInfo, CExpr)> = clock_names
        .iter()
        .map(|id| (VArgInfo::ClockArg(id.clone()), CExpr::Var(id_clk.clone())))
        .collect();
    let reset_args: Vec<(VArgInfo, CExpr)> = reset_names
        .iter()
        .map(|id| (VArgInfo::ResetArg(id.clone()), CExpr::Var(id_rst.clone())))
        .collect();
    let param_args: Vec<(VArgInfo, CExpr)> = params
        .iter()
        .map(|(name, expr)| {
            (
                VArgInfo::Param(VName::new(name.to_string())),
                expr.clone(),
            )
        })
        .collect();
    let mut all_args = Vec::new();
    all_args.extend(clock_args);
    all_args.extend(reset_args);
    all_args.extend(param_args);
    fn parse_port_props(props: &[Id]) -> Vec<VeriPortProp> {
        props
            .iter()
            .filter_map(|id| {
                match id.name().as_str() {
                    "reg" => Some(VeriPortProp::Reg),
                    "const" => Some(VeriPortProp::Const),
                    "unused" => Some(VeriPortProp::Unused),
                    "inhigh" => Some(VeriPortProp::InHigh),
                    _ => None,
                }
            })
            .collect()
    }
    let method_infos: Vec<VFieldInfo> = fields
        .iter()
        .map(|((((name, mult), input_ports), output), enable)| {
            let inputs: Vec<VPort> = input_ports
                .iter()
                .map(|(port_name, props)| VPort {
                    name: VName::new(port_name.to_string()),
                    props: parse_port_props(props),
                })
                .collect();
            let output_port = output.as_ref().map(|(port_name, props)| VPort {
                name: VName::new(port_name.to_string()),
                props: parse_port_props(props),
            });
            let enable_port = enable.as_ref().map(|(port_name, props)| VPort {
                name: VName::new(port_name.to_string()),
                props: parse_port_props(props),
            });
            VFieldInfo::Method {
                name: name.clone(),
                clock: default_clk.clone(),
                reset: default_rst.clone(),
                multiplicity: BigInt::from(*mult),
                inputs,
                output: output_port,
                enable: enable_port,
            }
        })
        .collect();
    let mut cf_pairs: Vec<(Id, Id)> = vec![];
    let mut sb_pairs: Vec<(Id, Id)> = vec![];
    let mut sbr_pairs: Vec<(Id, Id)> = vec![];
    let mut c_pairs: Vec<(Id, Id)> = vec![];
    if let Some(sched_items) = schedule {
        for (lhs_methods, op, rhs_methods) in sched_items {
            for i1 in &lhs_methods {
                for i2 in &rhs_methods {
                    match op {
                        SchedConflictOp::CF => cf_pairs.push((i1.clone(), i2.clone())),
                        SchedConflictOp::SB => sb_pairs.push((i1.clone(), i2.clone())),
                        SchedConflictOp::SBR => sbr_pairs.push((i1.clone(), i2.clone())),
                        SchedConflictOp::C => c_pairs.push((i1.clone(), i2.clone())),
                    }
                }
            }
        }
    }
    let sched_info = SchedInfo {
        method_conflict_info: MethodConflictInfo {
            conflict_free: cf_pairs,
            sequenced_before: sb_pairs,
            mutually_exclusive: vec![],
            preempts: vec![],
            sequenced_before_reverse: sbr_pairs,
            conflicts: c_pairs,
            external: vec![],
        },
        rules_between_methods: vec![],
        rules_before_methods: vec![],
        clock_crossing_methods: vec![],
    };
    let path_info = VPathInfo::empty();
    let module_verilog_expr = CExpr::ModuleVerilog {
        name_expr: Box::new(name_expr),
        user_imported: true,
        clock_info,
        reset_info,
        args: all_args,
        fields: method_infos,
        sched_info,
        path_info,
    };
    let verilog_stmt = CModuleItem::Stmt(CStmt::Expr {
        instance_name: None,
        expr: module_verilog_expr,
        span: Span::DUMMY,
    });
    let mut module_items = Vec::new();
    module_items.extend(clock_stmt);
    module_items.extend(reset_stmt);
    module_items.push(verilog_stmt);
    CExpr::Module(pos, module_items)
}

// ============================================================================
// Package parsing
// ============================================================================

/// Parse an export specification.
fn p_exports<'a>() -> impl Parser<'a, TokenStream<'a>, ExportSpec, ParserExtra<'a>> + Clone {
    let explicit = p_exp_id()
        .separated_by(comma())
        .collect::<Vec<_>>()
        .delimited_by(lparen(), rparen())
        .map(ExportSpec::Only);

    let hiding = any()
        .try_map(|t: Token, span| {
            if let TokenKind::VarId(s) = &t.kind {
                if s == "hiding" {
                    return Ok(());
                }
            }
            Err(Rich::custom(span, "expected hiding"))
        })
        .ignore_then(
            p_exp_id()
                .separated_by(comma())
                .collect::<Vec<_>>()
                .delimited_by(lparen(), rparen()),
        )
        .map(ExportSpec::Hiding);

    explicit
        .or(hiding)
        .or(empty().to(ExportSpec::Hiding(vec![])))
}

/// Parse an export item.
fn p_exp_id<'a>() -> impl Parser<'a, TokenStream<'a>, CExport, ParserExtra<'a>> + Clone {
    let pkg = kw_package().ignore_then(p_mod_id()).map(CExport::Package);

    let con_all = p_con_id()
        .then_ignore(lparen())
        .then_ignore(dotdot())
        .then_ignore(rparen())
        .map(CExport::ConAll);

    let con = p_con_id().map(CExport::Con);
    let var = p_var_id().map(CExport::Var);

    let op = lparen()
        .ignore_then(p_operator())
        .then_ignore(rparen())
        .map(CExport::Var);

    choice((pkg, con_all, con, var, op))
}

/// Parse an import declaration.
fn p_import<'a>() -> impl Parser<'a, TokenStream<'a>, CImport, ParserExtra<'a>> + Clone {
    kw_import()
        .ignore_then(kw_qualified().or_not().map(|opt| opt.is_some()))
        .then(p_mod_id())
        .map(|(qualified, module)| CImport::Simple {
            qualified,
            module,
            alias: None,
            spec: None,
            span: Span::DUMMY,
        })
}

/// Parse a fixity declaration.
/// Each source declaration can have multiple operators, but Haskell stores each as separate CFixity.
/// Returns a Vec<CFixity> to allow flattening later.
fn p_fixity<'a>() -> impl Parser<'a, TokenStream<'a>, Vec<CFixity>, ParserExtra<'a>> + Clone {
    let infix = kw_infix().to(0u8);
    let infixl = kw_infixl().to(1u8);
    let infixr = kw_infixr().to(2u8);

    choice((infix, infixl, infixr))
        .then(integer().map(|(_, _, v, _, _)| v.to_string().parse::<i64>().unwrap_or(9)))
        .then(p_any_sym().repeated().at_least(1).collect::<Vec<_>>())
        .map(|((kind, precedence), operators): ((u8, i64), Vec<Id>)| {
            operators.into_iter().map(|op| {
                match kind {
                    0 => CFixity::Infix(precedence, op),
                    1 => CFixity::Infixl(precedence, op),
                    _ => CFixity::Infixr(precedence, op),
                }
            }).collect()
        })
}

/// Parse a complete package.
fn p_package<'a>() -> impl Parser<'a, TokenStream<'a>, CPackage, ParserExtra<'a>> + Clone {
    kw_package()
        .ignore_then(p_mod_id())
        .then(p_exports())
        .then_ignore(kw_where())
        .then(
            lc().ignore_then(
                p_import()
                    .separated_by(dsm())
                    .collect::<Vec<_>>()
                    .then(osm())
                    .then(p_fixity().separated_by(dsm()).collect::<Vec<_>>().map(|fss| fss.into_iter().flatten().collect::<Vec<_>>()))
                    .then(osm())
                    .then(
                        p_defn()
                            .separated_by(sm())
                            .collect::<Vec<_>>()
                            .map(|ds| ds.into_iter().flatten().collect::<Vec<_>>()),
                    )
                    .then(osm()),
            )
            .then_ignore(rc()),
        )
        .then_ignore(end())
        .map(
            |((name, exports), (((((imports, _), fixities), _), definitions), _))| CPackage {
                name,
                exports,
                imports,
                fixities,
                definitions,
                includes: vec![],
                span: Span::DUMMY,
            },
        )
}

// ============================================================================
// Public API
// ============================================================================

/// Prepare tokens for parsing by adding spans.
fn prepare_tokens(tokens: Vec<Token>) -> Vec<(Token, SimpleSpan<u32>)> {
    tokens
        .into_iter()
        .map(|t| {
            let span: SimpleSpan<u32> = SimpleSpan::new((), t.span.start..t.span.end);
            (t, span)
        })
        .collect()
}

/// Convert chumsky errors to our error type.
fn convert_errors(errors: Vec<Rich<Token, SimpleSpan<u32>>>) -> Vec<ParseError> {
    errors
        .into_iter()
        .map(|e| ParseError {
            message: format!("{:?}", e),
            span: Span::new(e.span().start, e.span().end),
        })
        .collect()
}

/// Parse a source string into a package.
pub fn parse_package(source: &str) -> ParseResult<CPackage> {
    parse_package_with_file(source, "")
}

/// Parse a source string into a package, with filename for positions.
pub fn parse_package_with_file(source: &str, filename: &str) -> ParseResult<CPackage> {
    let lexer = Lexer::with_file(source, LexerFlags::default(), filename);
    let raw_tokens = lexer.tokenize().map_err(|e| {
        vec![ParseError {
            message: e.to_string(),
            span: Span::DUMMY,
        }]
    })?;

    let tokens = process_layout(raw_tokens);
    let tokens: Vec<_> = tokens
        .into_iter()
        .filter(|t| !matches!(t.kind, TokenKind::Eof))
        .collect();

    let tokens = prepare_tokens(tokens);
    let eoi = tokens
        .last()
        .map(|(_, s)| s.end)
        .unwrap_or(0);
    let eoi_span: SimpleSpan<u32> = SimpleSpan::new((), eoi..eoi);

    let result = p_package().parse(tokens.as_slice().map(eoi_span, |(t, s)| (t, s)));

    match result.into_result() {
        Ok(pkg) => Ok(pkg),
        Err(errors) => Err(convert_errors(errors)),
    }
}

/// Parse a source string into definitions (for testing).
pub fn parse_definitions(source: &str) -> ParseResult<Vec<CDefn>> {
    let lexer = Lexer::new(source);
    let raw_tokens = lexer.tokenize().map_err(|e| {
        vec![ParseError {
            message: e.to_string(),
            span: Span::DUMMY,
        }]
    })?;

    let tokens = process_layout(raw_tokens);
    let tokens: Vec<_> = tokens
        .into_iter()
        .filter(|t| !matches!(t.kind, TokenKind::Eof))
        .collect();

    let tokens = prepare_tokens(tokens);
    let eoi = tokens.last().map(|(_, s)| s.end).unwrap_or(0);
    let eoi_span: SimpleSpan<u32> = SimpleSpan::new((), eoi..eoi);

    let result = p_defn()
        .repeated()
        .collect::<Vec<_>>()
        .then_ignore(end())
        .map(|ds| ds.into_iter().flatten().collect())
        .parse(tokens.as_slice().map(eoi_span, |(t, s)| (t, s)));

    match result.into_result() {
        Ok(defs) => Ok(defs),
        Err(errors) => Err(convert_errors(errors)),
    }
}

/// Parse a source string into a type.
pub fn parse_type(source: &str) -> ParseResult<CType> {
    let lexer = Lexer::new(source);
    let tokens = lexer.tokenize().map_err(|e| {
        vec![ParseError {
            message: e.to_string(),
            span: Span::DUMMY,
        }]
    })?;

    let tokens: Vec<_> = tokens
        .into_iter()
        .filter(|t| !matches!(t.kind, TokenKind::Eof))
        .collect();

    let tokens = prepare_tokens(tokens);
    let eoi = tokens.last().map(|(_, s)| s.end).unwrap_or(0);
    let eoi_span: SimpleSpan<u32> = SimpleSpan::new((), eoi..eoi);

    let result = p_type()
        .then_ignore(end())
        .parse(tokens.as_slice().map(eoi_span, |(t, s)| (t, s)));

    match result.into_result() {
        Ok(ty) => Ok(ty),
        Err(errors) => Err(convert_errors(errors)),
    }
}

/// Parse a source string into an expression.
pub fn parse_expr(source: &str) -> ParseResult<CExpr> {
    let lexer = Lexer::new(source);
    let tokens = lexer.tokenize().map_err(|e| {
        vec![ParseError {
            message: e.to_string(),
            span: Span::DUMMY,
        }]
    })?;

    let tokens: Vec<_> = tokens
        .into_iter()
        .filter(|t| !matches!(t.kind, TokenKind::Eof))
        .collect();

    let tokens = prepare_tokens(tokens);
    let eoi = tokens.last().map(|(_, s)| s.end).unwrap_or(0);
    let eoi_span: SimpleSpan<u32> = SimpleSpan::new((), eoi..eoi);

    let result = p_expr()
        .then_ignore(end())
        .parse(tokens.as_slice().map(eoi_span, |(t, s)| (t, s)));

    match result.into_result() {
        Ok(expr) => Ok(expr),
        Err(errors) => Err(convert_errors(errors)),
    }
}

/// Parse a source string into a pattern.
pub fn parse_pattern(source: &str) -> ParseResult<CPat> {
    let lexer = Lexer::new(source);
    let tokens = lexer.tokenize().map_err(|e| {
        vec![ParseError {
            message: e.to_string(),
            span: Span::DUMMY,
        }]
    })?;

    let tokens: Vec<_> = tokens
        .into_iter()
        .filter(|t| !matches!(t.kind, TokenKind::Eof))
        .collect();

    let tokens = prepare_tokens(tokens);
    let eoi = tokens.last().map(|(_, s)| s.end).unwrap_or(0);
    let eoi_span: SimpleSpan<u32> = SimpleSpan::new((), eoi..eoi);

    let result = p_pattern()
        .then_ignore(end())
        .parse(tokens.as_slice().map(eoi_span, |(t, s)| (t, s)));

    match result.into_result() {
        Ok(pat) => Ok(pat),
        Err(errors) => Err(convert_errors(errors)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bsc_test_utils::{get_bsc_path, get_libraries_dir, run_differential_test_fail_fast, SyntaxMode};

    #[test]
    fn test_differential_all_libraries() {
        let bsc_path = match get_bsc_path() {
            Some(p) => p,
            None => {
                eprintln!("BSC_PATH not set, skipping differential test");
                return;
            }
        };

        let libraries_dir = match get_libraries_dir() {
            Some(d) => d,
            None => {
                eprintln!("BSC_LIBRARIES_DIR not set, skipping differential test");
                return;
            }
        };

        run_differential_test_fail_fast(
            SyntaxMode::Classic,
            &libraries_dir,
            &bsc_path,
            |source, filename| {
                parse_package_with_file(source, filename)
                    .map_err(|errs| format!("{:?}", errs.first()))
            },
        );
    }
}
