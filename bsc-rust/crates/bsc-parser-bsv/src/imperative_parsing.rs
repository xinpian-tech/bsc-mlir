//! Imperative statement parsing for BSV.
//!
//! This module implements parsing for BSV imperative statements that are used
//! in the top-level package parsing. These mirror the imperative parsing functions
//! from `src/comp/Parser/BSV/CVParser.lhs`.

use crate::imperative::{ImperativeStatement, convert_stmts_to_expr};
use bsc_diagnostics::{Position, Span};
use bsc_lexer_bsv::TokenKind;
use bsc_syntax::csyntax::*;
use bsc_syntax::id::Id;
use bsc_syntax::literal::{IntLiteral, Literal, IntBase};
use chumsky::input::MappedInput;
use chumsky::prelude::*;
use smol_str::SmolStr;

/// Parser error type - uses SimpleSpan<u32> to match our Span type.
pub type PError<'a> = Rich<'a, TokenKind, SimpleSpan<u32>>;
/// Token stream type.
type TokenStream<'a> = MappedInput<'a, TokenKind, SimpleSpan<u32>, &'a [(TokenKind, SimpleSpan<u32>)]>;
type ParserExtra<'a> = extra::Err<PError<'a>>;

fn make_id(name: SmolStr, pos: Position) -> Id {
    Id::new(name, pos)
}

fn to_span(simple_span: SimpleSpan<u32>) -> Span {
    Span::new(simple_span.start, simple_span.end)
}

/// Convert SimpleSpan to Position by looking up from the position map.
/// Mirrors Haskell's approach where each token carries its Position.
fn to_position(simple_span: SimpleSpan<u32>) -> Position {
    crate::lookup_position(simple_span.start)
}

fn p_mk_tuple(pos: Position, pats: Vec<CPat>) -> CPat {
    match pats.len() {
        0 => {
            let unit_id = Id::qualified("Prelude", "PrimUnit", pos);
            CPat::Struct(Some(true), unit_id, vec![], Span::DUMMY)
        }
        1 => pats.into_iter().next().unwrap(),
        _ => {
            let mut iter = pats.into_iter().rev();
            let last = iter.next().unwrap();
            iter.fold(last, |rest, p| {
                CPat::Con(Id::new(SmolStr::new_static(","), pos.clone()), vec![p, rest], Span::DUMMY)
            })
        }
    }
}

fn parse_attribute_name<'a>() -> impl Parser<'a, TokenStream<'a>, SmolStr, ParserExtra<'a>> + Clone {
    select! {
        TokenKind::Id(name) => name,
        TokenKind::KwClockedBy => SmolStr::from("clocked_by"),
        TokenKind::KwResetBy => SmolStr::from("reset_by"),
        TokenKind::KwParameter => SmolStr::from("parameter"),
    }.labelled("attribute name")
}

fn parse_single_attribute<'a>() -> impl Parser<'a, TokenStream<'a>, (SmolStr, Option<String>), ParserExtra<'a>> + Clone {
    parse_attribute_name()
        .then(
            symbol(TokenKind::SymEq)
                .ignore_then(
                    any()
                        .and_is(symbol(TokenKind::SymStarRParen).not())
                        .and_is(comma().not())
                        .repeated()
                        .collect::<Vec<_>>()
                )
                .or_not()
        )
        .map(|(name, value_tokens)| {
            let value = value_tokens.and_then(|tokens: Vec<TokenKind>| {
                if tokens.len() == 1 {
                    if let TokenKind::String(s) = &tokens[0] {
                        return Some(s.clone());
                    }
                }
                None
            });
            (name, value)
        })
        .labelled("single attribute")
}

fn parse_attributes<'a>() -> impl Parser<'a, TokenStream<'a>, Vec<(SmolStr, Option<String>)>, ParserExtra<'a>> + Clone {
    symbol(TokenKind::SymLParenStar)
        .ignore_then(
            parse_single_attribute()
                .separated_by(comma())
                .collect::<Vec<_>>()
        )
        .then_ignore(symbol(TokenKind::SymStarRParen))
        .repeated()
        .collect::<Vec<_>>()
        .map(|lists| lists.into_iter().flatten().collect())
        .labelled("attributes")
}

fn skip_attributes<'a>() -> impl Parser<'a, TokenStream<'a>, (), ParserExtra<'a>> + Clone {
    parse_attributes().ignored().labelled("skip attributes")
}

fn keyword<'a>(expected: TokenKind) -> impl Parser<'a, TokenStream<'a>, (), ParserExtra<'a>> + Clone {
    any().try_map(move |token: TokenKind, span| {
        if std::mem::discriminant(&token) == std::mem::discriminant(&expected) {
            Ok(())
        } else {
            Err(Rich::custom(span, format!("expected {:?}", expected)))
        }
    }).labelled("keyword")
}

fn semicolon<'a>() -> impl Parser<'a, TokenStream<'a>, (), ParserExtra<'a>> + Clone {
    any().try_map(|token: TokenKind, span| {
        if matches!(token, TokenKind::SymSemi) {
            Ok(())
        } else {
            Err(Rich::custom(span, "expected semicolon"))
        }
    }).labelled("semicolon")
}

fn word<'a>() -> impl Parser<'a, TokenStream<'a>, SmolStr, ParserExtra<'a>> + Clone {
    any().try_map(|token: TokenKind, span| {
        if let TokenKind::Id(name) = token {
            Ok(name)
        } else {
            Err(Rich::custom(span, "expected identifier"))
        }
    }).labelled("identifier")
}

fn comma<'a>() -> impl Parser<'a, TokenStream<'a>, (), ParserExtra<'a>> + Clone {
    any().try_map(|token: TokenKind, span| {
        if matches!(token, TokenKind::SymComma) {
            Ok(())
        } else {
            Err(Rich::custom(span, "expected comma"))
        }
    }).labelled("comma")
}

fn symbol<'a>(expected: TokenKind) -> impl Parser<'a, TokenStream<'a>, (), ParserExtra<'a>> + Clone {
    any().try_map(move |token: TokenKind, span| {
        if std::mem::discriminant(&token) == std::mem::discriminant(&expected) {
            Ok(())
        } else {
            Err(Rich::custom(span, format!("expected {:?}", expected)))
        }
    }).labelled("symbol")
}

fn constructor<'a>() -> impl Parser<'a, TokenStream<'a>, Id, ParserExtra<'a>> + Clone {
    any().try_map(|token: TokenKind, span| {
        if let TokenKind::Id(name) = token {
            if name.chars().next().map_or(false, |c| c.is_uppercase()) {
                return Ok(make_id(name, to_position(span)));
            }
        }
        Err(Rich::custom(span, "expected constructor"))
    }).labelled("constructor")
}

fn type_expr<'a>() -> impl Parser<'a, TokenStream<'a>, CType, ParserExtra<'a>> + Clone {
    recursive(|ty| {
        // Parse type variables (lowercase identifiers)
        let tyvar = any().try_map(|token: TokenKind, span| {
            if let TokenKind::Id(name) = token {
                if name.chars().next().unwrap_or('A').is_ascii_lowercase() {
                    return Ok(CType::Var(make_id(name, to_position(span))));
                }
            }
            Err(Rich::custom(span, "expected type variable"))
        });

        // Parse type constructors (uppercase identifiers)
        let tycon = any().try_map(|token: TokenKind, span| {
            if let TokenKind::Id(name) = token {
                if name.chars().next().unwrap_or('a').is_ascii_uppercase() {
                    return Ok(CType::Con(make_id(name, to_position(span)).into()));
                }
            }
            Err(Rich::custom(span, "expected type constructor"))
        });

        let bit_type = keyword(TokenKind::KwBit)
            .map_with(|_, e| to_position(e.span()))
            .then(
                symbol(TokenKind::SymLBracket)
                    .map_with(|_, e| to_position(e.span()))
                    .then(
                        any().try_map(|token: TokenKind, span| {
                            match token {
                                TokenKind::Integer { value, .. } => {
                                    let v: i128 = value.to_string().parse().unwrap_or(0);
                                    Ok(v)
                                }
                                _ => Err(Rich::custom(span, "expected number"))
                            }
                        })
                    )
                    .then_ignore(symbol(TokenKind::SymColon))
                    .then_ignore(
                        any().try_map(|token: TokenKind, span| {
                            match token {
                                TokenKind::Integer { value, .. } => {
                                    let v: i128 = value.to_string().parse().unwrap_or(0);
                                    if v == 0 { Ok(()) } else { Err(Rich::custom(span, "low index must be 0")) }
                                }
                                _ => Err(Rich::custom(span, "expected number"))
                            }
                        })
                    )
                    .then_ignore(symbol(TokenKind::SymRBracket))
                    .or_not()
            )
            .map_with(|(bit_pos, opt_range), e| {
                let bit_con = CType::Con(Id::qualified("Prelude", "Bit", bit_pos.clone()).into());
                match opt_range {
                    Some((bracket_pos, high)) => {
                        let width_type = CType::Num(high + 1, bracket_pos);
                        CType::Apply(
                            Box::new(bit_con),
                            Box::new(width_type),
                            to_span(e.span()),
                        )
                    }
                    None => {
                        let width_type = CType::Num(1, bit_pos);
                        CType::Apply(
                            Box::new(bit_con),
                            Box::new(width_type),
                            to_span(e.span()),
                        )
                    }
                }
            });

        // Parse numeric type literals
        let num_type = any().try_map(|token: TokenKind, span| {
            match token {
                TokenKind::Integer { value, .. } => {
                    let v: i128 = value.to_string().parse().unwrap_or(0);
                    Ok(CType::Num(v, to_position(span)))
                }
                _ => Err(Rich::custom(span, "expected number"))
            }
        });

        // Parse string type literals
        let str_type = any().try_map(|token: TokenKind, span| {
            if let TokenKind::String(s) = token {
                Ok(CType::Str(s, to_position(span)))
            } else {
                Err(Rich::custom(span, "expected string"))
            }
        });

        // Parse parenthesized types and tuples
        let paren_or_tuple = ty
            .clone()
            .separated_by(comma())
            .collect::<Vec<_>>()
            .delimited_by(
                symbol(TokenKind::SymLParen),
                symbol(TokenKind::SymRParen)
            )
            .map(|ts| {
                if ts.is_empty() {
                    // Empty tuple () represents unit type
                    CType::Con(Id::new("()", Position::unknown()).into())
                } else if ts.len() == 1 {
                    // Single parenthesized type
                    CType::Paren(Box::new(ts.into_iter().next().unwrap()), to_span(SimpleSpan::new((), 0..0)))
                } else {
                    // Multiple types form a tuple
                    CType::Tuple(ts, to_span(SimpleSpan::new((), 0..0)))
                }
            });

        let action_type = keyword(TokenKind::KwActionType)
            .map_with(|_, e| {
                let pos = to_position(e.span());
                let av = CType::Con(CTyCon::full(
                    Id::qualified("Prelude", "ActionValue", pos.clone()),
                    Some(CKind::Fun(Box::new(CKind::Star(Span::DUMMY)), Box::new(CKind::Star(Span::DUMMY)), Span::DUMMY)),
                    CTyConSort::Struct(StructSubType::Struct, vec![
                        Id::qualified("Prelude", "__value", pos.clone()),
                        Id::qualified("Prelude", "__action", pos.clone()),
                    ]),
                ));
                let pu = CType::Con(CTyCon::full(
                    Id::qualified("Prelude", "PrimUnit", pos.clone()),
                    Some(CKind::Star(Span::DUMMY)),
                    CTyConSort::Struct(StructSubType::Struct, vec![]),
                ));
                let expansion = CType::Apply(Box::new(av), Box::new(pu), Span::DUMMY);
                CType::Con(CTyCon::full(
                    Id::qualified("Prelude", "Action", pos),
                    Some(CKind::Star(Span::DUMMY)),
                    CTyConSort::TypeSyn(0, Box::new(expansion)),
                ))
            });

        let actionvalue_type = keyword(TokenKind::KwActionValueType)
            .map_with(|_, e| {
                let pos = to_position(e.span());
                CType::Con(CTyCon::full(
                    Id::qualified("Prelude", "ActionValue", pos.clone()),
                    Some(CKind::Fun(Box::new(CKind::Star(Span::DUMMY)), Box::new(CKind::Star(Span::DUMMY)), Span::DUMMY)),
                    CTyConSort::Struct(StructSubType::Struct, vec![
                        Id::qualified("Prelude", "__value", pos.clone()),
                        Id::qualified("Prelude", "__action", pos),
                    ]),
                ))
            });

        let void_type = keyword(TokenKind::KwVoid)
            .map_with(|_, e| {
                let pos = to_position(e.span());
                CType::Con(CTyCon::new(
                    Id::qualified("Prelude", "PrimUnit", pos),
                ))
            });

        let integer_type = keyword(TokenKind::KwInteger)
            .map_with(|_, e| CType::Con(Id::qualified("Prelude", "Integer", to_position(e.span())).into()));

        let int_type = keyword(TokenKind::KwInt)
            .map_with(|_, e| {
                let pos = to_position(e.span());
                let int_con = CType::Con(CTyCon::full(
                    Id::qualified("Prelude", "Int", pos.clone()),
                    Some(CKind::Fun(Box::new(CKind::Num(Span::DUMMY)), Box::new(CKind::Star(Span::DUMMY)), Span::DUMMY)),
                    CTyConSort::Abstract,
                ));
                CType::Apply(
                    Box::new(int_con),
                    Box::new(CType::Num(32, pos)),
                    Span::DUMMY,
                )
            });

        let atype = choice((paren_or_tuple, bit_type, action_type, actionvalue_type, void_type, integer_type, int_type, tyvar, tycon, num_type, str_type)).boxed();

        // Parse type application with # syntax: Type#(arg1, arg2, ...)
        let type_with_params = atype
            .clone()
            .then(
                symbol(TokenKind::SymHash)
                    .ignore_then(
                        symbol(TokenKind::SymLParen)
                            .ignore_then(
                                ty.clone()
                                    .separated_by(comma())
                                    .collect::<Vec<_>>()
                            )
                            .then_ignore(symbol(TokenKind::SymRParen))
                    )
                    .or_not()
            )
            .map(|(base_type, opt_params)| {
                if let Some(params) = opt_params {
                    // Apply parameters left-associatively
                    params.into_iter().fold(base_type, |acc, param| {
                        CType::Apply(Box::new(acc), Box::new(param), to_span(SimpleSpan::new((), 0..0)))
                    })
                } else {
                    base_type
                }
            });

        type_with_params
    })
    .labelled("type expression")
}

fn proviso<'a>() -> impl Parser<'a, TokenStream<'a>, CPred, ParserExtra<'a>> + Clone {
    word().map_with(|name, e| make_id(name, to_position(e.span())))
        .then(
            symbol(TokenKind::SymHash)
                .ignore_then(
                    symbol(TokenKind::SymLParen)
                        .ignore_then(
                            type_expr()
                                .separated_by(comma())
                                .collect::<Vec<_>>()
                        )
                        .then_ignore(symbol(TokenKind::SymRParen))
                )
                .or_not()
                .map(|opt| opt.unwrap_or_default())
        )
        .map_with(|(class, args), e| CPred {
            class,
            args,
            span: to_span(e.span()),
        })
        .labelled("proviso")
}

fn function_arg<'a>() -> impl Parser<'a, TokenStream<'a>, (Id, Option<CType>), ParserExtra<'a>> + Clone {
    choice((
        type_expr()
            .then(word().map_with(|name, e| make_id(name, to_position(e.span()))))
            .map(|(ty, name)| (name, Some(ty))),
        word().map_with(|name, e| make_id(name, to_position(e.span())))
            .map(|name| (name, None)),
    ))
    .labelled("function argument")
}

fn method_prototype<'a>() -> impl Parser<'a, TokenStream<'a>, CField, ParserExtra<'a>> + Clone {
    keyword(TokenKind::KwMethod)
        .ignore_then(type_expr())
        .then(word().map_with(|name, e| make_id(name, to_position(e.span()))))
        .then(
            symbol(TokenKind::SymLParen)
                .ignore_then(
                    function_arg()
                        .separated_by(comma())
                        .collect::<Vec<_>>()
                        .or_not()
                        .map(|opt| opt.unwrap_or_default())
                )
                .then_ignore(symbol(TokenKind::SymRParen))
                .or_not()
        )
        .then_ignore(semicolon())
        .map_with(|((ret_type, name), args), e| {
            let params = args.unwrap_or_default();
            let arg_names: Vec<Id> = params.iter()
                .map(|(name, _ty)| name.clone())
                .collect();
            let arg_types: Vec<CType> = params.into_iter()
                .filter_map(|(_name, ty)| ty)
                .collect();
            let method_type = arg_types.into_iter().rev().fold(ret_type, |acc, arg_ty| {
                crate::make_fn_type(arg_ty, acc)
            });
            CField {
                name,
                pragmas: Some(vec![IfcPragma::ArgNames(arg_names)]),
                orig_type: None,
                ty: CQType {
                    context: Vec::new(),
                    ty: method_type,
                    span: to_span(e.span()),
                },
                default: Vec::new(),
                span: to_span(e.span()),
            }
        })
        .labelled("method prototype")
}

fn subinterface_prototype<'a>() -> impl Parser<'a, TokenStream<'a>, CField, ParserExtra<'a>> + Clone {
    keyword(TokenKind::KwInterface)
        .ignore_then(type_expr())
        .then(word().map_with(|name, e| make_id(name, to_position(e.span()))))
        .then_ignore(semicolon())
        .map_with(|(ifc_type, name), e| {
            CField {
                name,
                pragmas: None,
                orig_type: None,
                ty: CQType {
                    context: Vec::new(),
                    ty: ifc_type,
                    span: to_span(e.span()),
                },
                default: Vec::new(),
                span: to_span(e.span()),
            }
        })
        .labelled("subinterface prototype")
}

fn attributes_to_ifc_pragmas(attrs: &[(SmolStr, Option<String>)], is_method: bool) -> Vec<IfcPragma> {
    let mut pragmas = Vec::new();
    for (name, value) in attrs.iter().rev() {
        match (name.as_str(), is_method) {
            ("prefix", _) => {
                if let Some(s) = value {
                    pragmas.push(IfcPragma::Prefix(s.clone()));
                }
            }
            ("ready", true) => {
                if let Some(s) = value {
                    pragmas.push(IfcPragma::Ready(s.clone()));
                }
            }
            ("enable", true) => {
                if let Some(s) = value {
                    pragmas.push(IfcPragma::Enable(s.clone()));
                }
            }
            ("result", true) => {
                if let Some(s) = value {
                    pragmas.push(IfcPragma::Result(s.clone()));
                }
            }
            ("always_ready", _) => {
                pragmas.push(IfcPragma::AlwaysReady);
            }
            ("always_enabled", _) => {
                pragmas.push(IfcPragma::AlwaysEnabled);
            }
            _ => {}
        }
    }
    pragmas
}

fn interface_member<'a>() -> impl Parser<'a, TokenStream<'a>, CField, ParserExtra<'a>> + Clone {
    parse_attributes()
        .then(choice((
            method_prototype(),
            subinterface_prototype(),
        )))
        .map(|(attrs, mut field)| {
            let is_method = field.pragmas.is_some();
            let attr_pragmas = attributes_to_ifc_pragmas(&attrs, is_method);
            match &mut field.pragmas {
                Some(prags) => {
                    prags.extend(attr_pragmas);
                }
                None => {
                    field.pragmas = Some(attr_pragmas);
                }
            }
            field
        })
        .labelled("interface member")
}

fn typedef_synonym<'a>() -> impl Parser<'a, TokenStream<'a>, Vec<CDefn>, ParserExtra<'a>> + Clone {
    type_expr()
        .then(constructor())
        .then(typedef_params())
        .then_ignore(semicolon())
        .map_with(|((original, name), type_params), e| {
            let (params, kinds): (Vec<Id>, Vec<CPartialKind>) = type_params.into_iter().unzip();
            let idk = mk_idk(name, &kinds);
            vec![CDefn::Type(CTypeDef {
                name: idk,
                params,
                body: original,
                span: to_span(e.span()),
            })]
        })
        .labelled("typedef synonym")
}

fn parse_deriving<'a>() -> impl Parser<'a, TokenStream<'a>, Vec<CTypeclass>, ParserExtra<'a>> + Clone {
    keyword(TokenKind::KwDeriving)
        .ignore_then(
            symbol(TokenKind::SymLParen)
                .ignore_then(
                    constructor()
                        .map(|name| CTypeclass { name })
                        .separated_by(comma())
                        .collect::<Vec<_>>()
                )
                .then_ignore(symbol(TokenKind::SymRParen))
        )
        .or_not()
        .map(|opt| opt.unwrap_or_default())
        .labelled("deriving clause")
}

fn typedef_enum<'a>() -> impl Parser<'a, TokenStream<'a>, Vec<CDefn>, ParserExtra<'a>> + Clone {
    keyword(TokenKind::KwEnum)
        .ignore_then(
            symbol(TokenKind::SymLBrace)
                .ignore_then(
                    constructor()
                        .separated_by(comma())
                        .allow_trailing()
                        .collect::<Vec<_>>()
                )
                .then_ignore(symbol(TokenKind::SymRBrace))
        )
        .then(constructor())
        .then(parse_deriving())
        .then_ignore(semicolon())
        .map_with(|((enum_tags, name), derivs), e| {
            let original_summands: Vec<COriginalSummand> = enum_tags.iter().map(|tag| {
                COriginalSummand {
                    names: vec![tag.clone()],
                    arg_types: Vec::new(),
                    field_names: None,
                    tag_encoding: None,
                }
            }).collect();
            let internal_summands: Vec<CInternalSummand> = enum_tags.iter().enumerate().map(|(i, tag)| {
                CInternalSummand {
                    names: vec![tag.clone()],
                    arg_type: CType::Con(Id::qualified("Prelude", "PrimUnit", Position::unknown()).into()),
                    tag_encoding: i as i64,
                }
            }).collect();
            vec![CDefn::Data(CDataDef {
                visible: true,
                name: IdK::Plain(name),
                params: Vec::new(),
                original_summands,
                internal_summands,
                deriving: derivs,
                span: to_span(e.span()),
            })]
        })
        .labelled("typedef enum")
}

fn typedef_param<'a>() -> impl Parser<'a, TokenStream<'a>, (Id, CPartialKind), ParserExtra<'a>> + Clone {
    keyword(TokenKind::KwParameter).or_not()
        .ignore_then(
            choice((
                any().try_map(|token: TokenKind, span| {
                    if let TokenKind::Id(name) = &token {
                        if name == "numeric" { return Ok(CPartialKind::Num); }
                    }
                    Err(Rich::custom(span, "expected 'numeric'"))
                }),
                keyword(TokenKind::KwString).to(CPartialKind::Str),
            ))
            .or_not()
            .map(|opt| opt.unwrap_or(CPartialKind::NoInfo))
        )
        .then_ignore(keyword(TokenKind::KwType))
        .then(word().map_with(|n, e| make_id(n, to_position(e.span()))))
        .map(|(pkind, name)| (name, pkind))
        .labelled("type parameter")
}

fn typedef_params<'a>() -> impl Parser<'a, TokenStream<'a>, Vec<(Id, CPartialKind)>, ParserExtra<'a>> + Clone {
    symbol(TokenKind::SymHash)
        .ignore_then(
            symbol(TokenKind::SymLParen)
                .ignore_then(
                    typedef_param()
                        .separated_by(comma())
                        .at_least(1)
                        .collect::<Vec<_>>()
                )
                .then_ignore(symbol(TokenKind::SymRParen))
        )
        .or_not()
        .map(|opt| opt.unwrap_or_default())
        .labelled("typedef parameters")
}

fn mk_idk(name: Id, kinds: &[CPartialKind]) -> IdK {
    if kinds.is_empty() || kinds.iter().all(|k| matches!(k, CPartialKind::NoInfo)) {
        IdK::Plain(name)
    } else {
        let pkind = kinds.iter().rev().fold(CPartialKind::NoInfo, |acc, k| {
            CPartialKind::Fun(Box::new(k.clone()), Box::new(acc))
        });
        IdK::WithPartialKind(name, pkind)
    }
}

fn typedef_struct<'a>() -> impl Parser<'a, TokenStream<'a>, Vec<CDefn>, ParserExtra<'a>> + Clone {
    keyword(TokenKind::KwStruct)
        .ignore_then(
            symbol(TokenKind::SymLBrace)
                .ignore_then(
                    type_expr()
                        .then(word().map_with(|n, e| make_id(n, to_position(e.span()))))
                        .then_ignore(semicolon())
                        .repeated()
                        .collect::<Vec<_>>()
                )
                .then_ignore(symbol(TokenKind::SymRBrace))
        )
        .then(constructor())
        .then(typedef_params())
        .then(parse_deriving())
        .then_ignore(semicolon())
        .map_with(|(((fields, name), type_params), derivs), e| {
            let (params, kinds): (Vec<Id>, Vec<CPartialKind>) = type_params.into_iter().unzip();
            let idk = mk_idk(name, &kinds);
            let cfields: Vec<CField> = fields.into_iter().map(|(ty, field_name)| {
                CField {
                    name: field_name,
                    pragmas: None,
                    orig_type: None,
                    ty: CQType {
                        context: Vec::new(),
                        ty,
                        span: Span::DUMMY,
                    },
                    default: Vec::new(),
                    span: Span::DUMMY,
                }
            }).collect();
            vec![CDefn::Struct(CStructDef {
                visible: true,
                sub_type: StructSubType::Struct,
                name: idk,
                params,
                fields: cfields,
                deriving: derivs,
                span: to_span(e.span()),
            })]
        })
        .labelled("typedef struct")
}

/// Represents a constructor in a tagged union
#[derive(Debug, Clone)]
enum TaggedUnionConstructor {
    Void { name: Id },
    SingleType { name: Id, ty: CType },
    Struct { name: Id, fields: Vec<(CType, Id)> },
}

/// Parse a tagged union field - can be void, single type, or struct
fn tagged_union_field<'a>() -> impl Parser<'a, TokenStream<'a>, TaggedUnionConstructor, ParserExtra<'a>> + Clone {
    choice((
        // void ConstructorName;
        keyword(TokenKind::KwVoid)
            .ignore_then(constructor())
            .then_ignore(semicolon())
            .map(|name| TaggedUnionConstructor::Void { name }),

        // struct { ... } ConstructorName;
        keyword(TokenKind::KwStruct)
            .ignore_then(
                symbol(TokenKind::SymLBrace)
                    .ignore_then(
                        type_expr()
                            .then(word().map_with(|n, e| make_id(n, to_position(e.span()))))
                            .then_ignore(semicolon())
                            .repeated()
                            .collect::<Vec<_>>()
                    )
                    .then_ignore(symbol(TokenKind::SymRBrace))
            )
            .then(constructor())
            .then_ignore(semicolon())
            .map(|(fields, name)| TaggedUnionConstructor::Struct { name, fields }),

        // Type ConstructorName;
        type_expr()
            .then(constructor())
            .then_ignore(semicolon())
            .map(|(ty, name)| TaggedUnionConstructor::SingleType { name, ty }),
    ))
    .labelled("tagged union field")
}

/// Parse deriving clause: deriving (Class1, Class2, ...)
fn deriving_clause<'a>() -> impl Parser<'a, TokenStream<'a>, Vec<CTypeclass>, ParserExtra<'a>> + Clone {
    keyword(TokenKind::KwDeriving)
        .ignore_then(
            symbol(TokenKind::SymLParen)
                .ignore_then(
                    word()
                        .map_with(|name, e| CTypeclass {
                            name: make_id(name, to_position(e.span())),
                        })
                        .separated_by(comma())
                        .collect::<Vec<_>>()
                )
                .then_ignore(symbol(TokenKind::SymRParen))
        )
        .or_not()
        .map(|opt| opt.unwrap_or_default())
        .labelled("deriving clause")
}


fn typedef_union<'a>() -> impl Parser<'a, TokenStream<'a>, Vec<CDefn>, ParserExtra<'a>> + Clone {
    keyword(TokenKind::KwUnion)
        .ignore_then(keyword(TokenKind::KwTagged))
        .ignore_then(
            symbol(TokenKind::SymLBrace)
                .ignore_then(tagged_union_field().repeated().collect::<Vec<_>>())
                .then_ignore(symbol(TokenKind::SymRBrace))
        )
        .then(constructor())
        .then(typedef_params())
        .then(deriving_clause())
        .then_ignore(semicolon())
        .map_with(|(((constructors, name), type_params), derivings), e| {
            let (params, kinds): (Vec<Id>, Vec<CPartialKind>) = type_params.into_iter().unzip();
            let idk = mk_idk(name.clone(), &kinds);
            // Convert constructors to summands
            let mut original_summands = Vec::new();
            let mut internal_summands = Vec::new();
            let mut additional_defns = Vec::new(); // For struct definitions

            for (tag_encoding, constructor) in constructors.into_iter().enumerate() {
                match constructor {
                    TaggedUnionConstructor::Void { name: con_name } => {
                        // void constructor - no arguments
                        original_summands.push(COriginalSummand {
                            names: vec![con_name.clone()],
                            arg_types: Vec::new(),
                            field_names: None,
                            tag_encoding: None,
                        });
                        internal_summands.push(CInternalSummand {
                            names: vec![con_name],
                            arg_type: CType::Con(Id::qualified("Prelude", "PrimUnit", Position::unknown()).into()),
                            tag_encoding: tag_encoding as i64,
                        });
                    },
                    TaggedUnionConstructor::SingleType { name: con_name, ty } => {
                        // single type constructor
                        let qtype = CQType {
                            context: Vec::new(),
                            ty: ty.clone(),
                            span: Span::DUMMY,
                        };
                        original_summands.push(COriginalSummand {
                            names: vec![con_name.clone()],
                            arg_types: vec![qtype],
                            field_names: None,
                            tag_encoding: None,
                        });
                        internal_summands.push(CInternalSummand {
                            names: vec![con_name],
                            arg_type: ty,
                            tag_encoding: tag_encoding as i64,
                        });
                    },
                    TaggedUnionConstructor::Struct { name: con_name, fields } => {
                        // struct constructor with named fields
                        let field_names: Vec<Id> = fields.iter().map(|(_, name)| name.clone()).collect();
                        let arg_types: Vec<CQType> = fields.iter().map(|(ty, _)| CQType {
                            context: Vec::new(),
                            ty: ty.clone(),
                            span: Span::DUMMY,
                        }).collect();

                        // For internal summand, we need to create a struct type containing all fields
                        // This mirrors the Haskell implementation's struct packing
                        let (struct_type, struct_defn_opt) = if arg_types.len() == 1 {
                            (arg_types[0].ty.clone(), None)
                        } else {
                            // Create both the struct type reference and the struct definition
                            // This mirrors the Haskell mkSubStruct logic from CVParser.lhs
                            let struct_type = create_tagged_union_struct_type(&name, &con_name);
                            let struct_defn = create_tagged_union_struct_definition(&name, &con_name, fields.clone());
                            (struct_type, Some(struct_defn))
                        };

                        // Add struct definition if created
                        if let Some(defn) = struct_defn_opt {
                            additional_defns.push(defn);
                        }

                        original_summands.push(COriginalSummand {
                            names: vec![con_name.clone()],
                            arg_types,
                            field_names: Some(field_names),
                            tag_encoding: None,
                        });
                        internal_summands.push(CInternalSummand {
                            names: vec![con_name],
                            arg_type: struct_type,
                            tag_encoding: tag_encoding as i64,
                        });
                    },
                }
            }

            // Create the main data definition
            let mut defns = vec![CDefn::Data(CDataDef {
                visible: true,
                name: idk,
                params,
                original_summands,
                internal_summands,
                deriving: derivings,
                span: to_span(e.span()),
            })];

            // Add any struct definitions
            defns.extend(additional_defns);
            defns
        })
        .labelled("typedef union")
}

/// Expression parsing mirroring Haskell's pPrimary and pPrimaryWithSuffix
/// from CVParser.lhs
fn system_id<'a>() -> impl Parser<'a, TokenStream<'a>, SmolStr, ParserExtra<'a>> + Clone {
    any().try_map(|token: TokenKind, span| {
        if let TokenKind::SystemId(name) = token {
            Ok(name)
        } else {
            Err(Rich::custom(span, "expected system identifier"))
        }
    }).labelled("system identifier")
}

fn expr<'a>() -> impl Parser<'a, TokenStream<'a>, CExpr, ParserExtra<'a>> + Clone {
    recursive(|expr| {
        // pVariable: Parse variables/identifiers -> CVar (lowercase only, like Haskell pIdentifier)
        let var = any().try_map(|token: TokenKind, span| {
            if let TokenKind::Id(name) = token {
                if name.chars().next().map_or(false, |c| !c.is_uppercase()) {
                    return Ok(CExpr::Var(make_id(name, to_position(span))));
                }
            }
            Err(Rich::custom(span, "expected lowercase identifier"))
        });

        // pConstructorPrimary: Parse uppercase constructors
        // Mirrors Haskell CVParser.lhs:1717-1731
        // Tries: Name { field: val, ... } -> CStruct, or Name -> CCon
        let field_init = word()
            .map_with(|name, e| make_id(name, to_position(e.span())))
            .then_ignore(symbol(TokenKind::SymColon))
            .then(expr.clone())
            .map(|(name, value)| CFieldInit { name, value, span: Span::DUMMY });
        let constructor_expr = constructor()
            .then(
                field_init
                    .separated_by(comma())
                    .collect::<Vec<CFieldInit>>()
                    .delimited_by(symbol(TokenKind::SymLBrace), symbol(TokenKind::SymRBrace))
                    .or_not()
            )
            .map(|(con, opt_fields)| {
                if let Some(fields) = opt_fields {
                    CExpr::Struct(Some(true), con, fields, Span::DUMMY)
                } else {
                    CExpr::Con(con, vec![], Span::DUMMY)
                }
            });

        // pTaskIdentifier: Parse system identifiers like $finish -> CTaskApply
        // Mirrors Haskell's cVar: task names become CTaskApply (CVar name) []
        let system_task = system_id()
            .map_with(|name, e| {
                let id = make_id(name, to_position(e.span()));
                CExpr::TaskApply(Box::new(CExpr::Var(id)), vec![], Span::DUMMY)
            });

        // Parse integer literals (both Integer and Number tokens)
        // - TokenKind::Integer: simple integers like 42
        // - TokenKind::Number: SystemVerilog-style numbers like 40'h80_00de_0007
        let int_lit = any().try_map(|token: TokenKind, span| {
            match token {
                TokenKind::Integer { value, size, base } => {
                    let int_lit = IntLiteral {
                        value: value.to_string().parse().unwrap_or(0),
                        width: size.as_ref().and_then(|s| s.to_string().parse().ok()),
                        base: match base {
                            2 => IntBase::Binary,
                            8 => IntBase::Octal,
                            16 => IntBase::Hexadecimal,
                            _ => IntBase::Decimal,
                        },
                    };
                    Ok(CExpr::Lit(Literal::Integer(int_lit), to_position(span)))
                }
                TokenKind::Number { value, bitwidth, base, .. } => {
                    use bsc_lexer_bsv::SvNumber;
                    let int_value: i128 = match value {
                        SvNumber::Integer(v) => v.to_string().parse().unwrap_or(0),
                        SvNumber::Real(f) => f as i128,
                        SvNumber::Repeated(_) => 0,
                        SvNumber::Mixed(_) => 0,
                    };
                    let int_lit = IntLiteral {
                        value: int_value,
                        width: bitwidth.as_ref().and_then(|s| s.to_string().parse().ok()),
                        base: match base {
                            Some(bsc_lexer_bsv::SvNumericBase::Bin) => IntBase::Binary,
                            Some(bsc_lexer_bsv::SvNumericBase::Oct) => IntBase::Octal,
                            Some(bsc_lexer_bsv::SvNumericBase::Hex) => IntBase::Hexadecimal,
                            _ => IntBase::Decimal,
                        },
                    };
                    Ok(CExpr::Lit(Literal::Integer(int_lit), to_position(span)))
                }
                _ => Err(Rich::custom(span, "expected integer"))
            }
        });

        // Parse string literals
        let str_lit = any().try_map(|token: TokenKind, span| {
            if let TokenKind::String(s) = token {
                Ok(CExpr::Lit(Literal::String(s.to_string()), to_position(span)))
            } else {
                Err(Rich::custom(span, "expected string"))
            }
        });

        // pInParens pExpression: parenthesized expressions
        let paren = expr.clone()
            .delimited_by(
                symbol(TokenKind::SymLParen),
                symbol(TokenKind::SymRParen)
            )
            .boxed();

        // ? (don't care / undefined value)
        let question = symbol(TokenKind::SymQuestion)
            .map_with(|_, e| CExpr::Any {
                position: to_position(e.span()),
                kind: UndefKind::DontCare,
                span: to_span(e.span()),
            });

        // tagged Constructor [expr]
        let tagged_expr = keyword(TokenKind::KwTagged)
            .ignore_then(constructor())
            .then(expr.clone().or_not())
            .map_with(|(con, opt_body), e| {
                let mut args = Vec::new();
                if let Some(body) = opt_body {
                    args.push(body);
                }
                CExpr::Con(con, args, to_span(e.span()))
            });

        // pBitConcatPrimary: bit concatenation {a, b, c}
        // Mirrors Haskell CVParser.lhs:1846-1853
        // foldr1 cat where cat (e,p) (es,_) = (cApply 19 (catAt p) [e, es], p)
        // catAt pos = cVar (idPrimConcatAt pos) = CVar (Prelude.primConcat)
        let bit_concat = symbol(TokenKind::SymLBrace)
            .ignore_then(
                expr.clone()
                    .separated_by(comma())
                    .at_least(1)
                    .collect::<Vec<CExpr>>()
            )
            .then_ignore(symbol(TokenKind::SymRBrace))
            .map(|exprs: Vec<CExpr>| {
                if exprs.len() == 1 {
                    return exprs.into_iter().next().unwrap();
                }
                let mut iter = exprs.into_iter().rev();
                let first = iter.next().unwrap();
                iter.fold(first, |acc, e| {
                    let concat_id = Id::qualified("Prelude", "primConcat", Position::unknown());
                    CExpr::Apply(
                        Box::new(CExpr::Var(concat_id)),
                        vec![e, acc],
                        Span::DUMMY,
                    )
                })
            })
            .labelled("expression");

        // pPrimary: primary expressions (atoms)
        let primary = choice((paren, system_task, question, tagged_expr, bit_concat, var, int_lit, str_lit, constructor_expr)).boxed();

        // Unary prefix operators: !, ~, -
        let unary_expr = choice((
            symbol(TokenKind::SymBang)
                .ignore_then(primary.clone())
                .map_with(|e, ctx| {
                    let pos = to_position(ctx.span());
                    let op_id = Id::qualified("Prelude", "not", pos);
                    CExpr::Apply(Box::new(CExpr::Var(op_id)), vec![e], Span::DUMMY)
                }),
            symbol(TokenKind::SymTilde)
                .ignore_then(primary.clone())
                .map_with(|e, ctx| {
                    let pos = to_position(ctx.span());
                    let op_id = Id::qualified("Prelude", "invert", pos);
                    CExpr::Apply(Box::new(CExpr::Var(op_id)), vec![e], Span::DUMMY)
                }),
            symbol(TokenKind::SymMinus)
                .ignore_then(primary.clone())
                .map_with(|e, ctx| {
                    let pos = to_position(ctx.span());
                    match e {
                        CExpr::Lit(Literal::Integer(mut int_lit), _) => {
                            int_lit.value = -int_lit.value;
                            CExpr::Lit(Literal::Integer(int_lit), pos)
                        }
                        other => {
                            let op_id = Id::qualified("Prelude", "negate", pos);
                            CExpr::Apply(Box::new(CExpr::Var(op_id)), vec![other], Span::DUMMY)
                        }
                    }
                }),
            primary.clone(),
        )).boxed();

        // Suffix enum to represent different suffix types
        // Mirrors Haskell's pPrimaryWithSuffix approach
        #[derive(Clone)]
        enum Suffix {
            Field(Id),                    // .field -> CSelect
            Args(Vec<CExpr>),             // (args) -> CApply
            BitSel(Position, CExpr),      // [index] -> CSub
            BitSelRange(CExpr, CExpr),    // [hi:lo] -> CSub2/IndexRange
            Params(Vec<CExpr>),           // #(exprs) -> CApply (BSV pParameters)
            QualAccess(SmolStr, Position), // ::name -> qualified identifier (Pkg::func or Pkg::Con)
        }

        // Parse all suffixes: .field, ::name, (args), [index], #(types)
        let suffix = choice((
            // ::name (pQualIdentifier: PackageName::identifier)
            // Mirrors Haskell's pQualIdentifier/pQualConstructor from CVParser.lhs:402-447
            symbol(TokenKind::SymColonColon)
                .ignore_then(word().map_with(|name, e| (name, to_position(e.span()))))
                .map(|(name, pos)| Suffix::QualAccess(name, pos)),
            // .field (pPrimaryWithFields: pSymbol SV_SYM_dot >> pQualIdentifier)
            symbol(TokenKind::SymDot)
                .ignore_then(word().map_with(|name, e| make_id(name, to_position(e.span()))))
                .map(Suffix::Field),
            // (args) (pPrimaryWithArgs: pPortListArgs)
            symbol(TokenKind::SymLParen)
                .ignore_then(
                    expr.clone()
                        .separated_by(comma())
                        .collect::<Vec<_>>()
                )
                .then_ignore(symbol(TokenKind::SymRParen))
                .map(Suffix::Args),
            // [index] or [hi:lo] (pPrimaryWithBitSel: pInBrackets pBitSelSubscript)
            symbol(TokenKind::SymLBracket)
                .map_with(|_, e| {
                    let span = e.span();
                    crate::lookup_position(span.start)
                })
                .then(
                    expr.clone()
                        .then(
                            symbol(TokenKind::SymColon)
                                .ignore_then(expr.clone())
                                .or_not()
                        )
                )
                .then_ignore(symbol(TokenKind::SymRBracket))
                .map(|(bracket_pos, (e1, opt_e2))| match opt_e2 {
                    Some(e2) => Suffix::BitSelRange(e1, e2),
                    None => Suffix::BitSel(bracket_pos, e1),
                }),
            // #(exprs) - BSV pParameters: module instantiation parameters
            // According to Haskell CVParser.lhs pParameters, these are EXPRESSIONS, not types:
            // > pParameters :: SV_Parser [CExpr]
            // > pParameters = option [] (pSymbol SV_SYM_hash >>
            // >                          pInParens (pCommaSep1 pExpression))
            symbol(TokenKind::SymHash)
                .ignore_then(
                    symbol(TokenKind::SymLParen)
                        .ignore_then(
                            expr.clone()
                                .separated_by(comma())
                                .collect::<Vec<_>>()
                        )
                        .then_ignore(symbol(TokenKind::SymRParen))
                )
                .map(Suffix::Params),
        ));

        // pPrimaryWithSuffix: apply suffixes left-associatively using foldl
        // Haskell: foldl mkSelect e selects, foldl mkSel expr es
        let primary_with_suffix = unary_expr.foldl(
            suffix.repeated(),
            |e, suf| match suf {
                Suffix::Field(field) => CExpr::Select(Box::new(e), field, Span::DUMMY),
                Suffix::Args(args) => if args.is_empty() {
                    e
                } else {
                    match e {
                        CExpr::TaskApply(f, mut es, span) => {
                            es.extend(args);
                            CExpr::TaskApply(f, es, span)
                        }
                        CExpr::Apply(f, mut es, span) => {
                            es.extend(args);
                            CExpr::Apply(f, es, span)
                        }
                        CExpr::Con(id, mut es, span) => {
                            es.extend(args);
                            CExpr::Con(id, es, span)
                        }
                        other => CExpr::Apply(Box::new(other), args, Span::DUMMY),
                    }
                },
                Suffix::BitSel(pos, index) => CExpr::Index { pos, expr: Box::new(e), index: Box::new(index), span: Span::DUMMY },
                Suffix::BitSelRange(hi, lo) => CExpr::IndexRange { expr: Box::new(e), hi: Box::new(hi), lo: Box::new(lo), span: Span::DUMMY },
                Suffix::Params(params) => if params.is_empty() { e } else { CExpr::Apply(Box::new(e), params, Span::DUMMY) },
                Suffix::QualAccess(name, pos) => {
                    let pkg_name = match &e {
                        CExpr::Var(id) => id.name().to_string(),
                        CExpr::Con(id, _, _) => id.name().to_string(),
                        _ => return e,
                    };
                    let pkg_pos = match &e {
                        CExpr::Var(id) => id.position().clone(),
                        CExpr::Con(id, _, _) => id.position().clone(),
                        _ => pos.clone(),
                    };
                    if name.chars().next().unwrap_or('a').is_uppercase() {
                        CExpr::Con(Id::qualified(pkg_name, name, pkg_pos), vec![], Span::DUMMY)
                    } else {
                        CExpr::Var(Id::qualified(pkg_name, name, pkg_pos))
                    }
                },
            },
        );

        fn make_bin(left: CExpr, op_id: Id, right: CExpr) -> CExpr {
            crate::operators::make_binary_expr(left, op_id, right)
        }

        let op_star_star = symbol(TokenKind::SymStarStar).map_with(|_, e| crate::operators::id_star_star_at(to_position(e.span())));
        let level_power = primary_with_suffix.clone().foldl(
            op_star_star.then(primary_with_suffix.clone()).repeated(),
            |l, (op, r)| make_bin(l, op, r),
        ).boxed();

        let op_mul = choice((
            symbol(TokenKind::SymStar).map_with(|_, e| crate::operators::id_star_at(to_position(e.span()))),
            symbol(TokenKind::SymSlash).map_with(|_, e| crate::operators::id_slash_at(to_position(e.span()))),
            symbol(TokenKind::SymPercent).map_with(|_, e| crate::operators::id_percent_at(to_position(e.span()))),
        ));
        let level_mul = level_power.clone().foldl(
            op_mul.then(level_power).repeated(),
            |l, (op, r)| make_bin(l, op, r),
        ).boxed();

        let op_add = choice((
            symbol(TokenKind::SymPlus).map_with(|_, e| crate::operators::id_plus_at(to_position(e.span()))),
            symbol(TokenKind::SymMinus).map_with(|_, e| crate::operators::id_minus_at(to_position(e.span()))),
        ));
        let level_add = level_mul.clone().foldl(
            op_add.then(level_mul).repeated(),
            |l, (op, r)| make_bin(l, op, r),
        ).boxed();

        let op_shift = choice((
            symbol(TokenKind::SymLtLt).map_with(|_, e| crate::operators::id_lsh_at(to_position(e.span()))),
            symbol(TokenKind::SymGtGt).map_with(|_, e| crate::operators::id_rsh_at(to_position(e.span()))),
        ));
        let level_shift = level_add.clone().foldl(
            op_shift.then(level_add).repeated(),
            |l, (op, r)| make_bin(l, op, r),
        ).boxed();

        let op_rel = choice((
            symbol(TokenKind::SymLtEq).map_with(|_, e| crate::operators::id_lt_eq_at(to_position(e.span()))),
            symbol(TokenKind::SymGtEq).map_with(|_, e| crate::operators::id_gt_eq_at(to_position(e.span()))),
            symbol(TokenKind::SymLt).map_with(|_, e| crate::operators::id_lt_at(to_position(e.span()))),
            symbol(TokenKind::SymGt).map_with(|_, e| crate::operators::id_gt_at(to_position(e.span()))),
        ));
        let level_rel = level_shift.clone().foldl(
            op_rel.then(level_shift).repeated(),
            |l, (op, r)| make_bin(l, op, r),
        ).boxed();

        let op_eq = choice((
            symbol(TokenKind::SymEqEq).map_with(|_, e| crate::operators::id_equal_at(to_position(e.span()))),
            symbol(TokenKind::SymBangEq).map_with(|_, e| crate::operators::id_not_equal_at(to_position(e.span()))),
        ));
        let level_eq = level_rel.clone().foldl(
            op_eq.then(level_rel).repeated(),
            |l, (op, r)| make_bin(l, op, r),
        ).boxed();

        let op_band = symbol(TokenKind::SymAnd).map_with(|_, e| crate::operators::id_bit_and_at(to_position(e.span())));
        let level_band = level_eq.clone().foldl(
            op_band.then(level_eq).repeated(),
            |l, (op, r)| make_bin(l, op, r),
        ).boxed();

        let op_bxor = choice((
            symbol(TokenKind::SymCaret).map_with(|_, e| crate::operators::id_caret_at(to_position(e.span()))),
            symbol(TokenKind::SymTildeCaret).map_with(|_, e| crate::operators::id_tilde_caret_at(to_position(e.span()))),
            symbol(TokenKind::SymCaretTilde).map_with(|_, e| crate::operators::id_caret_tilde_at(to_position(e.span()))),
        ));
        let level_bxor = level_band.clone().foldl(
            op_bxor.then(level_band).repeated(),
            |l, (op, r)| make_bin(l, op, r),
        ).boxed();

        let op_bor = symbol(TokenKind::SymPipe).map_with(|_, e| crate::operators::id_bit_or_at(to_position(e.span())));
        let level_bor = level_bxor.clone().foldl(
            op_bor.then(level_bxor).repeated(),
            |l, (op, r)| make_bin(l, op, r),
        ).boxed();

        let op_land = symbol(TokenKind::SymAndAnd).map_with(|_, e| crate::operators::id_and_at(to_position(e.span())));
        let level_land = level_bor.clone().foldl(
            op_land.then(level_bor).repeated(),
            |l, (op, r)| make_bin(l, op, r),
        ).boxed();

        let op_lor = symbol(TokenKind::SymPipePipe).map_with(|_, e| crate::operators::id_or_at(to_position(e.span())));
        let binary_expr = level_land.clone().foldl(
            op_lor.then(level_land).repeated(),
            |l, (op, r)| make_bin(l, op, r),
        ).boxed();

        // Ternary conditional: cond ? then_expr : else_expr
        binary_expr.clone()
            .then(
                symbol(TokenKind::SymQuestion)
                    .map_with(|_, e| to_position(e.span()))
                    .then(expr.clone())
                    .then_ignore(symbol(TokenKind::SymColon))
                    .then(expr.clone())
                    .or_not()
            )
            .map(|(cond, opt_ternary)| {
                if let Some(((pos, then_e), else_e)) = opt_ternary {
                    CExpr::If(pos, Box::new(cond), Box::new(then_e), Box::new(else_e))
                } else {
                    cond
                }
            })
    })
    .labelled("expression")
}

/// Parse variable declaration: Type#(params) varName();
fn var_decl<'a>() -> impl Parser<'a, TokenStream<'a>, ImperativeStatement, ParserExtra<'a>> + Clone {
    type_expr()
        .then(word().map_with(|name, e| make_id(name, to_position(e.span()))))
        .then_ignore(symbol(TokenKind::SymLParen))
        .then_ignore(symbol(TokenKind::SymRParen))
        .then_ignore(semicolon())
        .map(|(ty, name)| {
            ImperativeStatement::InterfaceVarDecl {
                name,
                ty,
            }
        })
        .labelled("variable declaration")
}

/// Parse typed variable declaration with initialization: Type name = expr;
fn typed_var_decl<'a>() -> impl Parser<'a, TokenStream<'a>, ImperativeStatement, ParserExtra<'a>> + Clone {
    type_expr()
        .then(word().map_with(|name, e| make_id(name, to_position(e.span()))))
        .then_ignore(symbol(TokenKind::SymEq))
        .then(expr())
        .then_ignore(semicolon())
        .map(|((ty, name), init_expr)| {
            ImperativeStatement::Decl {
                ty: Some(ty),
                name,
                init: Some(init_expr),
            }
        })
        .labelled("typed variable declaration")
}

/// Parse module instantiation with arrow: InterfaceType instName <- mkModule(args);
fn module_inst_arrow<'a>() -> impl Parser<'a, TokenStream<'a>, ImperativeStatement, ParserExtra<'a>> + Clone {
    type_expr()
        .then(word().map_with(|name, e| make_id(name, to_position(e.span()))))
        .then_ignore(symbol(TokenKind::SymLArrow))
        .then(expr())
        .then_ignore(semicolon())
        .map(|((ifc_type, ifc_var), constructor)| {
            ImperativeStatement::Bind {
                name: ifc_var,
                ty: Some(ifc_type),
                expr: constructor,
            }
        })
        .labelled("typed bind with arrow")
}

/// Parse old-style instantiation: mkModule instName(interfaces);
fn module_inst_old_style<'a>() -> impl Parser<'a, TokenStream<'a>, ImperativeStatement, ParserExtra<'a>> + Clone {
    expr()
        .then(word().map_with(|name, e| make_id(name, to_position(e.span()))))
        .then(
            symbol(TokenKind::SymLParen)
                .ignore_then(word().map_with(|name, e| make_id(name, to_position(e.span()))))
                .then_ignore(symbol(TokenKind::SymRParen))
        )
        .then_ignore(semicolon())
        .map_with(|((constructor, inst_var), ifc_var), e| {
            ImperativeStatement::Inst {
                pos: to_position(e.span()),
                attrs: Vec::new(),
                ifc_var,
                inst_var,
                ifc_type: None, // No explicit type in old-style syntax
                clocked_by: None,
                reset_by: None,
                powered_by: None,
                constructor,
            }
        })
        .labelled("old-style module instantiation")
}

pub fn parse_imperative_statements<'a>() -> impl Parser<'a, TokenStream<'a>, ImperativeStatement, ParserExtra<'a>> + Clone {
    recursive(|stmt| {
        let module_param = type_expr()
            .then(word().map_with(|name, e| make_id(name, to_position(e.span()))))
            .map(|(ty, name)| (name, ty));

        let portlike_arg = parse_attributes()
            .then(type_expr())
            .then(word().map_with(|name, e| make_id(name, to_position(e.span()))))
            .map(|((attrs, ty), name)| (name, ty, attrs));

        let simple_ifc = symbol(TokenKind::SymLParen)
            .ignore_then(type_expr().or_not())
            .then_ignore(symbol(TokenKind::SymRParen))
            .map(|ty| (Vec::<(Id, CType)>::new(), ty));

        let portlike_ifc = symbol(TokenKind::SymLParen)
            .ignore_then(
                portlike_arg
                    .separated_by(comma())
                    .at_least(1)
                    .collect::<Vec<_>>()
            )
            .then_ignore(symbol(TokenKind::SymRParen))
            .map(|mut ports: Vec<(Id, CType, Vec<(SmolStr, Option<String>)>)>| {
                let last = ports.pop().unwrap();
                let ifc_type = last.1;
                let args: Vec<(Id, CType)> = ports.into_iter().map(|(n, t, _)| (n, t)).collect();
                (args, Some(ifc_type))
            });

        let module_def = keyword(TokenKind::KwModule)
            .ignore_then(
                symbol(TokenKind::SymLBracket)
                    .ignore_then(type_expr())
                    .then_ignore(symbol(TokenKind::SymRBracket))
                    .or_not()
            )
            .then(word().map_with(|name, e| make_id(name, to_position(e.span()))))
            .then(
                symbol(TokenKind::SymHash)
                    .ignore_then(
                        symbol(TokenKind::SymLParen)
                            .ignore_then(
                                module_param.clone()
                                    .separated_by(comma())
                                    .collect::<Vec<_>>()
                            )
                            .then_ignore(symbol(TokenKind::SymRParen))
                    )
                    .or_not()
                    .map(|opt| opt.unwrap_or_default())
            )
            .then(
                simple_ifc.or(portlike_ifc)
                    .or_not()
                    .map(|opt| opt.unwrap_or((vec![], None)))
            )
            .then(
                keyword(TokenKind::KwProvisos)
                    .ignore_then(
                        symbol(TokenKind::SymLParen)
                            .ignore_then(proviso().separated_by(comma()).collect::<Vec<_>>())
                            .then_ignore(symbol(TokenKind::SymRParen))
                    )
                    .or_not()
                    .map(|opt| opt.unwrap_or_default())
            )
            .then_ignore(semicolon())
            .then(stmt.clone().repeated().collect::<Vec<_>>())
            .then_ignore(
                keyword(TokenKind::KwEndmodule)
                    .then_ignore(
                        symbol(TokenKind::SymColon)
                            .ignore_then(word())
                            .or_not()
                    )
            )
            .map_with(|(((((monad_ctx, name), static_params), (port_args, ifc_type)), provisos), body), e| {
                use crate::imperative::build_module_body_expr;
                let pos = to_position(e.span());
                let default_ifc = ifc_type.clone().unwrap_or_else(|| {
                    CType::Con(Id::qualified("Prelude", "Empty", Position::unknown()).into())
                });
                let mut all_params: Vec<(Id, CType)> = static_params;
                all_params.extend(port_args);
                let (monad_type, context_preds) = match monad_ctx {
                    Some(t) => (t, vec![]),
                    None => {
                        let m_tyvar = CType::Var(Id::new(SmolStr::new_static("_m__"), Position::unknown()));
                        let c_tyvar = CType::Var(Id::new(SmolStr::new_static("_c__"), Position::unknown()));
                        let is_module_pred = CPred {
                            class: Id::qualified("Prelude", "IsModule", Position::unknown()),
                            args: vec![m_tyvar.clone(), c_tyvar],
                            span: Span::DUMMY,
                        };
                        (m_tyvar, vec![is_module_pred])
                    }
                };
                let result_type = CType::Apply(
                    Box::new(monad_type),
                    Box::new(default_ifc.clone()),
                    Span::DUMMY,
                );
                let param_types: Vec<CType> = all_params.iter().map(|(_, t)| t.clone()).collect();
                let full_type = if param_types.is_empty() {
                    result_type
                } else {
                    param_types.into_iter().rev().fold(result_type, |acc, param_ty| {
                        crate::make_fn_type(param_ty, acc)
                    })
                };
                let mut all_context = context_preds;
                all_context.extend(provisos);
                let module_type = CQType {
                    context: all_context,
                    ty: full_type,
                    span: Span::DUMMY,
                };
                let body_expr = build_module_body_expr(pos.clone(), Some(default_ifc.clone()), body);
                let patterns: Vec<CPat> = all_params.iter().map(|(n, _)| CPat::Var(n.clone())).collect();
                let def_clause = CClause {
                    patterns,
                    qualifiers: vec![],
                    body: body_expr,
                    span: Span::DUMMY,
                };
                ImperativeStatement::ModuleDefn {
                    pos,
                    name,
                    pragma: None,
                    module_type,
                    def_clause,
                }
            })
            .labelled("module definition");

        // Mirrors pFunctionAfterKeyword from CVParser.lhs:4084-4123
        // Return type is optional: either "type name" or just "name"
        let function_def = keyword(TokenKind::KwFunction)
            .ignore_then(
                // Try: return_type name
                type_expr()
                    .then(word().map_with(|name, e| make_id(name, to_position(e.span()))))
                    .map(|(ty, name)| (Some(ty), name))
                    // Fallback: just name (no return type)
                    .or(word().map_with(|name, e| (None, make_id(name, to_position(e.span())))))
            )
            .then(
                symbol(TokenKind::SymLParen)
                    .ignore_then(
                        function_arg()
                            .separated_by(comma())
                            .collect::<Vec<_>>()
                            .or_not()
                            .map(|opt| opt.unwrap_or_default())
                    )
                    .then_ignore(symbol(TokenKind::SymRParen))
                    .or_not()
                    .map(|opt| opt.unwrap_or_default())
            )
            .then(
                keyword(TokenKind::KwProvisos)
                    .ignore_then(
                        symbol(TokenKind::SymLParen)
                            .ignore_then(proviso().separated_by(comma()).collect::<Vec<_>>())
                            .then_ignore(symbol(TokenKind::SymRParen))
                    )
                    .or_not()
                    .map(|opt| opt.unwrap_or_default())
            )
            .then_ignore(semicolon())
            .then(stmt.clone().repeated().collect::<Vec<_>>())
            .then_ignore(
                keyword(TokenKind::KwEndfunction)
                    .then_ignore(
                        symbol(TokenKind::SymColon)
                            .ignore_then(word())
                            .or_not()
                    )
            )
            .map_with(|((((opt_ret_type_and_name), params), provisos), body), e| {
                let (ret_type, name) = opt_ret_type_and_name;
                ImperativeStatement::FunctionDefn {
                    pos: to_position(e.span()),
                    name,
                    ret_type,
                    params,
                    provisos,
                    body,
                    attrs: Vec::new(),
                }
            })
            .labelled("function definition");

        let interface_decl = keyword(TokenKind::KwInterface)
            .ignore_then(constructor())
            .then(typedef_params())
            .then_ignore(semicolon())
            .then(interface_member().repeated().collect::<Vec<_>>())
            .then_ignore(
                keyword(TokenKind::KwEndinterface)
                    .then_ignore(
                        symbol(TokenKind::SymColon)
                            .ignore_then(word())
                            .or_not()
                    )
            )
            .map_with(|((name, type_params), members), e| {
                let (params, kinds): (Vec<Id>, Vec<CPartialKind>) = type_params.into_iter().unzip();
                let idk = mk_idk(name, &kinds);
                ImperativeStatement::InterfaceDecl {
                    pos: to_position(e.span()),
                    name: idk,
                    type_vars: params,
                    members,
                }
            })
            .labelled("interface declaration");

        let typedef_def = keyword(TokenKind::KwTypedef)
            .ignore_then(choice((
                typedef_enum(),
                typedef_struct(),
                typedef_union(),
                typedef_synonym(),
            )))
            .map(ImperativeStatement::Typedef)
            .labelled("typedef definition");

        let rule_def = keyword(TokenKind::KwRule)
            .ignore_then(word().map_with(|name, e| make_id(name, to_position(e.span()))))
            .then(
                keyword(TokenKind::KwIf).or_not()
                    .ignore_then(
                        symbol(TokenKind::SymLParen)
                            .ignore_then(expr())
                            .then_ignore(symbol(TokenKind::SymRParen))
                    )
                    .or_not()
            )
            .then_ignore(semicolon())
            .then(empty().map_with(|_, e| to_position(e.span())))
            .then(stmt.clone().repeated().collect::<Vec<_>>())
            .then_ignore(
                keyword(TokenKind::KwEndrule)
                    .then_ignore(
                        symbol(TokenKind::SymColon)
                            .ignore_then(word())
                            .or_not()
                    )
            )
            .map_with(|(((name, guard), body_pos), body), e| {
                ImperativeStatement::Rule {
                    pos: to_position(e.span()),
                    name,
                    guard,
                    body_pos,
                    body,
                    schedule_pragmas: Vec::new(),
                    rule_pragmas: Vec::new(),
                }
            })
            .labelled("rule definition");

        let rules_expr = keyword(TokenKind::KwRules)
            .ignore_then(
                symbol(TokenKind::SymColon)
                    .ignore_then(word())
                    .or_not()
            )
            .ignore_then(stmt.clone().repeated().collect::<Vec<ImperativeStatement>>())
            .then_ignore(
                keyword(TokenKind::KwEndrules)
                    .then_ignore(
                        symbol(TokenKind::SymColon)
                            .ignore_then(word())
                            .or_not()
                    )
            )
            .map_with(|stmts, e| {
                crate::imperative::convert_rules_block_to_expr(stmts, to_position(e.span()))
            })
            .labelled("rules expression");

        let expr_or_rules = choice((rules_expr.clone(), expr()));

        let typed_var_decl_with_rules = type_expr()
            .then(word().map_with(|name, e| make_id(name, to_position(e.span()))))
            .then(
                symbol(TokenKind::SymEq)
                    .ignore_then(expr_or_rules.clone())
                    .or_not()
            )
            .then_ignore(semicolon())
            .map(|((ty, name), opt_init)| {
                let init = opt_init.unwrap_or_else(|| {
                    let pos = name.position().clone();
                    let uninit_id = Id::qualified("Prelude", "primUninitialized", pos.clone());
                    let pos_lit = CExpr::Lit(Literal::Position, pos.clone());
                    let name_lit = CExpr::Lit(Literal::String(name.name().to_string()), pos);
                    CExpr::Apply(
                        Box::new(CExpr::Var(uninit_id)),
                        vec![pos_lit, name_lit],
                        Span::DUMMY,
                    )
                });
                ImperativeStatement::Decl {
                    ty: Some(ty),
                    name,
                    init: Some(init),
                }
            })
            .labelled("typed variable declaration");

        let module_inst_arrow_with_rules = type_expr()
            .then(word().map_with(|name, e| make_id(name, to_position(e.span()))))
            .then_ignore(symbol(TokenKind::SymLArrow))
            .then(expr_or_rules)
            .then_ignore(semicolon())
            .map(|((ifc_type, ifc_var), constructor)| {
                ImperativeStatement::Bind {
                    name: ifc_var,
                    ty: Some(ifc_type),
                    expr: constructor,
                }
            })
            .labelled("typed bind with arrow");

        let method_def = keyword(TokenKind::KwMethod)
            .ignore_then(type_expr().or_not())
            .then(word().map_with(|name, e| make_id(name, to_position(e.span()))))
            .then(
                symbol(TokenKind::SymLParen)
                    .ignore_then(
                        function_arg()
                            .separated_by(comma())
                            .collect::<Vec<_>>()
                            .or_not()
                            .map(|opt| opt.unwrap_or_default())
                    )
                    .then_ignore(symbol(TokenKind::SymRParen))
                    .or_not()
                    .map(|opt| opt.unwrap_or_default())
            )
            .then_ignore(semicolon().or_not())
            .then(stmt.clone().repeated().collect::<Vec<_>>())
            .then_ignore(
                keyword(TokenKind::KwEndmethod)
                    .then_ignore(
                        symbol(TokenKind::SymColon)
                            .ignore_then(word())
                            .or_not()
                    )
            )
            .map_with(|(((ret_type, name), params), body), e| {
                ImperativeStatement::MethodDefn {
                    pos: to_position(e.span()),
                    name,
                    ret_type,
                    params,
                    guard: None,
                    body,
                }
            })
            .labelled("method definition");

        // let name = expr; OR let { a, b } = expr;
        let let_simple = keyword(TokenKind::KwLet)
            .ignore_then(word().map_with(|name, e| make_id(name, to_position(e.span()))))
            .then_ignore(symbol(TokenKind::SymEq))
            .then(expr())
            .then_ignore(semicolon())
            .map(|(name, expr)| ImperativeStatement::Let { name, expr });

        let let_tuple = keyword(TokenKind::KwLet)
            .ignore_then(
                symbol(TokenKind::SymLBrace)
                    .ignore_then(
                        word().map_with(|name, e| make_id(name, to_position(e.span())))
                            .separated_by(comma())
                            .collect::<Vec<_>>()
                    )
                    .then_ignore(symbol(TokenKind::SymRBrace))
            )
            .then_ignore(symbol(TokenKind::SymEq))
            .then(expr())
            .then_ignore(semicolon())
            .map(|(names, init_expr)| ImperativeStatement::TupleDecl {
                names,
                ty: None,
                init: Some(init_expr),
            });

        let let_bind = keyword(TokenKind::KwLet)
            .ignore_then(word().map_with(|name, e| make_id(name, to_position(e.span()))))
            .then_ignore(symbol(TokenKind::SymLArrow))
            .then(expr())
            .then_ignore(semicolon())
            .map(|(name, expr)| ImperativeStatement::LetBind { name, expr });

        let let_stmt = choice((let_tuple, let_bind, let_simple))
            .labelled("let statement");

        let return_stmt = keyword(TokenKind::KwReturn)
            .ignore_then(expr().or_not())
            .then_ignore(semicolon())
            .map_with(|expr, e| ImperativeStatement::Return { pos: to_position(e.span()), expr })
            .labelled("return statement");

        let pattern = recursive(|pat: Recursive<dyn Parser<'a, TokenStream<'a>, CPat, ParserExtra<'a>> + 'a>| {
            let pattern_variable = symbol(TokenKind::SymDot)
                .ignore_then(word().map_with(|name, e| CPat::Var(make_id(name, to_position(e.span())))))
                .labelled("pattern variable");

            let wildcard_pat = symbol(TokenKind::SymDotStar)
                .map_with(|_, e| CPat::Wildcard(to_position(e.span())))
                .labelled("wildcard pattern");

            let tuple_pat = pat.clone()
                .separated_by(comma())
                .at_least(1)
                .collect::<Vec<_>>()
                .delimited_by(symbol(TokenKind::SymLBrace), symbol(TokenKind::SymRBrace))
                .map_with(|pats, e| {
                    let pos = to_position(e.span());
                    p_mk_tuple(pos, pats)
                })
                .labelled("tuple pattern");

            let tagged_pat = keyword(TokenKind::KwTagged)
                .ignore_then(constructor())
                .then(
                    choice((
                        pat.clone()
                            .separated_by(comma())
                            .at_least(1)
                            .collect::<Vec<_>>()
                            .delimited_by(symbol(TokenKind::SymLBrace), symbol(TokenKind::SymRBrace))
                            .map_with(|pats, e| {
                                let pos = to_position(e.span());
                                vec![p_mk_tuple(pos, pats)]
                            }),
                        symbol(TokenKind::SymDot)
                            .ignore_then(word().map_with(|name, e| CPat::Var(make_id(name, to_position(e.span())))))
                            .map(|p| vec![p]),
                        pat.clone()
                            .delimited_by(symbol(TokenKind::SymLParen), symbol(TokenKind::SymRParen))
                            .map(|p| vec![p]),
                        symbol(TokenKind::SymDotStar)
                            .map_with(|_, e| CPat::Wildcard(to_position(e.span())))
                            .map(|p| vec![p]),
                    ))
                    .or_not()
                    .map(|opt| opt.unwrap_or_default())
                )
                .map(|(con, args)| CPat::Con(con, args, Span::DUMMY))
                .labelled("tagged pattern");

            let enum_or_struct_pat = constructor()
                .map(|name| CPat::Con(name, Vec::new(), Span::DUMMY))
                .labelled("enum pattern");

            let paren_pat = pat.clone()
                .delimited_by(symbol(TokenKind::SymLParen), symbol(TokenKind::SymRParen))
                .labelled("parenthesized pattern");

            let const_pat = any().try_map(|token: TokenKind, span| {
                match token {
                    TokenKind::Integer { value, size, base } => {
                        let lit = Literal::Integer(IntLiteral {
                            value: value.to_string().parse().unwrap_or(0),
                            width: size.as_ref().and_then(|s| s.to_string().parse().ok()),
                            base: match base {
                                2 => IntBase::Binary,
                                8 => IntBase::Octal,
                                16 => IntBase::Hexadecimal,
                                _ => IntBase::Decimal,
                            },
                        });
                        Ok(CPat::Lit(lit, to_position(span)))
                    }
                    TokenKind::Number { value, bitwidth, base, .. } => {
                        use bsc_lexer_bsv::SvNumber;
                        let int_value: i128 = match value {
                            SvNumber::Integer(v) => v.to_string().parse().unwrap_or(0),
                            SvNumber::Real(f) => f as i128,
                            _ => 0,
                        };
                        let lit = Literal::Integer(IntLiteral {
                            value: int_value,
                            width: bitwidth.as_ref().and_then(|s| s.to_string().parse().ok()),
                            base: match base {
                                Some(bsc_lexer_bsv::SvNumericBase::Bin) => IntBase::Binary,
                                Some(bsc_lexer_bsv::SvNumericBase::Oct) => IntBase::Octal,
                                Some(bsc_lexer_bsv::SvNumericBase::Hex) => IntBase::Hexadecimal,
                                _ => IntBase::Decimal,
                            },
                        });
                        Ok(CPat::Lit(lit, to_position(span)))
                    }
                    TokenKind::String(s) => {
                        let lit = Literal::String(s.to_string());
                        Ok(CPat::Lit(lit, to_position(span)))
                    }
                    _ => Err(Rich::custom(span, "expected constant pattern")),
                }
            })
            .labelled("constant pattern");

            choice((pattern_variable, tagged_pat, paren_pat, tuple_pat, wildcard_pat, enum_or_struct_pat, const_pat))
                .labelled("pattern")
        });

        let cond_expression = expr()
            .then(
                keyword(TokenKind::KwMatches)
                    .ignore_then(pattern.clone())
                    .or_not()
            )
            .map(|(e, pat_opt)| {
                match pat_opt {
                    Some(pat) => CQual::Gen(CType::NoType, pat, e),
                    None => CQual::Filter(e),
                }
            });

        let cond_expressions = cond_expression
            .separated_by(symbol(TokenKind::SymAndAndAnd))
            .at_least(1)
            .collect::<Vec<CQual>>()
            .labelled("condition expressions");

        let if_stmt = keyword(TokenKind::KwIf)
            .ignore_then(
                symbol(TokenKind::SymLParen)
                    .ignore_then(cond_expressions)
                    .then_ignore(symbol(TokenKind::SymRParen))
            )
            .then(stmt.clone())
            .then(
                keyword(TokenKind::KwElse)
                    .ignore_then(stmt.clone())
                    .or_not()
            )
            .map_with(|((cond, then_stmt), else_stmt), e| {
                ImperativeStatement::If {
                    pos: to_position(e.span()),
                    cond,
                    then_branch: vec![then_stmt],
                    else_branch: else_stmt.map(|s| vec![s]),
                }
            })
            .labelled("if statement");

        let begin_end = keyword(TokenKind::KwBegin)
            .ignore_then(stmt.clone().repeated().collect::<Vec<_>>())
            .then_ignore(keyword(TokenKind::KwEnd))
            .map_with(|stmts, e| ImperativeStatement::BeginEnd {
                pos: to_position(e.span()),
                stmts,
            })
            .labelled("begin-end block");

        // for-loop init/update: typed decl or simple assignment (no semicolons)
        // "Integer x = 0" → Decl, "x = x+1" → Equal
        let for_init_or_update = choice((
            type_expr()
                .then(word().map_with(|name, e| make_id(name, to_position(e.span()))))
                .then_ignore(symbol(TokenKind::SymEq))
                .then(expr())
                .map(|((ty, name), init_expr)| {
                    ImperativeStatement::Decl {
                        ty: Some(ty),
                        name,
                        init: Some(init_expr),
                    }
                }),
            word().map_with(|name, e| make_id(name, to_position(e.span())))
                .then_ignore(symbol(TokenKind::SymEq))
                .then(expr())
                .map(|(name, rhs)| {
                    ImperativeStatement::Equal { name, expr: rhs }
                }),
        ));

        // for (init; cond; update) body
        let for_stmt = keyword(TokenKind::KwFor)
            .ignore_then(
                symbol(TokenKind::SymLParen)
                    .ignore_then(
                        for_init_or_update.clone()
                            .separated_by(comma())
                            .collect::<Vec<_>>()
                    )
                    .then_ignore(semicolon())
                    .then(expr())
                    .then_ignore(semicolon())
                    .then(
                        for_init_or_update
                            .separated_by(comma())
                            .collect::<Vec<_>>()
                    )
                    .then_ignore(symbol(TokenKind::SymRParen))
            )
            .then(stmt.clone())
            .map_with(|(((init, cond), update), body), e| {
                ImperativeStatement::For {
                    pos: to_position(e.span()),
                    init,
                    cond,
                    update,
                    body: vec![body],
                }
            })
            .labelled("for statement");

        #[derive(Clone)]
        enum RegSuffix {
            Field(Id),
            Args(Vec<CExpr>),
            Index(Position, CExpr),
            Range(CExpr, CExpr),
        }

        let reg_write_lhs = choice((
            word().map_with(|name, e| CExpr::Var(make_id(name, to_position(e.span())))),
            symbol(TokenKind::SymLParen)
                .ignore_then(expr())
                .then_ignore(symbol(TokenKind::SymRParen)),
        )).foldl(
            choice((
                symbol(TokenKind::SymDot)
                    .map_with(|_, e| to_position(e.span()))
                    .then(word())
                    .map(|(dot_pos, name)| make_id(name, dot_pos))
                    .map(RegSuffix::Field),
                symbol(TokenKind::SymLParen)
                    .ignore_then(
                        expr()
                            .separated_by(comma())
                            .collect::<Vec<_>>()
                    )
                    .then_ignore(symbol(TokenKind::SymRParen))
                    .map(RegSuffix::Args),
                symbol(TokenKind::SymLBracket)
                    .map_with(|_, e| crate::lookup_position(e.span().start))
                    .then(expr())
                    .then(
                        symbol(TokenKind::SymColon)
                            .ignore_then(expr())
                            .or_not()
                    )
                    .then_ignore(symbol(TokenKind::SymRBracket))
                    .map(|((pos, idx), opt_hi)| match opt_hi {
                        Some(hi) => RegSuffix::Range(idx, hi),
                        None => RegSuffix::Index(pos, idx),
                    }),
            )).repeated(),
            |e, suf| match suf {
                RegSuffix::Field(f) => CExpr::Select(Box::new(e), f, Span::DUMMY),
                RegSuffix::Args(args) => CExpr::Apply(Box::new(e), args, Span::DUMMY),
                RegSuffix::Index(pos, idx) => CExpr::Index { pos, expr: Box::new(e), index: Box::new(idx), span: Span::DUMMY },
                RegSuffix::Range(hi, lo) => CExpr::IndexRange { expr: Box::new(e), hi: Box::new(hi), lo: Box::new(lo), span: Span::DUMMY },
            },
        );

        let reg_write = reg_write_lhs
            .then(symbol(TokenKind::SymLtEq).map_with(|_, e| e.span()))
            .then(expr())
            .then_ignore(semicolon())
            .map(|((lhs, lt_eq_span), rhs)| {
                let pos = to_position(lt_eq_span);
                ImperativeStatement::RegWrite { pos, lhs, rhs }
            })
            .labelled("register write");

        // case (expr) matches tagged Pattern : stmt; ... endcase
        // Mirrors pImperativeCaseMatches from CVParser.lhs
        let case_matches_arm = pattern.clone()
            .then(
                symbol(TokenKind::SymAndAndAnd)
                    .ignore_then(expr())
                    .repeated()
                    .collect::<Vec<_>>()
            )
            .then_ignore(symbol(TokenKind::SymColon))
            .then(stmt.clone().repeated().at_least(1).collect::<Vec<_>>())
            .map_with(|((pat, guards), body), e| {
                (to_position(e.span()), pat, guards, body)
            })
            .labelled("case matches arm");

        let case_matches_default = keyword(TokenKind::KwDefault)
            .ignore_then(symbol(TokenKind::SymColon).or_not())
            .ignore_then(stmt.clone().repeated().at_least(1).collect::<Vec<_>>())
            .labelled("case matches default");

        let case_matches_stmt = keyword(TokenKind::KwCase)
            .ignore_then(
                symbol(TokenKind::SymLParen)
                    .ignore_then(expr())
                    .then_ignore(symbol(TokenKind::SymRParen))
            )
            .then_ignore(keyword(TokenKind::KwMatches))
            .then(case_matches_arm.repeated().collect::<Vec<_>>())
            .then(case_matches_default.or_not())
            .then_ignore(keyword(TokenKind::KwEndcase))
            .map_with(|((subject, arms), default), e| {
                ImperativeStatement::CaseTagged {
                    pos: to_position(e.span()),
                    subject,
                    arms,
                    default,
                }
            })
            .labelled("case matches statement");

        // case (expr) value: stmt; ... default: stmt; endcase
        // Mirrors pImperativeCaseIf from CVParser.lhs
        let case_arm = expr()
            .separated_by(comma())
            .at_least(1)
            .collect::<Vec<_>>()
            .then_ignore(symbol(TokenKind::SymColon))
            .then(stmt.clone().repeated().at_least(1).collect::<Vec<_>>())
            .map_with(|(conds, body), e| (to_position(e.span()), conds, body))
            .labelled("case arm");

        let case_default = keyword(TokenKind::KwDefault)
            .map_with(|_, e| to_position(e.span()))
            .then_ignore(symbol(TokenKind::SymColon).or_not())
            .then(stmt.clone().repeated().at_least(1).collect::<Vec<_>>())
            .map(|(pos, stmts)| (pos, stmts))
            .labelled("case default");

        let case_stmt = keyword(TokenKind::KwCase)
            .ignore_then(
                symbol(TokenKind::SymLParen)
                    .ignore_then(expr())
                    .then_ignore(symbol(TokenKind::SymRParen))
            )
            .then(case_arm.repeated().collect::<Vec<_>>())
            .then(case_default.or_not())
            .then_ignore(keyword(TokenKind::KwEndcase))
            .map_with(|((subject, arms), default), e| {
                ImperativeStatement::Case {
                    pos: to_position(e.span()),
                    subject,
                    arms,
                    default,
                }
            })
            .labelled("case statement");

        // while (cond) body
        let while_stmt = keyword(TokenKind::KwWhile)
            .ignore_then(
                symbol(TokenKind::SymLParen)
                    .ignore_then(expr())
                    .then_ignore(symbol(TokenKind::SymRParen))
            )
            .then(stmt.clone())
            .map_with(|(cond, body), e| {
                ImperativeStatement::While {
                    pos: to_position(e.span()),
                    cond,
                    body: vec![body],
                }
            })
            .labelled("while statement");

        // action ... endaction
        let action_block = keyword(TokenKind::KwAction)
            .ignore_then(stmt.clone().repeated().collect::<Vec<_>>())
            .then_ignore(keyword(TokenKind::KwEndaction))
            .map_with(|stmts, e| ImperativeStatement::Action {
                pos: to_position(e.span()),
                stmts,
            })
            .labelled("action block");

        // actionvalue ... endactionvalue
        let actionvalue_block = keyword(TokenKind::KwActionvalue)
            .ignore_then(stmt.clone().repeated().collect::<Vec<_>>())
            .then_ignore(keyword(TokenKind::KwEndactionvalue))
            .map_with(|stmts, e| ImperativeStatement::Action {
                pos: to_position(e.span()),
                stmts,
            })
            .labelled("actionvalue block");

        // Simple assignment: name = expr;
        // Mirrors pImperativeWithVarEq from CVParser.lhs: ISEqual pos vars expr
        let simple_assign = word().map_with(|name, e| make_id(name, to_position(e.span())))
            .then_ignore(symbol(TokenKind::SymEq))
            .then(expr())
            .then_ignore(semicolon())
            .map(|(name, rhs)| ImperativeStatement::Equal { name, expr: rhs })
            .labelled("simple assignment");

        // Expression-based assignment: expr.field = rhs; or expr[idx] = rhs;
        // Mirrors pImperativeWithExprEq from CVParser.lhs: ISUpdate pos expr rhs
        let expr_assign = expr()
            .then_ignore(symbol(TokenKind::SymEq))
            .then(expr())
            .then_ignore(semicolon())
            .map_with(|(lhs, rhs), e| ImperativeStatement::Update {
                pos: to_position(e.span()),
                lhs,
                rhs,
            })
            .labelled("expression assignment");

        let naked_expr = expr()
            .then_ignore(semicolon())
            .map(ImperativeStatement::NakedExpr)
            .labelled("expression statement");

        let typeclass_member = choice((
            keyword(TokenKind::KwFunction)
                .ignore_then(type_expr())
                .then(word().map_with(|name, e| make_id(name, to_position(e.span()))))
                .then(
                    symbol(TokenKind::SymLParen)
                        .ignore_then(
                            function_arg()
                                .separated_by(comma())
                                .collect::<Vec<_>>()
                                .or_not()
                                .map(|opt| opt.unwrap_or_default())
                        )
                        .then_ignore(symbol(TokenKind::SymRParen))
                        .or_not()
                        .map(|opt| opt.unwrap_or_default())
                )
                .then(
                    choice((
                        semicolon().ignore_then(
                            choice((
                                choice((
                                    keyword(TokenKind::KwFunction),
                                    keyword(TokenKind::KwModule),
                                    keyword(TokenKind::KwEndtypeclass),
                                )).rewind().to(None),
                                stmt.clone().repeated().collect::<Vec<ImperativeStatement>>()
                                    .then_ignore(
                                        keyword(TokenKind::KwEndfunction)
                                            .then_ignore(
                                                symbol(TokenKind::SymColon)
                                                    .ignore_then(word())
                                                    .or_not()
                                            )
                                    )
                                    .map(Some),
                            ))
                        ),
                        symbol(TokenKind::SymEq)
                            .ignore_then(expr())
                            .then_ignore(semicolon())
                            .map(|e| Some(vec![ImperativeStatement::Return { pos: Position::unknown(), expr: Some(e) }])),
                    ))
                )
                .map_with(|(((ret_type, name), params), body_opt), e| {
                    let arg_names: Vec<Id> = params.iter()
                        .map(|(name, _ty)| name.clone())
                        .collect();
                    let arg_types: Vec<CType> = params.iter()
                        .filter_map(|(_name, ty)| ty.clone())
                        .collect();
                    let method_type = arg_types.into_iter().rev().fold(ret_type, |acc, arg_ty| {
                        crate::make_fn_type(arg_ty, acc)
                    });
                    let default = match body_opt {
                        Some(body) => {
                            let body_expr = convert_stmts_to_expr(body);
                            vec![CClause {
                                patterns: params.iter().map(|(id, _)| CPat::Var(id.clone())).collect(),
                                qualifiers: vec![],
                                body: body_expr,
                                span: Span::DUMMY,
                            }]
                        }
                        None => vec![],
                    };
                    CField {
                        name,
                        pragmas: Some(vec![IfcPragma::ArgNames(arg_names)]),
                        orig_type: None,
                        ty: CQType {
                            context: Vec::new(),
                            ty: method_type,
                            span: to_span(e.span()),
                        },
                        default,
                        span: to_span(e.span()),
                    }
                }),
            type_expr()
                .then(word().map_with(|name, e| make_id(name, to_position(e.span()))))
                .then_ignore(semicolon())
                .map_with(|(ty, name), e| {
                    CField {
                        name,
                        pragmas: None,
                        orig_type: None,
                        ty: CQType {
                            context: Vec::new(),
                            ty,
                            span: to_span(e.span()),
                        },
                        default: Vec::new(),
                        span: to_span(e.span()),
                    }
                }),
        )).labelled("typeclass member");

        let typeclass_def = keyword(TokenKind::KwTypeclass)
            .ignore_then(word().map_with(|name, e| make_id(name, to_position(e.span()))))
            .then(
                symbol(TokenKind::SymHash)
                    .ignore_then(
                        symbol(TokenKind::SymLParen)
                            .ignore_then(
                                keyword(TokenKind::KwType)
                                    .ignore_then(word().map_with(|name, e| make_id(name, to_position(e.span()))))
                                    .separated_by(comma())
                                    .collect::<Vec<_>>()
                            )
                            .then_ignore(symbol(TokenKind::SymRParen))
                    )
                    .or_not()
                    .map(|opt| opt.unwrap_or_default())
            )
            .then(
                keyword(TokenKind::KwProvisos)
                    .ignore_then(
                        symbol(TokenKind::SymLParen)
                            .ignore_then(proviso().separated_by(comma()).collect::<Vec<_>>())
                            .then_ignore(symbol(TokenKind::SymRParen))
                    )
                    .or_not()
                    .map(|opt| opt.unwrap_or_default())
            )
            .then({
                let id_or_tuple = word()
                    .map_with(|name, e| make_id(name, to_position(e.span())))
                    .map(|id| vec![id])
                    .or(
                        symbol(TokenKind::SymLParen)
                            .ignore_then(
                                word()
                                    .map_with(|name, e| make_id(name, to_position(e.span())))
                                    .separated_by(comma())
                                    .collect::<Vec<_>>()
                            )
                            .then_ignore(symbol(TokenKind::SymRParen))
                    );

                let dependency = id_or_tuple.clone()
                    .then_ignore(
                        any().try_map(|token: TokenKind, span| {
                            if let TokenKind::Id(name) = &token {
                                if name == "determines" { return Ok(()); }
                            }
                            Err(Rich::custom(span, "expected 'determines'"))
                        })
                    )
                    .then(id_or_tuple)
                    .map(|(from, to)| (from, to));

                any().try_map(|token: TokenKind, span| {
                    if let TokenKind::Id(name) = &token {
                        if name == "dependencies" { return Ok(()); }
                    }
                    Err(Rich::custom(span, "expected 'dependencies'"))
                })
                .ignore_then(
                    symbol(TokenKind::SymLParen)
                        .ignore_then(
                            dependency
                                .separated_by(comma())
                                .at_least(1)
                                .collect::<Vec<_>>()
                        )
                        .then_ignore(symbol(TokenKind::SymRParen))
                )
                .or_not()
                .map(|opt| opt.unwrap_or_default())
            })
            .then_ignore(semicolon())
            .then(typeclass_member.repeated().collect::<Vec<_>>())
            .then_ignore(
                keyword(TokenKind::KwEndtypeclass)
                    .then_ignore(
                        symbol(TokenKind::SymColon)
                            .ignore_then(word())
                            .or_not()
                    )
            )
            .map_with(|((((name, type_vars), provisos), fundeps), members), _e| {
                ImperativeStatement::TypeclassDefn {
                    name,
                    type_vars,
                    provisos,
                    fundeps,
                    members,
                }
            })
            .labelled("typeclass definition");

        let instance_def = keyword(TokenKind::KwInstance)
            .ignore_then(word().map_with(|name, e| make_id(name, to_position(e.span()))))
            .then(
                symbol(TokenKind::SymHash)
                    .ignore_then(
                        symbol(TokenKind::SymLParen)
                            .ignore_then(type_expr().separated_by(comma()).collect::<Vec<_>>())
                            .then_ignore(symbol(TokenKind::SymRParen))
                    )
                    .or_not()
                    .map(|opt| opt.unwrap_or_default())
            )
            .then(
                keyword(TokenKind::KwProvisos)
                    .ignore_then(
                        symbol(TokenKind::SymLParen)
                            .ignore_then(proviso().separated_by(comma()).collect::<Vec<_>>())
                            .then_ignore(symbol(TokenKind::SymRParen))
                    )
                    .or_not()
                    .map(|opt| opt.unwrap_or_default())
            )
            .then_ignore(semicolon())
            .then(
                stmt.clone().repeated().collect::<Vec<_>>()
            )
            .then_ignore(
                keyword(TokenKind::KwEndinstance)
                    .then_ignore(
                        symbol(TokenKind::SymColon)
                            .ignore_then(word())
                            .or_not()
                    )
            )
            .map_with(|(((class_name, type_args), provisos), _body), _e| {
                ImperativeStatement::InstanceDefn {
                    class_name,
                    type_args,
                    provisos,
                    body: Vec::new(),
                }
            })
            .labelled("instance definition");

        parse_attributes()
            .then(choice((
                module_def,
                function_def,
                interface_decl,
                typedef_def,
                typeclass_def,
                instance_def,
                rule_def,
                method_def,
                case_matches_stmt,
                case_stmt,
                action_block,
                actionvalue_block,
                while_stmt,
                var_decl(),
                typed_var_decl_with_rules,
                module_inst_old_style(),
                module_inst_arrow_with_rules,
                if_stmt,
                for_stmt,
                begin_end,
                let_stmt,
                return_stmt,
                simple_assign,
                reg_write,
                expr_assign,
                naked_expr,
            )))
            .map(|(attrs, stmt)| {
                attach_attributes_to_stmt(attrs, stmt)
            })
    })
    .labelled("imperative statement")
}

fn attr_to_module_pprop(attr_name: &str, attr_value: &Option<String>) -> Option<CPragmaProperty> {
    let (name, value) = match attr_name {
        "synthesize" => ("verilog", None),
        "always_ready" => ("alwaysReady", None),
        "always_enabled" => ("alwaysEnabled", None),
        "enabled_when_ready" => ("enabledWhenReady", None),
        "CLK" | "clock_prefix" => ("CLK", attr_value.clone()),
        "RSTN" | "RST_N" | "reset_prefix" => ("RSTN", attr_value.clone()),
        "gate_prefix" => ("GATE", attr_value.clone()),
        "doc" => ("doc", attr_value.clone()),
        "no_default_clock" => ("noClock", None),
        "no_default_reset" => ("noReset", None),
        "clock_ancestors" => return None,
        "clock_family" => return None,
        _ => return None,
    };
    Some(CPragmaProperty {
        name: name.to_string(),
        value,
    })
}

fn attach_attributes_to_stmt(attrs: Vec<(SmolStr, Option<String>)>, stmt: ImperativeStatement) -> ImperativeStatement {
    if attrs.is_empty() {
        return stmt;
    }

    match stmt {
        ImperativeStatement::ModuleDefn { pos, name, module_type, def_clause, .. } => {
            let mut props = Vec::new();
            for (attr_name, attr_value) in &attrs {
                if let Some(prop) = attr_to_module_pprop(attr_name, attr_value) {
                    props.push(prop);
                }
            }
            let pragma = if !props.is_empty() {
                Some(CPragma::Properties(name.clone(), props))
            } else {
                None
            };
            ImperativeStatement::ModuleDefn {
                pos,
                name,
                pragma,
                module_type,
                def_clause,
            }
        }
        ImperativeStatement::FunctionDefn { pos, name, ret_type, params, provisos, body, .. } => {
            let new_attrs: Vec<(Id, Option<CExpr>)> = attrs.iter()
                .map(|(a, _)| (Id::new(a.clone(), pos.clone()), None))
                .collect();
            ImperativeStatement::FunctionDefn {
                pos,
                name,
                ret_type,
                params,
                provisos,
                body,
                attrs: new_attrs,
            }
        }
        ImperativeStatement::Rule { pos, name, guard, body_pos, body, .. } => {
            let schedule_pragmas = attrs_to_schedule_pragmas(&attrs);
            let rule_pragmas = attrs_to_rule_pragmas(&attrs);
            ImperativeStatement::Rule {
                pos,
                name,
                guard,
                body_pos,
                body,
                schedule_pragmas,
                rule_pragmas,
            }
        }
        other => other,
    }
}

fn attrs_to_schedule_pragmas(attrs: &[(SmolStr, Option<String>)]) -> Vec<CSchedulePragma> {
    let mut pragmas = Vec::new();
    for (name, value) in attrs {
        match name.as_str() {
            "descending_urgency" => {
                if let Some(s) = value {
                    let longnames: Vec<Vec<Id>> = s.split(',')
                        .map(|part| {
                            let trimmed = part.trim();
                            trimmed.split('.')
                                .map(|seg| Id::new(SmolStr::from(seg.trim()), Position::unknown()))
                                .collect()
                        })
                        .collect();
                    pragmas.push(CSchedulePragma::Urgency(longnames));
                }
            }
            _ => {}
        }
    }
    pragmas
}

fn attrs_to_rule_pragmas(attrs: &[(SmolStr, Option<String>)]) -> Vec<bsc_syntax::csyntax::RulePragma> {
    let mut pragmas = Vec::new();
    for (name, _value) in attrs {
        match name.as_str() {
            "fire_when_enabled" => {
                pragmas.push(bsc_syntax::csyntax::RulePragma::FireWhenEnabled);
            }
            "no_implicit_conditions" => {
                pragmas.push(bsc_syntax::csyntax::RulePragma::NoImplicitConditions);
            }
            _ => {}
        }
    }
    pragmas
}

/// Create a struct type name for a tagged union constructor with multiple fields.
///
/// This mirrors the Haskell implementation from CVParser.lhs where `mkSubStruct`
/// creates an anonymous struct type to hold multiple fields of a tagged union constructor.
/// The name follows the pattern `UnionName_$ConstructorName` and includes the
/// `IdProp::TypeJoin` property to track the original type and constructor names.
fn create_tagged_union_struct_type(union_name: &Id, constructor_name: &Id) -> CType {
    use bsc_syntax::id::IdProp;

    // Create struct type name: UnionName_$ConstructorName
    let combined_name = format!("{}_${}", union_name.name(), constructor_name.name());
    let mut struct_type_id = Id::new(combined_name, union_name.position().clone());

    // Copy qualifier from the union type
    struct_type_id.set_qualifier(union_name.qualifier().clone());

    // Add TypeJoin property to track original type and constructor
    // This mirrors mkTCId from Haskell's Id.hs
    struct_type_id.add_prop(IdProp::TypeJoin {
        original_type: Box::new(union_name.clone()),
        constructor: Box::new(constructor_name.clone()),
    });

    CType::Con(struct_type_id.into())
}

/// Create a struct definition for a tagged union constructor with multiple fields.
///
/// This mirrors the Haskell implementation from CVParser.lhs where `mkSubStruct`
/// creates a complete struct definition to accompany the type reference.
/// The struct contains all the fields from the tagged union constructor.
fn create_tagged_union_struct_definition(
    union_name: &Id,
    constructor_name: &Id,
    fields: Vec<(CType, Id)>,
) -> CDefn {
    use bsc_syntax::id::IdProp;
    use bsc_syntax::csyntax::{CField, CStructDef, StructSubType};

    // Create the struct type name with TypeJoin property
    let combined_name = format!("{}_${}", union_name.name(), constructor_name.name());
    let mut struct_type_id = Id::new(combined_name, union_name.position().clone());
    struct_type_id.set_qualifier(union_name.qualifier().clone());
    struct_type_id.add_prop(IdProp::TypeJoin {
        original_type: Box::new(union_name.clone()),
        constructor: Box::new(constructor_name.clone()),
    });

    // Convert fields to CField format
    let cfields: Vec<CField> = fields
        .into_iter()
        .map(|(ty, field_name)| CField {
            name: field_name,
            pragmas: None,
            ty: CQType {
                context: Vec::new(),
                ty,
                span: Span::DUMMY,
            },
            default: Vec::new(),
            orig_type: None,
            span: Span::DUMMY,
        })
        .collect();

    // Create the struct definition
    CDefn::Struct(CStructDef {
        visible: true,
        sub_type: StructSubType::DataCon {
            type_id: union_name.clone(),
            named_fields: true, // Tagged union struct fields are always named
        },
        name: IdK::Plain(struct_type_id),
        params: Vec::new(), // Tagged union struct fields don't have type parameters
        fields: cfields,
        deriving: Vec::new(), // No derivings for sub-structs
        span: Span::DUMMY,
    })
}
