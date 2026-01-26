//! Imperative statement parsing for BSV.
//!
//! This module implements parsing for BSV imperative statements that are used
//! in the top-level package parsing. These mirror the imperative parsing functions
//! from `src/comp/Parser/BSV/CVParser.lhs`.

use crate::imperative::ImperativeStatement;
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

fn parse_attribute_name<'a>() -> impl Parser<'a, TokenStream<'a>, SmolStr, ParserExtra<'a>> + Clone {
    select! {
        TokenKind::Id(name) => name,
    }.labelled("attribute name")
}

fn parse_single_attribute<'a>() -> impl Parser<'a, TokenStream<'a>, SmolStr, ParserExtra<'a>> + Clone {
    parse_attribute_name()
        .then(
            symbol(TokenKind::SymEq)
                .ignore_then(any().and_is(symbol(TokenKind::SymStarRParen).not()).and_is(comma().not()).repeated())
                .or_not()
        )
        .map(|(name, _value)| name)
        .labelled("single attribute")
}

fn parse_attributes<'a>() -> impl Parser<'a, TokenStream<'a>, Vec<SmolStr>, ParserExtra<'a>> + Clone {
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

        // Parse bit type: bit or bit[h:0]
        let bit_type = keyword(TokenKind::KwBit)
            .ignore_then(
                symbol(TokenKind::SymLBracket)
                    .ignore_then(
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
            .map_with(|high, e| {
                let pos = to_position(e.span());
                let bit_con = CType::Con(Id::qualified("Prelude", "Bit", pos.clone()).into());
                let width = high.map_or(1, |h| h + 1);
                let width_type = CType::Num(width, pos.clone());
                CType::Apply(
                    Box::new(bit_con),
                    Box::new(width_type),
                    to_span(e.span()),
                )
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
                CType::Con(CTyCon::full(
                    Id::qualified("Prelude", "PrimUnit", pos),
                    Some(CKind::Star(Span::DUMMY)),
                    CTyConSort::Struct(StructSubType::Struct, vec![]),
                ))
            });

        // Parse Integer keyword as type
        let integer_type = keyword(TokenKind::KwInteger)
            .map_with(|_, e| CType::Con(Id::qualified("Prelude", "Integer", to_position(e.span())).into()));

        // Parse atomic type expressions
        let atype = choice((paren_or_tuple, bit_type, action_type, actionvalue_type, void_type, integer_type, tyvar, tycon, num_type, str_type)).boxed();

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
    type_expr()
        .then(word().map_with(|name, e| make_id(name, to_position(e.span()))))
        .map(|(ty, name)| (name, Some(ty)))
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
            let arg_names: Vec<Id> = args.unwrap_or_default()
                .into_iter()
                .map(|(name, _ty)| name)
                .collect();
            CField {
                name,
                pragmas: Some(vec![IfcPragma::ArgNames(arg_names)]),
                orig_type: None,
                ty: CQType {
                    context: Vec::new(),
                    ty: ret_type,
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

fn interface_member<'a>() -> impl Parser<'a, TokenStream<'a>, CField, ParserExtra<'a>> + Clone {
    skip_attributes()
        .ignore_then(choice((
            method_prototype(),
            subinterface_prototype(),
        )))
        .labelled("interface member")
}

fn typedef_synonym<'a>() -> impl Parser<'a, TokenStream<'a>, Vec<CDefn>, ParserExtra<'a>> + Clone {
    type_expr()
        .then(constructor())
        .then_ignore(semicolon())
        .map_with(|(original, name), e| {
            vec![CDefn::Type(CTypeDef {
                name: IdK::Plain(name),
                params: Vec::new(),
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
                    arg_type: CType::Con(Id::unpositioned("Prelude::PrimUnit").into()),
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
        .then(parse_deriving())
        .then_ignore(semicolon())
        .map_with(|((fields, name), derivs), e| {
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
                name: IdK::Plain(name),
                params: Vec::new(),
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
        .then(deriving_clause())
        .then_ignore(semicolon())
        .map_with(|((constructors, name), derivings), e| {
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
                            arg_type: CType::Con(make_id("PrimUnit".into(), Position::unknown()).into()), // Unit type for void
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
                name: IdK::Plain(name),
                params: Vec::new(),
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

        // pConstructorPrimary: Parse uppercase constructors -> CCon name []
        let constructor_expr = constructor()
            .map(|con| CExpr::Con(con, vec![], Span::DUMMY));

        // pTaskIdentifier: Parse system identifiers like $finish -> CTaskApply
        let system_task = system_id()
            .map_with(|name, e| CExpr::Var(make_id(name, to_position(e.span()))));

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

        // pPrimary: primary expressions (atoms)
        let primary = choice((paren, system_task, question, tagged_expr, var, int_lit, str_lit, constructor_expr)).boxed();

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
                    let op_id = Id::qualified("Prelude", "negate", pos);
                    CExpr::Apply(Box::new(CExpr::Var(op_id)), vec![e], Span::DUMMY)
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
        }

        // Parse all suffixes: .field, (args), [index], #(types)
        let suffix = choice((
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
                Suffix::Args(args) => CExpr::Apply(Box::new(e), args, Span::DUMMY),
                Suffix::BitSel(pos, index) => CExpr::Index { pos, expr: Box::new(e), index: Box::new(index), span: Span::DUMMY },
                Suffix::BitSelRange(hi, lo) => CExpr::IndexRange { expr: Box::new(e), hi: Box::new(hi), lo: Box::new(lo), span: Span::DUMMY },
                Suffix::Params(params) => CExpr::Apply(Box::new(e), params, Span::DUMMY),
            },
        );

        // Binary operators for comparison and arithmetic expressions
        // This is a simplified pratt-style parser for common operators
        #[derive(Clone)]
        enum BinOp {
            LtEq,      // <=
            GtEq,      // >=
            Lt,        // <
            Gt,        // >
            Eq,        // ==
            NotEq,     // !=
            Plus,      // +
            Minus,     // -
            Star,      // *
            Slash,     // /
            And,       // &&
            Or,        // ||
            BitAnd,    // &
            BitOr,     // |
            BitXor,    // ^
            LShift,    // <<
            RShift,    // >>
        }

        let binop = choice((
            symbol(TokenKind::SymLtEq).to(BinOp::LtEq),
            symbol(TokenKind::SymGtEq).to(BinOp::GtEq),
            symbol(TokenKind::SymLt).to(BinOp::Lt),
            symbol(TokenKind::SymGt).to(BinOp::Gt),
            symbol(TokenKind::SymEqEq).to(BinOp::Eq),
            symbol(TokenKind::SymBangEq).to(BinOp::NotEq),
            symbol(TokenKind::SymPlus).to(BinOp::Plus),
            symbol(TokenKind::SymMinus).to(BinOp::Minus),
            symbol(TokenKind::SymStar).to(BinOp::Star),
            symbol(TokenKind::SymSlash).to(BinOp::Slash),
            symbol(TokenKind::SymAndAnd).to(BinOp::And),
            symbol(TokenKind::SymPipePipe).to(BinOp::Or),
            symbol(TokenKind::SymAnd).to(BinOp::BitAnd),
            symbol(TokenKind::SymPipe).to(BinOp::BitOr),
            symbol(TokenKind::SymCaret).to(BinOp::BitXor),
            symbol(TokenKind::SymLtLt).to(BinOp::LShift),
            symbol(TokenKind::SymGtGt).to(BinOp::RShift),
        ));

        fn op_to_id(op: &BinOp, pos: Position) -> Id {
            use crate::operators::*;
            match op {
                BinOp::LtEq => id_lt_eq_at(pos),
                BinOp::GtEq => id_gt_eq_at(pos),
                BinOp::Lt => id_lt_at(pos),
                BinOp::Gt => id_gt_at(pos),
                BinOp::Eq => id_equal_at(pos),
                BinOp::NotEq => id_not_equal_at(pos),
                BinOp::Plus => id_plus_at(pos),
                BinOp::Minus => id_minus_at(pos),
                BinOp::Star => id_star_at(pos),
                BinOp::Slash => id_slash_at(pos),
                BinOp::And => id_and_at(pos),
                BinOp::Or => id_or_at(pos),
                BinOp::BitAnd => id_bit_and_at(pos),
                BinOp::BitOr => id_bit_or_at(pos),
                BinOp::BitXor => id_caret_at(pos),
                BinOp::LShift => id_lsh_at(pos),
                BinOp::RShift => id_rsh_at(pos),
            }
        }

        // Parse binary expressions: primary (op primary)*
        // This creates left-associative expressions
        let binary_expr = primary_with_suffix.clone().foldl(
            binop.then(primary_with_suffix).repeated(),
            |left, (op, right)| {
                let op_id = op_to_id(&op, Position::unknown());
                crate::operators::make_binary_expr(left, op_id, right)
            },
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
        .map_with(|((ifc_type, ifc_var), constructor), e| {
            let ifc_var_clone = ifc_var.clone(); // Clone before moving
            ImperativeStatement::Inst {
                pos: to_position(e.span()),
                attrs: Vec::new(),
                ifc_var,
                inst_var: ifc_var_clone, // For arrow syntax, instance and interface vars are same
                ifc_type: Some(ifc_type),
                clocked_by: None,
                reset_by: None,
                powered_by: None,
                constructor,
            }
        })
        .labelled("module instantiation with arrow")
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

        let module_def = keyword(TokenKind::KwModule)
            .ignore_then(word().map_with(|name, e| make_id(name, to_position(e.span()))))
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
                symbol(TokenKind::SymLParen)
                    .ignore_then(type_expr().or_not())
                    .then_ignore(symbol(TokenKind::SymRParen))
                    .or_not()
                    .map(|opt| opt.flatten())
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
            .map_with(|(((name, _params), ifc_type), body), e| {
                use crate::imperative::build_module_body_expr;
                let pos = to_position(e.span());
                let default_ifc = ifc_type.clone().unwrap_or_else(|| {
                    CType::Con(Id::qualified("Prelude", "Empty", Position::unknown()).into())
                });
                let m_tyvar = CType::Var(Id::new(SmolStr::new_static("_m__"), Position::unknown()));
                let c_tyvar = CType::Var(Id::new(SmolStr::new_static("_c__"), Position::unknown()));
                let result_type = CType::Apply(
                    Box::new(m_tyvar.clone()),
                    Box::new(default_ifc.clone()),
                    Span::DUMMY,
                );
                let is_module_pred = CPred {
                    class: Id::qualified("Prelude", "IsModule", Position::unknown()),
                    args: vec![m_tyvar, c_tyvar],
                    span: Span::DUMMY,
                };
                let module_type = CQType {
                    context: vec![is_module_pred],
                    ty: result_type,
                    span: Span::DUMMY,
                };
                let body_expr = build_module_body_expr(pos.clone(), Some(default_ifc.clone()), body);
                let def_clause = CClause {
                    patterns: vec![],
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
            .ignore_then(word().map_with(|name, e| make_id(name, to_position(e.span()))))
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
            .map_with(|(name, members), e| {
                ImperativeStatement::InterfaceDecl {
                    pos: to_position(e.span()),
                    name,
                    type_vars: Vec::new(),
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
            .then(stmt.clone().repeated().collect::<Vec<_>>())
            .then_ignore(
                keyword(TokenKind::KwEndrule)
                    .then_ignore(
                        symbol(TokenKind::SymColon)
                            .ignore_then(word())
                            .or_not()
                    )
            )
            .map_with(|((name, guard), body), e| {
                ImperativeStatement::Rule {
                    pos: to_position(e.span()),
                    name,
                    guard,
                    body_pos: to_position(e.span()),
                    body,
                }
            })
            .labelled("rule definition");

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

        let let_stmt = choice((let_tuple, let_simple))
            .labelled("let statement");

        let return_stmt = keyword(TokenKind::KwReturn)
            .ignore_then(expr().or_not())
            .then_ignore(semicolon())
            .map_with(|expr, e| ImperativeStatement::Return { pos: to_position(e.span()), expr })
            .labelled("return statement");

        let if_stmt = keyword(TokenKind::KwIf)
            .ignore_then(
                symbol(TokenKind::SymLParen)
                    .ignore_then(expr())
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

        let reg_write = expr()
            .then_ignore(symbol(TokenKind::SymLtEq))
            .then(expr())
            .then_ignore(semicolon())
            .map(|(lhs, rhs)| ImperativeStatement::RegWrite { lhs, rhs })
            .labelled("register write");

        // Pattern parser for case matches
        // Mirrors pPattern from CVParser.lhs
        // Mirrors pPattern from CVParser.lhs:2669-2677
        // pPattern = pPatternVariable <|> tagged_constr <|> constr <|> paren <|> tuple <|> wildcard <|> const
        let pattern = recursive(|pat: Recursive<dyn Parser<'a, TokenStream<'a>, CPat, ParserExtra<'a>> + 'a>| {
            // pPatternVariable: .name => CPVar name (Haskell CVParser.lhs:2712-2716)
            let pattern_variable = symbol(TokenKind::SymDot)
                .ignore_then(word().map_with(|name, e| CPat::Var(make_id(name, to_position(e.span())))))
                .labelled("pattern variable");

            // pWildcardPattern: .* => CPAny pos (Haskell CVParser.lhs:2788-2792)
            let wildcard_pat = symbol(TokenKind::SymDotStar)
                .map_with(|_, e| CPat::Wildcard(to_position(e.span())))
                .labelled("wildcard pattern");

            // pConstrPatternWith: after 'tagged Constructor', parse the body
            // Haskell CVParser.lhs:2679-2692
            let tagged_pat = keyword(TokenKind::KwTagged)
                .ignore_then(constructor())
                .then(
                    choice((
                        // .var => CPCon constr [CPVar var]
                        symbol(TokenKind::SymDot)
                            .ignore_then(word().map_with(|name, e| CPat::Var(make_id(name, to_position(e.span())))))
                            .map(|p| vec![p]),
                        // (pattern) => CPCon constr [pat]
                        pat.clone()
                            .delimited_by(symbol(TokenKind::SymLParen), symbol(TokenKind::SymRParen))
                            .map(|p| vec![p]),
                        // wildcard/const/enum pattern => CPCon constr [pat]
                        symbol(TokenKind::SymDotStar)
                            .map_with(|_, e| CPat::Wildcard(to_position(e.span())))
                            .map(|p| vec![p]),
                    ))
                    .or_not()
                    .map(|opt| opt.unwrap_or_default())
                )
                .map(|(con, args)| CPat::Con(con, args, Span::DUMMY))
                .labelled("tagged pattern");

            // pStructOrEnumPatternWith: Constructor {fields} or just Constructor
            // Haskell CVParser.lhs:2694-2699
            let enum_or_struct_pat = constructor()
                .map(|name| CPat::Con(name, Vec::new(), Span::DUMMY))
                .labelled("enum pattern");

            // Parenthesized pattern
            let paren_pat = pat.clone()
                .delimited_by(symbol(TokenKind::SymLParen), symbol(TokenKind::SymRParen))
                .labelled("parenthesized pattern");

            // pConstPattern: numeric or string literal
            // Haskell CVParser.lhs:2779-2782
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

            // Order mirrors Haskell: pattern_variable, tagged, constr, paren, wildcard, const
            choice((pattern_variable, tagged_pat, paren_pat, wildcard_pat, enum_or_struct_pat, const_pat))
                .labelled("pattern")
        });

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
            .map(|(conds, body)| (conds, body))
            .labelled("case arm");

        let case_default = keyword(TokenKind::KwDefault)
            .ignore_then(symbol(TokenKind::SymColon).or_not())
            .ignore_then(stmt.clone().repeated().at_least(1).collect::<Vec<_>>())
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
                .then_ignore(semicolon())
                .map_with(|((ret_type, name), _params), e| {
                    CField {
                        name,
                        pragmas: None,
                        orig_type: None,
                        ty: CQType {
                            context: Vec::new(),
                            ty: ret_type,
                            span: to_span(e.span()),
                        },
                        default: Vec::new(),
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
            .map_with(|(((name, type_vars), provisos), members), _e| {
                ImperativeStatement::TypeclassDefn {
                    name,
                    type_vars,
                    provisos,
                    fundeps: Vec::new(),
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
                typed_var_decl(),
                module_inst_old_style(),
                module_inst_arrow(),
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

fn attach_attributes_to_stmt(attrs: Vec<SmolStr>, stmt: ImperativeStatement) -> ImperativeStatement {
    if attrs.is_empty() {
        return stmt;
    }

    let has_synthesize = attrs.iter().any(|a| a == "synthesize");

    match stmt {
        ImperativeStatement::ModuleDefn { pos, name, module_type, def_clause, .. } => {
            let pragma = if has_synthesize {
                Some(CPragma::Properties(
                    name.clone(),
                    vec![CPragmaProperty {
                        name: "verilog".to_string(),
                        value: None,
                    }],
                ))
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
                .map(|a| (Id::new(a.clone(), pos.clone()), None))
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
        other => other,
    }
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
