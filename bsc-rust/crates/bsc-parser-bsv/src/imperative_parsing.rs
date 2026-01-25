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
                    return Ok(CType::Con(make_id(name, to_position(span))));
                }
            }
            Err(Rich::custom(span, "expected type constructor"))
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
                    CType::Con(Id::new("()", Position::unknown()))
                } else if ts.len() == 1 {
                    // Single parenthesized type
                    CType::Paren(Box::new(ts.into_iter().next().unwrap()), to_span(SimpleSpan::new((), 0..0)))
                } else {
                    // Multiple types form a tuple
                    CType::Tuple(ts, to_span(SimpleSpan::new((), 0..0)))
                }
            });

        // Parse atomic type expressions
        let atype = choice((paren_or_tuple, tyvar, tycon, num_type, str_type)).boxed();

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
        .map_with(|((ret_type, name), _args), e| {
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
        .then_ignore(semicolon())
        .map_with(|(_enum_tags, name), e| {
            vec![CDefn::Type(CTypeDef {
                name: IdK::Plain(name.clone()),
                params: Vec::new(),
                body: CType::Con(name),
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
        .then_ignore(semicolon())
        .map_with(|(fields, name), e| {
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
                deriving: Vec::new(),
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
                            arg_type: CType::Con(make_id("PrimUnit".into(), Position::unknown())), // Unit type for void
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
fn expr<'a>() -> impl Parser<'a, TokenStream<'a>, CExpr, ParserExtra<'a>> + Clone {
    recursive(|expr| {
        // pVariable: Parse variables/identifiers -> CVar
        let var = word().map_with(|name, e| {
            CExpr::Var(make_id(name, to_position(e.span())))
        });

        // Parse integer literals
        let int_lit = any().try_map(|token: TokenKind, span| {
            match token {
                TokenKind::Integer { value, .. } => {
                    let int_lit = IntLiteral {
                        value: value.to_string().parse().unwrap_or(0),
                        width: None,
                        base: IntBase::Decimal,
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

        // pPrimary: primary expressions (atoms)
        let primary = choice((paren, var, int_lit, str_lit)).boxed();

        // Suffix enum to represent different suffix types
        // Mirrors Haskell's pPrimaryWithSuffix approach
        #[derive(Clone)]
        enum Suffix {
            Field(Id),                    // .field -> CSelect
            Args(Vec<CExpr>),             // (args) -> CApply
            BitSel(CExpr),                // [index] -> CSub
            TypeApp(Vec<CType>),          // #(types) -> CTypeApply (BSV extension)
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
            // [index] (pPrimaryWithBitSel: pInBrackets pBitSelSubscript)
            symbol(TokenKind::SymLBracket)
                .ignore_then(expr.clone())
                .then_ignore(symbol(TokenKind::SymRBracket))
                .map(Suffix::BitSel),
            // #(types) - BSV type application
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
                .map(Suffix::TypeApp),
        ));

        // pPrimaryWithSuffix: apply suffixes left-associatively using foldl
        // Haskell: foldl mkSelect e selects, foldl mkSel expr es
        primary.foldl(
            suffix.repeated(),
            |e, suf| match suf {
                Suffix::Field(field) => CExpr::Select(Box::new(e), field, Span::DUMMY),
                Suffix::Args(args) => CExpr::Apply(Box::new(e), args, Span::DUMMY),
                Suffix::BitSel(index) => CExpr::Index { expr: Box::new(e), index: Box::new(index), span: Span::DUMMY },
                Suffix::TypeApp(types) => CExpr::TypeApply(Box::new(e), types, Span::DUMMY),
            },
        )
    })
    .labelled("expression")
}

/// Parse variable declaration: Type#(params) varName;
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
        let module_def = keyword(TokenKind::KwModule)
            .ignore_then(word().map_with(|name, e| make_id(name, to_position(e.span()))))
            .then(
                symbol(TokenKind::SymLParen)
                    .ignore_then(type_expr().or_not())
                    .then_ignore(symbol(TokenKind::SymRParen))
                    .or_not()
                    .map(|opt| opt.flatten())
            )
            .then_ignore(semicolon())
            .then(stmt.clone().repeated().collect::<Vec<_>>())
            .then_ignore(keyword(TokenKind::KwEndmodule))
            .map_with(|((name, ifc_type), body), e| {
                use crate::imperative::build_module_body_expr;
                let pos = to_position(e.span());
                let default_ifc = ifc_type.clone().unwrap_or_else(|| {
                    CType::Con(Id::qualified("Prelude", "Empty", Position::unknown()))
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
                let body_expr = build_module_body_expr(pos.clone(), ifc_type, body);
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

        let function_def = keyword(TokenKind::KwFunction)
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
            .then_ignore(keyword(TokenKind::KwEndfunction))
            .map_with(|((((ret_type, name), params), provisos), body), e| {
                ImperativeStatement::FunctionDefn {
                    pos: to_position(e.span()),
                    name,
                    ret_type: Some(ret_type),
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
            .then_ignore(keyword(TokenKind::KwEndinterface))
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
                symbol(TokenKind::SymLParen)
                    .ignore_then(any().map(|_| ()))
                    .repeated()
                    .then_ignore(symbol(TokenKind::SymRParen))
                    .or_not()
            )
            .then_ignore(semicolon())
            .then(stmt.clone().repeated().collect::<Vec<_>>())
            .then_ignore(keyword(TokenKind::KwEndrule))
            .map_with(|((name, _guard), body), e| {
                ImperativeStatement::Rule {
                    pos: to_position(e.span()),
                    name,
                    guard: None,
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
            .then_ignore(keyword(TokenKind::KwEndmethod))
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

        let let_stmt = keyword(TokenKind::KwLet)
            .ignore_then(word().map_with(|name, e| make_id(name, to_position(e.span()))))
            .then_ignore(symbol(TokenKind::SymEq))
            .then(any().map(|_| CExpr::Any { position: Position::unknown(), kind: UndefKind::NoMatch, span: Span::DUMMY }))
            .then_ignore(semicolon())
            .map(|(name, expr)| ImperativeStatement::Let { name, expr })
            .labelled("let statement");

        let return_stmt = keyword(TokenKind::KwReturn)
            .ignore_then(any().map(|_| CExpr::Any { position: Position::unknown(), kind: UndefKind::NoMatch, span: Span::DUMMY }).or_not())
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

        let naked_expr = expr()
            .then_ignore(semicolon())
            .map(ImperativeStatement::NakedExpr)
            .labelled("expression statement");

        parse_attributes()
            .then(choice((
                module_def,
                function_def,
                interface_decl,
                typedef_def,
                rule_def,
                method_def,
                module_inst_arrow(),
                module_inst_old_style(),
                var_decl(),
                if_stmt,
                begin_end,
                let_stmt,
                return_stmt,
                naked_expr,
            )))
            .map(|(attrs, stmt)| {
                attach_attributes_to_stmt(attrs, stmt)
            })
    })
    .labelled("imperative statement")
}

fn attach_attributes_to_stmt(attrs: Vec<SmolStr>, stmt: ImperativeStatement) -> ImperativeStatement {
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

    CType::Con(struct_type_id)
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
