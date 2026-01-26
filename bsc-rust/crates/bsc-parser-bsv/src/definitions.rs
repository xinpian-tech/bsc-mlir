//! Definition parsing for BSV.
//!
//! This module mirrors the definition parsing functions from `src/comp/Parser/BSV/CVParser.lhs`.
//! It implements BSV's definition syntax including modules, functions, interfaces, typedefs, rules, etc.
//!
//! # BSV Definition Syntax
//!
//! BSV supports several forms of top-level definitions:
//!
//! ## Module Definitions
//! ```text
//! module [#(params)] mkName(IfcType);
//!     <module body>
//! endmodule
//! ```
//!
//! ## Function Definitions
//! ```text
//! function RetType funcName(args);
//!     <function body>
//! endfunction
//! ```
//!
//! ## Interface Declarations
//! ```text
//! interface IfcName [#(params)];
//!     method RetType methodName(args);
//!     interface SubIfc sub;
//! endinterface
//! ```
//!
//! ## Typedef Declarations
//! ```text
//! typedef OldType NewType;                    // synonym
//! typedef enum { Tag1, Tag2, ... } EnumName;  // enum
//! typedef struct { ... } StructName;          // struct
//! typedef union tagged { ... } UnionName;    // tagged union
//! ```
//!
//! ## Rule Definitions
//! ```text
//! rule ruleName [conditions];
//!     <rule body>
//! endrule
//! ```
//!
//! ## Typeclass Declarations
//! ```text
//! typeclass ClassName#(type a);
//!     <typeclass body>
//! endtypeclass
//! ```
//!
//! ## Instance Declarations
//! ```text
//! instance ClassName#(ConcreteType);
//!     <instance body>
//! endinstance
//! ```

use crate::imperative::ImperativeStatement;
use crate::BsvParser;
use bsc_diagnostics::{Position, Span, ParseError};
use bsc_lexer_bsv::TokenKind;
use bsc_syntax::csyntax::*;
use bsc_syntax::id::Id;

impl<'src> BsvParser<'src> {
    // ========================================================================
    // Module Parsing
    // ========================================================================

    /// Parse a module definition.
    ///
    /// Grammar:
    /// ```text
    /// module [#(params)] mkName(IfcType) [provisos];
    ///     <module body>
    /// endmodule
    /// ```
    ///
    /// This mirrors `pImperativeModule` from CVParser.lhs.
    pub fn parse_module(&mut self) -> crate::ParseResult<ImperativeStatement> {
        let start_pos = self.current_span().start;
        self.expect(&TokenKind::KwModule)?;

        // Parse optional type parameters: #(param1, param2, ...)
        let _type_params = if self.eat(&TokenKind::SymHash) {
            self.expect(&TokenKind::SymLParen)?;
            let params = self.parse_comma_separated(Self::parse_type_param)?;
            self.expect(&TokenKind::SymRParen)?;
            params
        } else {
            Vec::new()
        };

        // Parse module name
        let name = self.parse_def_identifier()?;

        // Parse module parameters and interface type: (IfcType)
        let (params, ifc_type) = self.parse_module_params()?;

        // Parse optional provisos
        let provisos = if self.check(&TokenKind::KwProvisos) {
            self.advance(); // consume 'provisos'
            self.expect(&TokenKind::SymLParen)?;
            let provs = self.parse_comma_separated(Self::parse_proviso)?;
            self.expect(&TokenKind::SymRParen)?;
            provs
        } else {
            Vec::new()
        };

        self.expect(&TokenKind::SymSemi)?;

        // Parse module body
        let body = self.parse_module_body()?;

        self.expect(&TokenKind::KwEndmodule)?;

        use crate::imperative::build_module_body_expr;
        use smol_str::SmolStr;
        let pos = Position::new("<unknown>", start_pos as i32, start_pos as i32);

        let m_tyvar = CType::Var(Id::new(SmolStr::new_static("_m__"), Position::unknown()));
        let c_tyvar = CType::Var(Id::new(SmolStr::new_static("_c__"), Position::unknown()));
        let result_type = CType::Apply(
            Box::new(m_tyvar.clone()),
            Box::new(ifc_type.clone()),
            Span::DUMMY,
        );

        let param_types: Vec<CType> = params.iter().map(|(_, t, _)| t.clone()).collect();
        let full_type = if param_types.is_empty() {
            result_type
        } else {
            param_types.into_iter().rev().fold(result_type, |acc, param_ty| {
                crate::make_fn_type(param_ty, acc)
            })
        };

        let is_module_pred = CPred {
            class: Id::qualified("Prelude", "IsModule", Position::unknown()),
            args: vec![m_tyvar, c_tyvar],
            span: Span::DUMMY,
        };
        let mut all_context = vec![is_module_pred];
        all_context.extend(provisos);

        let module_type = CQType {
            context: all_context,
            ty: full_type,
            span: Span::DUMMY,
        };

        let body_expr = build_module_body_expr(pos.clone(), Some(ifc_type), body);
        let patterns: Vec<CPat> = params.into_iter().map(|(n, _, _)| CPat::Var(n)).collect();
        let def_clause = CClause {
            patterns,
            qualifiers: vec![],
            body: body_expr,
            span: Span::DUMMY,
        };

        Ok(ImperativeStatement::ModuleDefn {
            pos,
            name,
            pragma: None,
            module_type,
            def_clause,
        })
    }

    /// Parse module parameters: (IfcType)
    /// This extracts the interface type that the module provides.
    fn parse_module_params(&mut self) -> crate::ParseResult<(Vec<(Id, CType, bool)>, CType)> {
        self.expect(&TokenKind::SymLParen)?;
        let ifc_type = self.parse_type_expr()?;
        self.expect(&TokenKind::SymRParen)?;

        // BSV modules don't have explicit parameters in the signature like functions do
        // The interface type is what the module provides
        Ok((Vec::new(), ifc_type))
    }

    /// Parse module body statements until `endmodule`.
    fn parse_module_body(&mut self) -> crate::ParseResult<Vec<ImperativeStatement>> {
        let mut statements = Vec::new();

        while !self.check(&TokenKind::KwEndmodule) && !self.is_eof() {
            let stmt = self.parse_module_statement()?;
            statements.push(stmt);
        }

        Ok(statements)
    }

    /// Parse a statement valid in module context.
    /// This includes rules, methods, instantiations, declarations, etc.
    fn parse_module_statement(&mut self) -> crate::ParseResult<ImperativeStatement> {
        match self.current_kind() {
            TokenKind::KwRule => self.parse_rule(),
            TokenKind::KwFunction => self.parse_function(),
            TokenKind::KwInterface => self.parse_interface_decl(),
            TokenKind::KwTypedef => self.parse_typedef(),
            _ => {
                // For now, return an error for unsupported statements
                Err(ParseError::InvalidSyntax {
                    message: format!("Unsupported module statement: {}", self.current_kind().name()),
                    span: self.current_span().into(),
                })
            }
        }
    }

    // ========================================================================
    // Function Parsing
    // ========================================================================

    /// Parse a function definition.
    ///
    /// Grammar:
    /// ```text
    /// function RetType funcName(args) [provisos];
    ///     <function body>
    /// endfunction
    /// ```
    ///
    /// This mirrors `pImperativeFunction` from CVParser.lhs.
    pub fn parse_function(&mut self) -> crate::ParseResult<ImperativeStatement> {
        let start_pos = self.current_span().start;
        self.expect(&TokenKind::KwFunction)?;

        // Parse return type
        let ret_type = Some(self.parse_type_expr()?);

        // Parse function name
        let name = self.parse_def_identifier()?;

        // Parse function arguments
        self.expect(&TokenKind::SymLParen)?;
        let params = if self.check(&TokenKind::SymRParen) {
            Vec::new()
        } else {
            self.parse_comma_separated(Self::parse_function_arg)?
        };
        self.expect(&TokenKind::SymRParen)?;

        // Parse optional provisos
        let provisos = if self.check(&TokenKind::KwProvisos) {
            self.advance(); // consume 'provisos'
            self.expect(&TokenKind::SymLParen)?;
            let provs = self.parse_comma_separated(Self::parse_proviso)?;
            self.expect(&TokenKind::SymRParen)?;
            provs
        } else {
            Vec::new()
        };

        self.expect(&TokenKind::SymSemi)?;

        // Parse function body
        let body = self.parse_function_body()?;

        self.expect(&TokenKind::KwEndfunction)?;

        let pos = Position::new("<unknown>", start_pos as i32, start_pos as i32);

        Ok(ImperativeStatement::FunctionDefn {
            pos,
            name,
            ret_type,
            params,
            provisos,
            body,
            attrs: Vec::new(), // Attributes would be parsed from function attributes if available
        })
    }

    /// Parse a function argument: Type argName
    fn parse_function_arg(&mut self) -> crate::ParseResult<(Id, Option<CType>)> {
        let ty = self.parse_type_expr()?;
        let name = self.parse_def_identifier()?;
        Ok((name, Some(ty)))
    }

    /// Parse a function argument with optional type (for some contexts).
    #[allow(dead_code)]
    fn parse_function_arg_opt_type(&mut self) -> crate::ParseResult<(Id, Option<CType>)> {
        // Try to parse as typed argument first
        if let Ok(checkpoint) = self.save_checkpoint() {
            if let Ok(ty) = self.parse_type_expr() {
                if let Ok(name) = self.parse_def_identifier() {
                    return Ok((name, Some(ty)));
                }
            }
            self.restore_checkpoint(checkpoint)?;
        }

        // Parse as untyped argument
        let name = self.parse_def_identifier()?;
        Ok((name, None))
    }

    /// Parse function body statements until `endfunction`.
    fn parse_function_body(&mut self) -> crate::ParseResult<Vec<ImperativeStatement>> {
        let mut statements = Vec::new();

        while !self.check(&TokenKind::KwEndfunction) && !self.is_eof() {
            let stmt = self.parse_function_statement()?;
            statements.push(stmt);
        }

        Ok(statements)
    }

    /// Parse a statement valid in function context.
    fn parse_function_statement(&mut self) -> crate::ParseResult<ImperativeStatement> {
        // For now, return an error for unsupported statements
        Err(ParseError::InvalidSyntax {
            message: format!("Function statement parsing not yet implemented: {}", self.current_kind().name()),
            span: self.current_span().into(),
        })
    }

    // ========================================================================
    // Interface Parsing
    // ========================================================================

    /// Parse an interface declaration.
    ///
    /// Grammar:
    /// ```text
    /// interface IfcName [#(params)];
    ///     method RetType methodName(args);
    ///     interface SubIfc sub;
    /// endinterface
    /// ```
    ///
    /// This mirrors `pImperativeInterfaceDeclAt` from CVParser.lhs.
    pub fn parse_interface_decl(&mut self) -> crate::ParseResult<ImperativeStatement> {
        let start_pos = self.current_span().start;
        self.expect(&TokenKind::KwInterface)?;

        // Parse interface name and optional type parameters
        let name = self.parse_def_identifier()?;

        let type_vars = if self.eat(&TokenKind::SymHash) {
            self.expect(&TokenKind::SymLParen)?;
            let params = self.parse_comma_separated(Self::parse_type_param)?;
            self.expect(&TokenKind::SymRParen)?;
            params.into_iter().map(|(id, _)| id).collect()
        } else {
            Vec::new()
        };

        self.expect(&TokenKind::SymSemi)?;

        // Parse interface members
        let mut members = Vec::new();
        while !self.check(&TokenKind::KwEndinterface) && !self.is_eof() {
            if self.check(&TokenKind::KwMethod) {
                let method = self.parse_method_prototype()?;
                members.push(method);
            } else if self.check(&TokenKind::KwInterface) {
                let subinterface = self.parse_subinterface_prototype()?;
                members.push(subinterface);
            } else {
                return Err(ParseError::InvalidSyntax {
                    message: format!("Expected method or subinterface in interface, found: {}", self.current_kind().name()),
                    span: self.current_span().into(),
                });
            }
        }

        self.expect(&TokenKind::KwEndinterface)?;

        let pos = Position::new("<unknown>", start_pos as i32, start_pos as i32);

        Ok(ImperativeStatement::InterfaceDecl {
            pos,
            name,
            type_vars,
            members,
        })
    }

    /// Parse a method prototype: `method RetType methodName(args);`
    fn parse_method_prototype(&mut self) -> crate::ParseResult<CField> {
        self.expect(&TokenKind::KwMethod)?;

        let ret_type = self.parse_type_expr()?;
        let name = self.parse_def_identifier()?;

        self.expect(&TokenKind::SymLParen)?;
        let args = if self.check(&TokenKind::SymRParen) {
            Vec::new()
        } else {
            self.parse_comma_separated(Self::parse_function_arg)?
        };
        self.expect(&TokenKind::SymRParen)?;
        self.expect(&TokenKind::SymSemi)?;

        // Construct method type with arguments: foldr fn rettype argtypes
        // This mirrors the Haskell `foldr fn rettype argtypes` pattern
        let arg_types: Vec<CType> = args.iter()
            .filter_map(|(_, ty_opt)| ty_opt.clone())
            .collect();

        let method_type = if arg_types.is_empty() {
            ret_type
        } else {
            // Build function type: arg1 -> arg2 -> ... -> rettype
            arg_types.into_iter().rev().fold(ret_type, |acc, arg_type| {
                crate::make_fn_type(arg_type, acc)
            })
        };

        let arg_names: Vec<Id> = args.iter().map(|(name, _)| name.clone()).collect();
        let pragmas = Some(vec![IfcPragma::ArgNames(arg_names)]);

        Ok(CField {
            name,
            pragmas,
            orig_type: None,
            ty: CQType {
                context: Vec::new(),
                ty: method_type,
                span: Span::DUMMY,
            },
            default: Vec::new(),
            span: Span::DUMMY,
        })
    }

    /// Parse a subinterface prototype: `interface SubIfc sub;`
    fn parse_subinterface_prototype(&mut self) -> crate::ParseResult<CField> {
        self.expect(&TokenKind::KwInterface)?;

        let ifc_type = self.parse_type_expr()?;
        let name = self.parse_def_identifier()?;
        self.expect(&TokenKind::SymSemi)?;

        // Convert to CField representation
        Ok(CField {
            name,
            pragmas: None,
            orig_type: None,
            ty: CQType {
                context: Vec::new(),
                ty: ifc_type,
                span: Span::DUMMY,
            },
            default: Vec::new(),
            span: Span::DUMMY,
        })
    }

    // ========================================================================
    // Typedef Parsing
    // ========================================================================

    /// Parse a typedef declaration.
    ///
    /// This is the main entry point that dispatches to specific typedef variants.
    /// This mirrors `pImperativeTypedef` from CVParser.lhs.
    pub fn parse_typedef(&mut self) -> crate::ParseResult<ImperativeStatement> {
        let _start_pos = self.current_span().start;
        self.expect(&TokenKind::KwTypedef)?;

        // Look ahead to determine typedef variant
        let defs = if self.check(&TokenKind::KwEnum) {
            vec![self.parse_typedef_enum()?]
        } else if self.check(&TokenKind::KwStruct) {
            self.parse_typedef_struct()?
        } else if self.check(&TokenKind::KwUnion) {
            self.parse_typedef_tagged_union()?
        } else {
            vec![self.parse_typedef_synonym()?]
        };

        Ok(ImperativeStatement::Typedef(defs))
    }

    /// Parse a type synonym: `typedef OldType NewType;`
    fn parse_typedef_synonym(&mut self) -> crate::ParseResult<CDefn> {
        let original = self.parse_type_expr()?;
        let (name, params) = self.parse_typedef_con_params()?;
        self.expect(&TokenKind::SymSemi)?;

        Ok(CDefn::Type(CTypeDef {
            name: IdK::Plain(name),
            params,
            body: original,
            span: Span::DUMMY,
        }))
    }

    /// Parse an enum typedef: `typedef enum { ... } EnumName;`
    fn parse_typedef_enum(&mut self) -> crate::ParseResult<CDefn> {
        self.expect(&TokenKind::KwEnum)?;

        self.expect(&TokenKind::SymLBrace)?;
        let enum_tags = self.parse_enum_tags()?;
        self.expect(&TokenKind::SymRBrace)?;

        let name = self.parse_constructor()?;
        let derivs = self.parse_derivations()?;
        self.expect(&TokenKind::SymSemi)?;

        // Create summands for each enum tag
        // Each tag becomes a constructor with no arguments (Unit type)
        let mut original_summands = Vec::new();
        let mut internal_summands = Vec::new();

        for (tag_name, tag_encoding) in enum_tags {
            // Original summand: no arguments, just the tag name
            original_summands.push(COriginalSummand {
                names: vec![tag_name.clone()],
                arg_types: Vec::new(),
                field_names: None,
                tag_encoding,
            });

            // Internal summand: single Unit type argument, actual encoding
            internal_summands.push(CInternalSummand {
                names: vec![tag_name],
                arg_type: CType::Con(Id::qualified("Prelude", "PrimUnit", Position::unknown()).into()),
                tag_encoding: tag_encoding.unwrap_or(0), // Use 0 if no encoding specified
            });
        }

        Ok(CDefn::Data(CDataDef {
            visible: true,
            name: IdK::Plain(name),
            params: Vec::new(),
            original_summands,
            internal_summands,
            deriving: derivs,
            span: Span::DUMMY,
        }))
    }

    /// Parse a struct typedef: `typedef struct { ... } StructName;`
    fn parse_typedef_struct(&mut self) -> crate::ParseResult<Vec<CDefn>> {
        self.expect(&TokenKind::KwStruct)?;

        self.expect(&TokenKind::SymLBrace)?;
        let fields = self.parse_struct_fields()?;
        self.expect(&TokenKind::SymRBrace)?;

        let name = self.parse_constructor()?;

        // Parse optional type parameters after the struct name
        let params = if self.eat(&TokenKind::SymHash) {
            self.expect(&TokenKind::SymLParen)?;
            let type_params = self.parse_comma_separated(Self::parse_type_param)?;
            self.expect(&TokenKind::SymRParen)?;
            type_params.into_iter().map(|(id, _)| id).collect()
        } else {
            Vec::new()
        };

        let derivs = self.parse_derivations()?;
        self.expect(&TokenKind::SymSemi)?;

        // Convert (Id, CType) pairs to CField structs
        let cfields: Vec<CField> = fields
            .into_iter()
            .map(|(field_name, field_type)| CField {
                name: field_name,
                pragmas: None,
                orig_type: None,
                ty: CQType {
                    context: Vec::new(),
                    ty: field_type,
                    span: Span::DUMMY,
                },
                default: Vec::new(),
                span: Span::DUMMY,
            })
            .collect();

        // Create CDefn::Struct with StructSubType::Struct
        let struct_def = CDefn::Struct(CStructDef {
            visible: true,
            sub_type: StructSubType::Struct,
            name: IdK::Plain(name),
            params,
            fields: cfields,
            deriving: derivs,
            span: Span::DUMMY,
        });

        Ok(vec![struct_def])
    }

    /// Parse struct fields: `Type field1; Type field2; ...`
    fn parse_struct_fields(&mut self) -> crate::ParseResult<Vec<(Id, CType)>> {
        let mut fields = Vec::new();

        while !self.check(&TokenKind::SymRBrace) && !self.is_eof() {
            let field_type = self.parse_type_expr()?;
            let field_name = self.parse_def_identifier()?;
            self.expect(&TokenKind::SymSemi)?;
            fields.push((field_name, field_type));
        }

        Ok(fields)
    }

    /// Parse a tagged union typedef: `typedef union tagged { ... } UnionName;`
    fn parse_typedef_tagged_union(&mut self) -> crate::ParseResult<Vec<CDefn>> {
        self.expect(&TokenKind::KwUnion)?;
        self.expect(&TokenKind::KwTagged)?;

        self.expect(&TokenKind::SymLBrace)?;
        let variants = self.parse_union_variants()?;
        self.expect(&TokenKind::SymRBrace)?;

        let name = self.parse_constructor()?;

        // Parse optional type parameters after the union name
        let params = if self.eat(&TokenKind::SymHash) {
            self.expect(&TokenKind::SymLParen)?;
            let type_params = self.parse_comma_separated(Self::parse_type_param)?;
            self.expect(&TokenKind::SymRParen)?;
            type_params.into_iter().map(|(id, _)| id).collect()
        } else {
            Vec::new()
        };

        let derivs = self.parse_derivations()?;
        self.expect(&TokenKind::SymSemi)?;

        // Create summands for each union variant
        // Each variant becomes both an original and internal summand
        let mut original_summands = Vec::new();
        let mut internal_summands = Vec::new();

        for (tag_index, (tag_name, opt_type)) in variants.iter().enumerate() {
            // Original summand: reflects the source syntax
            let original_summand = COriginalSummand {
                names: vec![tag_name.clone()],
                arg_types: if let Some(arg_type) = opt_type {
                    vec![CQType {
                        context: Vec::new(),
                        ty: arg_type.clone(),
                        span: Span::DUMMY,
                    }]
                } else {
                    Vec::new()  // No arguments for void variants
                },
                field_names: None,  // Tagged unions don't use field names
                tag_encoding: None,  // Encoding is handled in internal summand
            };

            // Internal summand: single argument type for compilation
            let internal_summand = CInternalSummand {
                names: vec![tag_name.clone()],
                arg_type: if let Some(arg_type) = opt_type {
                    arg_type.clone()
                } else {
                    // Use PrimUnit for void variants (like Haskell's idPrimUnit)
                    CType::Con(Id::qualified("Prelude", "PrimUnit", Position::unknown()).into())
                },
                tag_encoding: tag_index as i64,  // Sequential encoding starting from 0
            };

            original_summands.push(original_summand);
            internal_summands.push(internal_summand);
        }

        let data_def = CDefn::Data(CDataDef {
            visible: true,
            name: IdK::Plain(name),
            params,
            original_summands,
            internal_summands,
            deriving: derivs,
            span: Span::DUMMY,
        });

        Ok(vec![data_def])
    }

    /// Parse union variants: `void Tag1; Type Tag2; ...`
    fn parse_union_variants(&mut self) -> crate::ParseResult<Vec<(Id, Option<CType>)>> {
        let mut variants = Vec::new();

        while !self.check(&TokenKind::SymRBrace) && !self.is_eof() {
            // Check for 'void' keyword first
            let variant_type = if self.check(&TokenKind::KwVoid) {
                self.advance(); // consume 'void'
                None
            } else {
                // Parse the type first, then the tag name
                Some(self.parse_type_expr()?)
            };

            let tag_name = self.parse_constructor()?;
            self.expect(&TokenKind::SymSemi)?;
            variants.push((tag_name, variant_type));
        }

        Ok(variants)
    }

    // ========================================================================
    // Rule Parsing
    // ========================================================================

    /// Parse a rule definition.
    ///
    /// Grammar:
    /// ```text
    /// rule ruleName [(condition)];
    ///     <rule body>
    /// endrule
    /// ```
    ///
    /// This mirrors `pImperativeRule` from CVParser.lhs.
    pub fn parse_rule(&mut self) -> crate::ParseResult<ImperativeStatement> {
        let start_pos = self.current_span().start;
        self.expect(&TokenKind::KwRule)?;

        let name = self.parse_def_identifier()?;

        // Parse optional rule condition/guard
        let guard = if self.eat(&TokenKind::SymLParen) {
            let condition = self.parse_expression()?;
            self.expect(&TokenKind::SymRParen)?;
            Some(condition)
        } else {
            None
        };

        self.expect(&TokenKind::SymSemi)?;

        // Parse rule body
        let body_pos_start = self.current_span().start;
        let body = self.parse_rule_body()?;

        self.expect(&TokenKind::KwEndrule)?;

        let pos = Position::new("<unknown>", start_pos as i32, start_pos as i32);
        let body_pos = Position::new("<unknown>", body_pos_start as i32, body_pos_start as i32);

        Ok(ImperativeStatement::Rule {
            pos,
            name,
            guard,
            body_pos,
            body,
        })
    }

    /// Parse rule body statements until `endrule`.
    fn parse_rule_body(&mut self) -> crate::ParseResult<Vec<ImperativeStatement>> {
        let mut statements = Vec::new();

        while !self.check(&TokenKind::KwEndrule) && !self.is_eof() {
            let stmt = self.parse_rule_statement()?;
            statements.push(stmt);
        }

        Ok(statements)
    }

    /// Parse a statement valid in rule context.
    fn parse_rule_statement(&mut self) -> crate::ParseResult<ImperativeStatement> {
        // For now, return an error for unsupported statements
        Err(ParseError::InvalidSyntax {
            message: format!("Rule statement parsing not yet implemented: {}", self.current_kind().name()),
            span: self.current_span().into(),
        })
    }

    // ========================================================================
    // Typeclass/Instance Parsing
    // ========================================================================

    /// Parse a typeclass declaration.
    ///
    /// Grammar:
    /// ```text
    /// typeclass ClassName#(type a) [provisos];
    ///     <typeclass body>
    /// endtypeclass
    /// ```
    pub fn parse_typeclass_decl(&mut self) -> crate::ParseResult<ImperativeStatement> {
        self.expect(&TokenKind::KwTypeclass)?;

        let name = self.parse_constructor()?;

        // Parse type parameters: #(type a, type b, ...)
        let type_vars = if self.eat(&TokenKind::SymHash) {
            self.expect(&TokenKind::SymLParen)?;
            let params = self.parse_comma_separated(Self::parse_type_param)?;
            self.expect(&TokenKind::SymRParen)?;
            params.into_iter().map(|(id, _)| id).collect()
        } else {
            Vec::new()
        };

        // Parse optional provisos
        let provisos = if self.check(&TokenKind::KwProvisos) {
            self.advance();
            self.expect(&TokenKind::SymLParen)?;
            let provs = self.parse_comma_separated(Self::parse_proviso)?;
            self.expect(&TokenKind::SymRParen)?;
            provs
        } else {
            Vec::new()
        };

        // Parse optional functional dependencies
        let fundeps = if self.check(&TokenKind::Id("dependencies".into())) {
            self.parse_functional_dependencies()?
        } else {
            Vec::new()
        };

        self.expect(&TokenKind::SymSemi)?;

        // Parse typeclass body (method signatures and default implementations)
        let mut members = Vec::new();
        while !self.check(&TokenKind::KwEndtypeclass) && !self.is_eof() {
            if self.check(&TokenKind::KwFunction) {
                let method = self.parse_typeclass_method()?;
                members.push(method);
            } else {
                return Err(ParseError::InvalidSyntax {
                    message: format!("Expected method in typeclass, found: {}", self.current_kind().name()),
                    span: self.current_span().into(),
                });
            }
        }

        self.expect(&TokenKind::KwEndtypeclass)?;

        Ok(ImperativeStatement::TypeclassDefn {
            name,
            type_vars,
            provisos,
            fundeps,
            members,
        })
    }

    /// Parse a typeclass method signature
    fn parse_typeclass_method(&mut self) -> crate::ParseResult<CField> {
        self.expect(&TokenKind::KwFunction)?;
        let ret_type = self.parse_type_expr()?;
        let name = self.parse_def_identifier()?;

        self.expect(&TokenKind::SymLParen)?;
        let args = if self.check(&TokenKind::SymRParen) {
            Vec::new()
        } else {
            self.parse_comma_separated(Self::parse_function_arg)?
        };
        self.expect(&TokenKind::SymRParen)?;
        self.expect(&TokenKind::SymSemi)?;

        // Build method type
        let arg_types: Vec<CType> = args.iter()
            .filter_map(|(_, ty_opt)| ty_opt.clone())
            .collect();

        let method_type = if arg_types.is_empty() {
            ret_type
        } else {
            arg_types.into_iter().rev().fold(ret_type, |acc, arg_type| {
                crate::make_fn_type(arg_type, acc)
            })
        };

        Ok(CField {
            name,
            pragmas: None,
            orig_type: None,
            ty: CQType {
                context: Vec::new(),
                ty: method_type,
                span: Span::DUMMY,
            },
            default: Vec::new(),
            span: Span::DUMMY,
        })
    }

    /// Parse an instance declaration.
    ///
    /// Grammar:
    /// ```text
    /// instance ClassName#(ConcreteType) [provisos];
    ///     <instance body>
    /// endinstance
    /// ```
    pub fn parse_instance_decl(&mut self) -> crate::ParseResult<ImperativeStatement> {
        self.expect(&TokenKind::KwInstance)?;

        // Parse class name and type arguments: ClassName#(Type1, Type2, ...)
        let class_name = self.parse_constructor()?;

        let type_args = if self.eat(&TokenKind::SymHash) {
            self.expect(&TokenKind::SymLParen)?;
            let types = self.parse_comma_separated(Self::parse_type_expr)?;
            self.expect(&TokenKind::SymRParen)?;
            types
        } else {
            return Err(ParseError::InvalidSyntax {
                message: "Instance declaration requires type arguments".to_string(),
                span: self.current_span().into(),
            });
        };

        // Parse optional provisos
        let provisos = if self.check(&TokenKind::KwProvisos) {
            self.advance();
            self.expect(&TokenKind::SymLParen)?;
            let provs = self.parse_comma_separated(Self::parse_proviso)?;
            self.expect(&TokenKind::SymRParen)?;
            provs
        } else {
            Vec::new()
        };

        self.expect(&TokenKind::SymSemi)?;

        // Parse instance body (method implementations)
        let mut body = Vec::new();
        while !self.check(&TokenKind::KwEndinstance) && !self.is_eof() {
            // For now, just skip the body - proper implementation would parse method definitions
            return Err(ParseError::InvalidSyntax {
                message: "Instance body parsing not yet implemented".to_string(),
                span: self.current_span().into(),
            });
        }

        self.expect(&TokenKind::KwEndinstance)?;

        Ok(ImperativeStatement::InstanceDefn {
            class_name,
            type_args,
            provisos,
            body,
        })
    }

    // ========================================================================
    // Helper Functions
    // ========================================================================

    /// Parse a type parameter: `type paramName`
    fn parse_type_param(&mut self) -> crate::ParseResult<(Id, PartialKind)> {
        // Optional 'parameter' keyword
        self.eat(&TokenKind::KwParameter);

        // Optional kind annotation
        let pkind = if self.eat(&TokenKind::Id("numeric".into())) {
            PartialKind::PKNum
        } else if self.check(&TokenKind::Id("string".into())) {
            self.advance();
            PartialKind::PKStr
        } else {
            PartialKind::PKNoInfo
        };

        self.expect(&TokenKind::KwType)?;
        let name = self.parse_def_identifier()?;

        Ok((name, pkind))
    }

    /// Parse typedef constructor name and parameters: `TypeName[#(params)]`
    fn parse_typedef_con_params(&mut self) -> crate::ParseResult<(Id, Vec<Id>)> {
        let name = self.parse_constructor()?;

        let params = if self.eat(&TokenKind::SymHash) {
            self.expect(&TokenKind::SymLParen)?;
            let type_params = self.parse_comma_separated(Self::parse_type_param)?;
            self.expect(&TokenKind::SymRParen)?;
            type_params.into_iter().map(|(id, _)| id).collect()
        } else {
            Vec::new()
        };

        Ok((name, params))
    }

    /// Parse enum tags with optional encoding: `Tag1, Tag2 = 5, Tag3[0:2], ...`
    /// Returns a list of (tag_name, optional_encoding) pairs
    fn parse_enum_tags(&mut self) -> crate::ParseResult<Vec<(Id, Option<i64>)>> {
        let mut tags = Vec::new();
        let mut current_encoding = 0i64;

        if self.check(&TokenKind::SymRBrace) {
            return Err(ParseError::InvalidSyntax {
                message: "Empty enum not allowed".to_string(),
                span: self.current_span().into(),
            });
        }

        loop {
            let tag_name = self.parse_constructor()?;

            // Check for range notation: Tag[0:2]
            let tag_range = if self.eat(&TokenKind::SymLBracket) {
                let from = self.parse_number()? as i64;
                if self.eat(&TokenKind::SymColon) {
                    let to = self.parse_number()? as i64;
                    self.expect(&TokenKind::SymRBracket)?;
                    Some((from, to))
                } else {
                    // Single range like Tag[5] means Tag[0:4]
                    self.expect(&TokenKind::SymRBracket)?;
                    Some((0, from - 1))
                }
            } else {
                None
            };

            // Check for explicit encoding: Tag = 5
            let explicit_encoding = if self.eat(&TokenKind::SymEq) {
                let enc = self.parse_number()? as i64;
                current_encoding = enc;
                Some(enc)
            } else {
                None
            };

            // Generate tags based on range or single tag
            match tag_range {
                Some((from, to)) => {
                    let start_encoding = explicit_encoding.unwrap_or(current_encoding);
                    if from <= to {
                        for i in from..=to {
                            let range_tag_name = if i == 0 && from == 0 {
                                tag_name.clone()
                            } else {
                                Id::new(
                                    format!("{}{}", tag_name.name(), i),
                                    tag_name.position().clone()
                                )
                            };
                            let encoding = if explicit_encoding.is_some() {
                                Some(start_encoding + (i - from))
                            } else {
                                None
                            };
                            tags.push((range_tag_name, encoding));
                            current_encoding += 1;
                        }
                    } else {
                        // Reverse order
                        for i in (to..=from).rev() {
                            let range_tag_name = if i == 0 && from != 0 {
                                tag_name.clone()
                            } else {
                                Id::new(
                                    format!("{}{}", tag_name.name(), i),
                                    tag_name.position().clone()
                                )
                            };
                            let encoding = if explicit_encoding.is_some() {
                                Some(start_encoding + (from - i))
                            } else {
                                None
                            };
                            tags.push((range_tag_name, encoding));
                            current_encoding += 1;
                        }
                    }
                }
                None => {
                    // Single tag
                    tags.push((tag_name, explicit_encoding));
                    current_encoding += 1;
                }
            }

            if !self.eat(&TokenKind::SymComma) {
                break;
            }

            if self.check(&TokenKind::SymRBrace) {
                break;
            }
        }

        Ok(tags)
    }

    /// Parse derivations: `deriving (Class, Class, ...)`
    fn parse_derivations(&mut self) -> crate::ParseResult<Vec<CTypeclass>> {
        if self.eat(&TokenKind::KwDeriving) {
            self.expect(&TokenKind::SymLParen)?;
            let classes = self.parse_comma_separated(Self::parse_typeclass)?;
            self.expect(&TokenKind::SymRParen)?;
            Ok(classes)
        } else {
            Ok(Vec::new())
        }
    }

    /// Parse a typeclass name for deriving
    fn parse_typeclass(&mut self) -> crate::ParseResult<CTypeclass> {
        let class_name = self.parse_constructor()?;
        Ok(CTypeclass { name: class_name })
    }

    /// Parse a proviso/constraint: `ClassName#(Type1, Type2, ...)`
    fn parse_proviso(&mut self) -> crate::ParseResult<CPred> {
        let class_name = self.parse_constructor()?;

        // Parse type parameters: #(Type1, Type2, ...)
        let types = if self.eat(&TokenKind::SymHash) {
            self.expect(&TokenKind::SymLParen)?;
            let params = self.parse_comma_separated(Self::parse_type_expr)?;
            self.expect(&TokenKind::SymRParen)?;
            if params.is_empty() {
                return Err(ParseError::InvalidSyntax {
                    message: format!("Proviso {} requires type arguments", class_name.name()),
                    span: self.current_span().into(),
                });
            }
            params
        } else {
            return Err(ParseError::InvalidSyntax {
                message: format!("Proviso {} requires type arguments", class_name.name()),
                span: self.current_span().into(),
            });
        };

        Ok(CPred {
            class: class_name,
            args: types,
            span: Span::DUMMY,
        })
    }

    /// Parse a constructor identifier (uppercase)
    fn parse_constructor(&mut self) -> crate::ParseResult<Id> {
        match self.current_kind() {
            TokenKind::Id(name) => {
                if name.chars().next().map_or(false, |c| c.is_uppercase()) {
                    let id = Id::unpositioned(name.as_str());
                    self.advance();
                    Ok(id)
                } else {
                    Err(ParseError::InvalidSyntax {
                        message: format!("Expected constructor (uppercase identifier), found: {name}"),
                        span: self.current_span().into(),
                    })
                }
            }
            _ => Err(ParseError::UnexpectedToken {
                expected: "constructor".to_string(),
                found: self.current_kind().name().to_string(),
                span: self.current_span().into(),
            }),
        }
    }

    /// Parse a definition identifier (lowercase or mixed case)
    fn parse_def_identifier(&mut self) -> crate::ParseResult<Id> {
        match self.current_kind() {
            TokenKind::Id(name) => {
                let id = Id::unpositioned(name.as_str());
                self.advance();
                Ok(id)
            }
            _ => Err(ParseError::UnexpectedToken {
                expected: "identifier".to_string(),
                found: self.current_kind().name().to_string(),
                span: self.current_span().into(),
            }),
        }
    }

    /// Parse comma-separated list of items
    fn parse_comma_separated<T>(&mut self, mut parser: impl FnMut(&mut Self) -> crate::ParseResult<T>) -> crate::ParseResult<Vec<T>> {
        let mut items = Vec::new();

        loop {
            items.push(parser(self)?);

            if !self.eat(&TokenKind::SymComma) {
                break;
            }
        }

        Ok(items)
    }

    /// Parse a decimal number
    fn parse_number(&mut self) -> crate::ParseResult<u64> {
        match self.current_kind() {
            TokenKind::Integer { value, .. } => {
                // Convert BigInt to u64 by trying to parse the string representation
                let value_str = value.to_string();
                if let Ok(n) = value_str.parse::<u64>() {
                    self.advance();
                    Ok(n)
                } else {
                    Err(ParseError::InvalidSyntax {
                        message: format!("Integer literal too large: {}", value),
                        span: self.current_span().into(),
                    })
                }
            }
            _ => Err(ParseError::UnexpectedToken {
                expected: "number".to_string(),
                found: self.current_kind().name().to_string(),
                span: self.current_span().into(),
            }),
        }
    }

    /// Save parser checkpoint for backtracking
    fn save_checkpoint(&self) -> Result<usize, ParseError> {
        Ok(self.pos)
    }

    /// Parse functional dependencies for typeclasses
    ///
    /// Grammar: dependencies ( id_or_tuple determines id_or_tuple, ... )
    /// Where id_or_tuple is either a single identifier or (id1, id2, ...)
    fn parse_functional_dependencies(&mut self) -> crate::ParseResult<Vec<(Vec<Id>, Vec<Id>)>> {
        self.expect(&TokenKind::Id("dependencies".into()))?;
        self.expect(&TokenKind::SymLParen)?;

        let fundeps = self.parse_comma_separated(|parser| parser.parse_functional_dependency())?;

        self.expect(&TokenKind::SymRParen)?;
        Ok(fundeps)
    }

    /// Parse a single functional dependency: id_or_tuple determines id_or_tuple
    fn parse_functional_dependency(&mut self) -> crate::ParseResult<(Vec<Id>, Vec<Id>)> {
        // Parse determining type vars (single or tuple)
        let from_vars = if self.check(&TokenKind::SymLParen) {
            self.advance(); // consume (
            let vars = self.parse_comma_separated(Self::parse_def_identifier)?;
            self.expect(&TokenKind::SymRParen)?;
            vars
        } else {
            vec![self.parse_def_identifier()?]
        };

        // Expect 'determines' keyword
        self.expect(&TokenKind::Id("determines".into()))?;

        // Parse determined type vars (single or tuple)
        let to_vars = if self.check(&TokenKind::SymLParen) {
            self.advance(); // consume (
            let vars = self.parse_comma_separated(Self::parse_def_identifier)?;
            self.expect(&TokenKind::SymRParen)?;
            vars
        } else {
            vec![self.parse_def_identifier()?]
        };

        Ok((from_vars, to_vars))
    }

    /// Restore parser to checkpoint
    fn restore_checkpoint(&mut self, checkpoint: usize) -> Result<(), ParseError> {
        self.pos = checkpoint;
        Ok(())
    }
}

// ========================================================================
// Placeholder Types and Constants
// ========================================================================

/// Placeholder for PartialKind from the Haskell code
#[allow(dead_code)]
#[derive(Debug, Clone)]
pub enum PartialKind {
    PKNoInfo,
    PKNum,
    PKStr,
}