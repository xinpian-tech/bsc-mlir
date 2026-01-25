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
        let provisos = if self.check(&TokenKind::Id("provisos".into())) {
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

        let pos = Position::unknown();

        Ok(ImperativeStatement::ModuleDefn {
            pos,
            name,
            params,
            ret_type: None, // BSV modules don't have explicit return types
            ifc_type: Some(ifc_type),
            provisos,
            body,
            attrs: Vec::new(), // TODO: Parse attributes
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
        let provisos = if self.check(&TokenKind::Id("provisos".into())) {
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

        let pos = Position::unknown();

        Ok(ImperativeStatement::FunctionDefn {
            pos,
            name,
            ret_type,
            params,
            provisos,
            body,
            attrs: Vec::new(), // TODO: Parse attributes
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
            if self.check(&TokenKind::Id("method".into())) {
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

        let pos = Position::unknown();

        Ok(ImperativeStatement::InterfaceDecl {
            pos,
            name,
            type_vars,
            members,
        })
    }

    /// Parse a method prototype: `method RetType methodName(args);`
    fn parse_method_prototype(&mut self) -> crate::ParseResult<CField> {
        self.expect(&TokenKind::Id("method".into()))?;

        let ret_type = self.parse_type_expr()?;
        let name = self.parse_def_identifier()?;

        self.expect(&TokenKind::SymLParen)?;
        let _args = if self.check(&TokenKind::SymRParen) {
            Vec::new()
        } else {
            self.parse_comma_separated(Self::parse_function_arg)?
        };
        self.expect(&TokenKind::SymRParen)?;
        self.expect(&TokenKind::SymSemi)?;

        // Convert to CField representation
        // TODO: Properly construct method type with arguments
        Ok(CField {
            name,
            pragmas: None,
            orig_type: None,
            ty: CQType {
                context: Vec::new(),
                ty: ret_type,
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
        let defs = if self.check(&TokenKind::Id("enum".into())) {
            vec![self.parse_typedef_enum()?]
        } else if self.check(&TokenKind::Id("struct".into())) {
            self.parse_typedef_struct()?
        } else if self.check(&TokenKind::Id("union".into())) {
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
        self.expect(&TokenKind::Id("enum".into()))?;

        self.expect(&TokenKind::SymLBrace)?;
        let _enum_tags = self.parse_enum_tags()?;
        self.expect(&TokenKind::SymRBrace)?;

        let name = self.parse_constructor()?;
        let _derivs = self.parse_derivations()?;
        self.expect(&TokenKind::SymSemi)?;

        // TODO: Implement complete enum construction
        // For now, return a placeholder
        Ok(CDefn::Type(CTypeDef {
            name: IdK::Plain(name.clone()),
            params: Vec::new(),
            body: CType::Con(name), // Placeholder
            span: Span::DUMMY,
        }))
    }

    /// Parse a struct typedef: `typedef struct { ... } StructName;`
    fn parse_typedef_struct(&mut self) -> crate::ParseResult<Vec<CDefn>> {
        // TODO: Implement struct parsing
        // This is complex and requires parsing struct fields
        Err(ParseError::InvalidSyntax {
            message: "Struct typedef parsing not yet implemented".to_string(),
            span: self.current_span().into(),
        })
    }

    /// Parse a tagged union typedef: `typedef union tagged { ... } UnionName;`
    fn parse_typedef_tagged_union(&mut self) -> crate::ParseResult<Vec<CDefn>> {
        // TODO: Implement tagged union parsing
        // This is complex and requires parsing union variants
        Err(ParseError::InvalidSyntax {
            message: "Tagged union typedef parsing not yet implemented".to_string(),
            span: self.current_span().into(),
        })
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

        let pos = Position::unknown();
        let body_pos = Position::unknown();

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
        // TODO: Implement typeclass parsing
        Err(ParseError::InvalidSyntax {
            message: "Typeclass declaration parsing not yet implemented".to_string(),
            span: self.current_span().into(),
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
        // TODO: Implement instance parsing
        Err(ParseError::InvalidSyntax {
            message: "Instance declaration parsing not yet implemented".to_string(),
            span: self.current_span().into(),
        })
    }

    // ========================================================================
    // Helper Functions
    // ========================================================================

    /// Parse a type parameter: `type paramName`
    fn parse_type_param(&mut self) -> crate::ParseResult<(Id, PartialKind)> {
        // Optional 'parameter' keyword
        self.eat(&TokenKind::Id("parameter".into()));

        // Optional kind annotation
        let _pkind = if self.eat(&TokenKind::Id("numeric".into())) {
            "numeric" // PKNum
        } else if self.check(&TokenKind::Id("string".into())) {
            self.advance();
            "string" // PKStr
        } else {
            "none" // PKNoInfo
        };

        self.expect(&TokenKind::Id("type".into()))?;
        let name = self.parse_def_identifier()?;

        // TODO: Convert string to PartialKind enum
        Ok((name, PartialKind::PKNoInfo))
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

    /// Parse enum tags (placeholder)
    fn parse_enum_tags(&mut self) -> crate::ParseResult<Vec<Id>> {
        // TODO: Implement enum tag parsing
        let mut tags = Vec::new();

        while !self.check(&TokenKind::SymRBrace) {
            let tag = self.parse_constructor()?;
            tags.push(tag);

            if !self.eat(&TokenKind::SymComma) {
                break;
            }
        }

        Ok(tags)
    }

    /// Parse derivations (placeholder)
    fn parse_derivations(&mut self) -> crate::ParseResult<Vec<Id>> {
        // TODO: Implement derivation parsing
        // This would parse things like `deriving (Eq, Bits, ...)`
        Ok(Vec::new())
    }

    /// Parse a proviso/constraint (placeholder)
    fn parse_proviso(&mut self) -> crate::ParseResult<CPred> {
        // TODO: Implement proviso parsing
        // For now, parse as a basic predicate
        let class_name = self.parse_def_identifier()?;
        let mut types = Vec::new();

        if self.eat(&TokenKind::SymHash) {
            self.expect(&TokenKind::SymLParen)?;
            types = self.parse_comma_separated(Self::parse_type_expr)?;
            self.expect(&TokenKind::SymRParen)?;
        }

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

    /// Save parser checkpoint for backtracking
    fn save_checkpoint(&self) -> Result<usize, ParseError> {
        Ok(self.pos)
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