//! CSyntax to ISyntax conversion.
//!
//! Mirrors `src/comp/IConv.hs` from the Haskell implementation.
//!
//! This module converts the concrete syntax AST (CSyntax, output of parsing
//! and type checking) to the internal syntax AST (ISyntax, ready for backends).
//! The conversion:
//! - Resolves names to their definitions
//! - Converts types from CType to IType
//! - Converts expressions and patterns
//! - Handles let bindings and pattern matching
//!
//! # Example
//!
//! ```ignore
//! use bsc_iconv::{convert, Converter};
//! use bsc_symtab::SymTab;
//! use bsc_syntax::CPackage;
//!
//! let symtab = SymTab::new();
//! let pkg: CPackage = /* parsed package */;
//!
//! // Using the convenience function
//! let ipackage = convert(&pkg, &symtab)?;
//!
//! // Or using the converter directly
//! let converter = Converter::new(&symtab);
//! let ipackage = converter.convert_package(&pkg)?;
//! ```

use bsc_diagnostics::Span;
use bsc_symtab::{ConTagInfo, SymTab, TISort, VarKind};
use bsc_types::Kind;
use bsc_syntax::{
    CCaseArm, CClause, CDefl, CDefn, CExpr, CImport, CKind, CPackage, CPat, CQType, CQual, CType,
    ConTagInfo as SynConTagInfo, IArg, IConInfo, IDef, IExpr, IKind, IPackage, IPragma, IProperty,
    ITyCon, ITyConInfo, ITySort, ITyVar, IType, Id, IntLiteral, Literal,
};
use rustc_hash::FxHashMap;
use thiserror::Error;

/// Error during CSyntax to ISyntax conversion.
#[derive(Debug, Error)]
pub enum ConvError {
    /// Unknown variable reference.
    #[error("unknown variable '{name}' at {span:?}")]
    UnknownVariable { name: String, span: Span },

    /// Unknown type reference.
    #[error("unknown type '{name}' at {span:?}")]
    UnknownType { name: String, span: Span },

    /// Unknown constructor reference.
    #[error("unknown constructor '{name}' at {span:?}")]
    UnknownConstructor { name: String, span: Span },

    /// Unknown field reference.
    #[error("unknown field '{name}' at {span:?}")]
    UnknownField { name: String, span: Span },

    /// Type mismatch during conversion.
    #[error("type mismatch: expected {expected}, found {found} at {span:?}")]
    TypeMismatch {
        expected: String,
        found: String,
        span: Span,
    },

    /// Invalid pattern in context.
    #[error("invalid pattern at {span:?}: {message}")]
    InvalidPattern { message: String, span: Span },

    /// Internal conversion error.
    #[error("internal error during conversion: {message}")]
    Internal { message: String },
}

impl ConvError {
    /// Get the span associated with this error, if any.
    #[must_use]
    pub fn span(&self) -> Option<Span> {
        match self {
            ConvError::UnknownVariable { span, .. }
            | ConvError::UnknownType { span, .. }
            | ConvError::UnknownConstructor { span, .. }
            | ConvError::UnknownField { span, .. }
            | ConvError::TypeMismatch { span, .. }
            | ConvError::InvalidPattern { span, .. } => Some(*span),
            ConvError::Internal { .. } => None,
        }
    }
}

/// Result type for conversion operations.
pub type ConvResult<T> = Result<T, ConvError>;

/// Environment mapping variable names to their expressions.
type Env = FxHashMap<Id, IExpr>;

/// Converter from CSyntax to ISyntax.
///
/// Holds the symbol table and environment needed for conversion.
/// The converter is the main entry point for converting CSyntax to ISyntax.
#[derive(Debug)]
pub struct Converter<'a> {
    /// The symbol table for name resolution.
    symtab: &'a SymTab,
}

impl<'a> Converter<'a> {
    /// Create a new converter with the given symbol table.
    #[must_use]
    pub fn new(symtab: &'a SymTab) -> Self {
        Self { symtab }
    }

    /// Convert a package from CSyntax to ISyntax.
    ///
    /// This is the main entry point for package conversion.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - Any definition fails to convert
    /// - Any type or variable reference cannot be resolved
    pub fn convert_package(&self, pkg: &CPackage) -> ConvResult<IPackage> {
        // Build initial environment from definitions
        let mut env = Env::default();
        let mut defs = Vec::new();

        // First pass: collect all definitions
        for defn in &pkg.definitions {
            if let Some(def) = self.convert_defn(defn, &env)? {
                // Add to environment for later definitions
                let var_expr = IExpr::Var(def.name.clone());
                env.insert(def.name.clone(), var_expr);
                defs.push(def);
            }
        }

        // Extract pragmas
        let pragmas = self.extract_pragmas(pkg);

        // Extract dependencies from imports
        let depends: Vec<(Id, String)> = pkg
            .imports
            .iter()
            .filter_map(|imp| match imp {
                CImport::Simple { module, .. } => Some((module.clone(), String::new())),
                CImport::Signature { name, .. } => {
                    Some((Id::unpositioned(name), name.clone()))
                }
            })
            .collect();

        Ok(IPackage {
            name: pkg.name.clone(),
            depends,
            pragmas,
            defs,
        })
    }

    /// Convert a single definition.
    ///
    /// Returns `None` for definitions that don't produce an IDef (e.g., type synonyms).
    ///
    /// # Errors
    ///
    /// Returns an error if the definition cannot be converted.
    pub fn convert_def(&self, def: &CDefn) -> ConvResult<IDef> {
        let env = Env::default();
        self.convert_defn(def, &env)?
            .ok_or_else(|| ConvError::Internal {
                message: "definition did not produce an IDef".to_string(),
            })
    }

    /// Convert an expression with a known type.
    ///
    /// # Errors
    ///
    /// Returns an error if the expression cannot be converted.
    pub fn convert_expr(&self, expr: &CExpr, ty: &IType) -> ConvResult<IExpr> {
        let env = Env::default();
        self.convert_expr_internal(expr, &env)
    }

    // ========================================================================
    // Internal conversion methods
    // ========================================================================

    /// Convert a definition to IDef.
    fn convert_defn(&self, defn: &CDefn, env: &Env) -> ConvResult<Option<IDef>> {
        match defn {
            CDefn::Value(def) => {
                // Value definition: f x = e
                let name = def.name.clone();

                // Get type from signature or infer
                let ty = self.lookup_var_type(&name)?;

                // Convert clauses to expression
                let expr = self.convert_clauses(&def.clauses, &ty, env)?;

                Ok(Some(IDef {
                    name,
                    ty,
                    expr,
                    props: Vec::new(),
                }))
            }
            CDefn::Signature(_) => {
                // Type signatures don't produce definitions on their own
                Ok(None)
            }
            CDefn::Type(_) | CDefn::Data(_) | CDefn::Struct(_) => {
                // Type definitions don't produce value definitions
                Ok(None)
            }
            CDefn::Class(_) | CDefn::Instance(_) => {
                // Class and instance definitions are handled separately
                Ok(None)
            }
            CDefn::Foreign(fdef) => {
                // Foreign import
                let name = fdef.name.clone();
                let ty = self.convert_qtype(&fdef.ty)?;
                let foreign_name = fdef.foreign_name.clone().unwrap_or_else(|| name.full_name());

                // Create a foreign function expression
                let expr = self.make_foreign_expr(&name, &ty, &foreign_name);

                Ok(Some(IDef {
                    name,
                    ty,
                    expr,
                    props: Vec::new(),
                }))
            }
            CDefn::Primitive(pdef) => {
                // Primitive declaration
                let name = pdef.name.clone();
                let ty = self.convert_qtype(&pdef.ty)?;

                // Create a primitive expression
                let expr = self.make_primitive_expr(&name, &ty);

                Ok(Some(IDef {
                    name,
                    ty,
                    expr,
                    props: vec![bsc_syntax::DefProp::Primitive],
                }))
            }
            CDefn::PrimitiveType(_) | CDefn::Pragma(_) => {
                // These don't produce value definitions
                Ok(None)
            }
            CDefn::ValueSign(def) => {
                // Value definition with type signature
                let name = def.name();
                let ty = self.lookup_var_type(&name)?;
                let expr = self.convert_clauses(def.clauses(), &ty, env)?;
                Ok(Some(IDef {
                    name,
                    ty,
                    expr,
                    props: Vec::new(),
                }))
            }
            CDefn::SigInstance { .. }
            | CDefn::SigType { .. }
            | CDefn::SigClass { .. }
            | CDefn::SigValue { .. } => {
                // Signature-related definitions don't produce value definitions
                Ok(None)
            }
        }
    }

    /// Convert clauses to an expression.
    fn convert_clauses(&self, clauses: &[CClause], ty: &IType, env: &Env) -> ConvResult<IExpr> {
        if clauses.is_empty() {
            return Err(ConvError::Internal {
                message: "empty clause list".to_string(),
            });
        }

        // Get argument types and return type
        let (arg_types, return_type) = self.split_function_type(ty);

        // For each clause, convert patterns and body
        let first_clause = &clauses[0];
        let num_args = first_clause.patterns.len();

        // Generate parameter names
        let params: Vec<(Id, IType)> = (0..num_args)
            .map(|i| {
                let param_name = Id::unpositioned(format!("_arg{i}"));
                let param_type = arg_types.get(i).cloned().unwrap_or_else(|| IType::Gen(0));
                (param_name, param_type)
            })
            .collect();

        // Build lambda expression
        let mut body = self.convert_clauses_body(clauses, &params, &return_type, env)?;

        // Wrap in lambdas
        for (name, param_ty) in params.into_iter().rev() {
            body = IExpr::Lam(name, param_ty, Box::new(body));
        }

        Ok(body)
    }

    /// Convert clause bodies with pattern matching.
    fn convert_clauses_body(
        &self,
        clauses: &[CClause],
        params: &[(Id, IType)],
        return_type: &IType,
        env: &Env,
    ) -> ConvResult<IExpr> {
        if clauses.is_empty() {
            // No match - return undefined
            return Ok(self.make_undefined(return_type));
        }

        let clause = &clauses[0];
        let rest = &clauses[1..];

        // Convert patterns to condition and bindings
        let mut new_env = env.clone();
        let (condition, bindings) =
            self.convert_patterns(&clause.patterns, params, &mut new_env)?;

        // Convert qualifiers (guards) and body
        let body = self.convert_clause_body(&clause.qualifiers, &clause.body, &new_env)?;

        // Wrap body with let bindings
        let body_with_bindings = self.wrap_with_bindings(body, bindings);

        // If there are more clauses, create an if-then-else
        if rest.is_empty() && condition.is_none() {
            Ok(body_with_bindings)
        } else {
            let else_branch = self.convert_clauses_body(rest, params, return_type, env)?;

            if let Some(cond) = condition {
                Ok(self.make_if(cond, body_with_bindings, else_branch))
            } else {
                Ok(body_with_bindings)
            }
        }
    }

    /// Convert patterns to condition expression and variable bindings.
    fn convert_patterns(
        &self,
        patterns: &[CPat],
        params: &[(Id, IType)],
        env: &mut Env,
    ) -> ConvResult<(Option<IExpr>, Vec<(Id, IType, IExpr)>)> {
        let mut conditions = Vec::new();
        let mut bindings = Vec::new();

        for (pattern, (param_name, param_type)) in patterns.iter().zip(params.iter()) {
            let param_expr = IExpr::Var(param_name.clone());
            let (cond, binding) = self.convert_pattern(pattern, param_expr, param_type, env)?;

            if let Some(c) = cond {
                conditions.push(c);
            }
            bindings.extend(binding);
        }

        let condition = if conditions.is_empty() {
            None
        } else {
            Some(self.and_all(conditions))
        };

        Ok((condition, bindings))
    }

    /// Convert a single pattern.
    fn convert_pattern(
        &self,
        pattern: &CPat,
        scrutinee: IExpr,
        ty: &IType,
        env: &mut Env,
    ) -> ConvResult<(Option<IExpr>, Vec<(Id, IType, IExpr)>)> {
        match pattern {
            CPat::Var(name) => {
                // Variable pattern - always matches, binds the value
                env.insert(name.clone(), scrutinee.clone());
                Ok((None, vec![(name.clone(), ty.clone(), scrutinee)]))
            }
            CPat::Wildcard(_) => {
                // Wildcard pattern - always matches, no binding
                Ok((None, vec![]))
            }
            CPat::Lit(lit, span) => {
                // Literal pattern - compare with the value
                let lit_expr = self.convert_literal(lit, ty);
                let condition = self.make_eq(scrutinee, lit_expr);
                Ok((Some(condition), vec![]))
            }
            CPat::As(name, inner, _span) => {
                // As pattern - bind the value and also match inner pattern
                env.insert(name.clone(), scrutinee.clone());
                let mut bindings = vec![(name.clone(), ty.clone(), scrutinee.clone())];
                let (cond, inner_bindings) = self.convert_pattern(inner, scrutinee, ty, env)?;
                bindings.extend(inner_bindings);
                Ok((cond, bindings))
            }
            CPat::Typed(inner, _ctype, _span) => {
                // Typed pattern - just match the inner pattern
                self.convert_pattern(inner, scrutinee, ty, env)
            }
            CPat::Paren(inner, _span) => {
                // Parenthesized pattern - just match the inner pattern
                self.convert_pattern(inner, scrutinee, ty, env)
            }
            CPat::Tuple(pats, _span) => {
                // Tuple pattern - match each component
                let mut conditions = Vec::new();
                let mut bindings = Vec::new();

                for (i, pat) in pats.iter().enumerate() {
                    // Extract the i-th element from the tuple
                    let elem_ty = self.get_tuple_element_type(ty, i);
                    let elem_expr = self.make_tuple_select(scrutinee.clone(), i, &elem_ty);

                    let (cond, pat_bindings) = self.convert_pattern(pat, elem_expr, &elem_ty, env)?;
                    if let Some(c) = cond {
                        conditions.push(c);
                    }
                    bindings.extend(pat_bindings);
                }

                let condition = if conditions.is_empty() {
                    None
                } else {
                    Some(self.and_all(conditions))
                };

                Ok((condition, bindings))
            }
            CPat::Con(con_name, sub_pats, _span) => {
                // Constructor pattern
                let (cond, bindings) =
                    self.convert_con_pattern(con_name, sub_pats, scrutinee, ty, env)?;
                Ok((cond, bindings))
            }
            CPat::Struct(_visible, ty_name, fields, _span) => {
                // Struct pattern
                let mut conditions = Vec::new();
                let mut bindings = Vec::new();

                for field in fields {
                    let field_ty = self.lookup_field_type(ty_name, &field.name)?;
                    let field_expr =
                        self.make_field_select(scrutinee.clone(), &field.name, &field_ty);

                    let (cond, field_bindings) =
                        self.convert_pattern(&field.pattern, field_expr, &field_ty, env)?;
                    if let Some(c) = cond {
                        conditions.push(c);
                    }
                    bindings.extend(field_bindings);
                }

                let condition = if conditions.is_empty() {
                    None
                } else {
                    Some(self.and_all(conditions))
                };

                Ok((condition, bindings))
            }
            CPat::List(pats, span) => {
                // List patterns are complex - for now, return an error
                Err(ConvError::InvalidPattern {
                    message: "list patterns not yet supported".to_string(),
                    span: *span,
                })
            }
            CPat::Infix(_, _, _, span) => {
                // Infix patterns should be resolved before this point
                Err(ConvError::InvalidPattern {
                    message: "unresolved infix pattern".to_string(),
                    span: *span,
                })
            }
            CPat::MixedLit { span, .. } => {
                // Mixed literals with don't-care bits - not yet supported
                Err(ConvError::InvalidPattern {
                    message: "mixed literal patterns not yet supported".to_string(),
                    span: *span,
                })
            }
            CPat::Con1 { con_id, arg, span, .. } => {
                // Internal single-argument constructor pattern from deriving
                let (cond, bindings) =
                    self.convert_con_pattern(&con_id, &[(**arg).clone()], scrutinee, ty, env)?;
                Ok((cond, bindings))
            }
            CPat::ConTs { con_id, args, span, .. } => {
                // Internal constructor with type args pattern
                let (cond, bindings) =
                    self.convert_con_pattern(&con_id, args, scrutinee, ty, env)?;
                Ok((cond, bindings))
            }
        }
    }

    /// Convert a constructor pattern.
    fn convert_con_pattern(
        &self,
        con_name: &Id,
        sub_pats: &[CPat],
        scrutinee: IExpr,
        ty: &IType,
        env: &mut Env,
    ) -> ConvResult<(Option<IExpr>, Vec<(Id, IType, IExpr)>)> {
        // Look up constructor info
        let type_id = self.get_type_constructor(ty)?;
        let con_info = self.symtab.find_con_for_type(con_name, &type_id).ok_or_else(|| {
            ConvError::UnknownConstructor {
                name: con_name.full_name(),
                span: Span::DUMMY,
            }
        })?;

        let mut conditions = Vec::new();
        let mut bindings = Vec::new();

        // Add constructor test if needed
        if !con_info.tag_info.is_single() {
            let is_test = self.make_constructor_test(&scrutinee, con_name, &con_info.tag_info);
            conditions.push(is_test);
        }

        // Extract and match sub-patterns
        let con_ty = self.convert_bsc_type(&con_info.assump.scheme.qual_type.ty);
        for (i, sub_pat) in sub_pats.iter().enumerate() {
            let field_ty = self.get_constructor_field_type(&con_ty, i);
            let field_expr =
                self.make_constructor_field_select(scrutinee.clone(), con_name, i, &field_ty);

            let (cond, field_bindings) =
                self.convert_pattern(sub_pat, field_expr, &field_ty, env)?;
            if let Some(c) = cond {
                conditions.push(c);
            }
            bindings.extend(field_bindings);
        }

        let condition = if conditions.is_empty() {
            None
        } else {
            Some(self.and_all(conditions))
        };

        Ok((condition, bindings))
    }

    /// Convert clause qualifiers and body to an expression.
    fn convert_clause_body(
        &self,
        qualifiers: &[CQual],
        body: &CExpr,
        env: &Env,
    ) -> ConvResult<IExpr> {
        // Convert body expression
        let mut result = self.convert_expr_internal(body, env)?;

        // Apply qualifiers (guards) in reverse order to build if-then-else chain
        for qual in qualifiers.iter().rev() {
            match qual {
                CQual::Filter(cond) => {
                    let cond_expr = self.convert_expr_internal(cond, env)?;
                    let undefined = self.make_undefined(&IType::Gen(0));
                    result = self.make_if(cond_expr, result, undefined);
                }
                CQual::Gen(_ty, _pat, _expr) => {
                    // Generators are more complex - for now, just pass through
                    // TODO: Handle list comprehension-style generators
                }
            }
        }

        Ok(result)
    }

    /// Convert an expression.
    fn convert_expr_internal(&self, expr: &CExpr, env: &Env) -> ConvResult<IExpr> {
        match expr {
            CExpr::Var(name) => {
                // Check local environment first
                if let Some(e) = env.get(name) {
                    return Ok(e.clone());
                }

                // Then check symbol table
                let ty = self.lookup_var_type(name)?;
                Ok(IExpr::Var(name.clone()))
            }
            CExpr::Con(name, args, _span) => {
                // Look up constructor
                if let Some(cons) = self.symtab.find_con(name) {
                    if let Some(con) = cons.first() {
                        let con_ty = self.convert_bsc_type(&con.assump.scheme.qual_type.ty);
                        // Convert from bsc_symtab::ConTagInfo to bsc_syntax::ConTagInfo
                        let tag_info = SynConTagInfo {
                            con_no: con.tag_info.con_no,
                            num_con: con.tag_info.num_con,
                            con_tag: con.tag_info.con_tag,
                            tag_size: con.tag_info.tag_size,
                        };
                        let con_expr = IExpr::Con(
                            name.clone(),
                            IConInfo::Con {
                                ty: con_ty.clone(),
                                tag_info,
                            },
                        );
                        // Apply arguments if any
                        if args.is_empty() {
                            return Ok(con_expr);
                        } else {
                            let converted_args: Vec<IArg> = args
                                .iter()
                                .map(|a| self.convert_expr_internal(a, env).map(IArg::Expr))
                                .collect::<ConvResult<Vec<_>>>()?;
                            return Ok(IExpr::App(Box::new(con_expr), converted_args));
                        }
                    }
                }
                Err(ConvError::UnknownConstructor {
                    name: name.full_name(),
                    span: Span::DUMMY,
                })
            }
            CExpr::Lit(lit, _span) => {
                // Convert literal
                Ok(self.convert_literal(lit, &IType::Gen(0)))
            }
            CExpr::Lambda(pats, body, _span) => {
                // Lambda expression
                let mut new_env = env.clone();
                let mut result = self.convert_expr_internal(body, &new_env)?;

                // Build lambda from patterns (in reverse order)
                for pat in pats.iter().rev() {
                    match pat {
                        CPat::Var(name) => {
                            let param_ty = IType::Gen(0); // Type to be inferred
                            new_env.insert(
                                name.clone(),
                                IExpr::Var(name.clone()),
                            );
                            result = IExpr::Lam(name.clone(), param_ty, Box::new(result));
                        }
                        _ => {
                            // Complex patterns need desugaring
                            let param_name = Id::unpositioned("_lambda_arg");
                            let param_ty = IType::Gen(0);
                            // TODO: Add pattern matching
                            result = IExpr::Lam(param_name, param_ty, Box::new(result));
                        }
                    }
                }

                Ok(result)
            }
            CExpr::Apply(func, args, _span) => {
                // Function application
                let func_expr = self.convert_expr_internal(func, env)?;
                let arg_exprs: Result<Vec<_>, _> = args
                    .iter()
                    .map(|a| self.convert_expr_internal(a, env).map(IArg::Expr))
                    .collect();

                Ok(IExpr::App(Box::new(func_expr), arg_exprs?))
            }
            CExpr::If(_pos, cond, then_branch, else_branch) => {
                // If-then-else
                let cond_expr = self.convert_expr_internal(cond, env)?;
                let then_expr = self.convert_expr_internal(then_branch, env)?;
                let else_expr = self.convert_expr_internal(else_branch, env)?;

                Ok(self.make_if(cond_expr, then_expr, else_expr))
            }
            CExpr::Case(_pos, scrutinee, arms) => {
                // Case expression
                self.convert_case(scrutinee, arms, env)
            }
            CExpr::LetSeq(defs, body, _span) | CExpr::LetRec(defs, body, _span) => {
                // Let expression
                let mut new_env = env.clone();

                for def in defs {
                    match def {
                        CDefl::ValueSign(cdef, _quals, _span) => {
                            let name = cdef.name();
                            let def_ty = self
                                .lookup_var_type(&name)
                                .unwrap_or_else(|_| IType::Gen(0));
                            let def_expr = self.convert_clauses(cdef.clauses(), &def_ty, &new_env)?;
                            new_env.insert(name.clone(), def_expr);
                        }
                        CDefl::Value(name, clauses, _quals, _span) => {
                            let def_ty = self
                                .lookup_var_type(name)
                                .unwrap_or_else(|_| IType::Gen(0));
                            let def_expr = self.convert_clauses(clauses, &def_ty, &new_env)?;
                            new_env.insert(name.clone(), def_expr);
                        }
                        CDefl::Match(pat, expr, _span) => {
                            // Pattern match binding - convert expression and bind to pattern
                            // For simplicity, only handle variable patterns
                            if let CPat::Var(name) = pat {
                                let def_expr = self.convert_expr_internal(expr, &new_env)?;
                                new_env.insert(name.clone(), def_expr);
                            }
                            // TODO: Handle more complex patterns
                        }
                    }
                }

                self.convert_expr_internal(body, &new_env)
            }
            CExpr::TypeAscription(inner, _ty, _span) => {
                // Type ascription - just convert the inner expression
                self.convert_expr_internal(inner, env)
            }
            CExpr::Paren(inner, _span) => {
                // Parenthesized expression
                self.convert_expr_internal(inner, env)
            }
            CExpr::Tuple(exprs, _span) => {
                // Tuple literal
                let converted: Result<Vec<_>, _> = exprs
                    .iter()
                    .map(|e| self.convert_expr_internal(e, env).map(IArg::Expr))
                    .collect();

                Ok(IExpr::App(
                    Box::new(self.make_tuple_constructor(exprs.len())),
                    converted?,
                ))
            }
            CExpr::List(exprs, _span) => {
                // List literal - desugar to Cons and Nil
                let mut result = self.make_nil();
                for expr in exprs.iter().rev() {
                    let elem = self.convert_expr_internal(expr, env)?;
                    result = self.make_cons(elem, result);
                }
                Ok(result)
            }
            CExpr::Select(obj, field, _span) => {
                // Field selection
                let obj_expr = self.convert_expr_internal(obj, env)?;
                let field_ty = IType::Gen(0); // Type to be inferred
                Ok(self.make_field_select(obj_expr, field, &field_ty))
            }
            CExpr::Struct(_visible, ty_name, fields, _span) => {
                // Struct literal
                let mut args = Vec::new();
                for field in fields {
                    let field_expr = self.convert_expr_internal(&field.value, env)?;
                    args.push(IArg::Expr(field_expr));
                }

                Ok(IExpr::App(
                    Box::new(self.make_struct_constructor(ty_name)),
                    args,
                ))
            }
            CExpr::Update(obj, fields, _span) => {
                // Struct update - for now, just evaluate the object
                // TODO: Implement proper struct update
                self.convert_expr_internal(obj, env)
            }
            CExpr::Infix(_, _, _, span) => {
                // Infix operators should be resolved before this point
                Err(ConvError::Internal {
                    message: format!("unresolved infix operator at {span:?}"),
                })
            }
            CExpr::SectionL(_, _, span) | CExpr::SectionR(_, _, span) => {
                // Sections should be desugared before this point
                Err(ConvError::Internal {
                    message: format!("unresolved section at {span:?}"),
                })
            }
            // Handle other expression forms
            _ => Err(ConvError::Internal {
                message: format!("unsupported expression form: {expr:?}"),
            }),
        }
    }

    /// Convert a case expression.
    fn convert_case(&self, scrutinee: &CExpr, arms: &[CCaseArm], env: &Env) -> ConvResult<IExpr> {
        let scrut_expr = self.convert_expr_internal(scrutinee, env)?;
        let scrut_ty = IType::Gen(0); // Type to be inferred

        // Generate a fresh name for the scrutinee
        let scrut_name = Id::unpositioned("_case_scrut");
        let mut new_env = env.clone();
        new_env.insert(
            scrut_name.clone(),
            IExpr::Var(scrut_name.clone()),
        );

        // Convert each arm
        // Mirrors Haskell IConv.hs - each arm has pattern, qualifiers, and body
        let mut result = self.make_undefined(&IType::Gen(0));

        for arm in arms.iter().rev() {
            let scrut_var = IExpr::Var(scrut_name.clone());
            let (condition, bindings) =
                self.convert_pattern(&arm.pattern, scrut_var, &scrut_ty, &mut new_env.clone())?;

            // Convert qualifiers and body using the clause_body converter
            let body = self.convert_clause_body(&arm.qualifiers, &arm.body, &new_env)?;
            let body_with_bindings = self.wrap_with_bindings(body, bindings);

            if let Some(cond) = condition {
                result = self.make_if(cond, body_with_bindings, result);
            } else {
                result = body_with_bindings;
            }
        }

        // Wrap in let for the scrutinee
        Ok(self.make_let(scrut_name, scrut_ty, scrut_expr, result))
    }

    // ========================================================================
    // Type conversion
    // ========================================================================

    /// Convert a qualified type.
    fn convert_qtype(&self, qtype: &CQType) -> ConvResult<IType> {
        // For now, just convert the main type, ignoring context
        self.convert_type(&qtype.ty)
    }

    /// Convert a type from CType to IType.
    fn convert_type(&self, ty: &CType) -> ConvResult<IType> {
        match ty {
            CType::Var(name) => {
                // Type variable
                Ok(IType::Var(ITyVar {
                    name: name.clone(),
                    num: 0,
                    kind: IKind::Star,
                }))
            }
            CType::Con(ref tycon) => {
                let name = &tycon.name;
                // Type constructor
                if let Some(type_info) = self.symtab.find_type(name) {
                    let sort = match &type_info.sort {
                        TISort::Synonym { arity, body } => {
                            let body_ty = self.convert_type(body)?;
                            ITySort::Synonym(num_bigint::BigInt::from(*arity), Box::new(body_ty))
                        }
                        TISort::Data { constructors, .. } => ITySort::Data(constructors.clone()),
                        TISort::Struct { fields, .. } => ITySort::Struct(fields.clone()),
                        TISort::Abstract => ITySort::Abstract,
                    };

                    Ok(IType::Con(ITyCon::Named(ITyConInfo {
                        name: name.clone(),
                        kind: self.convert_bsc_kind(&type_info.kind),
                        sort,
                    })))
                } else {
                    // Unknown type - assume abstract with kind *
                    Ok(IType::Con(ITyCon::Named(ITyConInfo {
                        name: name.clone(),
                        kind: IKind::Star,
                        sort: ITySort::Abstract,
                    })))
                }
            }
            CType::Apply(func, arg, _span) => {
                let func_ty = self.convert_type(func)?;
                let arg_ty = self.convert_type(arg)?;
                Ok(IType::App(Box::new(func_ty), Box::new(arg_ty)))
            }
            CType::Num(n, _span) => Ok(IType::Con(ITyCon::Num(num_bigint::BigInt::from(*n)))),
            CType::Str(s, _span) => Ok(IType::Con(ITyCon::Str(s.clone()))),
            CType::Fun(arg, result, _span) => {
                let arg_ty = self.convert_type(arg)?;
                let result_ty = self.convert_type(result)?;
                // Function type is represented as ((->) arg result)
                Ok(self.make_function_type(arg_ty, result_ty))
            }
            CType::Forall(params, body, _span) => {
                let body_ty = self.convert_type(body)?;
                // Wrap with foralls
                let mut result = body_ty;
                for param in params.iter().rev() {
                    let kind = param
                        .kind
                        .as_ref()
                        .map(|k| self.convert_kind(k))
                        .unwrap_or(IKind::Star);
                    // In IType, forall is represented differently
                    // For now, just return the body type
                    // TODO: Implement proper forall handling
                    let _ = kind; // Suppress unused warning
                }
                Ok(result)
            }
            CType::Paren(inner, _span) => self.convert_type(inner),
            CType::Tuple(tys, _span) => {
                // Tuple type is a nested application of Tuple type constructor
                // For now, just return the first type
                if tys.is_empty() {
                    Ok(self.make_unit_type())
                } else {
                    self.convert_type(&tys[0])
                }
            }
            CType::List(elem, _span) => {
                let elem_ty = self.convert_type(elem)?;
                Ok(self.make_list_type(elem_ty))
            }
            CType::Infix(_, _, _, _span) => Err(ConvError::Internal {
                message: "unresolved infix type operator".to_string(),
            }),
            CType::NoType => Err(ConvError::Internal {
                message: "attempted to convert NoType (should not exist after type checking)".to_string(),
            }),
        }
    }

    /// Convert a kind from CKind to IKind.
    fn convert_kind(&self, kind: &CKind) -> IKind {
        match kind {
            CKind::Star(_) => IKind::Star,
            CKind::Num(_) => IKind::Num,
            CKind::Str(_) => IKind::Str,
            CKind::Fun(arg, result, _) => {
                IKind::Fun(Box::new(self.convert_kind(arg)), Box::new(self.convert_kind(result)))
            }
            CKind::Paren(inner, _) => self.convert_kind(inner),
        }
    }

    /// Convert a Kind (from bsc_types) to IKind.
    fn convert_bsc_kind(&self, kind: &Kind) -> IKind {
        match kind {
            Kind::Star => IKind::Star,
            Kind::Num => IKind::Num,
            Kind::Str => IKind::Str,
            Kind::Fun(arg, result) => {
                IKind::Fun(
                    Box::new(self.convert_bsc_kind(arg)),
                    Box::new(self.convert_bsc_kind(result)),
                )
            }
            Kind::Var(n) => IKind::Var(*n as u32),
        }
    }

    /// Convert a Type (from bsc_types) to IType.
    fn convert_bsc_type(&self, ty: &bsc_types::Type) -> IType {
        match ty {
            bsc_types::Type::Var(tv) => IType::Var(ITyVar {
                name: tv.name.clone(),
                num: tv.num as u32,
                kind: self.convert_bsc_kind(&tv.kind),
            }),
            bsc_types::Type::Con(tc) => match tc {
                bsc_types::TyCon::Named { name, kind, sort } => {
                    let ikind = kind
                        .as_ref()
                        .map(|k| self.convert_bsc_kind(k))
                        .unwrap_or(IKind::Star);
                    let isort = self.convert_tycon_sort(sort);
                    IType::Con(ITyCon::Named(ITyConInfo {
                        name: name.clone(),
                        kind: ikind,
                        sort: isort,
                    }))
                }
                bsc_types::TyCon::TyNum { value, .. } => IType::Con(ITyCon::Num(value.clone())),
                bsc_types::TyCon::TyStr { value, .. } => {
                    IType::Con(ITyCon::Str(value.to_string()))
                }
            },
            bsc_types::Type::App(f, a) => IType::App(
                Box::new(self.convert_bsc_type(f)),
                Box::new(self.convert_bsc_type(a)),
            ),
            bsc_types::Type::Gen { index, .. } => IType::Gen(*index as i64),
            bsc_types::Type::DefMonad(_) => {
                // DefMonad is used during type checking; convert to a placeholder
                IType::Var(ITyVar {
                    name: Id::unpositioned("_defMonad"),
                    num: 0,
                    kind: IKind::Star,
                })
            }
        }
    }

    /// Convert a TyConSort (from bsc_types) to ITySort.
    fn convert_tycon_sort(&self, sort: &bsc_types::TyConSort) -> ITySort {
        match sort {
            bsc_types::TyConSort::TypeSyn { arity, expansion } => {
                ITySort::Synonym(arity.clone(), Box::new(self.convert_bsc_type(expansion)))
            }
            bsc_types::TyConSort::Data { constructors, .. } => {
                ITySort::Data(constructors.clone())
            }
            bsc_types::TyConSort::Struct { fields, .. } => ITySort::Struct(fields.clone()),
            bsc_types::TyConSort::Abstract => ITySort::Abstract,
        }
    }

    // ========================================================================
    // Helper methods
    // ========================================================================

    /// Look up the type of a variable.
    fn lookup_var_type(&self, name: &Id) -> ConvResult<IType> {
        if let Some(var_info) = self.symtab.find_var(name) {
            Ok(self.convert_bsc_type(&var_info.assump.scheme.qual_type.ty))
        } else {
            Err(ConvError::UnknownVariable {
                name: name.full_name(),
                span: Span::DUMMY,
            })
        }
    }

    /// Look up the type of a field.
    fn lookup_field_type(&self, type_name: &Id, field_name: &Id) -> ConvResult<IType> {
        if let Some(field_info) = self.symtab.find_field_for_type(field_name, type_name) {
            Ok(self.convert_bsc_type(&field_info.assump.scheme.qual_type.ty))
        } else {
            Err(ConvError::UnknownField {
                name: field_name.full_name(),
                span: Span::DUMMY,
            })
        }
    }

    /// Split a function type into argument types and return type.
    fn split_function_type(&self, ty: &IType) -> (Vec<IType>, IType) {
        // For now, return empty args and the type itself
        // TODO: Implement proper function type splitting
        (vec![], ty.clone())
    }

    /// Get the type constructor from a type.
    fn get_type_constructor(&self, ty: &IType) -> ConvResult<Id> {
        match ty {
            IType::Con(ITyCon::Named(info)) => Ok(info.name.clone()),
            IType::App(f, _) => self.get_type_constructor(f),
            _ => Err(ConvError::Internal {
                message: "cannot get type constructor".to_string(),
            }),
        }
    }

    /// Get the type of a tuple element.
    fn get_tuple_element_type(&self, _ty: &IType, _index: usize) -> IType {
        // TODO: Implement proper tuple type extraction
        IType::Gen(0)
    }

    /// Get the type of a constructor field.
    fn get_constructor_field_type(&self, _con_ty: &IType, _index: usize) -> IType {
        // TODO: Implement proper constructor field type extraction
        IType::Gen(0)
    }

    /// Wrap an expression with let bindings.
    fn wrap_with_bindings(&self, body: IExpr, bindings: Vec<(Id, IType, IExpr)>) -> IExpr {
        let mut result = body;
        for (name, ty, expr) in bindings.into_iter().rev() {
            result = self.make_let(name, ty, expr, result);
        }
        result
    }

    /// Extract pragmas from a package.
    fn extract_pragmas(&self, pkg: &CPackage) -> Vec<IPragma> {
        let mut pragmas = Vec::new();

        for defn in &pkg.definitions {
            if let CDefn::Pragma(pragma) = defn {
                match pragma {
                    bsc_syntax::CPragma::Properties(id, props) => {
                        let iprops: Vec<IProperty> = props
                            .iter()
                            .map(|p| IProperty {
                                name: p.name.clone(),
                                value: p.value.clone(),
                            })
                            .collect();
                        pragmas.push(IPragma::Properties(id.clone(), iprops));
                    }
                    _ => {}
                }
            }
        }

        pragmas
    }

    // ========================================================================
    // Expression constructors
    // ========================================================================

    /// Create an undefined expression.
    fn make_undefined(&self, _ty: &IType) -> IExpr {
        // Create a reference to the undefined primitive
        let name = Id::unpositioned("_undefined");
        IExpr::Var(name)
    }

    /// Create a let expression.
    fn make_let(&self, name: Id, ty: IType, value: IExpr, body: IExpr) -> IExpr {
        // Let is represented as ((\name -> body) value)
        let lambda = IExpr::Lam(name, ty, Box::new(body));
        IExpr::App(Box::new(lambda), vec![IArg::Expr(value)])
    }

    /// Create an if-then-else expression.
    fn make_if(&self, cond: IExpr, then_branch: IExpr, else_branch: IExpr) -> IExpr {
        // If is represented as a primitive application
        let if_prim = Id::unpositioned("_if");
        let if_expr = IExpr::Var(if_prim);
        IExpr::App(
            Box::new(if_expr),
            vec![
                IArg::Expr(cond),
                IArg::Expr(then_branch),
                IArg::Expr(else_branch),
            ],
        )
    }

    /// Create an equality test expression.
    fn make_eq(&self, left: IExpr, right: IExpr) -> IExpr {
        let eq_prim = Id::unpositioned("_eq");
        let eq_expr = IExpr::Var(eq_prim);
        IExpr::App(Box::new(eq_expr), vec![IArg::Expr(left), IArg::Expr(right)])
    }

    /// Create an AND expression.
    fn make_and(&self, left: IExpr, right: IExpr) -> IExpr {
        let and_prim = Id::unpositioned("_and");
        let and_expr = IExpr::Var(and_prim);
        IExpr::App(
            Box::new(and_expr),
            vec![IArg::Expr(left), IArg::Expr(right)],
        )
    }

    /// Create an AND of multiple expressions.
    fn and_all(&self, exprs: Vec<IExpr>) -> IExpr {
        if exprs.is_empty() {
            // Return true
            let true_con = Id::unpositioned("True");
            IExpr::Var(true_con)
        } else {
            let mut iter = exprs.into_iter();
            let first = iter.next().expect("non-empty");
            iter.fold(first, |acc, e| self.make_and(acc, e))
        }
    }

    /// Create a constructor test expression.
    fn make_constructor_test(
        &self,
        scrutinee: &IExpr,
        con_name: &Id,
        tag_info: &ConTagInfo,
    ) -> IExpr {
        // Create an "is" test for the constructor
        let is_prim = Id::unpositioned(format!("_is_{}", con_name.name()));
        let is_expr = IExpr::Var(is_prim);
        IExpr::App(
            Box::new(is_expr),
            vec![IArg::Expr(scrutinee.clone())],
        )
    }

    /// Create a constructor field selection expression.
    fn make_constructor_field_select(
        &self,
        scrutinee: IExpr,
        con_name: &Id,
        index: usize,
        ty: &IType,
    ) -> IExpr {
        let sel_name = Id::unpositioned(format!("_sel_{}_{index}", con_name.name()));
        let sel_expr = IExpr::Var(sel_name);
        IExpr::App(Box::new(sel_expr), vec![IArg::Expr(scrutinee)])
    }

    /// Create a tuple selection expression.
    fn make_tuple_select(&self, tuple: IExpr, index: usize, ty: &IType) -> IExpr {
        let sel_name = Id::unpositioned(format!("_tuple_sel_{index}"));
        let sel_expr = IExpr::Var(sel_name);
        IExpr::App(Box::new(sel_expr), vec![IArg::Expr(tuple)])
    }

    /// Create a field selection expression.
    fn make_field_select(&self, obj: IExpr, field: &Id, ty: &IType) -> IExpr {
        let sel_name = Id::unpositioned(format!("_sel_{}", field.name()));
        let sel_expr = IExpr::Var(sel_name);
        IExpr::App(Box::new(sel_expr), vec![IArg::Expr(obj)])
    }

    /// Create a tuple constructor expression.
    fn make_tuple_constructor(&self, size: usize) -> IExpr {
        let name = Id::unpositioned(format!("_Tuple{size}"));
        IExpr::Var(name)
    }

    /// Create a struct constructor expression.
    fn make_struct_constructor(&self, ty_name: &Id) -> IExpr {
        IExpr::Var(ty_name.clone())
    }

    /// Create a Nil expression for empty list.
    fn make_nil(&self) -> IExpr {
        let nil = Id::unpositioned("Nil");
        IExpr::Var(nil)
    }

    /// Create a Cons expression for list construction.
    fn make_cons(&self, head: IExpr, tail: IExpr) -> IExpr {
        let cons = Id::unpositioned("Cons");
        let cons_expr = IExpr::Var(cons);
        IExpr::App(
            Box::new(cons_expr),
            vec![IArg::Expr(head), IArg::Expr(tail)],
        )
    }

    /// Convert a literal to an expression.
    fn convert_literal(&self, lit: &Literal, ty: &IType) -> IExpr {
        match lit {
            Literal::Integer(int_lit) => {
                let id = Id::unpositioned("_lit_int");
                IExpr::Con(id, IConInfo::Int { ty: ty.clone(), value: int_lit.clone() })
            }
            Literal::Float(f) => {
                let id = Id::unpositioned("_lit_real");
                IExpr::Con(id, IConInfo::Real { ty: ty.clone(), value: (*f).into() })
            }
            Literal::Char(c) => {
                let id = Id::unpositioned("_lit_char");
                IExpr::Con(id, IConInfo::Char { ty: ty.clone(), value: *c })
            }
            Literal::String(s) => {
                let id = Id::unpositioned("_lit_string");
                IExpr::Con(id, IConInfo::String { ty: ty.clone(), value: s.clone() })
            }
            Literal::Position => {
                // Position literals are used for source location tracking
                // Convert to a unit value (empty tuple)
                let id = Id::unpositioned("()");
                IExpr::Var(id)
            }
        }
    }

    /// Create a foreign function expression.
    fn make_foreign_expr(&self, name: &Id, ty: &IType, foreign_name: &str) -> IExpr {
        // Foreign functions use IConInfo::Foreign
        IExpr::Con(
            name.clone(),
            IConInfo::Foreign {
                ty: ty.clone(),
                name: foreign_name.to_string(),
                is_c: true,
                ports: None,
                call_no: None,
            },
        )
    }

    /// Create a primitive expression.
    fn make_primitive_expr(&self, name: &Id, ty: &IType) -> IExpr {
        // Primitives use IConInfo::Prim with a PrimOp
        // For now, use a placeholder PrimOp - the actual op should be determined
        // from the primitive name in a real implementation
        IExpr::Con(
            name.clone(),
            IConInfo::Prim {
                ty: ty.clone(),
                op: bsc_syntax::PrimOp::Error, // Placeholder
            },
        )
    }

    /// Make a function type.
    fn make_function_type(&self, arg: IType, result: IType) -> IType {
        // Function type is ((->) arg result)
        let arrow = ITyCon::Named(ITyConInfo {
            name: Id::unpositioned("->"),
            kind: IKind::Fun(
                Box::new(IKind::Star),
                Box::new(IKind::Fun(Box::new(IKind::Star), Box::new(IKind::Star))),
            ),
            sort: ITySort::Abstract,
        });
        let arrow_ty = IType::Con(arrow);
        IType::App(
            Box::new(IType::App(Box::new(arrow_ty), Box::new(arg))),
            Box::new(result),
        )
    }

    /// Make a unit type.
    fn make_unit_type(&self) -> IType {
        IType::Con(ITyCon::Named(ITyConInfo {
            name: Id::unpositioned("()"),
            kind: IKind::Star,
            sort: ITySort::Struct(vec![]),
        }))
    }

    /// Make a list type.
    fn make_list_type(&self, elem: IType) -> IType {
        let list = ITyCon::Named(ITyConInfo {
            name: Id::unpositioned("List"),
            kind: IKind::Fun(Box::new(IKind::Star), Box::new(IKind::Star)),
            sort: ITySort::Data(vec![Id::unpositioned("Nil"), Id::unpositioned("Cons")]),
        });
        IType::App(Box::new(IType::Con(list)), Box::new(elem))
    }
}

/// Convenience function to convert a package.
///
/// # Errors
///
/// Returns an error if conversion fails.
pub fn convert(pkg: &CPackage, symtab: &SymTab) -> ConvResult<IPackage> {
    let converter = Converter::new(symtab);
    converter.convert_package(pkg)
}

