//! Expression type inference (mirrors `TCheck.hs`).
//!
//! This module provides type inference for BSC expressions and definitions.
//! It implements a bidirectional type checking algorithm with:
//! - Inference mode: synthesize a type from the expression structure
//! - Checking mode: verify that an expression has an expected type
//!
//! # Algorithm
//!
//! The inference algorithm follows standard Hindley-Milner type inference:
//! 1. Assign fresh type variables to unknowns
//! 2. Generate constraints through expression traversal
//! 3. Solve constraints via unification
//! 4. Apply the resulting substitution to get final types

use bsc_diagnostics::{Span, TypeError};
use bsc_symtab::SymTab;
use bsc_syntax::{
    CCaseArm, CClause, CDef, CDefl, CDefn, CExpr, CPat, CQual, CStmt, CValueDef, Id, Literal,
};
use bsc_types::{Kind, Type};

use crate::context::{
    make_action_type, make_action_value_type, make_bool_type, make_char_type, make_fun_type,
    make_integer_type, make_list_type, make_module_type, make_real_type, make_rules_type,
    make_string_type, make_tuple_type, make_unit_type, split_fun_type, TypeCheckContext,
};

/// Infer the type of an expression.
///
/// This is the main entry point for expression type inference. It walks
/// the expression tree, generating type constraints and unifying them
/// to produce a final type.
///
/// # Arguments
///
/// * `ctx` - The type checking context (mutable for unification)
/// * `env` - The symbol table containing variable bindings
/// * `expr` - The expression to type check
///
/// # Returns
///
/// Returns `Ok(Type)` with the inferred type, or `Err(TypeError)` if
/// the expression cannot be typed.
///
/// # Errors
///
/// Returns a `TypeError` if:
/// - An undefined variable is referenced
/// - Types cannot be unified
/// - Other type checking errors occur
///
/// # Example
///
/// ```ignore
/// use bsc_typecheck::{TypeCheckContext, infer_expr};
/// use bsc_symtab::SymTab;
///
/// let mut ctx = TypeCheckContext::new();
/// let env = SymTab::new();
/// let ty = infer_expr(&mut ctx, &env, &expr)?;
/// ```
pub fn infer_expr(ctx: &mut TypeCheckContext, env: &SymTab, expr: &CExpr) -> Result<Type, TypeError> {
    match expr {
        CExpr::Var(id) => infer_var(ctx, env, id),

        CExpr::Con(id, args, span) => {
            // Constructor application
            let mut result_ty = infer_con(ctx, env, id)?;
            // Apply arguments
            for arg in args {
                let arg_ty = infer_expr(ctx, env, arg)?;
                // Extract function parameter and result types
                let (param_ty, ret_ty) = split_fun_type(&result_ty)
                    .ok_or_else(|| TypeError::TypeMismatch {
                        expected: "function type".to_string(),
                        found: result_ty.to_string(),
                        span: (*span).into(),
                    })?;
                ctx.unify_with_span(&arg_ty, param_ty, *span)?;
                result_ty = ret_ty.clone();
            }
            Ok(ctx.apply_subst(&result_ty))
        }

        CExpr::Lit(lit, _pos) => infer_literal(ctx, lit),

        CExpr::Lambda(patterns, body, span) => infer_lambda(ctx, env, patterns, body, *span),

        CExpr::Apply(func, args, span) => infer_apply(ctx, env, func, args, *span),

        CExpr::Infix(left, op, right, span) => infer_infix(ctx, env, left, op, right, *span),

        CExpr::SectionL(op, arg, span) => infer_section_l(ctx, env, op, arg, *span),

        CExpr::SectionR(arg, op, span) => infer_section_r(ctx, env, arg, op, *span),

        CExpr::If(_pos, cond, then_branch, else_branch) => {
            infer_if(ctx, env, cond, then_branch, else_branch, Span::DUMMY)
        }

        CExpr::Case(_pos, scrutinee, arms) => infer_case(ctx, env, scrutinee, arms, Span::DUMMY),

        CExpr::LetSeq(defs, body, span) => infer_let_seq_defl(ctx, env, defs, body, *span),

        CExpr::LetRec(defs, body, span) => infer_let_rec_defl(ctx, env, defs, body, *span),

        CExpr::Do { stmts, span, .. } => infer_do(ctx, env, stmts, *span),

        CExpr::Struct(_visible, name, fields, span) => infer_struct(ctx, env, name, fields, *span),

        CExpr::Update(base, fields, span) => infer_update(ctx, env, base, fields, *span),

        CExpr::Select(base, field, span) => infer_select(ctx, env, base, field, *span),

        CExpr::TypeAscription(inner_expr, ty, span) => infer_typed(ctx, env, inner_expr, ty, *span),

        CExpr::Paren(inner, _) => infer_expr(ctx, env, inner),

        CExpr::List(elements, span) => infer_list(ctx, env, elements, *span),

        CExpr::Tuple(elements, span) => infer_tuple(ctx, env, elements, *span),

        CExpr::Action(_pos, stmts) => infer_action(ctx, env, stmts, Span::DUMMY),

        CExpr::ActionValue(stmts, span) => infer_action_value(ctx, env, stmts, *span),

        CExpr::Module(_pos, items) => infer_module(ctx, env, items, Span::DUMMY),

        CExpr::Interface(_pos, ty, items) => infer_interface(ctx, env, ty, items, Span::DUMMY),

        CExpr::Rules(_pragmas, rules, span) => infer_rules(ctx, env, rules, *span),

        CExpr::Verilog(verilog, span) => infer_verilog(ctx, env, verilog, *span),

        CExpr::Attributed(attrs, inner, _span) => {
            // Attributes don't affect typing; just infer the inner expression
            let _ = attrs; // Attributes may be used for other purposes
            infer_expr(ctx, env, inner)
        }

        CExpr::ValueOf(ty, span) => infer_value_of(ctx, env, ty, *span),

        CExpr::StringOf(ty, span) => infer_string_of(ctx, env, ty, *span),

        // Typed lambda: \(x :: T) -> e
        CExpr::LambdaTyped { body, span, .. } => {
            // Infer body type (parameter type is already annotated)
            let body_ty = infer_expr(ctx, env, body)?;
            let param_ty = ctx.new_tvar(Kind::Star);
            Ok(make_fun_type(param_ty, body_ty))
        }

        // Operator chain (before fixity resolution)
        CExpr::OperChain(operands, span) => {
            // Operator chains should be resolved before type checking
            Err(TypeError::TypeMismatch {
                expected: "resolved expression".to_string(),
                found: "unresolved operator chain".to_string(),
                span: (*span).into(),
            })
        }

        // Hardware write: lhs <= rhs
        CExpr::Write { lhs, rhs, span, .. } => {
            let _lhs_ty = infer_expr(ctx, env, lhs)?;
            let _rhs_ty = infer_expr(ctx, env, rhs)?;
            // Write returns Action type
            Ok(make_action_type())
        }

        // Undefined value
        CExpr::Any { span, .. } => {
            // Any can have any type
            Ok(ctx.new_tvar(Kind::Star))
        }

        // Array/bit indexing: e[i]
        CExpr::Index { expr, index, span } => {
            let _array_ty = infer_expr(ctx, env, expr)?;
            let _index_ty = infer_expr(ctx, env, index)?;
            // Result is element type
            Ok(ctx.new_tvar(Kind::Star))
        }

        // Bit range selection: e[hi:lo]
        CExpr::IndexRange { expr, hi, lo, span } => {
            let _vec_ty = infer_expr(ctx, env, expr)?;
            let _hi_ty = infer_expr(ctx, env, hi)?;
            let _lo_ty = infer_expr(ctx, env, lo)?;
            // Result is bit vector type
            Ok(ctx.new_tvar(Kind::Star))
        }

        // Bit range update: e[hi:lo] = v
        CExpr::IndexUpdate { expr, range, value, span, .. } => {
            let _vec_ty = infer_expr(ctx, env, expr)?;
            let _hi_ty = infer_expr(ctx, env, &range.0)?;
            let _lo_ty = infer_expr(ctx, env, &range.1)?;
            let _val_ty = infer_expr(ctx, env, value)?;
            // Result is same as vector type
            Ok(ctx.new_tvar(Kind::Star))
        }

        // System task application: $display(...)
        CExpr::TaskApply(task, args, span) => {
            let _task_ty = infer_expr(ctx, env, task)?;
            for arg in args {
                let _ = infer_expr(ctx, env, arg)?;
            }
            Ok(make_action_type())
        }

        // Typed system task application
        CExpr::TaskApplyTyped(task, _ty, args, span) => {
            let _task_ty = infer_expr(ctx, env, task)?;
            for arg in args {
                let _ = infer_expr(ctx, env, arg)?;
            }
            Ok(make_action_type())
        }

        // Type application: e @T
        CExpr::TypeApply(expr, _types, span) => {
            infer_expr(ctx, env, expr)
        }

        // Foreign C function
        CExpr::ForeignFuncC { span, .. } => {
            Ok(ctx.new_tvar(Kind::Star))
        }

        // Internal: Typed constructor application
        CExpr::ConTyped { con_name, args, span, .. } => {
            let con_ty = infer_con(ctx, env, con_name)?;
            for arg in args {
                let _ = infer_expr(ctx, env, arg)?;
            }
            Ok(con_ty)
        }

        // Internal: Typed literal
        CExpr::LitTyped(_ty, lit, span) => {
            infer_literal(ctx, lit)
        }

        // Internal: Typed undefined
        CExpr::AnyTyped { span, .. } => {
            Ok(ctx.new_tvar(Kind::Star))
        }

        // Internal: Typed field selection
        CExpr::SelectTyped { expr, span, .. } => {
            let _obj_ty = infer_expr(ctx, env, expr)?;
            Ok(ctx.new_tvar(Kind::Star))
        }

        // Internal: Typed struct literal
        CExpr::StructTyped(_ty, fields, span) => {
            for field in fields {
                let _ = infer_expr(ctx, env, &field.value)?;
            }
            Ok(ctx.new_tvar(Kind::Star))
        }

        // Internal: Typed Verilog module
        CExpr::VerilogTyped(_ty, _verilog, span) => {
            let ifc_ty = ctx.new_tvar(Kind::Star);
            Ok(make_module_type(ifc_ty))
        }

        // Internal: Typed foreign C function
        CExpr::ForeignFuncCTyped { span, .. } => {
            Ok(ctx.new_tvar(Kind::Star))
        }

        // Internal: Constructor with single argument (from deriving)
        CExpr::Con1 { con_id, arg, span, .. } => {
            let con_ty = infer_con(ctx, env, con_id)?;
            let _arg_ty = infer_expr(ctx, env, arg)?;
            Ok(con_ty)
        }

        // Internal: Typed selection with expression type
        CExpr::SelectTT { expr, span, .. } => {
            let _obj_ty = infer_expr(ctx, env, expr)?;
            Ok(ctx.new_tvar(Kind::Star))
        }

        // Internal: Nullary constructor
        CExpr::Con0 { con_id, span, .. } => {
            infer_con(ctx, env, con_id)
        }

        // Internal: Typed selector (no expression, just selector function)
        CExpr::SelectT { span, .. } => {
            // Selector function type
            Ok(ctx.new_tvar(Kind::Star))
        }

        CExpr::ModuleVerilog { args, .. } => {
            for (_arg_info, arg_expr) in args {
                let _ = infer_expr(ctx, env, arg_expr)?;
            }
            let ifc_ty = ctx.new_tvar(Kind::Star);
            Ok(make_module_type(ifc_ty))
        }
    }
}

/// Type check a top-level definition.
///
/// This function verifies that a definition is well-typed and updates
/// the environment with the binding.
///
/// # Arguments
///
/// * `ctx` - The type checking context
/// * `env` - The symbol table (may be extended with the new binding)
/// * `defn` - The definition to check
///
/// # Returns
///
/// Returns `Ok(())` if the definition type checks successfully.
///
/// # Errors
///
/// Returns a `TypeError` if the definition cannot be typed.
pub fn check_defn(ctx: &mut TypeCheckContext, env: &SymTab, defn: &CDefn) -> Result<(), TypeError> {
    match defn {
        CDefn::Type(typedef) => check_type_def(ctx, env, typedef),

        CDefn::Data(datadef) => check_data_def(ctx, env, datadef),

        CDefn::Struct(structdef) => check_struct_def(ctx, env, structdef),

        CDefn::Class(classdef) => check_class_def(ctx, env, classdef),

        CDefn::Instance(instdef) => check_instance_def(ctx, env, instdef),

        CDefn::Value(def) => check_value_def(ctx, env, def),

        CDefn::Signature(sig) => check_signature(ctx, env, sig),

        CDefn::Foreign(foreign) => check_foreign_def(ctx, env, foreign),

        CDefn::Primitive(prim) => check_primitive_def(ctx, env, prim),

        CDefn::PrimitiveType(primty) => check_primitive_type(ctx, env, primty),

        CDefn::Pragma(pragma) => {
            // Pragmas don't require type checking
            let _ = pragma;
            Ok(())
        }

        CDefn::ValueSign(def) => {
            // Value definition with type signature
            let _ty = infer_def_body(ctx, env, def)?;
            Ok(())
        }

        CDefn::SigInstance { .. }
        | CDefn::SigType { .. }
        | CDefn::SigClass { .. }
        | CDefn::SigValue { .. } => {
            // Signature-only variants are handled in signature processing
            Ok(())
        }
    }
}

// ============================================================================
// Expression inference helpers
// ============================================================================

/// Infer the type of a variable reference.
fn infer_var(ctx: &TypeCheckContext, env: &SymTab, id: &Id) -> Result<Type, TypeError> {
    match env.find_var(id) {
        Some(var_info) => {
            // The VarInfo contains an IType; we need to convert and instantiate
            // For now, return a fresh type variable as a placeholder
            // TODO: Proper IType -> Type conversion and instantiation
            Ok(ctx.new_tvar(Kind::Star))
        }
        None => Err(TypeError::UndefinedVar {
            name: id.to_string(),
            span: Span::DUMMY.into(),
        }),
    }
}

/// Infer the type of a constructor reference.
fn infer_con(ctx: &TypeCheckContext, env: &SymTab, id: &Id) -> Result<Type, TypeError> {
    match env.find_con(id) {
        Some(con_infos) if !con_infos.is_empty() => {
            // Use the first constructor info
            // TODO: Proper IType -> Type conversion and instantiation
            Ok(ctx.new_tvar(Kind::Star))
        }
        _ => Err(TypeError::UndefinedVar {
            name: id.to_string(),
            span: Span::DUMMY.into(),
        }),
    }
}

/// Infer the type of a literal.
fn infer_literal(_ctx: &TypeCheckContext, lit: &Literal) -> Result<Type, TypeError> {
    match lit {
        Literal::Integer(_) => {
            // Integer literals have type Integer or can be overloaded
            // For now, return a concrete Integer type
            Ok(make_integer_type())
        }
        Literal::Float(_) => {
            // Float literals have type Real
            Ok(make_real_type())
        }
        Literal::String(_) => {
            // String literals have type String
            Ok(make_string_type())
        }
        Literal::Char(_) => {
            // Char literals have type Char
            Ok(make_char_type())
        }
        Literal::Position => {
            // Position literals are internal markers, not normally user-visible
            // Return a unit type as a placeholder
            Ok(make_unit_type())
        }
    }
}

/// Infer the type of a lambda expression.
fn infer_lambda(
    ctx: &mut TypeCheckContext,
    env: &SymTab,
    patterns: &[CPat],
    body: &CExpr,
    _span: Span,
) -> Result<Type, TypeError> {
    // Create fresh type variables for each parameter
    let param_types: Vec<Type> = patterns.iter().map(|_| ctx.new_tvar(Kind::Star)).collect();

    // Extend environment with pattern bindings
    let mut inner_env = env.clone();
    for (pat, ty) in patterns.iter().zip(&param_types) {
        bind_pattern(ctx, &mut inner_env, pat, ty)?;
    }

    // Infer the body type
    let body_type = infer_expr(ctx, &inner_env, body)?;

    // Build function type: t1 -> t2 -> ... -> tn -> body_type
    let result = param_types
        .into_iter()
        .rev()
        .fold(body_type, |acc, param| make_fun_type(param, acc));

    Ok(result)
}

/// Infer the type of a function application.
fn infer_apply(
    ctx: &mut TypeCheckContext,
    env: &SymTab,
    func: &CExpr,
    args: &[CExpr],
    span: Span,
) -> Result<Type, TypeError> {
    // Infer the function type
    let func_type = infer_expr(ctx, env, func)?;

    // Infer argument types and apply function
    let mut result_type = func_type;
    for arg in args {
        let arg_type = infer_expr(ctx, env, arg)?;

        // Create fresh type variable for result
        let result_var = ctx.new_tvar(Kind::Star);

        // Unify func_type with (arg_type -> result_var)
        let expected_func = make_fun_type(arg_type, result_var.clone());
        ctx.unify_with_span(&result_type, &expected_func, span)?;

        result_type = ctx.apply_subst(&result_var);
    }

    Ok(result_type)
}

/// Infer the type of an infix operator application.
fn infer_infix(
    ctx: &mut TypeCheckContext,
    env: &SymTab,
    left: &CExpr,
    op: &Id,
    right: &CExpr,
    span: Span,
) -> Result<Type, TypeError> {
    // Desugar: left `op` right => op left right
    let op_type = infer_var(ctx, env, op)?;
    let left_type = infer_expr(ctx, env, left)?;
    let right_type = infer_expr(ctx, env, right)?;

    // op :: a -> b -> c
    let result_var = ctx.new_tvar(Kind::Star);
    let intermediate = make_fun_type(right_type, result_var.clone());
    let expected = make_fun_type(left_type, intermediate);

    ctx.unify_with_span(&op_type, &expected, span)?;

    Ok(ctx.apply_subst(&result_var))
}

/// Infer the type of a left operator section: (op x).
fn infer_section_l(
    ctx: &mut TypeCheckContext,
    env: &SymTab,
    op: &Id,
    arg: &CExpr,
    span: Span,
) -> Result<Type, TypeError> {
    let op_type = infer_var(ctx, env, op)?;
    let arg_type = infer_expr(ctx, env, arg)?;

    // op :: a -> b -> c, arg :: a => result :: b -> c
    let b = ctx.new_tvar(Kind::Star);
    let c = ctx.new_tvar(Kind::Star);
    let expected = make_fun_type(arg_type, make_fun_type(b.clone(), c.clone()));

    ctx.unify_with_span(&op_type, &expected, span)?;

    Ok(make_fun_type(ctx.apply_subst(&b), ctx.apply_subst(&c)))
}

/// Infer the type of a right operator section: (x op).
fn infer_section_r(
    ctx: &mut TypeCheckContext,
    env: &SymTab,
    arg: &CExpr,
    op: &Id,
    span: Span,
) -> Result<Type, TypeError> {
    let op_type = infer_var(ctx, env, op)?;
    let arg_type = infer_expr(ctx, env, arg)?;

    // op :: a -> b -> c, arg :: b => result :: a -> c
    let a = ctx.new_tvar(Kind::Star);
    let c = ctx.new_tvar(Kind::Star);
    let expected = make_fun_type(a.clone(), make_fun_type(arg_type, c.clone()));

    ctx.unify_with_span(&op_type, &expected, span)?;

    Ok(make_fun_type(ctx.apply_subst(&a), ctx.apply_subst(&c)))
}

/// Infer the type of an if-then-else expression.
fn infer_if(
    ctx: &mut TypeCheckContext,
    env: &SymTab,
    cond: &CExpr,
    then_branch: &CExpr,
    else_branch: &CExpr,
    span: Span,
) -> Result<Type, TypeError> {
    let cond_type = infer_expr(ctx, env, cond)?;
    let then_type = infer_expr(ctx, env, then_branch)?;
    let else_type = infer_expr(ctx, env, else_branch)?;

    // Condition must be Bool
    ctx.unify_with_span(&cond_type, &make_bool_type(), span)?;

    // Both branches must have the same type
    ctx.unify_with_span(&then_type, &else_type, span)?;

    Ok(ctx.apply_subst(&then_type))
}

/// Infer the type of a case expression.
///
/// Mirrors the Haskell implementation in TCheck.hs which converts case arms
/// to clauses: `CClause [cca_pattern arm] (cca_filters arm) (cca_consequent arm)`
fn infer_case(
    ctx: &mut TypeCheckContext,
    env: &SymTab,
    scrutinee: &CExpr,
    arms: &[CCaseArm],
    span: Span,
) -> Result<Type, TypeError> {
    let scrutinee_type = infer_expr(ctx, env, scrutinee)?;
    let result_type = ctx.new_tvar(Kind::Star);

    for arm in arms {
        // Pattern must match scrutinee type
        let mut arm_env = env.clone();
        bind_pattern(ctx, &mut arm_env, &arm.pattern, &scrutinee_type)?;

        // Check qualifiers (filters/guards) - extend environment for generators
        for qual in &arm.qualifiers {
            infer_qualifier(ctx, &mut arm_env, qual, span)?;
        }

        // Body must match result type
        let body_type = infer_expr(ctx, &arm_env, &arm.body)?;
        ctx.unify_with_span(&body_type, &result_type, span)?;
    }

    Ok(ctx.apply_subst(&result_type))
}

/// Infer and check a qualifier (guard or generator).
///
/// Mirrors CQual handling in Haskell:
/// - CQGen: generator that binds pattern to expression
/// - CQFilter: guard condition that must be Bool
fn infer_qualifier(
    ctx: &mut TypeCheckContext,
    env: &mut SymTab,
    qual: &CQual,
    span: Span,
) -> Result<(), TypeError> {
    match qual {
        CQual::Filter(cond) => {
            // Filter must be Bool type
            let cond_type = infer_expr(ctx, env, cond)?;
            ctx.unify_with_span(&cond_type, &make_bool_type(), span)?;
        }
        CQual::Gen(_ty, pattern, expr) => {
            // Generator: bind pattern to expression type
            let expr_type = infer_expr(ctx, env, expr)?;
            bind_pattern(ctx, env, pattern, &expr_type)?;
        }
    }
    Ok(())
}

/// Infer the type of a sequential let expression.
fn infer_let_seq(
    ctx: &mut TypeCheckContext,
    env: &SymTab,
    defs: &[CDef],
    body: &CExpr,
    _span: Span,
) -> Result<Type, TypeError> {
    let mut inner_env = env.clone();

    // Process definitions sequentially
    for def in defs {
        infer_def(ctx, &mut inner_env, def)?;
    }

    infer_expr(ctx, &inner_env, body)
}

/// Infer the type of a recursive let expression.
fn infer_let_rec(
    ctx: &mut TypeCheckContext,
    env: &SymTab,
    defs: &[CDef],
    body: &CExpr,
    _span: Span,
) -> Result<Type, TypeError> {
    let mut inner_env = env.clone();

    // First pass: add all definitions with fresh type variables
    let mut def_types: Vec<Type> = Vec::new();
    for def in defs {
        let ty = ctx.new_tvar(Kind::Star);
        add_var_to_env(&mut inner_env, &def.name(), ty.clone());
        def_types.push(ty);
    }

    // Second pass: infer types and unify
    for (def, expected_ty) in defs.iter().zip(&def_types) {
        let inferred_ty = infer_def_body(ctx, &inner_env, def)?;
        ctx.unify(&inferred_ty, expected_ty)?;
    }

    infer_expr(ctx, &inner_env, body)
}

/// Infer the type of a let-seq expression with CDefl definitions.
fn infer_let_seq_defl(
    ctx: &mut TypeCheckContext,
    env: &SymTab,
    defs: &[CDefl],
    body: &CExpr,
    _span: Span,
) -> Result<Type, TypeError> {
    let mut inner_env = env.clone();

    // Process definitions sequentially
    for def in defs {
        infer_defl(ctx, &mut inner_env, def)?;
    }

    infer_expr(ctx, &inner_env, body)
}

/// Infer the type of a let-rec expression with CDefl definitions.
fn infer_let_rec_defl(
    ctx: &mut TypeCheckContext,
    env: &SymTab,
    defs: &[CDefl],
    body: &CExpr,
    _span: Span,
) -> Result<Type, TypeError> {
    let mut inner_env = env.clone();

    // First pass: add all definitions with fresh type variables
    let mut def_types: Vec<Type> = Vec::new();
    for def in defs {
        let ty = ctx.new_tvar(Kind::Star);
        add_var_to_env(&mut inner_env, &get_defl_name(def), ty.clone());
        def_types.push(ty);
    }

    // Second pass: infer types
    for def in defs.iter() {
        infer_defl(ctx, &mut inner_env, def)?;
    }

    infer_expr(ctx, &inner_env, body)
}

/// Infer the type of a local definition (CDefl).
fn infer_defl(
    ctx: &mut TypeCheckContext,
    env: &mut SymTab,
    def: &CDefl,
) -> Result<(), TypeError> {
    match def {
        CDefl::ValueSign(cdef, _quals, _span) => {
            let ty = infer_def_body(ctx, env, cdef)?;
            add_var_to_env(env, &cdef.name(), ctx.apply_subst(&ty));
            Ok(())
        }
        CDefl::Value(name, clauses, _quals, _span) => {
            let ty = infer_clauses(ctx, env, clauses)?;
            add_var_to_env(env, name, ctx.apply_subst(&ty));
            Ok(())
        }
        CDefl::Match(pat, expr, _span) => {
            let ty = infer_expr(ctx, env, expr)?;
            bind_pattern(ctx, env, pat, &ty)?;
            Ok(())
        }
    }
}

/// Get the name of a local definition.
fn get_defl_name(def: &CDefl) -> Id {
    match def {
        CDefl::ValueSign(cdef, _, _) => cdef.name(),
        CDefl::Value(name, _, _, _) => name.clone(),
        CDefl::Match(pat, _, _) => {
            // For match, use the first variable in the pattern if possible
            if let CPat::Var(id) = pat {
                id.clone()
            } else {
                Id::unpositioned("_")
            }
        }
    }
}

/// Infer the type of a do expression.
fn infer_do(
    ctx: &mut TypeCheckContext,
    env: &SymTab,
    stmts: &[CStmt],
    span: Span,
) -> Result<Type, TypeError> {
    infer_stmts(ctx, env, stmts, span)
}

/// Infer the type of a sequence of statements.
fn infer_stmts(
    ctx: &mut TypeCheckContext,
    env: &SymTab,
    stmts: &[CStmt],
    span: Span,
) -> Result<Type, TypeError> {
    if stmts.is_empty() {
        return Err(TypeError::TypeMismatch {
            expected: "non-empty do block".to_string(),
            found: "empty do block".to_string(),
            span: span.into(),
        });
    }

    let mut current_env = env.clone();
    let monad_type = ctx.new_tvar(Kind::Star);

    for (i, stmt) in stmts.iter().enumerate() {
        let is_last = i == stmts.len() - 1;

        match stmt {
            CStmt::Expr { expr, .. } => {
                let ty = infer_expr(ctx, &current_env, expr)?;
                if is_last {
                    return Ok(ty);
                }
                // Non-final expressions should have monadic type
                let inner = ctx.new_tvar(Kind::Star);
                let expected = Type::app(monad_type.clone(), inner);
                ctx.unify_with_span(&ty, &expected, span)?;
            }
            CStmt::Bind { pattern, expr, .. } => {
                let expr_ty = infer_expr(ctx, &current_env, expr)?;
                let inner_ty = ctx.new_tvar(Kind::Star);
                let expected = Type::app(monad_type.clone(), inner_ty.clone());
                ctx.unify_with_span(&expr_ty, &expected, span)?;

                // Bind pattern
                bind_pattern(ctx, &mut current_env, pattern, &ctx.apply_subst(&inner_ty))?;
            }
            CStmt::BindT { pattern, ty, expr, .. } => {
                let expr_ty = infer_expr(ctx, &current_env, expr)?;
                // TODO: Check against declared type
                let inner_ty = ctx.new_tvar(Kind::Star);
                let expected = Type::app(monad_type.clone(), inner_ty.clone());
                ctx.unify_with_span(&expr_ty, &expected, span)?;

                // Bind pattern
                bind_pattern(ctx, &mut current_env, pattern, &ctx.apply_subst(&inner_ty))?;
            }
            CStmt::LetSeq(defls, _stmt_span) => {
                for defl in defls {
                    infer_defl(ctx, &mut current_env, defl)?;
                }
            }
            CStmt::LetRec(defls, _stmt_span) => {
                for defl in defls {
                    infer_defl(ctx, &mut current_env, defl)?;
                }
            }
        }
    }

    // This should be unreachable due to the is_empty check and loop logic
    Err(TypeError::TypeMismatch {
        expected: "expression".to_string(),
        found: "statement".to_string(),
        span: span.into(),
    })
}

/// Infer the type of a struct literal.
fn infer_struct(
    ctx: &mut TypeCheckContext,
    env: &SymTab,
    name: &Id,
    fields: &[bsc_syntax::CFieldInit],
    span: Span,
) -> Result<Type, TypeError> {
    // Look up struct definition
    let _type_info = env.find_type(name).ok_or_else(|| TypeError::UndefinedType {
        name: name.to_string(),
        span: span.into(),
    })?;

    // Check each field
    for field in fields {
        let _field_ty = infer_expr(ctx, env, &field.value)?;
        // TODO: Unify with expected field type from struct definition
    }

    // Return fresh type variable for now
    // TODO: Return actual struct type
    Ok(ctx.new_tvar(Kind::Star))
}

/// Infer the type of a struct update.
fn infer_update(
    ctx: &mut TypeCheckContext,
    env: &SymTab,
    base: &CExpr,
    fields: &[bsc_syntax::CFieldInit],
    _span: Span,
) -> Result<Type, TypeError> {
    let base_ty = infer_expr(ctx, env, base)?;

    // Check field updates
    for field in fields {
        let _field_ty = infer_expr(ctx, env, &field.value)?;
        // TODO: Verify field exists and type matches
    }

    Ok(base_ty)
}

/// Infer the type of a field selection.
fn infer_select(
    ctx: &mut TypeCheckContext,
    env: &SymTab,
    base: &CExpr,
    field: &Id,
    _span: Span,
) -> Result<Type, TypeError> {
    let _base_ty = infer_expr(ctx, env, base)?;

    // Look up field type in the base type
    // TODO: Proper field lookup
    Ok(ctx.new_tvar(Kind::Star))
}

/// Infer the type of a type-annotated expression.
fn infer_typed(
    ctx: &mut TypeCheckContext,
    env: &SymTab,
    inner_expr: &CExpr,
    _ty: &bsc_syntax::CQType,
    _span: Span,
) -> Result<Type, TypeError> {
    let inferred = infer_expr(ctx, env, inner_expr)?;

    // Convert CQType to Type and unify
    // TODO: Proper CQType -> Type conversion
    // let annotated = convert_cqtype_to_type(ty);
    // ctx.unify_with_span(&inferred, &annotated, span)?;

    Ok(inferred)
}

/// Infer the type of a list literal.
fn infer_list(
    ctx: &mut TypeCheckContext,
    env: &SymTab,
    elements: &[CExpr],
    span: Span,
) -> Result<Type, TypeError> {
    let elem_ty = ctx.new_tvar(Kind::Star);

    for elem in elements {
        let ty = infer_expr(ctx, env, elem)?;
        ctx.unify_with_span(&ty, &elem_ty, span)?;
    }

    Ok(make_list_type(ctx.apply_subst(&elem_ty)))
}

/// Infer the type of a tuple literal.
fn infer_tuple(
    ctx: &mut TypeCheckContext,
    env: &SymTab,
    elements: &[CExpr],
    _span: Span,
) -> Result<Type, TypeError> {
    let elem_types: Result<Vec<Type>, _> = elements
        .iter()
        .map(|e| infer_expr(ctx, env, e))
        .collect();

    Ok(make_tuple_type(elem_types?))
}

/// Infer the type of an action block.
fn infer_action(
    ctx: &mut TypeCheckContext,
    env: &SymTab,
    stmts: &[CStmt],
    span: Span,
) -> Result<Type, TypeError> {
    let _inner_ty = infer_stmts(ctx, env, stmts, span)?;
    Ok(make_action_type())
}

/// Infer the type of an action-value block.
fn infer_action_value(
    ctx: &mut TypeCheckContext,
    env: &SymTab,
    stmts: &[CStmt],
    span: Span,
) -> Result<Type, TypeError> {
    let inner_ty = infer_stmts(ctx, env, stmts, span)?;
    Ok(make_action_value_type(inner_ty))
}

/// Infer the type of a module expression.
fn infer_module(
    ctx: &mut TypeCheckContext,
    _env: &SymTab,
    _items: &[bsc_syntax::CModuleItem],
    _span: Span,
) -> Result<Type, TypeError> {
    // TODO: Full module type inference
    let interface_ty = ctx.new_tvar(Kind::Star);
    Ok(make_module_type(interface_ty))
}

/// Infer the type of an interface expression.
fn infer_interface(
    ctx: &mut TypeCheckContext,
    _env: &SymTab,
    _name: &Option<Id>,
    _defls: &[bsc_syntax::CDefl],
    _span: Span,
) -> Result<Type, TypeError> {
    // TODO: Full interface type inference
    Ok(ctx.new_tvar(Kind::Star))
}

/// Infer the type of a rules block.
fn infer_rules(
    ctx: &mut TypeCheckContext,
    env: &SymTab,
    rules: &[bsc_syntax::CRule],
    span: Span,
) -> Result<Type, TypeError> {
    for rule in rules {
        infer_rule(ctx, env, rule, span)?;
    }
    Ok(make_rules_type())
}

/// Infer the type of a single rule.
fn infer_rule(
    ctx: &mut TypeCheckContext,
    env: &SymTab,
    rule: &bsc_syntax::CRule,
    span: Span,
) -> Result<(), TypeError> {
    use bsc_syntax::CRule;
    match rule {
        CRule::Rule { qualifiers, body, .. } => {
            // Check qualifiers (guards)
            let mut rule_env = env.clone();
            for qual in qualifiers {
                infer_qualifier(ctx, &mut rule_env, qual, span)?;
            }
            // Check body (should be Action)
            let body_ty = infer_expr(ctx, &rule_env, body)?;
            ctx.unify_with_span(&body_ty, &make_action_type(), span)?;
            Ok(())
        }
        CRule::Nested { qualifiers, rules, .. } => {
            // Check qualifiers (guards)
            let mut rule_env = env.clone();
            for qual in qualifiers {
                infer_qualifier(ctx, &mut rule_env, qual, span)?;
            }
            // Recursively check nested rules
            for nested_rule in rules {
                infer_rule(ctx, &rule_env, nested_rule, span)?;
            }
            Ok(())
        }
    }
}

/// Infer the type of a Verilog module instantiation.
fn infer_verilog(
    ctx: &mut TypeCheckContext,
    _env: &SymTab,
    _verilog: &bsc_syntax::CVerilog,
    _span: Span,
) -> Result<Type, TypeError> {
    // Verilog instantiations have polymorphic type
    Ok(ctx.new_tvar(Kind::Star))
}

/// Infer the type of a valueOf expression.
fn infer_value_of(
    _ctx: &mut TypeCheckContext,
    _env: &SymTab,
    _ty: &bsc_syntax::CType,
    _span: Span,
) -> Result<Type, TypeError> {
    // valueOf(n) :: Integer where n is a numeric type
    Ok(make_integer_type())
}

/// Infer the type of a stringOf expression.
fn infer_string_of(
    _ctx: &mut TypeCheckContext,
    _env: &SymTab,
    _ty: &bsc_syntax::CType,
    _span: Span,
) -> Result<Type, TypeError> {
    // stringOf(s) :: String where s is a string type
    Ok(make_string_type())
}

// ============================================================================
// Definition checking helpers
// ============================================================================

/// Add a variable to the environment with a given type.
///
/// This is a helper that wraps the type in the appropriate VarInfo structure.
fn add_var_to_env(env: &mut SymTab, id: &Id, _ty: Type) {
    // TODO: Convert Type to IType and add to env
    // For now, this is a no-op placeholder
    // env.add_var(id.clone(), VarInfo { ... });
}

/// Infer the type of a local definition and add it to the environment.
fn infer_def(
    ctx: &mut TypeCheckContext,
    env: &mut SymTab,
    def: &CDef,
) -> Result<(), TypeError> {
    let ty = infer_def_body(ctx, env, def)?;
    add_var_to_env(env, &def.name(), ctx.apply_subst(&ty));
    Ok(())
}

/// Infer the type of a definition body.
fn infer_def_body(
    ctx: &mut TypeCheckContext,
    env: &SymTab,
    def: &CDef,
) -> Result<Type, TypeError> {
    // For simplicity, just check the first clause
    // Get clauses from the CDef enum
    let (clauses, span) = match def {
        CDef::Untyped { clauses, span, .. } => (clauses, *span),
        CDef::Typed { clauses, span, .. } => (clauses, *span),
    };

    // TODO: Handle multiple clauses properly
    if clauses.is_empty() {
        return Err(TypeError::TypeMismatch {
            expected: "definition with clauses".to_string(),
            found: "empty definition".to_string(),
            span: span.into(),
        });
    }

    let clause = &clauses[0];
    infer_clause(ctx, env, clause)
}

/// Infer the type of a clause.
fn infer_clause(
    ctx: &mut TypeCheckContext,
    env: &SymTab,
    clause: &CClause,
) -> Result<Type, TypeError> {
    let param_types: Vec<Type> = clause
        .patterns
        .iter()
        .map(|_| ctx.new_tvar(Kind::Star))
        .collect();

    let mut inner_env = env.clone();
    for (pat, ty) in clause.patterns.iter().zip(&param_types) {
        bind_pattern(ctx, &mut inner_env, pat, ty)?;
    }

    // Process qualifiers (guards)
    for qual in &clause.qualifiers {
        // Qualifiers should have boolean type
        infer_qualifier(ctx, &mut inner_env, qual, clause.body.span())?;
    }

    // Infer body type
    let result_type = infer_expr(ctx, &inner_env, &clause.body)?;

    // Build function type
    let result = param_types
        .into_iter()
        .rev()
        .fold(ctx.apply_subst(&result_type), |acc, param| {
            make_fun_type(ctx.apply_subst(&param), acc)
        });

    Ok(result)
}

/// Infer the type of multiple clauses.
fn infer_clauses(
    ctx: &mut TypeCheckContext,
    env: &SymTab,
    clauses: &[CClause],
) -> Result<Type, TypeError> {
    if clauses.is_empty() {
        // No clauses - return a fresh type variable
        return Ok(ctx.new_tvar(Kind::Star));
    }

    // Infer type from first clause (all clauses should have same type)
    infer_clause(ctx, env, &clauses[0])
}


/// Bind pattern variables to types in the environment.
fn bind_pattern(
    ctx: &mut TypeCheckContext,
    env: &mut SymTab,
    pat: &CPat,
    ty: &Type,
) -> Result<(), TypeError> {
    match pat {
        CPat::Var(id) => {
            add_var_to_env(env, id, ty.clone());
            Ok(())
        }
        CPat::Wildcard(_) => Ok(()),
        CPat::Con(con_id, sub_pats, span) => {
            // Look up constructor type
            let con_ty = infer_con(ctx, env, con_id)?;

            // Extract argument types from constructor type
            let mut arg_types = Vec::new();
            let mut result = con_ty;
            for _ in sub_pats {
                match split_fun_type(&result) {
                    Some((arg, ret)) => {
                        arg_types.push(arg.clone());
                        result = ret.clone();
                    }
                    None => {
                        return Err(TypeError::TypeMismatch {
                            expected: "function type".to_string(),
                            found: result.to_string(),
                            span: (*span).into(),
                        });
                    }
                }
            }

            // Unify result type with expected type
            ctx.unify_with_span(&result, ty, *span)?;

            // Bind sub-patterns
            for (sub_pat, arg_ty) in sub_pats.iter().zip(arg_types) {
                bind_pattern(ctx, env, sub_pat, &ctx.apply_subst(&arg_ty))?;
            }

            Ok(())
        }
        CPat::Lit(lit, _pos) => {
            let lit_ty = infer_literal(ctx, lit)?;
            ctx.unify_with_span(&lit_ty, ty, Span::DUMMY)?;
            Ok(())
        }
        CPat::As(id, inner, _span) => {
            add_var_to_env(env, id, ty.clone());
            bind_pattern(ctx, env, inner, ty)
        }
        CPat::Typed(inner, _anno_ty, _span) => {
            // TODO: Convert CType to Type and unify
            bind_pattern(ctx, env, inner, ty)
        }
        CPat::Paren(inner, _) => bind_pattern(ctx, env, inner, ty),
        CPat::Tuple(pats, span) => {
            let elem_types: Vec<Type> = pats.iter().map(|_| ctx.new_tvar(Kind::Star)).collect();
            let tuple_ty = make_tuple_type(elem_types.clone());
            ctx.unify_with_span(&tuple_ty, ty, *span)?;

            for (sub_pat, elem_ty) in pats.iter().zip(elem_types) {
                bind_pattern(ctx, env, sub_pat, &ctx.apply_subst(&elem_ty))?;
            }
            Ok(())
        }
        CPat::List(pats, span) => {
            let elem_ty = ctx.new_tvar(Kind::Star);
            let list_ty = make_list_type(elem_ty.clone());
            ctx.unify_with_span(&list_ty, ty, *span)?;

            for sub_pat in pats {
                bind_pattern(ctx, env, sub_pat, &ctx.apply_subst(&elem_ty))?;
            }
            Ok(())
        }
        CPat::Struct(_visible, name, fields, span) => {
            // Look up struct type
            let _type_info = env.find_type(name).ok_or_else(|| TypeError::UndefinedType {
                name: name.to_string(),
                span: (*span).into(),
            })?;
            // TODO: Unify struct type with ty and bind field patterns
            let _ = fields;

            Ok(())
        }
        CPat::Infix(left, _op, right, span) => {
            // Infix patterns should be resolved before type checking
            // For now, treat as an error
            let _ = (left, right);
            Err(TypeError::TypeMismatch {
                expected: "resolved pattern".to_string(),
                found: "infix pattern".to_string(),
                span: (*span).into(),
            })
        }
        CPat::MixedLit { span, .. } => {
            // Mixed literals are bit patterns with don't-cares
            // They should unify with Bit types
            // TODO: Implement proper Bit type handling
            let _ = span;
            Ok(())
        }
        CPat::Con1 { type_id, con_id, arg, span } => {
            // Internal: Single-argument constructor from deriving
            // Bind the argument pattern
            let _ = (type_id, con_id, span);
            let elem_ty = ctx.new_tvar(Kind::Star);
            bind_pattern(ctx, env, arg, &elem_ty)?;
            Ok(())
        }
        CPat::ConTs { type_id, con_id, type_args, args, span } => {
            // Internal: Constructor with type arguments (after type checking)
            let _ = (type_id, con_id, type_args, span);
            for arg in args {
                let elem_ty = ctx.new_tvar(Kind::Star);
                bind_pattern(ctx, env, arg, &elem_ty)?;
            }
            Ok(())
        }
    }
}

// ============================================================================
// Top-level definition checking
// ============================================================================

fn check_type_def(
    _ctx: &mut TypeCheckContext,
    _env: &SymTab,
    _typedef: &bsc_syntax::CTypeDef,
) -> Result<(), TypeError> {
    // Type synonyms just need kind checking
    // TODO: Implement kind checking
    Ok(())
}

fn check_data_def(
    _ctx: &mut TypeCheckContext,
    _env: &SymTab,
    _datadef: &bsc_syntax::CDataDef,
) -> Result<(), TypeError> {
    // Check constructors
    // TODO: Implement data type checking
    Ok(())
}

fn check_struct_def(
    _ctx: &mut TypeCheckContext,
    _env: &SymTab,
    _structdef: &bsc_syntax::CStructDef,
) -> Result<(), TypeError> {
    // Check field types
    // TODO: Implement struct checking
    Ok(())
}

fn check_class_def(
    _ctx: &mut TypeCheckContext,
    _env: &SymTab,
    _classdef: &bsc_syntax::CClassDef,
) -> Result<(), TypeError> {
    // Check method signatures
    // TODO: Implement class checking
    Ok(())
}

fn check_instance_def(
    _ctx: &mut TypeCheckContext,
    _env: &SymTab,
    _instdef: &bsc_syntax::CInstanceDef,
) -> Result<(), TypeError> {
    // Check method implementations
    // TODO: Implement instance checking
    Ok(())
}

fn check_value_def(
    ctx: &mut TypeCheckContext,
    env: &SymTab,
    def: &CValueDef,
) -> Result<(), TypeError> {
    let _ty = infer_clauses(ctx, env, &def.clauses)?;
    Ok(())
}

fn check_signature(
    _ctx: &mut TypeCheckContext,
    _env: &SymTab,
    _sig: &bsc_syntax::CTypeSignature,
) -> Result<(), TypeError> {
    // Signatures are just recorded, not checked
    // TODO: Validate the type is well-formed
    Ok(())
}

fn check_foreign_def(
    _ctx: &mut TypeCheckContext,
    _env: &SymTab,
    _foreign: &bsc_syntax::CForeignDef,
) -> Result<(), TypeError> {
    // Foreign imports have their type given
    // TODO: Validate the type
    Ok(())
}

fn check_primitive_def(
    _ctx: &mut TypeCheckContext,
    _env: &SymTab,
    _prim: &bsc_syntax::CPrimitiveDef,
) -> Result<(), TypeError> {
    // Primitives have their type given
    Ok(())
}

fn check_primitive_type(
    _ctx: &mut TypeCheckContext,
    _env: &SymTab,
    _primty: &bsc_syntax::CPrimitiveTypeDef,
) -> Result<(), TypeError> {
    // Primitive types have their kind given
    Ok(())
}

