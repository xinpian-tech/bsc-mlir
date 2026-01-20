//! Type checking context (mirrors `TIMonad.hs`).
//!
//! This module provides the core type checking context that tracks:
//! - Type substitutions (unification results)
//! - Bound type variables at each scope level
//! - Fresh type variable generation
//! - Accumulated type errors
//!
//! The context is mutable and threaded through type checking operations,
//! similar to the `TI` monad in the Haskell implementation.

use bsc_diagnostics::{Span, TypeError};
use bsc_syntax::Id;
use bsc_types::{Kind, Substitution, TyCon, TyConSort, TyVar, Type, Types};
use std::cell::{Cell, RefCell};

/// The type checking context.
///
/// This context maintains all state needed during type inference:
/// - A substitution mapping type variables to types
/// - Scoped stacks of bound type variables
/// - A counter for generating fresh type variables
/// - A collection of type errors encountered
///
/// # Example
///
/// ```
/// use bsc_typecheck::TypeCheckContext;
/// use bsc_types::Kind;
///
/// let mut ctx = TypeCheckContext::new();
///
/// // Generate fresh type variables
/// let t1 = ctx.new_tvar(Kind::Star);
/// let t2 = ctx.new_tvar(Kind::Star);
///
/// // Unify types
/// ctx.unify(&t1, &t2).expect("unification should succeed");
/// ```
#[derive(Debug)]
pub struct TypeCheckContext {
    /// The current type substitution (accumulated unification results).
    subst: Substitution,

    /// Stack of bound type variables at each scope level.
    /// Each entry represents a scope (e.g., a `forall` or let binding).
    bound_tyvars: Vec<Vec<TyVar>>,

    /// Counter for generating fresh type variable names.
    next_tyvar: Cell<i64>,

    /// Accumulated type errors.
    errors: RefCell<Vec<TypeError>>,
}

impl Default for TypeCheckContext {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeCheckContext {
    /// Create a new type checking context.
    #[must_use]
    pub fn new() -> Self {
        Self {
            subst: Substitution::null(),
            bound_tyvars: Vec::new(),
            next_tyvar: Cell::new(0),
            errors: RefCell::new(Vec::new()),
        }
    }

    /// Create a fresh type variable with the given kind.
    ///
    /// Each call generates a unique type variable name.
    #[must_use]
    pub fn new_tvar(&self, kind: Kind) -> Type {
        let n = self.next_tyvar.get();
        self.next_tyvar.set(n + 1);
        let name = format!("_t{n}");
        Type::Var(TyVar::generated(Id::unpositioned(name), n, kind))
    }

    /// Create multiple fresh type variables with the given kinds.
    #[must_use]
    pub fn new_tvars(&self, kinds: &[Kind]) -> Vec<Type> {
        kinds.iter().map(|k| self.new_tvar(k.clone())).collect()
    }

    /// Unify two types, updating the substitution.
    ///
    /// Returns `Ok(())` if unification succeeds, or `Err(TypeError)` if
    /// the types cannot be unified.
    ///
    /// # Errors
    ///
    /// Returns a `TypeError` if:
    /// - The types have incompatible structures
    /// - An occurs check fails (infinite type)
    /// - Kind mismatch between type variables
    pub fn unify(&mut self, t1: &Type, t2: &Type) -> Result<(), TypeError> {
        self.unify_with_span(t1, t2, Span::DUMMY)
    }

    /// Unify two types with a source span for error reporting.
    ///
    /// # Errors
    ///
    /// Returns a `TypeError` if unification fails.
    pub fn unify_with_span(&mut self, t1: &Type, t2: &Type, span: Span) -> Result<(), TypeError> {
        // Apply current substitution to both types
        let t1 = self.apply_subst(t1);
        let t2 = self.apply_subst(t2);

        self.unify_impl(&t1, &t2, span)
    }

    /// Internal unification implementation.
    fn unify_impl(&mut self, t1: &Type, t2: &Type, span: Span) -> Result<(), TypeError> {
        match (t1, t2) {
            // Two type variables that are equal
            (Type::Var(v1), Type::Var(v2)) if v1 == v2 => Ok(()),

            // Type variable with another type - bind it
            (Type::Var(v), t) | (t, Type::Var(v)) => self.bind_var(v.clone(), t.clone(), span),

            // Type constructors must match
            (Type::Con(c1), Type::Con(c2)) if c1 == c2 => Ok(()),

            // Type applications: unify both parts
            (Type::App(f1, a1), Type::App(f2, a2)) => {
                self.unify_impl(f1, f2, span)?;
                // Re-apply substitution to arguments after unifying functions
                let a1 = self.apply_subst(a1);
                let a2 = self.apply_subst(a2);
                self.unify_impl(&a1, &a2, span)
            }

            // Generic type variables (from type schemes)
            (Type::Gen { index: i1, .. }, Type::Gen { index: i2, .. }) if i1 == i2 => Ok(()),

            // Mismatch
            _ => Err(TypeError::TypeMismatch {
                expected: t1.to_string(),
                found: t2.to_string(),
                span: span.into(),
            }),
        }
    }

    /// Bind a type variable to a type, performing occurs check.
    fn bind_var(&mut self, var: TyVar, ty: Type, span: Span) -> Result<(), TypeError> {
        // Occurs check: ensure var doesn't appear in ty
        if ty.free_type_vars().contains(&var) {
            return Err(TypeError::OccursCheck {
                var: var.to_string(),
                ty: ty.to_string(),
                span: span.into(),
            });
        }

        // Kind check (if kinds are available)
        if let Type::Var(other_var) = &ty {
            if var.kind != other_var.kind && !var.kind.is_var() && !other_var.kind.is_var() {
                return Err(TypeError::KindMismatch {
                    expected: format!("{}", var.kind),
                    found: format!("{}", other_var.kind),
                    span: span.into(),
                });
            }
        }

        // Add binding to substitution
        self.subst = self.subst.compose(&Substitution::singleton(var, ty));
        Ok(())
    }

    /// Apply the current substitution to a type.
    #[must_use]
    pub fn apply_subst<T: Types>(&self, t: &T) -> T {
        t.apply_subst(&self.subst)
    }

    /// Get the current substitution.
    #[must_use]
    pub fn substitution(&self) -> &Substitution {
        &self.subst
    }

    /// Enter a new scope with bound type variables.
    ///
    /// Type variables bound in this scope will be tracked and can be
    /// generalized when exiting the scope.
    pub fn enter_scope(&mut self, vars: Vec<TyVar>) {
        self.bound_tyvars.push(vars);
    }

    /// Exit the current scope, returning the bound type variables.
    ///
    /// # Panics
    ///
    /// Panics if there is no scope to exit (programming error).
    pub fn exit_scope(&mut self) -> Vec<TyVar> {
        self.bound_tyvars
            .pop()
            .expect("exit_scope called without matching enter_scope")
    }

    /// Get all type variables bound in the current scope stack.
    #[must_use]
    pub fn all_bound_vars(&self) -> Vec<TyVar> {
        self.bound_tyvars.iter().flatten().cloned().collect()
    }

    /// Check if a type variable is bound in the current scope.
    #[must_use]
    pub fn is_bound(&self, var: &TyVar) -> bool {
        self.bound_tyvars.iter().any(|scope| scope.contains(var))
    }

    /// Record a type error.
    ///
    /// Errors are accumulated and can be retrieved later, allowing
    /// type checking to continue and report multiple errors.
    pub fn record_error(&self, error: TypeError) {
        self.errors.borrow_mut().push(error);
    }

    /// Check if any errors have been recorded.
    #[must_use]
    pub fn has_errors(&self) -> bool {
        !self.errors.borrow().is_empty()
    }

    /// Get the number of recorded errors.
    #[must_use]
    pub fn error_count(&self) -> usize {
        self.errors.borrow().len()
    }

    /// Take all recorded errors, leaving the error list empty.
    pub fn take_errors(&self) -> Vec<TypeError> {
        std::mem::take(&mut *self.errors.borrow_mut())
    }

    /// Get a reference to the recorded errors.
    #[must_use]
    pub fn errors(&self) -> std::cell::Ref<'_, Vec<TypeError>> {
        self.errors.borrow()
    }

    /// Instantiate a polymorphic type by replacing bound variables with fresh ones.
    ///
    /// Given a type scheme `forall a b. T`, this creates fresh type variables
    /// and substitutes them for the bound variables.
    #[must_use]
    pub fn instantiate(&self, ty: &Type, bound_vars: &[TyVar]) -> Type {
        if bound_vars.is_empty() {
            return ty.clone();
        }

        // Create fresh type variables for each bound variable
        let fresh_vars: Vec<Type> = bound_vars
            .iter()
            .map(|v| self.new_tvar(v.kind.clone()))
            .collect();

        // Build substitution from bound vars to fresh vars
        let subst = Substitution::from_pairs(bound_vars.iter().cloned().zip(fresh_vars));

        ty.apply_subst(&subst)
    }

    /// Generalize a type by quantifying over free type variables not in the environment.
    ///
    /// Returns the list of type variables to quantify over and the generalized type.
    #[must_use]
    pub fn generalize(&self, ty: &Type, env_free_vars: &[TyVar]) -> (Vec<TyVar>, Type) {
        let ty = self.apply_subst(ty);
        let ty_vars = ty.free_type_vars();

        // Variables to generalize: free in type but not in environment
        let gen_vars: Vec<TyVar> = ty_vars
            .into_iter()
            .filter(|v| !env_free_vars.contains(v) && !self.is_bound(v))
            .collect();

        (gen_vars, ty)
    }

    /// Reset the context to its initial state.
    pub fn reset(&mut self) {
        self.subst = Substitution::null();
        self.bound_tyvars.clear();
        self.next_tyvar.set(0);
        self.errors.borrow_mut().clear();
    }
}

// ============================================================================
// Type construction helpers
// ============================================================================

/// Create a function type: `arg -> result`.
#[must_use]
pub fn make_fun_type(arg: Type, result: Type) -> Type {
    let arrow = Type::Con(TyCon::abstract_type(
        Id::unpositioned("->"),
        Kind::fun(Kind::Star, Kind::fun(Kind::Star, Kind::Star)),
    ));
    Type::app(Type::app(arrow, arg), result)
}

/// Check if a type is a function type and extract its argument and result types.
#[must_use]
pub fn split_fun_type(ty: &Type) -> Option<(&Type, &Type)> {
    if let Type::App(f, result) = ty {
        if let Type::App(arrow, arg) = f.as_ref() {
            if let Type::Con(TyCon::Named { name, .. }) = arrow.as_ref() {
                if name.name().as_str() == "->" {
                    return Some((arg.as_ref(), result.as_ref()));
                }
            }
        }
    }
    None
}

/// Create the Bool type.
#[must_use]
pub fn make_bool_type() -> Type {
    Type::Con(TyCon::abstract_type(Id::unpositioned("Bool"), Kind::Star))
}

/// Create the Integer type.
#[must_use]
pub fn make_integer_type() -> Type {
    Type::Con(TyCon::abstract_type(
        Id::unpositioned("Integer"),
        Kind::Star,
    ))
}

/// Create the Real type.
#[must_use]
pub fn make_real_type() -> Type {
    Type::Con(TyCon::abstract_type(Id::unpositioned("Real"), Kind::Star))
}

/// Create the String type.
#[must_use]
pub fn make_string_type() -> Type {
    Type::Con(TyCon::abstract_type(
        Id::unpositioned("String"),
        Kind::Star,
    ))
}

/// Create the Char type.
#[must_use]
pub fn make_char_type() -> Type {
    Type::Con(TyCon::abstract_type(Id::unpositioned("Char"), Kind::Star))
}

/// Create a List type: `List a`.
#[must_use]
pub fn make_list_type(elem: Type) -> Type {
    let list_con = Type::Con(TyCon::Named {
        name: Id::unpositioned("List"),
        kind: Some(Kind::fun(Kind::Star, Kind::Star)),
        sort: TyConSort::Abstract,
    });
    Type::app(list_con, elem)
}

/// Create a tuple type from element types.
#[must_use]
pub fn make_tuple_type(elems: Vec<Type>) -> Type {
    match elems.len() {
        0 => Type::Con(TyCon::abstract_type(Id::unpositioned("()"), Kind::Star)),
        1 => elems.into_iter().next().expect("checked length"),
        n => {
            // Build tuple kind: * -> * -> ... -> *
            let mut kind = Kind::Star;
            for _ in 0..n {
                kind = Kind::fun(Kind::Star, kind);
            }

            let tuple_name = format!("Tuple{n}");
            let tuple_con = Type::Con(TyCon::Named {
                name: Id::unpositioned(tuple_name),
                kind: Some(kind),
                sort: TyConSort::Abstract,
            });

            elems.into_iter().fold(tuple_con, Type::app)
        }
    }
}

/// Create the Action type.
#[must_use]
pub fn make_action_type() -> Type {
    Type::Con(TyCon::abstract_type(
        Id::unpositioned("Action"),
        Kind::Star,
    ))
}

/// Create an ActionValue type: `ActionValue a`.
#[must_use]
pub fn make_action_value_type(result: Type) -> Type {
    let av_con = Type::Con(TyCon::Named {
        name: Id::unpositioned("ActionValue"),
        kind: Some(Kind::fun(Kind::Star, Kind::Star)),
        sort: TyConSort::Abstract,
    });
    Type::app(av_con, result)
}

/// Create a Module type: `Module ifc`.
#[must_use]
pub fn make_module_type(ifc: Type) -> Type {
    let module_con = Type::Con(TyCon::Named {
        name: Id::unpositioned("Module"),
        kind: Some(Kind::fun(Kind::Star, Kind::Star)),
        sort: TyConSort::Abstract,
    });
    Type::app(module_con, ifc)
}

/// Create the Rules type.
#[must_use]
pub fn make_rules_type() -> Type {
    Type::Con(TyCon::abstract_type(Id::unpositioned("Rules"), Kind::Star))
}

/// Create the Unit type (empty tuple).
#[must_use]
pub fn make_unit_type() -> Type {
    Type::Con(TyCon::abstract_type(Id::unpositioned("PrimUnit"), Kind::Star))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_tvar_uniqueness() {
        let ctx = TypeCheckContext::new();
        let t1 = ctx.new_tvar(Kind::Star);
        let t2 = ctx.new_tvar(Kind::Star);

        // Each call should produce a different variable
        assert_ne!(t1, t2);
    }

    #[test]
    fn test_scope_management() {
        let mut ctx = TypeCheckContext::new();

        let v1 = TyVar::new(Id::unpositioned("a"), Kind::Star);
        let v2 = TyVar::new(Id::unpositioned("b"), Kind::Star);

        ctx.enter_scope(vec![v1.clone()]);
        assert!(ctx.is_bound(&v1));
        assert!(!ctx.is_bound(&v2));

        ctx.enter_scope(vec![v2.clone()]);
        assert!(ctx.is_bound(&v1));
        assert!(ctx.is_bound(&v2));

        let exited = ctx.exit_scope();
        assert_eq!(exited, vec![v2.clone()]);
        assert!(ctx.is_bound(&v1));
        assert!(!ctx.is_bound(&v2));
    }

    #[test]
    fn test_error_recording() {
        let ctx = TypeCheckContext::new();
        assert!(!ctx.has_errors());

        ctx.record_error(TypeError::UndefinedVar {
            name: "x".to_string(),
            span: Span::DUMMY.into(),
        });

        assert!(ctx.has_errors());
        assert_eq!(ctx.error_count(), 1);

        let errors = ctx.take_errors();
        assert_eq!(errors.len(), 1);
        assert!(!ctx.has_errors());
    }

    #[test]
    fn test_unify_same_var() {
        let mut ctx = TypeCheckContext::new();
        let t1 = ctx.new_tvar(Kind::Star);
        let t2 = t1.clone();

        assert!(ctx.unify(&t1, &t2).is_ok());
    }

    #[test]
    fn test_unify_different_vars() {
        let mut ctx = TypeCheckContext::new();
        let t1 = ctx.new_tvar(Kind::Star);
        let t2 = ctx.new_tvar(Kind::Star);

        assert!(ctx.unify(&t1, &t2).is_ok());

        // After unification, applying subst should give same result
        let s1 = ctx.apply_subst(&t1);
        let s2 = ctx.apply_subst(&t2);
        assert_eq!(s1, s2);
    }

    #[test]
    fn test_make_fun_type() {
        let arg = make_bool_type();
        let result = make_integer_type();
        let fun_ty = make_fun_type(arg.clone(), result.clone());

        let split = split_fun_type(&fun_ty);
        assert!(split.is_some());
        let (a, r) = split.expect("checked some");
        assert_eq!(a, &arg);
        assert_eq!(r, &result);
    }
}
