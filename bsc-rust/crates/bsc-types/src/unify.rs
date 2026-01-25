//! Unification algorithm for BSC types.
//!
//! Mirrors `src/comp/Unify.hs` from the Haskell implementation.
//!
//! This module provides:
//! - `unify` - Unify two types, returning a substitution
//! - `match_type` - One-way matching (only instantiates the first type)
//! - Special handling for numeric type unification

use crate::subst::{Substitution, Types};
use crate::ty::{Kind, TyCon, TyConSort, TyVar, Type};
use miette::SourceSpan;
use thiserror::Error;

/// Errors that can occur during unification.
#[derive(Debug, Error, miette::Diagnostic)]
pub enum UnifyError {
    /// Types cannot be unified
    #[error("cannot unify types: {t1} and {t2}")]
    CannotUnify {
        t1: String,
        t2: String,
        #[label("type mismatch")]
        span: Option<SourceSpan>,
    },

    /// Occurs check failure (infinite type)
    #[error("occurs check failed: {var} occurs in {ty}")]
    OccursCheck {
        var: String,
        ty: String,
        #[label("would create infinite type")]
        span: Option<SourceSpan>,
    },

    /// Kind mismatch
    #[error("kind mismatch: expected {expected}, found {found}")]
    KindMismatch {
        expected: String,
        found: String,
        #[label("kind mismatch")]
        span: Option<SourceSpan>,
    },

    /// Cannot bind to unsaturated type synonym
    #[error("cannot bind variable to unsaturated type synonym")]
    UnsaturatedTypeSyn {
        #[label("unsaturated type synonym")]
        span: Option<SourceSpan>,
    },

    /// Bound type variables cannot be unified with each other
    #[error("cannot unify bound type variables {v1} and {v2}")]
    BoundVarConflict {
        v1: String,
        v2: String,
        #[label("bound variable conflict")]
        span: Option<SourceSpan>,
    },
}

impl UnifyError {
    /// Create a CannotUnify error.
    #[must_use]
    pub fn cannot_unify(t1: &Type, t2: &Type) -> Self {
        UnifyError::CannotUnify {
            t1: format!("{t1}"),
            t2: format!("{t2}"),
            span: None,
        }
    }

    /// Create an OccursCheck error.
    #[must_use]
    pub fn occurs_check(var: &TyVar, ty: &Type) -> Self {
        UnifyError::OccursCheck {
            var: format!("{var}"),
            ty: format!("{ty}"),
            span: None,
        }
    }

    /// Create a KindMismatch error.
    #[must_use]
    pub fn kind_mismatch(expected: &Kind, found: &Kind) -> Self {
        UnifyError::KindMismatch {
            expected: format!("{expected}"),
            found: format!("{found}"),
            span: None,
        }
    }
}

/// Result of unification, containing:
/// - The unifying substitution
/// - A list of numeric type equalities that need to be checked by the constraint solver
pub type UnifyResult = Result<(Substitution, Vec<(Type, Type)>), UnifyError>;

/// Unify two types, returning a substitution that makes them equal.
///
/// # Arguments
/// - `bound_tyvars` - Type variables that are bound (e.g., by a type lambda)
///   and should not be substituted with other type variables
/// - `t1`, `t2` - The types to unify
///
/// # Returns
/// - `Ok((subst, eqs))` - The unifying substitution and numeric equalities to check
/// - `Err(e)` - If the types cannot be unified
pub fn unify(bound_tyvars: &[TyVar], t1: &Type, t2: &Type) -> UnifyResult {
    // Check if we're dealing with numeric kinds
    if let (Some(Kind::Num), Some(Kind::Num)) = (t1.kind(), t2.kind()) {
        return num_unify(bound_tyvars, t1, t2);
    }

    match (t1, t2) {
        // Type application: unify both parts
        (Type::App(f1, a1), Type::App(f2, a2)) => {
            let (s1, eqs1) = unify(bound_tyvars, f1, f2)?;
            let a1_subst = s1.apply(a1);
            let a2_subst = s1.apply(a2);
            let (s2, eqs2) = unify(bound_tyvars, &a1_subst, &a2_subst)?;
            let composed = s2.compose(&s1);
            let mut eqs = eqs1;
            for eq in eqs2 {
                if !eqs.contains(&eq) {
                    eqs.push(eq);
                }
            }
            Ok((composed, eqs))
        }

        // Two type variables
        (Type::Var(u), Type::Var(v)) => var_unify(bound_tyvars, u, v, t1, t2),

        // Type variable with another type
        (Type::Var(u), t) | (t, Type::Var(u)) => var_bind_with_eqs(u, t),

        // Two type constructors: must be equal
        (Type::Con(c1), Type::Con(c2)) if c1 == c2 => Ok((Substitution::null(), vec![])),

        // Nothing else can be unified
        _ => Err(UnifyError::cannot_unify(t1, t2)),
    }
}

/// Unify numeric types.
///
/// Numeric types require special handling because we may need to defer
/// equality constraints to the constraint solver.
fn num_unify(bound_tyvars: &[TyVar], t1: &Type, t2: &Type) -> UnifyResult {
    // Equal types unify trivially
    if t1 == t2 {
        return Ok((Substitution::null(), vec![]));
    }

    match (t1, t2) {
        // Two different numeric literals cannot unify
        (Type::Con(TyCon::TyNum { value: n1, .. }), Type::Con(TyCon::TyNum { value: n2, .. }))
            if n1 != n2 =>
        {
            Err(UnifyError::cannot_unify(t1, t2))
        }

        // Two type variables
        (Type::Var(u), Type::Var(v)) => match var_unify(bound_tyvars, u, v, t1, t2) {
            Err(_) => {
                // If we can't unify them directly, defer to constraint solver
                Ok((Substitution::null(), vec![(t1.clone(), t2.clone())]))
            }
            ok => ok,
        },

        // Variable with non-variable: check if we can bind
        (Type::Var(u), t) | (t, Type::Var(u)) => {
            let t_vars = t.free_type_vars();

            // Don't bind if u is bound or occurs in t
            if !bound_tyvars.contains(u) && !t_vars.contains(u) {
                var_bind_with_eqs(u, t)
            } else {
                // Defer to constraint solver
                Ok((Substitution::null(), vec![(t1.clone(), t2.clone())]))
            }
        }

        // For complex numeric types, defer to constraint solver
        _ => Ok((Substitution::null(), vec![(t1.clone(), t2.clone())])),
    }
}

/// Unify two type variables.
fn var_unify(
    bound_tyvars: &[TyVar],
    u: &TyVar,
    v: &TyVar,
    tu: &Type,
    tv: &Type,
) -> UnifyResult {
    // Same variable: trivial
    if u == v {
        return Ok((Substitution::null(), vec![]));
    }

    let u_bound = bound_tyvars.contains(u);
    let v_bound = bound_tyvars.contains(v);

    match (u_bound, v_bound) {
        // Both bound: cannot unify
        (true, true) => Err(UnifyError::BoundVarConflict {
            v1: format!("{u}"),
            v2: format!("{v}"),
            span: None,
        }),

        // u bound, v not: bind v to u
        (true, false) => var_bind_with_eqs(v, tu),

        // v bound, u not: bind u to v
        (false, true) => var_bind_with_eqs(u, tv),

        // Neither bound
        (false, false) => {
            // Prefer to bind generated variables
            let u_gen = u.is_generated();
            let v_gen = v.is_generated();

            match (u_gen, v_gen) {
                // Both generated: bind the newer one (higher num)
                (true, true) => {
                    if u.num > v.num {
                        var_bind_with_eqs(u, tv)
                    } else {
                        var_bind_with_eqs(v, tu)
                    }
                }
                // Only u generated: bind u
                (true, false) => var_bind_with_eqs(u, tv),
                // Only v generated: bind v
                (false, true) => var_bind_with_eqs(v, tu),
                // Neither generated: arbitrarily bind u
                (false, false) => var_bind_with_eqs(u, tv),
            }
        }
    }
}

/// Bind a type variable to a type, returning empty equations.
fn var_bind_with_eqs(var: &TyVar, ty: &Type) -> UnifyResult {
    var_bind(var, ty).map(|s| (s, vec![]))
}

/// Bind a type variable to a type.
fn var_bind(var: &TyVar, ty: &Type) -> Result<Substitution, UnifyError> {
    // Don't bind to self
    if let Type::Var(tv) = ty {
        if var == tv {
            return Ok(Substitution::null());
        }
    }

    // Check for unsaturated type synonym
    if is_unsaturated_syn(ty) {
        return Err(UnifyError::UnsaturatedTypeSyn { span: None });
    }

    // Occurs check
    let fvs = ty.free_type_vars();
    if fvs.contains(var) {
        return Err(UnifyError::occurs_check(var, ty));
    }

    // Kind check
    if let Some(ty_kind) = ty.kind() {
        if !var.kind.is_var() && ty_kind != var.kind {
            return Err(UnifyError::kind_mismatch(&var.kind, &ty_kind));
        }
    }

    Ok(Substitution::singleton(var.clone(), ty.clone()))
}

/// Check if a type is an unsaturated type synonym.
fn is_unsaturated_syn(ty: &Type) -> bool {
    is_unsaturated_syn_with_args(ty, 0)
}

fn is_unsaturated_syn_with_args(ty: &Type, args: u64) -> bool {
    use num_bigint::BigInt;

    match ty {
        Type::Con(TyCon::Named {
            sort: TyConSort::TypeSyn { arity, .. },
            ..
        }) => *arity > BigInt::from(args),
        Type::App(f, _) => is_unsaturated_syn_with_args(f, args + 1),
        _ => false,
    }
}

/// One-way type matching: find a substitution that makes t1 equal to t2.
///
/// Unlike unification, this only instantiates variables in t1.
pub fn match_type(t1: &Type, t2: &Type) -> Result<Substitution, UnifyError> {
    match (t1, t2) {
        (Type::App(f1, a1), Type::App(f2, a2)) => {
            let s1 = match_type(f1, f2)?;
            let s2 = match_type(a1, a2)?;
            s1.try_merge(&s2)
                .ok_or_else(|| UnifyError::cannot_unify(t1, t2))
        }

        (Type::Var(u1), Type::Var(u2)) if u1 == u2 => Ok(Substitution::null()),

        (Type::Var(u), t) => {
            if let Some(tk) = t.kind() {
                if u.kind == tk {
                    return Ok(Substitution::singleton(u.clone(), t.clone()));
                }
            }
            Err(UnifyError::cannot_unify(t1, t2))
        }

        (Type::Con(c1), Type::Con(c2)) if c1 == c2 => Ok(Substitution::null()),

        _ => Err(UnifyError::cannot_unify(t1, t2)),
    }
}

/// Match a list of types against another list.
pub fn match_types(ts1: &[Type], ts2: &[Type]) -> Result<Substitution, UnifyError> {
    if ts1.len() != ts2.len() {
        return Err(UnifyError::CannotUnify {
            t1: format!("[{} types]", ts1.len()),
            t2: format!("[{} types]", ts2.len()),
            span: None,
        });
    }

    let mut result = Substitution::null();
    for (t1, t2) in ts1.iter().zip(ts2.iter()) {
        let s = match_type(t1, t2)?;
        result = result
            .try_merge(&s)
            .ok_or_else(|| UnifyError::cannot_unify(t1, t2))?;
    }
    Ok(result)
}

/// Trait for types that can be unified.
pub trait Unify {
    /// Most general unifier.
    fn mgu(&self, other: &Self, bound_tyvars: &[TyVar]) -> UnifyResult;
}

impl Unify for Type {
    fn mgu(&self, other: &Self, bound_tyvars: &[TyVar]) -> UnifyResult {
        unify(bound_tyvars, self, other)
    }
}

impl<T: Unify + Types> Unify for Vec<T> {
    fn mgu(&self, other: &Self, bound_tyvars: &[TyVar]) -> UnifyResult {
        if self.len() != other.len() {
            return Err(UnifyError::CannotUnify {
                t1: format!("[{} elements]", self.len()),
                t2: format!("[{} elements]", other.len()),
                span: None,
            });
        }

        let mut subst = Substitution::null();
        let mut eqs = Vec::new();

        for (x, y) in self.iter().zip(other.iter()) {
            let x_subst = x.apply_subst(&subst);
            let y_subst = y.apply_subst(&subst);
            let (s, new_eqs) = x_subst.mgu(&y_subst, bound_tyvars)?;
            subst = s.compose(&subst);
            for eq in new_eqs {
                if !eqs.contains(&eq) {
                    eqs.push(eq);
                }
            }
        }

        Ok((subst, eqs))
    }
}

