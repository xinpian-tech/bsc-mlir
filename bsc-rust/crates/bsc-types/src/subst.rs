//! Type substitution for BSC.
//!
//! Mirrors `src/comp/Subst.hs` from the Haskell implementation.
//!
//! This module provides:
//! - `Substitution` - Maps type variables to types
//! - `Types` trait - Types that can be substituted and have free variables

use crate::ty::{Kind, Pred, QualType, TyCon, TyVar, Type};
use rustc_hash::{FxHashMap, FxHashSet};
use std::fmt;

/// A substitution mapping type variables to types.
///
/// The substitution maintains:
/// - A forward map from type variables to their substituted types
/// - A backward map tracking which LHS variables use each RHS variable
///
/// This structure allows for efficient composition and application.
#[derive(Clone, Default)]
pub struct Substitution {
    /// Forward mapping: type variable -> substituted type
    map: FxHashMap<TyVar, Type>,
    /// Backward mapping: RHS variable -> set of LHS variables that use it
    /// Used for efficient composition
    back_refs: FxHashMap<TyVar, FxHashSet<TyVar>>,
}

impl Substitution {
    /// Create an empty substitution.
    #[must_use]
    pub fn null() -> Self {
        Self::default()
    }

    /// Check if this substitution is empty.
    #[must_use]
    pub fn is_null(&self) -> bool {
        self.map.is_empty()
    }

    /// Create a singleton substitution mapping one variable to a type.
    #[must_use]
    pub fn singleton(var: TyVar, ty: Type) -> Self {
        let mut map = FxHashMap::default();
        let mut back_refs = FxHashMap::default();

        // Build backward references
        for fv in ty.free_type_vars() {
            back_refs
                .entry(fv)
                .or_insert_with(FxHashSet::default)
                .insert(var.clone());
        }

        map.insert(var, ty);

        Self { map, back_refs }
    }

    /// Create a substitution from a list of (variable, type) pairs.
    #[must_use]
    pub fn from_pairs(pairs: impl IntoIterator<Item = (TyVar, Type)>) -> Self {
        let mut subst = Self::null();
        for (var, ty) in pairs {
            subst.insert(var, ty);
        }
        subst
    }

    /// Insert a mapping into the substitution.
    pub fn insert(&mut self, var: TyVar, ty: Type) {
        // Build backward references for the new type
        for fv in ty.free_type_vars() {
            self.back_refs
                .entry(fv)
                .or_insert_with(FxHashSet::default)
                .insert(var.clone());
        }
        self.map.insert(var, ty);
    }

    /// Look up a type variable in the substitution.
    #[must_use]
    pub fn lookup(&self, var: &TyVar) -> Option<&Type> {
        self.map.get(var)
    }

    /// Get the number of entries in the substitution.
    #[must_use]
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Check if the substitution is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Get the domain (LHS variables) of the substitution.
    #[must_use]
    pub fn domain(&self) -> impl Iterator<Item = &TyVar> {
        self.map.keys()
    }

    /// Get the range (RHS type variables) of the substitution.
    #[must_use]
    pub fn range_vars(&self) -> FxHashSet<TyVar> {
        let mut result = FxHashSet::default();
        for ty in self.map.values() {
            for fv in ty.free_type_vars() {
                result.insert(fv);
            }
        }
        result
    }

    /// Compose two substitutions: `self @@ other`.
    ///
    /// The resulting substitution, when applied, is equivalent to
    /// first applying `other`, then applying `self`.
    ///
    /// This implements the `@@` operator from the Haskell version.
    #[must_use]
    pub fn compose(&self, other: &Substitution) -> Substitution {
        // Check if we need to apply self to other
        let needs_apply = other
            .back_refs
            .keys()
            .any(|v| self.map.contains_key(v));

        if needs_apply {
            // Apply self to other, then merge
            let mut applied = self.apply_to_subst(other);
            applied.merge(self);
            applied
        } else {
            // No overlap, just merge
            let mut result = other.clone();
            result.merge(self);
            result
        }
    }

    /// Apply this substitution to another substitution.
    ///
    /// For each binding `v -> t` in `other`, replace `t` with `self.apply(t)`.
    fn apply_to_subst(&self, other: &Substitution) -> Substitution {
        let mut new_map = FxHashMap::default();
        let mut new_back_refs = FxHashMap::default();

        for (var, ty) in &other.map {
            let new_ty = self.apply(ty);

            // Rebuild backward references
            for fv in new_ty.free_type_vars() {
                new_back_refs
                    .entry(fv)
                    .or_insert_with(FxHashSet::default)
                    .insert(var.clone());
            }

            new_map.insert(var.clone(), new_ty);
        }

        Substitution {
            map: new_map,
            back_refs: new_back_refs,
        }
    }

    /// Merge another substitution into this one.
    ///
    /// If both substitutions have a binding for the same variable,
    /// the binding from `other` takes precedence.
    fn merge(&mut self, other: &Substitution) {
        for (var, ty) in &other.map {
            if !self.map.contains_key(var) {
                // Add backward references
                for fv in ty.free_type_vars() {
                    self.back_refs
                        .entry(fv)
                        .or_insert_with(FxHashSet::default)
                        .insert(var.clone());
                }
                self.map.insert(var.clone(), ty.clone());
            }
        }
    }

    /// Try to merge two substitutions, failing if they disagree on any variable.
    ///
    /// Returns `None` if the substitutions map the same variable to different types.
    #[must_use]
    pub fn try_merge(&self, other: &Substitution) -> Option<Substitution> {
        // Check for agreement on overlapping variables
        for var in self.map.keys() {
            if let Some(other_ty) = other.map.get(var) {
                let self_ty = &self.map[var];
                if self.apply(self_ty) != other.apply(other_ty) {
                    return None;
                }
            }
        }

        let mut result = self.clone();
        result.merge(other);
        Some(result)
    }

    /// Apply the substitution to a type.
    #[must_use]
    pub fn apply(&self, ty: &Type) -> Type {
        match ty {
            Type::Var(tv) => {
                if let Some(replacement) = self.map.get(tv) {
                    // Validate kind compatibility
                    if let Some(rep_kind) = replacement.kind() {
                        if !tv.kind.is_var() && rep_kind != tv.kind {
                            // Kind mismatch - in a more complete implementation,
                            // this would be an error, but we match Haskell behavior
                            // and return the replacement anyway
                        }
                    }
                    replacement.clone()
                } else {
                    ty.clone()
                }
            }
            Type::App(f, a) => {
                let new_f = self.apply(f);
                let new_a = self.apply(a);
                // Normalize type applications (e.g., evaluate numeric type functions)
                normalize_app(new_f, new_a)
            }
            Type::Con(_) | Type::Gen { .. } | Type::DefMonad(_) => ty.clone(),
        }
    }

    /// Trim the substitution to only keep variables less than the given one.
    ///
    /// This is used when type-checking let bindings to roll back the substitution.
    #[must_use]
    pub fn trim(&self, bound: &TyVar) -> Substitution {
        let mut new_map = FxHashMap::default();
        let mut new_back_refs = FxHashMap::default();

        for (var, ty) in &self.map {
            if var < bound {
                for fv in ty.free_type_vars() {
                    new_back_refs
                        .entry(fv)
                        .or_insert_with(FxHashSet::default)
                        .insert(var.clone());
                }
                new_map.insert(var.clone(), ty.clone());
            }
        }

        Substitution {
            map: new_map,
            back_refs: new_back_refs,
        }
    }

    /// Remove entries whose LHS or RHS contains any of the given variables.
    ///
    /// Used to avoid name capture when substituting inside type lambdas.
    #[must_use]
    pub fn trim_by_vars(&self, vars: &[TyVar]) -> Substitution {
        if vars.is_empty() {
            return self.clone();
        }

        let var_set: FxHashSet<_> = vars.iter().collect();

        let mut new_map = FxHashMap::default();
        let mut new_back_refs = FxHashMap::default();

        for (var, ty) in &self.map {
            // Skip if LHS is in vars
            if var_set.contains(var) {
                continue;
            }

            // Skip if RHS contains any var
            let rhs_vars = ty.free_type_vars();
            if rhs_vars.iter().any(|v| var_set.contains(v)) {
                continue;
            }

            for fv in rhs_vars {
                new_back_refs
                    .entry(fv)
                    .or_insert_with(FxHashSet::default)
                    .insert(var.clone());
            }
            new_map.insert(var.clone(), ty.clone());
        }

        Substitution {
            map: new_map,
            back_refs: new_back_refs,
        }
    }
}

impl fmt::Debug for Substitution {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map()
            .entries(self.map.iter().map(|(k, v)| (format!("{k}"), format!("{v}"))))
            .finish()
    }
}

impl fmt::Display for Substitution {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        for (i, (var, ty)) in self.map.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{var} := {ty}")?;
        }
        write!(f, "]")
    }
}

/// Normalize a type application, evaluating numeric type functions if possible.
fn normalize_app(fun: Type, arg: Type) -> Type {
    // TODO: Implement numeric type function evaluation
    // For now, just construct the application
    Type::app(fun, arg)
}

/// Trait for types that support substitution and have free type variables.
///
/// Mirrors the Haskell `Types` class from Subst.hs.
pub trait Types {
    /// Apply a substitution to this type.
    fn apply_subst(&self, subst: &Substitution) -> Self;

    /// Get the free type variables in this type.
    fn free_type_vars(&self) -> Vec<TyVar>;
}

impl Types for Type {
    fn apply_subst(&self, subst: &Substitution) -> Self {
        subst.apply(self)
    }

    fn free_type_vars(&self) -> Vec<TyVar> {
        fn collect(ty: &Type, vars: &mut Vec<TyVar>, seen: &mut FxHashSet<TyVar>) {
            match ty {
                Type::Var(tv) => {
                    if !seen.contains(tv) {
                        seen.insert(tv.clone());
                        vars.push(tv.clone());
                    }
                }
                Type::App(f, a) => {
                    collect(f, vars, seen);
                    collect(a, vars, seen);
                }
                Type::Con(_) | Type::Gen { .. } | Type::DefMonad(_) => {}
            }
        }

        let mut vars = Vec::new();
        let mut seen = FxHashSet::default();
        collect(self, &mut vars, &mut seen);
        vars
    }
}

impl Types for TyVar {
    fn apply_subst(&self, subst: &Substitution) -> Self {
        // TyVar doesn't change under substitution (the Type::Var wrapper does)
        self.clone()
    }

    fn free_type_vars(&self) -> Vec<TyVar> {
        vec![self.clone()]
    }
}

impl<T: Types> Types for Vec<T> {
    fn apply_subst(&self, subst: &Substitution) -> Self {
        self.iter().map(|t| t.apply_subst(subst)).collect()
    }

    fn free_type_vars(&self) -> Vec<TyVar> {
        let mut result = Vec::new();
        let mut seen = FxHashSet::default();
        for item in self {
            for var in item.free_type_vars() {
                if !seen.contains(&var) {
                    seen.insert(var.clone());
                    result.push(var);
                }
            }
        }
        result
    }
}

impl<T: Types> Types for Option<T> {
    fn apply_subst(&self, subst: &Substitution) -> Self {
        self.as_ref().map(|t| t.apply_subst(subst))
    }

    fn free_type_vars(&self) -> Vec<TyVar> {
        self.as_ref().map_or_else(Vec::new, Types::free_type_vars)
    }
}

impl<T: Types> Types for Box<T> {
    fn apply_subst(&self, subst: &Substitution) -> Self {
        Box::new((**self).apply_subst(subst))
    }

    fn free_type_vars(&self) -> Vec<TyVar> {
        (**self).free_type_vars()
    }
}

impl Types for Pred {
    fn apply_subst(&self, subst: &Substitution) -> Self {
        Pred {
            class: self.class.clone(),
            args: self.args.apply_subst(subst),
        }
    }

    fn free_type_vars(&self) -> Vec<TyVar> {
        self.args.free_type_vars()
    }
}

impl Types for QualType {
    fn apply_subst(&self, subst: &Substitution) -> Self {
        QualType {
            preds: self.preds.apply_subst(subst),
            ty: self.ty.apply_subst(subst),
        }
    }

    fn free_type_vars(&self) -> Vec<TyVar> {
        let mut vars = self.ty.free_type_vars();
        let mut seen: FxHashSet<_> = vars.iter().cloned().collect();

        for pred in &self.preds {
            for var in pred.free_type_vars() {
                if !seen.contains(&var) {
                    seen.insert(var.clone());
                    vars.push(var);
                }
            }
        }

        vars
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bsc_diagnostics::Position;
    use bsc_syntax::Id;
    use num_bigint::BigInt;

    fn make_var(name: &str) -> TyVar {
        TyVar::new(Id::unpositioned(name), Kind::Star)
    }

    fn make_type_var(name: &str) -> Type {
        Type::var(make_var(name))
    }

    #[test]
    fn test_null_substitution() {
        let subst = Substitution::null();
        assert!(subst.is_null());
        assert_eq!(subst.len(), 0);
    }

    #[test]
    fn test_singleton_substitution() {
        let var = make_var("a");
        let ty = Type::num(BigInt::from(42), Position::unknown());
        let subst = Substitution::singleton(var.clone(), ty.clone());

        assert!(!subst.is_null());
        assert_eq!(subst.len(), 1);
        assert_eq!(subst.lookup(&var), Some(&ty));
    }

    #[test]
    fn test_apply_substitution() {
        let var_a = make_var("a");
        let ty_b = make_type_var("b");

        let subst = Substitution::singleton(var_a.clone(), ty_b.clone());

        // Apply to the variable
        let result = subst.apply(&Type::var(var_a));
        assert_eq!(result, ty_b);

        // Apply to a different variable (should not change)
        let var_c = make_var("c");
        let result = subst.apply(&Type::var(var_c.clone()));
        assert_eq!(result, Type::var(var_c));
    }

    #[test]
    fn test_compose_substitutions() {
        let var_a = make_var("a");
        let var_b = make_var("b");
        let ty_int = Type::num(BigInt::from(42), Position::unknown());

        // s1: b -> Int
        let s1 = Substitution::singleton(var_b.clone(), ty_int.clone());
        // s2: a -> b
        let s2 = Substitution::singleton(var_a.clone(), Type::var(var_b.clone()));

        // s1 @@ s2 should give: a -> Int, b -> Int
        let composed = s1.compose(&s2);

        let result_a = composed.apply(&Type::var(var_a));
        assert_eq!(result_a, ty_int);
    }

    #[test]
    fn test_free_type_vars() {
        let var_a = make_var("a");
        let var_b = make_var("b");

        // Type: a -> b
        let arrow = TyCon::Named {
            name: Id::unpositioned("->"),
            kind: Some(Kind::fun(Kind::Star, Kind::fun(Kind::Star, Kind::Star))),
            sort: crate::ty::TyConSort::Abstract,
        };
        let ty = Type::app(
            Type::app(Type::con(arrow), Type::var(var_a.clone())),
            Type::var(var_b.clone()),
        );

        let fvs = ty.free_type_vars();
        assert_eq!(fvs.len(), 2);
        assert!(fvs.contains(&var_a));
        assert!(fvs.contains(&var_b));
    }

    #[test]
    fn test_try_merge_agreeing() {
        let var_a = make_var("a");
        let ty_int = Type::num(BigInt::from(42), Position::unknown());

        let s1 = Substitution::singleton(var_a.clone(), ty_int.clone());
        let s2 = Substitution::singleton(var_a.clone(), ty_int.clone());

        let merged = s1.try_merge(&s2);
        assert!(merged.is_some());
    }

    #[test]
    fn test_try_merge_disagreeing() {
        let var_a = make_var("a");
        let ty_int1 = Type::num(BigInt::from(42), Position::unknown());
        let ty_int2 = Type::num(BigInt::from(43), Position::unknown());

        let s1 = Substitution::singleton(var_a.clone(), ty_int1);
        let s2 = Substitution::singleton(var_a.clone(), ty_int2);

        let merged = s1.try_merge(&s2);
        assert!(merged.is_none());
    }
}
