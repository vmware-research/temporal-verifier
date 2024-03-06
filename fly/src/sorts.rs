// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Infer and check sorts.
//!
//! Throughout this file we use "sort checking" and "sort inference" interchangeably.
//!
//! The main entry points are [sort_check_module], [sort_check_term],
//! and the [Scope] struct.
//!
//! The parser represents missing sort annotations as `Sort::Uninterpreted("")`.
//! One of the main purposes of sort inference is to replace these placeholders
//! with proper sort annotations. Sort inference is combined with sort checking,
//! so another main purpose of this module is to make sure the given fly program
//! is well sorted.
//!
//! Note that sort inference is a *mutable* operation on the AST! Sort inference will
//! write its results back into the AST so that future passes can easily find
//! the type of a bound variable.
//!
//! Sort inference allows the user to leave off the sort annotation of most
//! quantified variables. Internally, it uses unification to discover the
//! missing sorts. The sorts on arguments to definitions are required to be
//! given explicitly. (This last requirement is enforced by the parser.)
//!
//! If sort checking detects an error (see [SortError]), it will attempt to
//! provide a [Span] to locate this error in the source code. The AST has
//! limited span information, so some errors will be returned without location
//! information (the span will be `None` in that case).

use crate::syntax::*;
use ena::unify::{UnifyKey, UnifyValue};
use itertools::Itertools;
use std::collections::HashSet;
use thiserror::Error;

/// An error encountered during sort checking
#[derive(Error, Debug, PartialEq)]
pub enum SortError {
    /// The program referred to an uninterpreted sort that was not declared.
    #[error("sort {0} was not declared")]
    UnknownSort(String),
    /// An uninterpreted sort was declared multiple times.
    #[error("sort {0} was declared multiple times")]
    RedeclaredSort(String),

    /// The program referred to a variable that was not declared.
    #[error("unknown variable/constant {0}")]
    UnknownVariable(String),
    /// The program referred to a function that was not declared.
    #[error("unknown function/definition {0}")]
    UnknownFunction(String),
    /// A name was declared multiple times in a context that did not allow shadowing.
    #[error("{0} was declared multiple times")]
    RedeclaredName(String),

    /// Sort inference detected a conflict between two sorts.
    #[error("could not unify {0} and {1}")]
    UnificationFail(Sort, Sort),
    /// Sort checking detected a mismatch between the expected and actual sorts of a term.
    #[error("expected {expected} but found {found}")]
    ExpectedButFoundSorts {
        /// Expected sort coming from sort annotations
        expected: Sort,
        #[allow(missing_docs)]
        found: Sort,
    },
    /// A function or definition was applied to the wrong number of arguments.
    #[allow(missing_docs)]
    #[error("function {function_name} expected {expected} args but found {found} args")]
    ExpectedButFoundArity {
        function_name: String,
        expected: usize,
        found: usize,
    },

    /// A function/definition was referred to without passing any arguments.
    #[error("{0} is a function/definition that takes arguments, but no arguments were passed")]
    Uncalled(String),
    /// A constant or variable was called like a function.
    #[error("{0} was called but it is not a function/definition")]
    Uncallable(String),

    /// Sort inference finished without gaining enough information to figure out
    /// the sort of the given variable or term.
    #[error("could not solve for the sort of {0}")]
    UnsolvedSort(String),
}

/// Sort check a module, including inferring sorts for bound variables.
pub fn sort_check_module(module: &mut Module) -> Result<(), (SortError, Option<Span>)> {
    Scope::new(&module.signature.clone())
        .map_err(|e| (e, None))?
        .sort_check_module(module)
}

/// Sort check the term in the given signature, including inferring sorts for bound variables.
pub fn sort_check_term(signature: &Signature, term: &mut Term) -> Result<Sort, SortError> {
    Scope::new(signature)?.sort_check_term(term)
}

/// Return whether every quantified variable in every term in the given fly
/// module has a (non-empty) sort annotation.
pub fn has_all_sort_annotations_module(module: &Module) -> bool {
    // This function should be kept in sync with the parser. Currently the
    // parser only generates Sort::Uninterpreted("") on quantified variables, so
    // that is the only place we need to check. If future changes to the parser
    // introduce more opportunities for sort inference, then this function
    // should be adjusted as well.

    module
        .defs
        .iter()
        .all(|def| has_all_sort_annotations_term(&def.body))
        && module.statements.iter().all(|statement| match statement {
            ThmStmt::Assume(term) => has_all_sort_annotations_term(term),
            ThmStmt::Assert(proof) => {
                proof
                    .invariants
                    .iter()
                    .all(|inv| has_all_sort_annotations_term(&inv.x))
                    && has_all_sort_annotations_term(&proof.assert.x)
            }
        })
}

/// Return whether every quantified variable in this term has a (non-empty) sort
/// annotation.
pub fn has_all_sort_annotations_term(term: &Term) -> bool {
    match term {
        Term::Literal(_) | Term::Id(_) => true,
        Term::App(_f, _p, xs) => xs.iter().all(has_all_sort_annotations_term),
        Term::UnaryOp(_, x) => has_all_sort_annotations_term(x),
        Term::BinOp(_, x, y) => {
            has_all_sort_annotations_term(x) && has_all_sort_annotations_term(y)
        }
        Term::NAryOp(_, xs) => xs.iter().all(has_all_sort_annotations_term),
        Term::Ite { cond, then, else_ } => {
            has_all_sort_annotations_term(cond)
                && has_all_sort_annotations_term(then)
                && has_all_sort_annotations_term(else_)
        }
        Term::Quantified {
            quantifier: _,
            binders,
            body,
        } => {
            binders.iter().all(|binder| binder.sort != Sort::unknown())
                && has_all_sort_annotations_term(body)
        }
    }
}

/// Represents the sort of a name, which can either name a relation or an individual.
/// Relations (including functions) always take at least one argument.
/// Individuals can additionally have "unknown" sort, which will be determined during sort inference.
#[derive(Clone, Debug)]
enum RelationOrIndividual {
    Relation(Vec<Sort> /* always nonempty */, Sort),
    Individual(MaybeUnknownSort),
}

impl RelationOrIndividual {
    fn args_ret(args: &[Sort], ret: &Sort) -> RelationOrIndividual {
        if args.is_empty() {
            Self::known(ret)
        } else {
            Self::Relation(args.to_owned(), ret.clone())
        }
    }

    fn definition(decl: &Definition) -> RelationOrIndividual {
        Self::args_ret(
            &decl.binders.iter().map(|b| b.sort.clone()).collect_vec(),
            &decl.ret_sort,
        )
    }

    fn relation(decl: &RelationDecl) -> RelationOrIndividual {
        Self::args_ret(&decl.args, &decl.sort)
    }

    fn known(sort: &Sort) -> RelationOrIndividual {
        Self::Individual(MaybeUnknownSort::Known(sort.clone()))
    }

    fn unknown(sort_var: SortVar) -> RelationOrIndividual {
        Self::Individual(MaybeUnknownSort::Unknown(sort_var))
    }
}

/// Represents a either known sort or an unknown sort (unification variable).
#[derive(Clone, Debug, PartialEq, Eq)]
enum MaybeUnknownSort {
    Known(Sort),
    Unknown(SortVar),
}

// wrappers to implement ena::unify traits on
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
struct SortVar(u32);
#[derive(Clone, Debug, PartialEq)]
struct OptionSort(Option<Sort>);

impl UnifyKey for SortVar {
    type Value = OptionSort;
    fn index(&self) -> u32 {
        self.0
    }
    fn from_index(u: u32) -> SortVar {
        SortVar(u)
    }
    fn tag() -> &'static str {
        "SortVar"
    }
}

impl UnifyValue for OptionSort {
    type Error = SortError;
    fn unify_values(a: &OptionSort, b: &OptionSort) -> Result<OptionSort, SortError> {
        match (&a.0, &b.0) {
            (None, None) => Ok(OptionSort(None)),
            (None, a @ Some(_)) | (a @ Some(_), None) => Ok(OptionSort(a.clone())),
            (Some(x), Some(y)) if x == y => Ok(OptionSort(Some(x.clone()))),
            (Some(x), Some(y)) => Err(SortError::UnificationFail(x.clone(), y.clone())),
        }
    }
}

#[derive(PartialEq, Eq, Clone, Copy)]
enum ShadowingConstraint {
    Allow,
    Disallow,
}

/// A scope for sort checking, which includes information about global symbols (sorts, relations)
/// and locally bound variables.
// Rep invariant for Scope and InternalContext:
// - (always) the signature has no spaces in any sort names
// - (between public calls) bound_names contains only Known sorts
// - (always) every var in bound_names with Known(sort) actually exists in the signature
// - (always) every var in bound_names with Unknown(sort_var) is a valid key in the unification table
// - (always) all values stored in the unification table are sorts that exist in the signature
// - (between public calls) the unification table is conceptually empty (it will be replaced at the
//   beginning of the next public call)
//
// Note that the second bullet point is enforced by the public API, but violated internally during
// sort inference (to store unknown sorts).
#[derive(Clone)]
pub struct Scope<'a> {
    /// The underlying signature for this scope
    pub signature: &'a Signature,
    bound_names: im::HashMap<String, RelationOrIndividual>,
}

impl Scope<'_> {
    /// Create a new scope from a signature. Initially the names bound by the scope are exactly
    /// the relations in the signature.
    ///
    /// This function also checks that the signature is well formed in the sense that all the sorts
    /// mentioned by the relations exist.
    pub fn new(signature: &Signature) -> Result<Scope, SortError> {
        let mut sorts = HashSet::new();
        for sort in &signature.sorts {
            // This assert is guaranteed to pass by the parser, but we double check it here for the
            // programmatic API. It is important that there are no sort names of the form "vec 17",
            // because we sneakily use those strings to represent unification variables during
            // inference.
            assert!(!sort.contains(' '));

            if !sorts.insert(sort.clone()) {
                return Err(SortError::RedeclaredSort(sort.clone()));
            }
        }
        let mut scope = Scope {
            signature,
            bound_names: im::HashMap::new(),
        };
        for rel in &signature.relations {
            for arg in &rel.args {
                scope.check_sort_exists(arg)?;
            }
            scope.check_sort_exists(&rel.sort)?;
            scope.add_name_internal(
                rel.name.clone(),
                RelationOrIndividual::relation(rel),
                ShadowingConstraint::Disallow,
            )?;
        }

        Ok(scope)
    }

    /// Sort check the term in the current scope, inferring any unannotated bound variable sorts,
    /// and return the sort of the term.
    pub fn sort_check_term(&self, term: &mut Term) -> Result<Sort, SortError> {
        let mut unification_table = UnificationTable::new();
        let mut internal_ctx = InternalContext::new(self.clone(), &mut unification_table);
        internal_ctx.sort_check_term(term)
    }

    /// Use sort inference to check that the term has the expected sort
    pub fn sort_check_term_expect(
        &self,
        term: &mut Term,
        expected: &Sort,
    ) -> Result<(), SortError> {
        let mut unification_table = UnificationTable::new();
        let mut internal_ctx = InternalContext::new(self.clone(), &mut unification_table);
        let sort = internal_ctx.collect_sort_constraints_term(term)?;
        internal_ctx.unify_var_value(expected, &sort)?;
        // Guaranteed because unify_var_value errors otherwise.
        assert_eq!(sort, MaybeUnknownSort::Known(expected.clone()));
        internal_ctx.annotate_solved_sorts_term(term)?;
        // Double check that we found all blank sort annotations in phase 1.
        assert!(has_all_sort_annotations_term(term));
        Ok(())
    }

    /// Use sort inference to check that the term has sort bool
    pub fn sort_check_term_bool(&mut self, term: &mut Term) -> Result<(), SortError> {
        self.sort_check_term_expect(term, &Sort::Bool)
    }

    /// Bind a local variable with the given name and sort in the scope.
    ///
    /// The name must not be already bound in the scope.
    /// The sort must exist in the signature.
    pub fn add_variable(&mut self, name: &str, sort: &Sort) -> Result<(), SortError> {
        self.check_sort_exists(sort)?;
        self.add_name_internal(
            name.to_owned(),
            RelationOrIndividual::known(sort),
            ShadowingConstraint::Disallow,
        )
    }

    /// Bind the given slice of local variables.
    ///
    /// None of the names can be bound already in the scope.
    /// All of the binders must have sort annotations. No sort inference is performed here.
    pub fn add_binders(&mut self, binders: &[Binder]) -> Result<(), SortError> {
        self.add_binders_internal(binders, ShadowingConstraint::Disallow)
    }

    // Internal method that lets the caller opt in to allowing binders to shadow outer bindings.
    // Even in this case, all names in the slice must still be distinct.
    fn add_binders_internal(
        &mut self,
        binders: &[Binder],
        shadow: ShadowingConstraint,
    ) -> Result<(), SortError> {
        let mut names = HashSet::new();
        for binder in binders {
            // First check that the name is not repeated *within* this slice.
            if !names.insert(binder.name.clone()) {
                return Err(SortError::RedeclaredName(binder.name.clone()));
            }
            self.check_sort_exists_or_empty(&binder.sort)?;
            let sort = RelationOrIndividual::known(&binder.sort);
            // Now add it to the scope, constraining shadowing as directed
            self.add_name_internal(binder.name.clone(), sort, shadow)?;
        }
        Ok(())
    }

    // if the given sort is uninterpreted, check that it is declared in the module and report an error if not.
    // if empty_allowed is true, then Sort::Uninterpreted("") does not cause an error.
    // callers should not call this function directly, but rather [check_sort_exists] or [check_sort_exists_or_empty]
    fn check_sort_exists_internal(
        &self,
        sort: &Sort,
        empty_allowed: bool,
    ) -> Result<(), SortError> {
        match sort {
            Sort::Bool => Ok(()),
            Sort::Uninterpreted(a) if a.is_empty() && empty_allowed => Ok(()),
            Sort::Uninterpreted(a) => {
                if !self.signature.contains_sort(a) {
                    Err(SortError::UnknownSort(a.clone()))
                } else {
                    Ok(())
                }
            }
        }
    }

    // if the given sort is uninterpreted, check that it is declared in the module and report an
    // error if not.
    fn check_sort_exists(&self, sort: &Sort) -> Result<(), SortError> {
        self.check_sort_exists_internal(sort, false)
    }

    // if the given sort is uninterpreted, check that it is declared in the module and report an
    // error if not. Sort::Uninterpreted("") does not cause an error.
    fn check_sort_exists_or_empty(&self, sort: &Sort) -> Result<(), SortError> {
        self.check_sort_exists_internal(sort, true)
    }

    fn add_name_internal(
        &mut self,
        name: String,
        sort: RelationOrIndividual,
        shadow: ShadowingConstraint,
    ) -> Result<(), SortError> {
        match shadow {
            ShadowingConstraint::Disallow if self.bound_names.contains_key(&name) => {
                return Err(SortError::RedeclaredName(name))
            }
            _ => (),
        }

        self.bound_names.insert(name, sort);
        Ok(())
    }

    /// Sort check the [Definition] in the current scope.
    pub fn sort_check_definition(&mut self, def: &mut Definition) -> Result<(), SortError> {
        {
            let mut scope = self.clone();
            scope.add_binders_internal(&def.binders, ShadowingConstraint::Allow)?;
            scope.check_sort_exists(&def.ret_sort)?;
            scope.sort_check_term_expect(&mut def.body, &def.ret_sort)?;
        }

        self.add_name_internal(
            def.name.clone(),
            RelationOrIndividual::definition(def),
            ShadowingConstraint::Disallow,
        )?;
        Ok(())
    }

    /// Sort check all the [Definition]s in the current scope.
    pub fn sort_check_definitions(&mut self, defs: &mut [Definition]) -> Result<(), SortError> {
        for def in defs {
            self.sort_check_definition(def)?
        }

        Ok(())
    }

    /// Sort check the [ThmStmt] in the current scope.
    pub fn sort_check_statement(
        &mut self,
        statement: &mut ThmStmt,
    ) -> Result<(), (SortError, Option<Span>)> {
        match statement {
            ThmStmt::Assume(term) => self.sort_check_term_bool(term).map_err(|x| (x, None))?,
            ThmStmt::Assert(proof) => {
                for invariant in &mut proof.invariants {
                    self.sort_check_term_bool(&mut invariant.x)
                        .map_err(|x| (x, invariant.span))?
                }
                self.sort_check_term_bool(&mut proof.assert.x)
                    .map_err(|x| (x, proof.assert.span))?
            }
        }
        Ok(())
    }

    /// Sort check all the [ThmStmt]s in the current scope.
    pub fn sort_check_statements(
        &mut self,
        statements: &mut [ThmStmt],
    ) -> Result<(), (SortError, Option<Span>)> {
        for statement in statements {
            self.sort_check_statement(statement)?
        }
        Ok(())
    }

    /// Sort check the [Module] in the current scope.
    pub fn sort_check_module(
        &mut self,
        module: &mut Module,
    ) -> Result<(), (SortError, Option<Span>)> {
        assert!(module.signature.as_ref() == self.signature);

        self.sort_check_definitions(&mut module.defs)
            .map_err(|e| (e, None))?;
        self.sort_check_statements(&mut module.statements)?;

        // Double check that we didn't miss any bound variables in the first pass.
        assert!(has_all_sort_annotations_module(module));
        Ok(())
    }

    fn get(&self, name: &str) -> Option<&RelationOrIndividual> {
        self.bound_names.get(name)
    }

    fn get_individual(&self, name: &str) -> Result<MaybeUnknownSort, SortError> {
        match self.get(name) {
            Some(RelationOrIndividual::Relation(_, _)) => Err(SortError::Uncalled(name.to_owned())),
            Some(RelationOrIndividual::Individual(ret)) => Ok(ret.clone()),
            None => Err(SortError::UnknownVariable(name.to_owned())),
        }
    }

    fn get_relation(&self, name: &str) -> Result<(Vec<Sort>, Sort), SortError> {
        match self.get(name).cloned() {
            Some(RelationOrIndividual::Individual(_)) => {
                Err(SortError::Uncallable(name.to_owned()))
            }
            Some(RelationOrIndividual::Relation(args, ret)) => Ok((args, ret)),
            None => Err(SortError::UnknownFunction(name.to_owned())),
        }
    }
}

type UnificationTable = ena::unify::InPlaceUnificationTable<SortVar>;
struct InternalContext<'a> {
    scope: Scope<'a>,
    unification_table: &'a mut UnificationTable,
}

impl InternalContext<'_> {
    fn new<'a>(
        scope: Scope<'a>,
        unification_table: &'a mut UnificationTable,
    ) -> InternalContext<'a> {
        InternalContext {
            scope,
            unification_table,
        }
    }

    /// Create a new context for an inner scope.
    fn new_inner_scope(&mut self) -> InternalContext {
        InternalContext {
            scope: self.scope.clone(),
            unification_table: self.unification_table,
        }
    }

    // doesn't allow `binders` to shadow each other, but does allow them to
    // shadow names already in scope
    //
    // for any variables that do not have a sort annotation, this function allocates
    // a fresh unification variable to represent its sort, and annotates the AST with
    // a string that uniquely identifies the unification variable. unification variables
    // are represented by integers, and the string "var 55" is used to represent, eg, the
    // unification variable numbered 55. since this string has a space in it, it is impossible
    // for it to be confused with a user sort annotation.
    fn add_binders_for_inference(&mut self, binders: &mut [Binder]) -> Result<(), SortError> {
        let mut names = HashSet::new();
        for binder in binders {
            // First check that the name is not repeated *within* this slice.
            if !names.insert(binder.name.clone()) {
                return Err(SortError::RedeclaredName(binder.name.clone()));
            }
            self.scope.check_sort_exists_or_empty(&binder.sort)?;
            let sort = if binder.sort == Sort::Uninterpreted("".to_owned()) {
                let sort_var = self.new_key();
                binder.sort = Sort::Uninterpreted(format!("var {}", sort_var.0));
                RelationOrIndividual::unknown(sort_var)
            } else {
                RelationOrIndividual::known(&binder.sort)
            };
            // Now add it to the context, allowing it to shadow bindings from
            // any outer scopes.
            self.scope
                .add_name_internal(binder.name.clone(), sort, ShadowingConstraint::Allow)?;
        }
        Ok(())
    }

    /// Check the given value sort with the given variable known-or-unknown sort.
    /// If the variable sort is known, check if its solution is equal, and if not, report an error.
    /// If the variable sort is unknown, resolve the variable to the given value sort.
    fn unify_var_value(&mut self, value: &Sort, var: &MaybeUnknownSort) -> Result<(), SortError> {
        match var {
            MaybeUnknownSort::Known(v) if value == v => Ok(()),
            MaybeUnknownSort::Known(v) => Err(SortError::ExpectedButFoundSorts {
                expected: value.clone(),
                found: v.clone(),
            }),
            MaybeUnknownSort::Unknown(v) => self
                .unification_table
                .unify_var_value(*v, OptionSort(Some(value.clone()))),
        }
    }

    /// Unify two sort variables, or return an error
    fn unify_var_var(
        &mut self,
        a: &MaybeUnknownSort,
        b: &MaybeUnknownSort,
    ) -> Result<(), SortError> {
        match (a, b) {
            (MaybeUnknownSort::Known(a), MaybeUnknownSort::Known(b)) if a == b => Ok(()),
            (MaybeUnknownSort::Known(a), MaybeUnknownSort::Known(b)) => {
                Err(SortError::UnificationFail(a.clone(), b.clone()))
            }
            (MaybeUnknownSort::Unknown(i), MaybeUnknownSort::Unknown(j)) => {
                self.unification_table.unify_var_var(*i, *j)
            }
            (MaybeUnknownSort::Known(a), MaybeUnknownSort::Unknown(i))
            | (MaybeUnknownSort::Unknown(i), MaybeUnknownSort::Known(a)) => self
                .unification_table
                .unify_var_value(*i, OptionSort(Some(a.clone()))),
        }
    }

    // "Phase 1"
    //
    // Recursively find the sort of a term while allocating unification variables for unknown sorts
    // and collecting unification constraints.
    fn collect_sort_constraints_term(
        &mut self,
        term: &mut Term,
    ) -> Result<MaybeUnknownSort, SortError> {
        match term {
            Term::Literal(_) => Ok(MaybeUnknownSort::Known(Sort::Bool)),
            Term::Id(name) => self.scope.get_individual(name),
            Term::App(f, _p, xs) => {
                let (args, ret) = self.scope.get_relation(f)?;
                if args.len() != xs.len() {
                    return Err(SortError::ExpectedButFoundArity {
                        function_name: f.clone(),
                        expected: args.len(),
                        found: xs.len(),
                    });
                }
                for (arg, x) in args.into_iter().zip(xs) {
                    let x = self.collect_sort_constraints_term(x)?;
                    self.unify_var_value(&arg, &x)?;
                }
                Ok(MaybeUnknownSort::Known(ret))
            }
            Term::UnaryOp(
                UOp::Not | UOp::Always | UOp::Eventually | UOp::Next | UOp::Previous,
                x,
            ) => {
                let x = self.collect_sort_constraints_term(x)?;
                self.unify_var_value(&Sort::Bool, &x)?;
                Ok(MaybeUnknownSort::Known(Sort::Bool))
            }
            Term::UnaryOp(UOp::Prime, x) => self.collect_sort_constraints_term(x),
            Term::BinOp(BinOp::Equals | BinOp::NotEquals, x, y) => {
                let a = self.collect_sort_constraints_term(x)?;
                let b = self.collect_sort_constraints_term(y)?;
                self.unify_var_var(&a, &b)?;
                Ok(MaybeUnknownSort::Known(Sort::Bool))
            }
            Term::BinOp(BinOp::Implies | BinOp::Iff | BinOp::Until | BinOp::Since, x, y) => {
                let x = self.collect_sort_constraints_term(x)?;
                self.unify_var_value(&Sort::Bool, &x)?;
                let y = self.collect_sort_constraints_term(y)?;
                self.unify_var_value(&Sort::Bool, &y)?;
                Ok(MaybeUnknownSort::Known(Sort::Bool))
            }
            Term::NAryOp(NOp::And | NOp::Or, xs) => {
                for x in xs {
                    let sort = self.collect_sort_constraints_term(x)?;
                    self.unify_var_value(&Sort::Bool, &sort)?;
                }
                Ok(MaybeUnknownSort::Known(Sort::Bool))
            }
            Term::Ite { cond, then, else_ } => {
                let cond = self.collect_sort_constraints_term(cond)?;
                self.unify_var_value(&Sort::Bool, &cond)?;
                let a = self.collect_sort_constraints_term(then)?;
                let b = self.collect_sort_constraints_term(else_)?;
                self.unify_var_var(&a, &b)?;
                Ok(a)
            }
            Term::Quantified {
                quantifier: Quantifier::Forall | Quantifier::Exists,
                binders,
                body,
            } => {
                let mut context = self.new_inner_scope();
                context.add_binders_for_inference(binders)?;
                let body = context.collect_sort_constraints_term(body)?;
                context.unify_var_value(&Sort::Bool, &body)?;
                Ok(MaybeUnknownSort::Known(Sort::Bool))
            }
        }
    }

    // "Phase 2".
    //
    // Walk the term AST, replacing any binders that still have "var {id}" sorts with their solution
    fn annotate_solved_sorts_term(&mut self, term: &mut Term) -> Result<(), SortError> {
        match term {
            Term::Literal(_) | Term::Id(_) => Ok(()),
            Term::App(_f, _p, xs) => {
                for x in xs {
                    self.annotate_solved_sorts_term(x)?;
                }
                Ok(())
            }
            Term::UnaryOp(
                UOp::Not | UOp::Always | UOp::Eventually | UOp::Prime | UOp::Next | UOp::Previous,
                x,
            ) => self.annotate_solved_sorts_term(x),
            Term::BinOp(
                BinOp::Equals
                | BinOp::NotEquals
                | BinOp::Implies
                | BinOp::Iff
                | BinOp::Until
                | BinOp::Since,
                x,
                y,
            ) => {
                self.annotate_solved_sorts_term(x)?;
                self.annotate_solved_sorts_term(y)?;
                Ok(())
            }
            Term::NAryOp(NOp::And | NOp::Or, xs) => {
                for x in xs {
                    self.annotate_solved_sorts_term(x)?;
                }
                Ok(())
            }
            Term::Ite { cond, then, else_ } => {
                self.annotate_solved_sorts_term(cond)?;
                self.annotate_solved_sorts_term(then)?;
                self.annotate_solved_sorts_term(else_)?;
                Ok(())
            }
            Term::Quantified {
                quantifier: Quantifier::Forall | Quantifier::Exists,
                binders,
                body,
            } => {
                for binder in binders {
                    if let Sort::Uninterpreted(s) = binder.sort.clone() {
                        let s: Vec<&str> = s.split_whitespace().collect();
                        match s[..] {
                            [_] => {} // user sort annotation
                            ["var", id] => {
                                // encodes a sort unification variable
                                let id = id.parse::<u32>().expect(
                                    "unexpected non-integer in a sort unification variable id",
                                );
                                match self.get_sort_var(SortVar(id)) {
                                    None => {
                                        return Err(SortError::UnsolvedSort(binder.name.clone()))
                                    }
                                    Some(v) => binder.sort = v,
                                }
                            }
                            _ => unreachable!("empty string, or contains spaces without var"),
                        }
                    }
                }
                self.annotate_solved_sorts_term(body)
            }
        }
    }

    /// Sort check the term in the current scope, inferring any unannotated bound variable sorts,
    /// and return the sort of the term.
    fn sort_check_term(&mut self, term: &mut Term) -> Result<Sort, SortError> {
        // The sort inference algorithm proceeds in two phases.
        //
        // First, we walk the entire AST and do normal "type checking" checks.
        // During this pass, if we encounter a bound variable without a sort
        // annotation, we allocate a unification variable for it. The unification
        // variable is recorded in the unification table (self.bound_names) and the bound
        // variable in the AST is labeled with a string that uniquely identifies its
        // corresponding variable. Other checks elsewhere in the AST (possibly above
        // the node!) should resolve the unification variable to a concrete sort.
        // This concrete sort gets stored in the unification table, but the AST
        // still has the unification variable recorded as the sort of the variable.
        //
        // Second, we walk the AST again, looking for bound variables with
        // unification variables. We assert that the variable was successfully
        // resolved to a concrete sort (if not, report an error to the user that a
        // type annotation is required), and then replace the unification variable
        // with the concrete sort.

        // Phase 1
        let sort = self.collect_sort_constraints_term(term)?;

        // Next check if we have enough information to fully determine the sort of term.
        // If not, error. If so, proceed to phase 2.
        match self.get_maybe_unknown_sort(&sort) {
            Some(sort) => {
                // At this point, bound variables without sort annotations have "var {id}"
                // as their sort annotation. Second pass fixes this.

                // Phase 2
                self.annotate_solved_sorts_term(term)?;
                // Double check that we found all blank sort annotations in phase 1.
                assert!(has_all_sort_annotations_term(term));
                Ok(sort)
            }
            None => Err(SortError::UnsolvedSort(
                "the term given to get_term_sort".to_owned(),
            )),
        }
    }

    /// Convert an [MaybeUnknownSort] into an `Option<Sort>` by either returning the known sort or
    /// looking up the sort variable.
    fn get_maybe_unknown_sort(&mut self, sort: &MaybeUnknownSort) -> Option<Sort> {
        match sort {
            MaybeUnknownSort::Known(sort) => Some(sort.clone()),
            MaybeUnknownSort::Unknown(sort_var) => self.get_sort_var(*sort_var),
        }
    }

    /// Allocate a new unification variable with unknown solution
    fn new_key(&mut self) -> SortVar {
        self.unification_table.new_key(OptionSort(None))
    }

    /// Look up the current value of a unification variable
    fn get_sort_var(&mut self, sort_var: SortVar) -> Option<Sort> {
        self.unification_table.probe_value(sort_var).0
    }
}
