// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

use crate::fly::syntax::*;
use ena::unify::{InPlace, UnificationTable, UnifyKey, UnifyValue};
use std::collections::HashSet;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum SortError {
    #[error("sort {0} was not declared")]
    UnknownSort(String),
    #[error("sort {0} was defined multiple times")]
    RedefinedSort(String),

    #[error("{0} was unknown")]
    UnknownName(String),
    #[error("{0} was declared multiple times")]
    RedefinedName(String),

    #[error("expected {0} but found {1}")]
    NotEqual(Sort, Sort),
    #[error("expected {0} args but found {1} args")]
    ArgMismatch(usize, usize),

    #[error("{0} expected args but didn't get them")]
    Uncalled(String),
    #[error("{0} was called but didn't take any args")]
    Uncallable(String),

    #[error("function sort inference is not currently supported")]
    UnknownFunctionSort,
    #[error("could not solve for the sort of {0}")]
    UnsolvedSort(String),
}

// checks that the program is well-sorted
// as well as modifying the module by filling in any missing sort annotations on binders
// entry point for this module
pub fn sort_check_and_infer(module: &mut Module) -> Result<(), (SortError, Option<Span>)> {
    let mut sorts = HashSet::new();
    for sort in &module.signature.sorts {
        if !sorts.insert(sort.clone()) {
            return Err((SortError::RedefinedSort(sort.clone()), None));
        }
    }
    let mut vars = UnificationTable::new();

    let mut context = Context {
        sorts: &sorts,
        names: im::HashMap::new(),
        vars: &mut vars,
    };

    for rel in &module.signature.relations {
        for arg in &rel.args {
            context
                .check_sort_exists(arg, false)
                .map_err(|e| (e, None))?;
        }
        context
            .check_sort_exists(&rel.sort, false)
            .map_err(|e| (e, None))?;
        context
            .add_name(
                rel.name.clone(),
                AbstractSort::Known(rel.args.clone(), rel.sort.clone()),
                false,
            )
            .map_err(|e| (e, None))?;
    }

    for def in &mut module.defs {
        {
            let mut context = context.clone();
            context
                .add_binders(&mut def.binders)
                .map_err(|e| (e, None))?;
            context
                .check_sort_exists(&def.ret_sort, false)
                .map_err(|e| (e, None))?;
            let ret = context.sort_of_term(&mut def.body).map_err(|e| (e, None))?;
            context
                .sort_eq(&ret, &AbstractSort::unit(def.ret_sort.clone()))
                .map_err(|e| (e, None))?;
        }

        let args = def
            .binders
            .iter()
            .map(|binder| binder.sort.clone())
            .collect();

        context
            .add_name(
                def.name.clone(),
                AbstractSort::Known(args, def.ret_sort.clone()),
                false,
            )
            .map_err(|e| (e, None))?;
    }

    for statement in &mut module.statements {
        match statement {
            ThmStmt::Assume(term) => match context.sort_of_term(term) {
                Ok(sort) => match context.sort_eq(&AbstractSort::unit(Sort::Bool), &sort) {
                    Ok(()) => {}
                    Err(e) => return Err((e, None)),
                },
                Err(e) => return Err((e, None)),
            },
            ThmStmt::Assert(proof) => {
                for invariant in &mut proof.invariants {
                    let sort = context
                        .sort_of_term(&mut invariant.x)
                        .map_err(|e| (e, Some(invariant.span)))?;
                    context
                        .sort_eq(&AbstractSort::unit(Sort::Bool), &sort)
                        .map_err(|e| (e, Some(invariant.span)))?;
                }
                let sort = context
                    .sort_of_term(&mut proof.assert.x)
                    .map_err(|e| (e, Some(proof.assert.span)))?;
                context
                    .sort_eq(&AbstractSort::unit(Sort::Bool), &sort)
                    .map_err(|e| (e, Some(proof.assert.span)))?;
            }
        }
    }

    // first pass done
    // at this point, unknown sorts are written as "var {id}"
    // the second pass here fixes this

    for def in &mut module.defs {
        context
            .fix_sorts_in_term(&mut def.body)
            .map_err(|e| (e, None))?;
    }

    for statement in &mut module.statements {
        match statement {
            ThmStmt::Assume(term) => context.fix_sorts_in_term(term).map_err(|e| (e, None))?,
            ThmStmt::Assert(proof) => {
                for invariant in &mut proof.invariants {
                    context
                        .fix_sorts_in_term(&mut invariant.x)
                        .map_err(|e| (e, Some(invariant.span)))?;
                }
                context
                    .fix_sorts_in_term(&mut proof.assert.x)
                    .map_err(|e| (e, Some(proof.assert.span)))?;
            }
        }
    }

    Ok(())
}

// can either hold a function sort or the index of a sort variable
// all sorts must be known by the time `check` returns
#[derive(Clone, Debug)]
enum AbstractSort {
    Known(Vec<Sort>, Sort),
    Unknown(SortVar),
}

impl AbstractSort {
    // helper to wrap regular sorts as known nullary function sorts
    #[inline]
    fn unit(sort: Sort) -> AbstractSort {
        AbstractSort::Known(vec![], sort)
    }
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
            (Some(x), Some(y)) => Err(SortError::NotEqual(x.clone(), y.clone())),
        }
    }
}

#[derive(Debug)]
struct Context<'a> {
    sorts: &'a HashSet<String>,
    names: im::HashMap<String, AbstractSort>,
    vars: &'a mut UnificationTable<InPlace<SortVar>>,
}

impl Context<'_> {
    // we don't want to clone the references, just the name map
    // this should be both fast and correct (with regards to scope)
    fn clone(&mut self) -> Context {
        Context {
            sorts: self.sorts,
            names: self.names.clone(),
            vars: self.vars,
        }
    }

    // all sorts must be declared in the module signature
    // this function checks that, assuming that it gets called on all sorts
    fn check_sort_exists(&self, sort: &Sort, empty_valid: bool) -> Result<(), SortError> {
        match sort {
            Sort::Bool => Ok(()),
            Sort::Id(a) if a.is_empty() && empty_valid => Ok(()),
            Sort::Id(a) => match self.sorts.contains(a) {
                true => Ok(()),
                false => Err(SortError::UnknownSort(a.clone())),
            },
        }
    }

    // adds `(name, sort)` to `context`, potentially giving an error if name already exists
    fn add_name(
        &mut self,
        name: String,
        sort: AbstractSort,
        allow_shadowing: bool,
    ) -> Result<(), SortError> {
        match self.names.insert(name.clone(), sort) {
            Some(_) if !allow_shadowing => Err(SortError::RedefinedName(name)),
            _ => Ok(()),
        }
    }

    // doesn't allow `binders` to shadow each other, but does allow them to
    // shadow names already in `context`
    fn add_binders(&mut self, binders: &mut [Binder]) -> Result<(), SortError> {
        let mut names = HashSet::new();
        for binder in binders {
            if !names.insert(binder.name.clone()) {
                return Err(SortError::RedefinedName(binder.name.clone()));
            }
            self.check_sort_exists(&binder.sort, true)?;
            let sort = if binder.sort == Sort::Id("".to_owned()) {
                let var = self.vars.new_key(OptionSort(None));
                binder.sort = Sort::Id(format!("var {}", var.0));
                AbstractSort::Unknown(var)
            } else {
                AbstractSort::unit(binder.sort.clone())
            };
            self.add_name(binder.name.clone(), sort, true)?;
        }
        Ok(())
    }

    // unify two types, or return an error if they can't be unified
    fn sort_eq(&mut self, a: &AbstractSort, b: &AbstractSort) -> Result<(), SortError> {
        match (a, b) {
            (AbstractSort::Known(xs, a), AbstractSort::Known(ys, b)) => {
                for (x, y) in xs.iter().zip(ys) {
                    if x != y {
                        return Err(SortError::NotEqual(x.clone(), y.clone()));
                    }
                }
                if a != b {
                    return Err(SortError::NotEqual(a.clone(), b.clone()));
                }
                Ok(())
            }
            (AbstractSort::Unknown(i), AbstractSort::Unknown(j)) => self.vars.unify_var_var(*i, *j),
            (AbstractSort::Known(xs, y), AbstractSort::Unknown(i))
            | (AbstractSort::Unknown(i), AbstractSort::Known(xs, y))
                if xs.is_empty() =>
            {
                self.vars.unify_var_value(*i, OptionSort(Some(y.clone())))
            }
            (AbstractSort::Known(..), AbstractSort::Unknown(..))
            | (AbstractSort::Unknown(..), AbstractSort::Known(..)) => {
                Err(SortError::UnknownFunctionSort)
            }
        }
    }

    // walk the term AST, fixing any binders that still have "var {id}" sorts
    fn fix_sorts_in_term(&mut self, term: &mut Term) -> Result<(), SortError> {
        match term {
            Term::Literal(_) | Term::Id(_) => Ok(()),
            Term::App(_f, _p, xs) => {
                for x in xs {
                    self.fix_sorts_in_term(x)?;
                }
                Ok(())
            }
            Term::UnaryOp(UOp::Not | UOp::Always | UOp::Eventually | UOp::Prime, x) => {
                self.fix_sorts_in_term(x)
            }
            Term::BinOp(BinOp::Equals | BinOp::NotEquals | BinOp::Implies | BinOp::Iff, x, y) => {
                self.fix_sorts_in_term(x)?;
                self.fix_sorts_in_term(y)?;
                Ok(())
            }
            Term::NAryOp(NOp::And | NOp::Or, xs) => {
                for x in xs {
                    self.fix_sorts_in_term(x)?;
                }
                Ok(())
            }
            Term::Ite { cond, then, else_ } => {
                self.fix_sorts_in_term(cond)?;
                self.fix_sorts_in_term(then)?;
                self.fix_sorts_in_term(else_)?;
                Ok(())
            }
            Term::Quantified {
                quantifier: Quantifier::Forall | Quantifier::Exists,
                binders,
                body,
            } => {
                for binder in binders {
                    if let Sort::Id(s) = binder.sort.clone() {
                        let s: Vec<&str> = s.split_whitespace().collect();
                        match s[..] {
                            [_] => {}
                            ["var", id] => {
                                let id = id.parse::<u32>().unwrap();
                                let sort = self.vars.probe_value(SortVar(id));
                                match sort.0 {
                                    None => {
                                        return Err(SortError::UnsolvedSort(binder.name.clone()))
                                    }
                                    Some(v) => binder.sort = v,
                                }
                            }
                            _ => unreachable!(),
                        }
                    }
                }
                self.fix_sorts_in_term(body)
            }
        }
    }

    // recursively finds the sort of a term
    fn sort_of_term(&mut self, term: &mut Term) -> Result<AbstractSort, SortError> {
        match term {
            Term::Literal(_) => Ok(AbstractSort::unit(Sort::Bool)),
            Term::Id(name) => match self.names.get(name) {
                Some(AbstractSort::Known(args, _)) if !args.is_empty() => {
                    Err(SortError::Uncalled(name.clone()))
                }
                Some(sort) => Ok(sort.clone()),
                None => Err(SortError::UnknownName(name.clone())),
            },
            Term::App(f, _p, xs) => match self.names.get(f).cloned() {
                Some(AbstractSort::Known(args, _)) if args.is_empty() => {
                    Err(SortError::Uncallable(f.clone()))
                }
                Some(AbstractSort::Known(args, ret)) => {
                    if args.len() != xs.len() {
                        return Err(SortError::ArgMismatch(args.len(), xs.len()));
                    }
                    for (arg, x) in args.into_iter().zip(xs) {
                        let x = self.sort_of_term(x)?;
                        self.sort_eq(&AbstractSort::unit(arg), &x)?;
                    }
                    Ok(AbstractSort::unit(ret))
                }
                Some(AbstractSort::Unknown(_)) => Err(SortError::UnknownFunctionSort),
                None => Err(SortError::UnknownName(f.clone())),
            },
            Term::UnaryOp(UOp::Not | UOp::Always | UOp::Eventually, x) => {
                let x = self.sort_of_term(x)?;
                self.sort_eq(&AbstractSort::unit(Sort::Bool), &x)?;
                Ok(AbstractSort::unit(Sort::Bool))
            }
            Term::UnaryOp(UOp::Prime, x) => self.sort_of_term(x),
            Term::BinOp(BinOp::Equals | BinOp::NotEquals, x, y) => {
                let a = self.sort_of_term(x)?;
                let b = self.sort_of_term(y)?;
                self.sort_eq(&a, &b)?;
                Ok(AbstractSort::unit(Sort::Bool))
            }
            Term::BinOp(BinOp::Implies | BinOp::Iff, x, y) => {
                let x = self.sort_of_term(x)?;
                self.sort_eq(&AbstractSort::unit(Sort::Bool), &x)?;
                let y = self.sort_of_term(y)?;
                self.sort_eq(&AbstractSort::unit(Sort::Bool), &y)?;
                Ok(AbstractSort::unit(Sort::Bool))
            }
            Term::NAryOp(NOp::And | NOp::Or, xs) => {
                for x in xs {
                    let sort = self.sort_of_term(x)?;
                    self.sort_eq(&AbstractSort::unit(Sort::Bool), &sort)?;
                }
                Ok(AbstractSort::unit(Sort::Bool))
            }
            Term::Ite { cond, then, else_ } => {
                let cond = self.sort_of_term(cond)?;
                self.sort_eq(&AbstractSort::unit(Sort::Bool), &cond)?;
                let a = self.sort_of_term(then)?;
                let b = self.sort_of_term(else_)?;
                self.sort_eq(&a, &b)?;
                Ok(a)
            }
            Term::Quantified {
                quantifier: Quantifier::Forall | Quantifier::Exists,
                binders,
                body,
            } => {
                let mut context = self.clone();
                context.add_binders(binders)?;
                let body = context.sort_of_term(body)?;
                context.sort_eq(&AbstractSort::unit(Sort::Bool), &body)?;
                Ok(AbstractSort::unit(Sort::Bool))
            }
        }
    }
}
