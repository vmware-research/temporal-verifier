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
}

// entry point for the sort checker
pub fn check(module: &Module) -> Result<(), (SortError, Option<Span>)> {
    let build_context = || {
        let mut sorts = HashSet::new();
        for sort in &module.signature.sorts {
            if !sorts.insert(sort.clone()) {
                return Err(SortError::RedefinedSort(sort.clone()));
            }
        }

        let mut context = Context {
            sorts,
            names: im::HashMap::new(),
            var_id: 0,
            vars: UnificationTable::new(),
        };

        for rel in &module.signature.relations {
            for arg in &rel.args {
                context.check_sort_exists(arg, false)?;
            }
            context.check_sort_exists(&rel.sort, false)?;
            context.add_name(
                rel.name.clone(),
                (rel.args.clone(), rel.sort.clone()),
                false,
            )?;
        }

        for def in &module.defs {
            {
                let mut context = context.clone();
                context.add_binders(&def.binders)?;
                context.check_sort_exists(&def.ret_sort, false)?;
                let ret = sort_of_term(&mut context, &def.body)?;
                context.sort_eq(&ret, &(vec![], def.ret_sort.clone()))?;
            }

            let args = def
                .binders
                .iter()
                .map(|binder| binder.sort.clone())
                .collect();
            context.add_name(def.name.clone(), (args, def.ret_sort.clone()), false)?;
        }

        Ok(context)
    };

    let mut context = match build_context() {
        Ok(context) => context,
        Err(e) => return Err((e, None)),
    };

    for statement in &module.statements {
        match statement {
            ThmStmt::Assume(term) => match sort_of_term(&mut context, term) {
                Ok(sort) => match context.sort_eq(&(vec![], Sort::Bool), &sort) {
                    Ok(()) => {}
                    Err(e) => return Err((e, None)),
                },
                Err(e) => return Err((e, None)),
            },
            ThmStmt::Assert(proof) => {
                for invariant in &proof.invariants {
                    match sort_of_term(&mut context, &invariant.x) {
                        Ok(sort) => match context.sort_eq(&(vec![], Sort::Bool), &sort) {
                            Ok(()) => {}
                            Err(e) => return Err((e, Some(invariant.span))),
                        },
                        Err(e) => return Err((e, Some(invariant.span))),
                    }
                }
                match sort_of_term(&mut context, &proof.assert.x) {
                    Ok(sort) => match context.sort_eq(&(vec![], Sort::Bool), &sort) {
                        Ok(()) => {}
                        Err(e) => return Err((e, Some(proof.assert.span))),
                    },
                    Err(e) => return Err((e, Some(proof.assert.span))),
                }
            }
        }
    }

    Ok(())
}

// will be changed to an enum when inference is added
type AbstractSort = (Vec<Sort>, Sort);

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
            (Some(x), Some(y)) if x != y => Err(SortError::NotEqual(x.clone(), y.clone())),
            (Some(x), Some(_)) => Ok(OptionSort(Some(x.clone()))),
        }
    }
}

#[derive(Clone, Debug)]
struct Context {
    sorts: HashSet<String>, // never changed
    names: im::HashMap<String, AbstractSort>,
    var_id: u32,
    vars: UnificationTable<InPlace<SortVar>>,
}

impl Context {
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
    fn add_binders(&mut self, binders: &[Binder]) -> Result<(), SortError> {
        let mut names = HashSet::new();
        for binder in binders {
            if !names.insert(binder.name.clone()) {
                return Err(SortError::RedefinedName(binder.name.clone()));
            }
            self.check_sort_exists(&binder.sort, true)?;
            if binder.sort == Sort::Id("".to_owned()) {
                todo!("handle empty sorts");
            } else {
                self.add_name(binder.name.clone(), (vec![], binder.sort.clone()), true)?;
            }
        }
        Ok(())
    }

    // unify two types, or return an error if they can't be unified
    fn sort_eq(&mut self, (xs, a): &AbstractSort, (ys, b): &AbstractSort) -> Result<(), SortError> {
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
}

// recursively finds the sort of a term
fn sort_of_term(context: &mut Context, term: &Term) -> Result<AbstractSort, SortError> {
    match term {
        Term::Literal(_) => Ok((vec![], Sort::Bool)),
        Term::Id(name) => match context.names.get(name) {
            Some(sort @ (args, _)) if args.is_empty() => Ok(sort.clone()),
            Some((_, _)) => Err(SortError::Uncalled(name.clone())),
            None => Err(SortError::UnknownName(name.clone())),
        },
        Term::App(f, _p, xs) => match context.names.get(f).cloned() {
            Some((args, _)) if args.is_empty() => Err(SortError::Uncallable(f.clone())),
            Some((args, ret)) => {
                if args.len() != xs.len() {
                    return Err(SortError::ArgMismatch(args.len(), xs.len()));
                }
                for (arg, x) in args.into_iter().zip(xs) {
                    let x = sort_of_term(context, x)?;
                    context.sort_eq(&(vec![], arg), &x)?;
                }
                Ok((vec![], ret))
            }
            None => Err(SortError::UnknownName(f.clone())),
        },
        Term::UnaryOp(UOp::Not | UOp::Always | UOp::Eventually, x) => {
            let x = sort_of_term(context, x)?;
            context.sort_eq(&(vec![], Sort::Bool), &x)?;
            Ok((vec![], Sort::Bool))
        }
        Term::UnaryOp(UOp::Prime, x) => sort_of_term(context, x),
        Term::BinOp(BinOp::Equals | BinOp::NotEquals, x, y) => {
            let a = sort_of_term(context, x)?;
            let b = sort_of_term(context, y)?;
            context.sort_eq(&a, &b)?;
            Ok((vec![], Sort::Bool))
        }
        Term::BinOp(BinOp::Implies | BinOp::Iff, x, y) => {
            let x = sort_of_term(context, x)?;
            context.sort_eq(&(vec![], Sort::Bool), &x)?;
            let y = sort_of_term(context, y)?;
            context.sort_eq(&(vec![], Sort::Bool), &y)?;
            Ok((vec![], Sort::Bool))
        }
        Term::NAryOp(NOp::And | NOp::Or, xs) => {
            for x in xs {
                let sort = sort_of_term(context, x)?;
                context.sort_eq(&(vec![], Sort::Bool), &sort)?;
            }
            Ok((vec![], Sort::Bool))
        }
        Term::Ite { cond, then, else_ } => {
            let cond = sort_of_term(context, cond)?;
            context.sort_eq(&(vec![], Sort::Bool), &cond)?;
            let a = sort_of_term(context, then)?;
            let b = sort_of_term(context, else_)?;
            context.sort_eq(&a, &b)?;
            Ok(a)
        }
        Term::Quantified {
            quantifier: Quantifier::Forall | Quantifier::Exists,
            binders,
            body,
        } => {
            let mut context = context.clone();
            context.add_binders(binders)?;
            let body = sort_of_term(&mut context, body)?;
            context.sort_eq(&(vec![], Sort::Bool), &body)?;
            Ok((vec![], Sort::Bool))
        }
    }
}
