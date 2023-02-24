// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

use crate::fly::syntax::*;
use std::collections::HashSet;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum SortError {
    #[error("module signature should not contain bool")]
    UninterpretedBool,

    #[error("this sort was not declared")]
    UnknownSort(String),
    #[error("this sort was defined multiple times")]
    RedefinedSort(String),

    #[error("this identifier was unknown")]
    UnknownName(String),
    #[error("this identifier was declared multiple times")]
    RedefinedName(String),

    #[error("expected one type but found another")]
    NotEqual(Sort, Sort),

    #[error("higher order functions aren't supported")]
    HigherOrder(Term),
    #[error("expected some number of args but found a different number")]
    ArgMismatch(String, usize, usize),
    #[error("function expected arguments but didn't get them")]
    Uncalled(String),
    #[error("tried to call something that didn't take any args")]
    Uncallable(String),
}

fn sort_assert_eq(a: &Sort, b: &Sort) -> Result<(), SortError> {
    if a == b {
        Ok(())
    } else {
        Err(SortError::NotEqual(a.clone(), b.clone()))
    }
}

pub fn check(module: &Module) -> Result<(), SortError> {
    let mut sorts = HashSet::new();
    for sort in &module.signature.sorts {
        match sort {
            Sort::Bool => Err(SortError::UninterpretedBool)?,
            Sort::Id(s) => {
                if !sorts.insert(s.clone()) {
                    Err(SortError::RedefinedSort(s.clone()))?
                }
            }
        }
    }

    let mut context = Context {
        sorts: &sorts,
        names: im::HashMap::new(),
    };

    for rel in &module.signature.relations {
        for arg in &rel.args {
            check_sort(&context, arg)?;
        }
        check_sort(&context, &rel.sort)?;
        let f = if rel.args.is_empty() {
            AbstractSort::Unit(rel.sort.clone())
        } else {
            AbstractSort::Function(rel.args.clone(), rel.sort.clone())
        };
        context.add_name(rel.name.clone(), f, false)?;
    }

    for def in &module.defs {
        {
            let mut context = context.clone();
            for binder in &def.binders {
                check_sort(&context, &binder.sort)?;
                context.add_name(
                    binder.name.clone(),
                    AbstractSort::Unit(binder.sort.clone()),
                    true,
                )?;
            }
            check_sort(&context, &def.ret_sort)?;
            let ret: Sort = check_term(&context, &def.body)?;
            sort_assert_eq(&ret, &def.ret_sort)?;
        }

        let f = AbstractSort::Function(
            def.binders
                .iter()
                .map(|binder| binder.sort.clone())
                .collect(),
            def.ret_sort.clone(),
        );
        context.add_name(def.name.clone(), f, false)?;
    }

    for statement in &module.statements {
        match statement {
            ThmStmt::Assume(term) => sort_assert_eq(&Sort::Bool, &check_term(&context, term)?)?,
            ThmStmt::Assert(proof) => {
                for invariant in &proof.invariants {
                    sort_assert_eq(&Sort::Bool, &check_term(&context, &invariant.x)?)?;
                }
                sort_assert_eq(&Sort::Bool, &check_term(&context, &proof.assert.x)?)?;
            }
        }
    }

    Ok(())
}

#[derive(Clone, Debug)]
enum AbstractSort {
    Unit(Sort),
    Function(Vec<Sort>, Sort),
}

#[derive(Clone, Debug)]
struct Context<'a> {
    sorts: &'a HashSet<String>,
    names: im::HashMap<String, AbstractSort>,
}

impl Context<'_> {
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
}

fn check_sort(context: &Context, sort: &Sort) -> Result<(), SortError> {
    match sort {
        Sort::Bool => Ok(()),
        Sort::Id(a) => match context.sorts.contains(a) {
            true => Ok(()),
            false => Err(SortError::UnknownSort(a.clone())),
        },
    }
}

fn check_term(context: &Context, term: &Term) -> Result<Sort, SortError> {
    match term {
        Term::Literal(_) => Ok(Sort::Bool),
        Term::Id(name) => match context.names.get(name) {
            Some(AbstractSort::Unit(sort)) => Ok(sort.clone()),
            Some(AbstractSort::Function(_, _)) => Err(SortError::Uncalled(name.clone())),
            None => Err(SortError::UnknownName(name.clone())),
        },
        Term::App(f, xs) => match &**f {
            Term::Id(name) => match context.names.get(name) {
                Some(AbstractSort::Function(args, ret)) => {
                    if args.len() != xs.len() {
                        Err(SortError::ArgMismatch(name.clone(), args.len(), xs.len()))?
                    }
                    for (x, arg) in xs.iter().zip(args) {
                        sort_assert_eq(arg, &check_term(context, x)?)?;
                    }
                    Ok(ret.clone())
                }
                Some(AbstractSort::Unit(_)) => Err(SortError::Uncallable(name.clone())),
                None => Err(SortError::UnknownName(name.clone())),
            },
            f => Err(SortError::HigherOrder(f.clone())),
        },
        Term::UnaryOp(UOp::Not | UOp::Always | UOp::Eventually, x) => {
            sort_assert_eq(&Sort::Bool, &check_term(context, x)?)?;
            Ok(Sort::Bool)
        }
        Term::UnaryOp(UOp::Prime, x) => check_term(context, x),
        Term::BinOp(BinOp::Equals | BinOp::NotEquals, x, y) => {
            let a = check_term(context, x)?;
            let b = check_term(context, y)?;
            sort_assert_eq(&a, &b)?;
            Ok(Sort::Bool)
        }
        Term::BinOp(BinOp::Implies | BinOp::Iff, x, y) => {
            sort_assert_eq(&Sort::Bool, &check_term(context, x)?)?;
            sort_assert_eq(&Sort::Bool, &check_term(context, y)?)?;
            Ok(Sort::Bool)
        }
        Term::NAryOp(NOp::And | NOp::Or, xs) => {
            for x in xs {
                sort_assert_eq(&Sort::Bool, &check_term(context, x)?)?;
            }
            Ok(Sort::Bool)
        }
        Term::Ite { cond, then, else_ } => {
            sort_assert_eq(&Sort::Bool, &check_term(context, cond)?)?;
            let a = check_term(context, then)?;
            let b = check_term(context, else_)?;
            sort_assert_eq(&a, &b)?;
            Ok(a)
        }
        Term::Quantified {
            quantifier: Quantifier::Forall | Quantifier::Exists,
            binders,
            body,
        } => {
            let mut context = context.clone();
            for binder in binders {
                check_sort(&context, &binder.sort)?;
                context.add_name(
                    binder.name.clone(),
                    AbstractSort::Unit(binder.sort.clone()),
                    true,
                )?;
            }
            sort_assert_eq(&Sort::Bool, &check_term(&context, body)?)?;
            Ok(Sort::Bool)
        }
    }
}
