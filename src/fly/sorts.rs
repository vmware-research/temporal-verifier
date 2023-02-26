// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

use crate::fly::syntax::*;
use std::collections::HashSet;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum SortError {
    #[error("module signature should not contain bool")]
    UninterpretedBool,

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

    #[error("expected {1} args but found {2} args for {0}")]
    ArgMismatch(String, usize, usize),
    #[error("{0} expected args but didn't get them")]
    Uncalled(String),
    #[error("{0} was called but didn't take any args")]
    Uncallable(String),

    #[error("sort inference isn't supported yet")]
    NoInference,
}

fn sort_eq(a: &Sort, b: &Sort) -> Result<(), SortError> {
    if a == b {
        Ok(())
    } else {
        Err(SortError::NotEqual(a.clone(), b.clone()))
    }
}

pub fn check(module: &Module) -> Result<(), (SortError, Option<Span>)> {
    let build_context = || {
        let mut sorts = HashSet::new();
        for sort in &module.signature.sorts {
            match sort {
                Sort::Bool => return Err(SortError::UninterpretedBool),
                Sort::Id(s) => {
                    if !sorts.insert(s.clone()) {
                        return Err(SortError::RedefinedSort(s.clone()));
                    }
                }
            }
        }

        let mut context = Context {
            sorts,
            names: im::HashMap::new(),
        };

        for rel in &module.signature.relations {
            for arg in &rel.args {
                check_sort_exists(&context, arg)?;
            }
            check_sort_exists(&context, &rel.sort)?;
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
                check_sort_exists(&context, &def.ret_sort)?;
                let ret: Sort = sort_of_term(&context, &def.body)?;
                sort_eq(&ret, &def.ret_sort)?;
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

    let context = match build_context() {
        Ok(context) => context,
        Err(e) => return Err((e, None)),
    };

    for statement in &module.statements {
        match statement {
            ThmStmt::Assume(term) => match sort_of_term(&context, term) {
                Ok(sort) => match sort_eq(&Sort::Bool, &sort) {
                    Ok(()) => {}
                    Err(e) => return Err((e, None)),
                },
                Err(e) => return Err((e, None)),
            },
            ThmStmt::Assert(proof) => {
                for invariant in &proof.invariants {
                    match sort_of_term(&context, &invariant.x) {
                        Ok(sort) => match sort_eq(&Sort::Bool, &sort) {
                            Ok(()) => {}
                            Err(e) => return Err((e, Some(invariant.span))),
                        },
                        Err(e) => return Err((e, Some(invariant.span))),
                    }
                }
                match sort_of_term(&context, &proof.assert.x) {
                    Ok(sort) => match sort_eq(&Sort::Bool, &sort) {
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

#[derive(Clone, Debug)]
struct Context {
    sorts: HashSet<String>, // never changed
    names: im::HashMap<String, AbstractSort>,
}

impl Context {
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

    fn add_binders(&mut self, binders: &[Binder]) -> Result<(), SortError> {
        let mut names = HashSet::new();
        for binder in binders {
            if !names.insert(binder.name.clone()) {
                return Err(SortError::RedefinedName(binder.name.clone()));
            }
            check_sort_exists(self, &binder.sort)?;
            self.add_name(binder.name.clone(), (vec![], binder.sort.clone()), true)?;
        }
        Ok(())
    }
}

fn check_sort_exists(context: &Context, sort: &Sort) -> Result<(), SortError> {
    match sort {
        Sort::Bool => Ok(()),
        Sort::Id(a) if a.is_empty() => Err(SortError::NoInference),
        Sort::Id(a) => match context.sorts.contains(a) {
            true => Ok(()),
            false => Err(SortError::UnknownSort(a.clone())),
        },
    }
}

fn sort_of_term(context: &Context, term: &Term) -> Result<Sort, SortError> {
    match term {
        Term::Literal(_) => Ok(Sort::Bool),
        Term::Id(name) => match context.names.get(name) {
            Some((args, ret)) if args.is_empty() => Ok(ret.clone()),
            Some((_, _)) => Err(SortError::Uncalled(name.clone())),
            None => Err(SortError::UnknownName(name.clone())),
        },
        Term::App(f, _p, xs) => match context.names.get(f) {
            Some((args, _)) if args.is_empty() => Err(SortError::Uncallable(f.clone())),
            Some((args, ret)) => {
                if args.len() != xs.len() {
                    return Err(SortError::ArgMismatch(f.clone(), args.len(), xs.len()));
                }
                for (x, arg) in xs.iter().zip(args) {
                    sort_eq(arg, &sort_of_term(context, x)?)?;
                }
                Ok(ret.clone())
            }
            None => Err(SortError::UnknownName(f.clone())),
        },
        Term::UnaryOp(UOp::Not | UOp::Always | UOp::Eventually, x) => {
            sort_eq(&Sort::Bool, &sort_of_term(context, x)?)?;
            Ok(Sort::Bool)
        }
        Term::UnaryOp(UOp::Prime, x) => sort_of_term(context, x),
        Term::BinOp(BinOp::Equals | BinOp::NotEquals, x, y) => {
            let a = sort_of_term(context, x)?;
            let b = sort_of_term(context, y)?;
            sort_eq(&a, &b)?;
            Ok(Sort::Bool)
        }
        Term::BinOp(BinOp::Implies | BinOp::Iff, x, y) => {
            sort_eq(&Sort::Bool, &sort_of_term(context, x)?)?;
            sort_eq(&Sort::Bool, &sort_of_term(context, y)?)?;
            Ok(Sort::Bool)
        }
        Term::NAryOp(NOp::And | NOp::Or, xs) => {
            for x in xs {
                sort_eq(&Sort::Bool, &sort_of_term(context, x)?)?;
            }
            Ok(Sort::Bool)
        }
        Term::Ite { cond, then, else_ } => {
            sort_eq(&Sort::Bool, &sort_of_term(context, cond)?)?;
            let a = sort_of_term(context, then)?;
            let b = sort_of_term(context, else_)?;
            sort_eq(&a, &b)?;
            Ok(a)
        }
        Term::Quantified {
            quantifier: Quantifier::Forall | Quantifier::Exists,
            binders,
            body,
        } => {
            let mut context = context.clone();
            context.add_binders(binders)?;
            sort_eq(&Sort::Bool, &sort_of_term(&context, body)?)?;
            Ok(Sort::Bool)
        }
    }
}
