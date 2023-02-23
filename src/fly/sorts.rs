// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

use crate::fly::syntax::*;
use thiserror::Error;
use std::collections::{HashMap, HashSet};

#[derive(Error, Debug)]
pub enum SortError {
    #[error("module signature should not contain bool")]
    UninterpretedBool,
    #[error("this sort was not declared")]
    UnknownSort(String),
    #[error("this sort was defined multiple times")]
    RedefinedSort(String),
    #[error("this relation was not declared")]
    UnknownRelation(String),
    #[error("this relation was defined multiple times")]
    RedefinedRelation(String),
    #[error("this binder was unknown")]
    UnknownName(String),
    #[error("expected one type but found another")]
    NotEqual(Sort, Sort),
    #[error("higher order functions aren't supported")]
    HigherOrder(Term),
    #[error("relation expected arguments but didn't get them")]
    UncalledRelation(String),
}

fn sort_is_bool(sort: &Sort) -> Result<(), SortError> {
    match sort {
        Sort::Bool => Ok(()),
        Sort::Id(_) => Err(SortError::NotEqual(sort.clone(), Sort::Bool)),
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
        relations: &HashMap::new(),
        names: im::HashMap::new(),
    };

    let mut relations = HashMap::new();
    for rel in &module.signature.relations {
        for arg in &rel.args {
            check_sort(&context, arg)?;
        }
        check_sort(&context, &rel.sort)?;
        if relations.insert(rel.name.clone(), (rel.args.clone(), rel.sort.clone())).is_some() {
            Err(SortError::RedefinedRelation(rel.name.clone()))?
        }
    }

    context.relations = &relations;

    for definition in &module.defs {
        check_definition(&context, definition)?;
    }

    for statement in &module.statements {
        check_statement(&mut context, statement)?;
    }

    Ok(())
}

#[derive(Clone, Debug)]
struct Context<'a> {
    sorts: &'a HashSet<String>,
    relations: &'a HashMap<String, (Vec<Sort>, Sort)>,
    names: im::HashMap<String, Sort>,
}

fn check_statement(context: &mut Context, statement: &ThmStmt) -> Result<(), SortError> {
    match statement {
        ThmStmt::Assume(term) => sort_is_bool(&check_term(context, term)?),
        ThmStmt::Assert(proof) => check_proof(context, proof),
    }
}

fn check_proof(context: &mut Context, proof: &Proof) -> Result<(), SortError> {
    for invariant in &proof.invariants {
        sort_is_bool(&check_term(context, &invariant.x)?)?;
    }
    sort_is_bool(&check_term(context, &proof.assert.x)?)
}

fn check_definition(_context: &Context, _definition: &Definition) -> Result<(), SortError> {
    todo!("we don't check definitions yet")
}

fn check_sort(context: &Context, sort: &Sort) -> Result<(), SortError> {
    match sort {
        Sort::Bool => Ok(()),
        Sort::Id(a) => match context.sorts.iter().find(|b| a == *b) {
            Some(_) => Ok(()),
            None => Err(SortError::UnknownSort(a.clone())),
        },
    }
}

fn check_binder(context: &Context, binder: &Binder) -> Result<(), SortError> {
    check_sort(context, &binder.sort)?;
    match context.names.get(&binder.name) {
        Some(sort) => match *sort == binder.sort {
            true => Ok(()),
            false => Err(SortError::NotEqual(sort.clone(), binder.sort.clone())),
        },
        None => Err(SortError::UnknownName(binder.name.clone())),
    }
}

fn check_term(context: &mut Context, term: &Term) -> Result<Sort, SortError> {
    match term {
        Term::Literal(_) => Ok(Sort::Bool),
        Term::Id(id) => match context.names.get(id) {
            Some(sort) => Ok(sort.clone()),
            None => match context.relations.get(id) {
                Some((args, ret)) => {
                    if !args.is_empty() {
                        Err(SortError::UncalledRelation(id.clone()))
                    } else {
                        Ok(ret.clone())
                    }
                },
                None => Err(SortError::UnknownName(id.clone())),
            },
        },
        Term::App(f, xs) => match &**f {
            Term::Id(f) => match context.relations.get(f) {
                Some((args, ret)) => {
                    for (x, arg) in xs.iter().zip(args) {
                        let a = check_term(context, x)?;
                        if a != *arg {
                            Err(SortError::NotEqual(a, arg.clone()))?
                        }
                    }
                    Ok(ret.clone())
                },
                None => Err(SortError::UnknownRelation(f.clone())),
            },
            f => Err(SortError::HigherOrder(f.clone())),
        },
        Term::UnaryOp(uop, x) => match uop {
            UOp::Not | UOp::Always | UOp::Eventually => {
                sort_is_bool(&check_term(context, x)?)?;
                Ok(Sort::Bool)
            },
            UOp::Prime => check_term(context, x),
        },
        Term::BinOp(binop, x, y) => match binop {
            BinOp::Equals | BinOp::NotEquals => {
                let a = check_term(context, x)?;
                let b = check_term(context, y)?;
                match a == b {
                    true => Ok(Sort::Bool),
                    false => Err(SortError::NotEqual(a, b)),
                }
            },
            BinOp::Implies | BinOp::Iff => {
                sort_is_bool(&check_term(context, x)?)?;
                sort_is_bool(&check_term(context, y)?)?;
                Ok(Sort::Bool)
            },
        },
        Term::NAryOp(_nop, xs) => {
            for x in xs {
                sort_is_bool(&check_term(context, x)?)?;
            }
            Ok(Sort::Bool)
        },
        Term::Ite { cond, then, else_ } => {
            sort_is_bool(&check_term(context, cond)?)?;
            let a = check_term(context, then)?;
            let b = check_term(context, else_)?;
            match a == b {
                true => Ok(Sort::Bool),
                false => Err(SortError::NotEqual(a, b)),
            }
        },
        Term::Quantified { quantifier: _, binders, body } => {
            let mut context = context.clone();
            for binder in binders {
                context.names.insert(binder.name.clone(), binder.sort.clone());
                check_binder(&context, binder)?;
            }
            sort_is_bool(&check_term(&mut context, body)?)?;
            Ok(Sort::Bool)
        },
    }
}
