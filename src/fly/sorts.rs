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

    #[error("could not unify {0} and {1}")]
    UnificationFail(Sort, Sort),
    #[error("expected {expected} but found {found}")]
    ExpectedButFoundSorts { expected: Sort, found: Sort },
    #[error("expected {expected} args but found {found} args")]
    ExpectedButFoundArity { expected: usize, found: usize },

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

    let mut context = Context {
        sorts: &sorts,
        names: im::HashMap::new(),
        vars: &mut UnificationTable::new(),
    };

    // using immediately invoked closure to tag errors with None spans
    (|| {
        for rel in &module.signature.relations {
            for arg in &rel.args {
                context.check_sort_exists(arg, false)?;
            }
            context.check_sort_exists(&rel.sort, false)?;
            context.add_name(
                rel.name.clone(),
                NamedSort::Known(rel.args.clone(), rel.sort.clone()),
                false,
            )?;
        }

        for def in &mut module.defs {
            {
                let mut context = context.clone();
                context.add_binders(&mut def.binders)?;
                context.check_sort_exists(&def.ret_sort, false)?;
                let ret = context.sort_of_term(&mut def.body)?;
                context.unify_var_value(&def.ret_sort, &ret)?;
            }

            let args = def
                .binders
                .iter()
                .map(|binder| binder.sort.clone())
                .collect();

            context.add_name(
                def.name.clone(),
                NamedSort::Known(args, def.ret_sort.clone()),
                false,
            )?;
        }

        Ok(())
    })()
    .map_err(|e| (e, None))?;

    // helper that wraps any errors
    let term_is_bool = |context: &mut Context, term: &mut Term, span: Option<Span>| {
        context
            .sort_of_term(term)
            .and_then(|sort| context.unify_var_value(&Sort::Bool, &sort))
            .map_err(|e| (e, span))
    };

    for statement in &mut module.statements {
        match statement {
            ThmStmt::Assume(term) => term_is_bool(&mut context, term, None)?,
            ThmStmt::Assert(proof) => {
                for invariant in &mut proof.invariants {
                    term_is_bool(&mut context, &mut invariant.x, Some(invariant.span))?
                }
                term_is_bool(&mut context, &mut proof.assert.x, Some(proof.assert.span))?
            }
        }
    }

    // first pass done
    // at this point, unknown sorts are written as "var {id}"
    // the second pass here fixes this

    // helper that wraps any errors
    let fix_sorts = |context: &mut Context, term: &mut Term, span: Option<Span>| {
        context.fix_sorts_in_term(term).map_err(|e| (e, span))
    };

    for def in &mut module.defs {
        fix_sorts(&mut context, &mut def.body, None)?
    }

    for statement in &mut module.statements {
        match statement {
            ThmStmt::Assume(term) => fix_sorts(&mut context, term, None)?,
            ThmStmt::Assert(proof) => {
                for invariant in &mut proof.invariants {
                    fix_sorts(&mut context, &mut invariant.x, Some(invariant.span))?
                }
                fix_sorts(&mut context, &mut proof.assert.x, Some(proof.assert.span))?
            }
        }
    }

    Ok(())
}

// can either hold a function sort or the index of a sort variable
// all sorts must be known by the time `check` returns
#[derive(Clone, Debug)]
enum NamedSort {
    Known(Vec<Sort>, Sort),
    Unknown(SortVar),
}

#[derive(Clone, Debug)]
enum AbstractSort {
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

#[derive(Debug)]
struct Context<'a> {
    sorts: &'a HashSet<String>,
    names: im::HashMap<String, NamedSort>,
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
        sort: NamedSort,
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
                NamedSort::Unknown(var)
            } else {
                NamedSort::Known(vec![], binder.sort.clone())
            };
            self.add_name(binder.name.clone(), sort, true)?;
        }
        Ok(())
    }

    // unify a sort and a sort variable, or return an error
    fn unify_var_value(&mut self, value: &Sort, var: &AbstractSort) -> Result<(), SortError> {
        match var {
            AbstractSort::Known(v) if value == v => Ok(()),
            AbstractSort::Known(v) => Err(SortError::ExpectedButFoundSorts {
                expected: value.clone(),
                found: v.clone(),
            }),
            AbstractSort::Unknown(v) => self
                .vars
                .unify_var_value(*v, OptionSort(Some(value.clone()))),
        }
    }

    // unify two sort variables, or return an error
    fn unify_var_var(&mut self, a: &AbstractSort, b: &AbstractSort) -> Result<(), SortError> {
        match (a, b) {
            (AbstractSort::Known(a), AbstractSort::Known(b)) if a == b => Ok(()),
            (AbstractSort::Known(a), AbstractSort::Known(b)) => {
                Err(SortError::UnificationFail(a.clone(), b.clone()))
            }
            (AbstractSort::Unknown(i), AbstractSort::Unknown(j)) => self.vars.unify_var_var(*i, *j),
            (AbstractSort::Known(a), AbstractSort::Unknown(i))
            | (AbstractSort::Unknown(i), AbstractSort::Known(a)) => {
                self.vars.unify_var_value(*i, OptionSort(Some(a.clone())))
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
            Term::Literal(_) => Ok(AbstractSort::Known(Sort::Bool)),
            Term::Id(name) => match self.names.get(name) {
                Some(NamedSort::Known(args, _)) if !args.is_empty() => {
                    Err(SortError::Uncalled(name.clone()))
                }
                Some(NamedSort::Known(_, ret)) => Ok(AbstractSort::Known(ret.clone())),
                Some(NamedSort::Unknown(var)) => Ok(AbstractSort::Unknown(*var)),
                None => Err(SortError::UnknownName(name.clone())),
            },
            Term::App(f, _p, xs) => match self.names.get(f).cloned() {
                Some(NamedSort::Known(args, _)) if args.is_empty() => {
                    Err(SortError::Uncallable(f.clone()))
                }
                Some(NamedSort::Known(args, ret)) => {
                    if args.len() != xs.len() {
                        return Err(SortError::ExpectedButFoundArity {
                            expected: args.len(),
                            found: xs.len(),
                        });
                    }
                    for (arg, x) in args.into_iter().zip(xs) {
                        let x = self.sort_of_term(x)?;
                        self.unify_var_value(&arg, &x)?;
                    }
                    Ok(AbstractSort::Known(ret))
                }
                Some(NamedSort::Unknown(_)) => Err(SortError::UnknownFunctionSort),
                None => Err(SortError::UnknownName(f.clone())),
            },
            Term::UnaryOp(UOp::Not | UOp::Always | UOp::Eventually, x) => {
                let x = self.sort_of_term(x)?;
                self.unify_var_value(&Sort::Bool, &x)?;
                Ok(AbstractSort::Known(Sort::Bool))
            }
            Term::UnaryOp(UOp::Prime, x) => self.sort_of_term(x),
            Term::BinOp(BinOp::Equals | BinOp::NotEquals, x, y) => {
                let a = self.sort_of_term(x)?;
                let b = self.sort_of_term(y)?;
                self.unify_var_var(&a, &b)?;
                Ok(AbstractSort::Known(Sort::Bool))
            }
            Term::BinOp(BinOp::Implies | BinOp::Iff, x, y) => {
                let x = self.sort_of_term(x)?;
                self.unify_var_value(&Sort::Bool, &x)?;
                let y = self.sort_of_term(y)?;
                self.unify_var_value(&Sort::Bool, &y)?;
                Ok(AbstractSort::Known(Sort::Bool))
            }
            Term::NAryOp(NOp::And | NOp::Or, xs) => {
                for x in xs {
                    let sort = self.sort_of_term(x)?;
                    self.unify_var_value(&Sort::Bool, &sort)?;
                }
                Ok(AbstractSort::Known(Sort::Bool))
            }
            Term::Ite { cond, then, else_ } => {
                let cond = self.sort_of_term(cond)?;
                self.unify_var_value(&Sort::Bool, &cond)?;
                let a = self.sort_of_term(then)?;
                let b = self.sort_of_term(else_)?;
                self.unify_var_var(&a, &b)?;
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
                context.unify_var_value(&Sort::Bool, &body)?;
                Ok(AbstractSort::Known(Sort::Bool))
            }
        }
    }
}
