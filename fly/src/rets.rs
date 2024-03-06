// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Utility to convert all non-boolean-returning relations in a Module to boolean-returning ones.

use std::collections::HashMap;
use std::sync::Arc;

use crate::{semantics::*, syntax::*, term::prime::Next};
use itertools::Itertools;
use thiserror::Error;

impl Module {
    /// Converts all non-boolean-returning relations to boolean-returning ones
    /// by adding an extra argument and axioms.
    pub fn convert_non_bool_relations(
        &mut self,
    ) -> Result<Box<dyn Fn(&Model) -> Model>, RetsError> {
        let old_signature = self.signature.clone();
        let changed: Vec<_> = old_signature
            .relations
            .iter()
            .filter(|r| r.sort != Sort::Bool)
            .cloned()
            .collect();

        let mut axioms = vec![];
        let mut new_signature = self.signature.as_ref().clone();
        for relation in &mut new_signature.relations {
            if relation.sort != Sort::Bool {
                let binders: Vec<Binder> = relation
                    .args
                    .iter()
                    .chain([&relation.sort, &relation.sort])
                    .enumerate()
                    .map(|(i, sort)| Binder {
                        sort: sort.clone(),
                        name: format!("__{i}"),
                    })
                    .collect();
                let other_args = &binders[0..relation.args.len()];
                let new_arg_twice = &binders[relation.args.len()..];
                let all_args_new: Vec<_> = binders[0..=relation.args.len()]
                    .iter()
                    .map(|b| Term::Id(b.name.clone()))
                    .collect();
                let mut all_args_new_alt = all_args_new.clone();
                *all_args_new_alt.last_mut().unwrap() =
                    Term::Id(binders.last().unwrap().name.clone());

                let at_least_one = Term::exists(
                    [binders[relation.args.len()].clone()],
                    Term::App(relation.name.clone(), 0, all_args_new.clone()),
                );
                let at_most_one = Term::forall(
                    new_arg_twice.iter().cloned(),
                    Term::implies(
                        Term::and([
                            Term::App(relation.name.clone(), 0, all_args_new),
                            Term::App(relation.name.clone(), 0, all_args_new_alt),
                        ]),
                        Term::equals(
                            Term::Id(new_arg_twice[0].name.clone()),
                            Term::Id(new_arg_twice[1].name.clone()),
                        ),
                    ),
                );

                let at_least_one = match relation.args.len() {
                    0 => at_least_one,
                    _ => Term::forall(other_args.iter().cloned(), at_least_one),
                };
                let at_most_one = match relation.args.len() {
                    0 => at_most_one,
                    _ => Term::forall(other_args.iter().cloned(), at_most_one),
                };

                axioms.push(ThmStmt::Assume(Term::UnaryOp(
                    UOp::Always,
                    Box::new(at_least_one),
                )));
                axioms.push(ThmStmt::Assume(Term::UnaryOp(
                    UOp::Always,
                    Box::new(at_most_one),
                )));

                relation.args.push(relation.sort.clone());
                relation.sort = Sort::Bool;
            }
        }
        self.signature = Arc::new(new_signature);

        for statement in &mut self.statements {
            match statement {
                ThmStmt::Assume(term) => {
                    *term = flatten_term(&old_signature, term);
                    fix_term(term, &changed)?
                }
                ThmStmt::Assert(Proof { assert, invariants }) => {
                    assert.x = flatten_term(&old_signature, &assert.x);
                    fix_term(&mut assert.x, &changed)?;
                    for invariant in invariants {
                        invariant.x = flatten_term(&old_signature, &invariant.x);
                        fix_term(&mut invariant.x, &changed)?;
                    }
                }
            }
        }

        self.statements.splice(0..0, axioms);

        Ok(Box::new(move |model| {
            Model::new(
                &old_signature,
                &model.universe,
                old_signature
                    .relations
                    .iter()
                    .map(|r| {
                        let interp = &model.interp[old_signature.relation_idx(&r.name)];
                        if r.sort == Sort::Bool {
                            return interp.clone();
                        }

                        let shape: Vec<_> = r
                            .args
                            .iter()
                            .map(|s| model.cardinality(s))
                            .chain([model.cardinality(&r.sort)])
                            .collect();
                        let f = |elements: &[Element]| {
                            for i in 0..model.cardinality(&r.sort) {
                                let mut elements = elements.to_vec();
                                elements.push(i);
                                if interp.get(&elements) == 1 {
                                    return i;
                                }
                            }
                            unreachable!()
                        };
                        Interpretation::new(&shape, f)
                    })
                    .collect(),
            )
        }))
    }

    /// Given a model from a module which underwent [`Module::convert_non_bool_relations`],
    /// convert it to one with the original non-boolean relations.
    /// It is assumed that the calling [`Module`] (`self`) is a copy of the original, non-converted module.
    pub fn to_non_bool_model(&self, model: &Model) -> Model {
        Model::new(
            &self.signature,
            &model.universe,
            self.signature
                .relations
                .iter()
                .map(|r| {
                    let interp = &model.interp[self.signature.relation_idx(&r.name)];
                    if r.sort == Sort::Bool {
                        return interp.clone();
                    }
                    assert_eq!(r.args.len(), interp.shape.len() - 2);

                    let shape: Vec<_> = r
                        .args
                        .iter()
                        .map(|s| model.cardinality(s))
                        .chain([model.cardinality(&r.sort)])
                        .collect();
                    let f = |elements: &[Element]| {
                        for i in 0..model.cardinality(&r.sort) {
                            let mut elements = elements.to_vec();
                            elements.push(i);
                            if interp.get(&elements) == 1 {
                                return i;
                            }
                        }
                        unreachable!()
                    };
                    Interpretation::new(&shape, f)
                })
                .collect(),
        )
    }

    /// Given a model convert it to one only boolean relations.
    /// It is assumed that the calling [`Module`] (`self`) is a copy of the module from which the model came,
    /// but which underwent the `convert_non_bool_relations` operations.
    pub fn to_bool_model(&self, model: &Model) -> Model {
        Model::new(
            &self.signature,
            &model.universe,
            self.signature
                .relations
                .iter()
                .map(|r| {
                    assert_eq!(r.sort, Sort::Bool);
                    let interp = &model.interp[self.signature.relation_idx(&r.name)];
                    if r.args.len() == interp.shape.len() - 1 {
                        return interp.clone();
                    }
                    assert_eq!(r.args.len(), interp.shape.len());

                    let shape: Vec<_> = r
                        .args
                        .iter()
                        .map(|s| model.cardinality(s))
                        .chain([2])
                        .collect();
                    let f = |elements: &[Element]| {
                        let (val, elements) = elements.split_last().unwrap();
                        if interp.get(elements) == *val {
                            return 1;
                        } else {
                            return 0;
                        }
                    };
                    Interpretation::new(&shape, f)
                })
                .collect(),
        )
    }
}

fn contains_changed(term: &Term, changed: &[RelationDecl]) -> bool {
    match term {
        Term::Literal(_) => false,
        Term::Id(id) => changed.iter().any(|c| id == &c.name),
        Term::App(id, ..) if changed.iter().any(|c| id == &c.name) => true,
        Term::App(.., xs) => xs.iter().any(|x| contains_changed(x, changed)),
        Term::NAryOp(_, xs) => xs.iter().any(|x| contains_changed(x, changed)),
        Term::UnaryOp(_, x) => contains_changed(x, changed),
        Term::BinOp(_, x, y) => contains_changed(x, changed) || contains_changed(y, changed),
        Term::Ite { cond, then, else_ } => {
            contains_changed(cond, changed)
                || contains_changed(then, changed)
                || contains_changed(else_, changed)
        }
        Term::Quantified { body, .. } => contains_changed(body, changed),
    }
}

fn strip_primes(term: &Term) -> Option<(Term, usize)> {
    match term {
        Term::Id(_) | Term::App(..) => Some((term.clone(), 0)),
        Term::UnaryOp(UOp::Prime, x) => strip_primes(x).map(|(t, i)| (t, i + 1)),
        Term::Literal(_)
        | Term::UnaryOp(..)
        | Term::BinOp(..)
        | Term::NAryOp(..)
        | Term::Ite { .. }
        | Term::Quantified { .. } => None,
    }
}

/// The result of an unsuccessful attempt to run `convert_non_bool_relations`.
#[derive(Debug, Error)]
pub enum RetsError {
    /// A function was found that wasn't the direct child of an `Equals`.
    #[error("could not remove non-boolean-returning relations from {0}")]
    FoundOutsideEquals(Term),
}

/// Return the variable associated with the given term if one exists.
/// Otherwise, return a fresh variable and add its binder to `subterm_vars`.
fn flat_var_for_term(subterm_vars: &mut HashMap<Term, Binder>, term: Term, sort: Sort) -> Term {
    if let Some(binder) = subterm_vars.get(&term) {
        Term::id(&binder.name)
    } else {
        let name = format!("__flat_{}", subterm_vars.len());
        subterm_vars.insert(
            term,
            Binder {
                name: name.clone(),
                sort,
            },
        );
        Term::Id(name)
    }
}

/// Quantify a flattened term using the binders of fresh variables associated with flattened subterms.
fn quantify_flattened(flat_term: Term, subterm_vars: HashMap<Term, Binder>) -> Term {
    let (terms, binders): (Vec<_>, Vec<_>) = subterm_vars
        .into_iter()
        .sorted_by(|(_, b1), (_, b2)| b1.name.cmp(&b2.name))
        .unzip();
    let body = Term::and(
        terms
            .into_iter()
            .enumerate()
            .map(|(i, t)| Term::equals(Term::id(&binders[i].name), t))
            .chain([flat_term]),
    );
    if binders.is_empty() {
        body
    } else {
        Term::Quantified {
            quantifier: Quantifier::Exists,
            binders,
            body: Box::new(body),
        }
    }
}

/// Get the sort of the given constant. Panics if given anything other then a constant wrapped in temporal operators.
fn get_const_sort(sig: &Signature, term: &Term) -> Sort {
    match term {
        Term::Id(name) => sig.relation_decl(name).sort.clone(),
        Term::UnaryOp(UOp::Prime | UOp::Next | UOp::Previous, t) => get_const_sort(sig, t),
        _ => panic!("tried to flatten non-normalized term: {term}"),
    }
}

fn is_flat(term: &Term) -> bool {
    matches!(
        term,
        Term::Id(_) | Term::UnaryOp(UOp::Next | UOp::Previous | UOp::Prime, _)
    )
}

/// A recursive helper function to get rid of nested functions. `subterm_vars` maintains a mapping
/// from nested terms to their fresh binders.
/// The basic transformation replaces a nested (sorted) term `t` is with a fresh variable `__flat_i`
/// (where `i` is some number) and quantifies the result as `exists __flat_i. (__flat_i = t) & ...`.
///
/// More precrisely, this returns the flattened version of the given `term`, and new variables
/// used in the flattening are added to `subterm_vars` as a mapping from their corresponding terms.
/// These variables are kept up to the deepest boolean level, where they are quantified accordingly.
/// If `make_var` is false, the topmost level will not be converted into a fresh variable; this is useful
/// for equalities, where we need to replace at most one side with a variable.
fn flatten_term_rec(
    sig: &Signature,
    term: &Term,
    subterm_vars: &mut HashMap<Term, Binder>,
    make_var: bool,
) -> Term {
    match term {
        // Literals are flat
        Term::Literal(_) => term.clone(),
        // A non-boolean constant is replaced with a fresh variable if necessary.
        Term::Id(s) => match sig.relations.iter().find(|r| &r.name == s) {
            Some(r) if make_var && matches!(r.sort, Sort::Uninterpreted(_)) => {
                flat_var_for_term(subterm_vars, term.clone(), r.sort.clone())
            }
            _ => term.clone(),
        },
        // A boolean function application is flattened, then quantified accordingly.
        // A non-boolean function application is just flattened, and adds a new variable for itself.
        Term::App(f, n_primes, args) => {
            let sort = sig.relation_decl(f).sort.clone();
            if matches!(sort, Sort::Bool) {
                let mut new_subterm_vars = HashMap::new();
                let new_args: Vec<_> = args
                    .iter()
                    .map(|arg| flatten_term_rec(sig, arg, &mut new_subterm_vars, true))
                    .collect();
                let flat_term = Term::app(f, *n_primes, new_args);
                quantify_flattened(flat_term, new_subterm_vars)
            } else {
                let new_args: Vec<_> = args
                    .iter()
                    .map(|arg| flatten_term_rec(sig, arg, subterm_vars, true))
                    .collect();
                let new_term = Term::app(f, *n_primes, new_args);
                if make_var {
                    flat_var_for_term(subterm_vars, new_term, sort)
                } else {
                    new_term
                }
            }
        }
        // If a unary operation produced a bool, it is flattened recursively.
        // Otherwise, we assume it is a constant, and make a variable for it depending on `make_var`.
        Term::UnaryOp(op, t) if term.is_bool(sig) => {
            Term::UnaryOp(*op, Box::new(flatten_term_rec(sig, t, subterm_vars, false)))
        }
        Term::UnaryOp(_, _) if make_var => {
            flat_var_for_term(subterm_vars, term.clone(), get_const_sort(sig, term))
        }
        Term::UnaryOp(_, _) => term.clone(),
        // Equalities and inequalities are flattened by flattening both sides. Note that at most one of the sides
        // needs to be replaced with a variable at this level. By default this is the lefthand side, unless
        // the righthand side is already a variable.
        Term::BinOp(op, t1, t2) if matches!(op, BinOp::Equals | BinOp::NotEquals) => {
            let mut new_subterm_vars = HashMap::new();
            let flat_term = Term::BinOp(
                *op,
                Box::new(flatten_term_rec(
                    sig,
                    t1,
                    &mut new_subterm_vars,
                    !is_flat(t2),
                )),
                Box::new(flatten_term_rec(sig, t2, &mut new_subterm_vars, false)),
            );
            quantify_flattened(flat_term, new_subterm_vars)
        }
        // All other binary operations are flattened recursively.
        Term::BinOp(op, t1, t2) => Term::BinOp(
            *op,
            Box::new(flatten_term_rec(sig, t1, subterm_vars, false)),
            Box::new(flatten_term_rec(sig, t2, subterm_vars, false)),
        ),
        // An n-ary operation is flattened recursively.
        Term::NAryOp(op, args) => Term::NAryOp(
            *op,
            args.iter()
                .map(|t| flatten_term_rec(sig, t, subterm_vars, false))
                .collect(),
        ),
        // For if-then-else, we only handle boolean terms.
        Term::Ite { cond, then, else_ } => {
            assert!(term.is_bool(sig));
            Term::Ite {
                cond: Box::new(flatten_term_rec(sig, cond, &mut HashMap::new(), false)),
                then: Box::new(flatten_term_rec(sig, then, &mut HashMap::new(), false)),
                else_: Box::new(flatten_term_rec(sig, else_, &mut HashMap::new(), false)),
            }
        }
        // A quantified term is flattened recursively.
        Term::Quantified {
            quantifier,
            binders,
            body,
        } => Term::Quantified {
            quantifier: *quantifier,
            binders: binders.clone(),
            body: Box::new(flatten_term_rec(sig, body, subterm_vars, false)),
        },
    }
}

/// Get rid of nested functions in the given term.
fn flatten_term(sig: &Signature, term: &Term) -> Term {
    flatten_term_rec(
        sig,
        &Next::new(sig).normalize(term),
        &mut HashMap::new(),
        false,
    )
}

fn fix_term(term: &mut Term, changed: &[RelationDecl]) -> Result<(), RetsError> {
    match term {
        Term::Literal(_) => Ok(()),
        Term::Id(_) | Term::App(..) => match contains_changed(term, changed) {
            true => Err(RetsError::FoundOutsideEquals(term.clone())),
            false => Ok(()),
        },
        Term::BinOp(BinOp::Equals, x, y) => {
            match strip_primes(x) {
                Some((Term::Id(f), x_primes)) if changed.iter().any(|c| c.name == *f) => {
                    **x = Term::App(f.clone(), x_primes, vec![])
                }
                Some((Term::App(f, p, xs), x_primes)) if changed.iter().any(|c| c.name == *f) => {
                    **x = Term::App(f.clone(), p + x_primes, xs.clone())
                }
                _ => match strip_primes(y) {
                    Some((Term::Id(f), y_primes)) if changed.iter().any(|c| c.name == *f) => {
                        **y = Term::App(f.clone(), y_primes, vec![])
                    }
                    Some((Term::App(f, p, xs), y_primes))
                        if changed.iter().any(|c| c.name == *f) =>
                    {
                        **y = Term::App(f.clone(), p + y_primes, xs.clone())
                    }
                    _ => {
                        fix_term(x, changed)?;
                        fix_term(y, changed)?;
                        return Ok(());
                    }
                },
            }

            if let Term::Id(id) = &**x {
                if changed.iter().any(|c| c.name == *id) {
                    **x = Term::App(id.clone(), 0, vec![]);
                }
            }
            if let Term::Id(id) = &**y {
                if changed.iter().any(|c| c.name == *id) {
                    **y = Term::App(id.clone(), 0, vec![]);
                }
            }

            let name = match &**x {
                Term::App(name, ..) => name,
                _ => match &**y {
                    Term::App(name, ..) => name,
                    _ => unreachable!(),
                },
            };
            let sort = changed
                .iter()
                .find(|c| c.name == *name)
                .unwrap()
                .sort
                .clone();
            let binder = Binder {
                name: "___1".to_string(),
                sort,
            };

            match &mut **x {
                Term::App(.., xs) => xs.push(Term::Id(binder.name.clone())),
                Term::Id(id) => {
                    **x = Term::equals(Term::Id(binder.name.clone()), Term::Id(id.clone()))
                }
                _ => unreachable!(),
            };
            match &mut **y {
                Term::App(.., xs) => xs.push(Term::Id(binder.name.clone())),
                Term::Id(id) => {
                    **y = Term::equals(Term::Id(binder.name.clone()), Term::Id(id.clone()))
                }
                _ => unreachable!(),
            };

            *term = Term::forall([binder], Term::equals((**x).clone(), (**y).clone()));
            Ok(())
        }
        Term::BinOp(BinOp::NotEquals, x, y) => {
            *term = Term::UnaryOp(
                UOp::Not,
                Box::new(Term::equals((**x).clone(), (**y).clone())),
            );
            fix_term(term, changed)
        }
        Term::UnaryOp(_, x) => fix_term(x, changed),
        Term::BinOp(_, x, y) => {
            fix_term(x, changed)?;
            fix_term(y, changed)?;
            Ok(())
        }
        Term::NAryOp(_, xs) => xs.iter_mut().try_for_each(|x| fix_term(x, changed)),
        Term::Ite { cond, then, else_ } => {
            fix_term(cond, changed)?;
            fix_term(then, changed)?;
            fix_term(else_, changed)?;
            Ok(())
        }
        Term::Quantified { body, .. } => fix_term(body, changed),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::{parse, term};

    #[test]
    fn non_bool_relations_module_conversion_basic() -> Result<(), RetsError> {
        let source1 = "
sort s
mutable f(s, bool): s

assume always forall s:s. f(s, true) = s
        ";
        let source2 = "
sort s
mutable f(s, bool, s): bool

assume always forall __0:s, __1: bool. exists __2:s. f(__0, __1, __2)
assume always forall __0:s, __1: bool, __2:s, __3:s.
    (f(__0, __1, __2) & f(__0, __1, __3)) -> (__2 = __3)

assume always forall s:s. forall ___1:s. f(s, true, ___1) = (___1 = s)
        ";

        let mut module1 = parse(source1).unwrap();
        let _ = module1.convert_non_bool_relations()?;

        let module2 = parse(source2).unwrap();

        assert_eq!(module2, module1);

        Ok(())
    }

    #[test]
    fn non_bool_relations_module_conversion_primes() -> Result<(), RetsError> {
        let source1 = "
sort s
mutable f(s): s

assume always forall s:s. (f(s))' = s
        ";
        let source2 = "
sort s
mutable f(s, s): bool

assume always forall __0:s. exists __1:s. f(__0, __1)
assume always forall __0:s, __1:s, __2:s. (f(__0, __1) & f(__0, __2)) -> (__1 = __2)

assume always forall s:s. forall ___1:s. f'(s, ___1) = (___1 = s)
        ";

        let mut module1 = parse(source1).unwrap();
        let _ = module1.convert_non_bool_relations()?;

        if let ThmStmt::Assume(t) = &module1.statements[2] {
            println!("{t}")
        };

        let module2 = parse(source2).unwrap();

        assert_eq!(module2, module1);

        Ok(())
    }

    #[test]
    fn non_bool_relations_module_conversion_nested() -> Result<(), RetsError> {
        let source1 = "
sort s
mutable f: s

assume always forall s:s. (f = s) & (forall s:s. s=s)
        ";
        let source2 = "
sort s
mutable f(s): bool

assume always exists __0:s. f(__0)
assume always forall __0:s, __1:s. (f(__0) & f(__1)) -> (__0 = __1)

assume always forall s:s. (forall ___1:s. f(___1) = (___1 = s)) & (forall s:s. s=s)
        ";

        let mut module1 = parse(source1).unwrap();
        let _ = module1.convert_non_bool_relations();

        let module2 = parse(source2).unwrap();

        assert_eq!(module2, module1);

        Ok(())
    }

    #[test]
    fn non_bool_relations_model_back_conversion() -> Result<(), RetsError> {
        let source = "
sort s

mutable f(bool): s
        ";
        let mut module = parse(source).unwrap();

        let model1 = Model::new(
            &module.signature,
            &vec![3],
            vec![Interpretation::new(
                &[2, 3],
                |xs| {
                    if xs[0] == 0 {
                        2
                    } else {
                        0
                    }
                },
            )],
        );

        let back_convert_model = module.convert_non_bool_relations()?;
        let model2 = Model::new(
            &module.signature,
            &vec![3],
            vec![Interpretation::new(&[2, 3, 2], |xs| match xs {
                [0, 2] | [1, 0] => 1,
                _ => 0,
            })],
        );

        let model3 = back_convert_model(&model2);

        assert_eq!(model1, model3);

        Ok(())
    }

    #[test]
    fn test_flatten_term() {
        let sort_name = |i: usize| format!("s{i}");
        let sort = |i: usize| Sort::Uninterpreted(sort_name(i));

        // Non-boolean constant
        let c = RelationDecl {
            mutable: true,
            name: "c".to_string(),
            args: vec![],
            sort: sort(2),
        };
        // Non-boolean unary function
        let t = RelationDecl {
            mutable: false,
            name: "t".to_string(),
            args: vec![sort(2)],
            sort: sort(1),
        };
        // Boolean binary relation
        let r = RelationDecl {
            mutable: true,
            name: "r".to_string(),
            args: vec![sort(1), sort(2)],
            sort: Sort::Bool,
        };
        // Non-boolean binary function
        let f = RelationDecl {
            mutable: false,
            name: "f".to_string(),
            args: vec![sort(1), sort(2)],
            sort: sort(2),
        };

        let sig = Signature {
            sorts: vec![sort_name(1), sort_name(2)],
            relations: vec![c, t, r, f],
        };

        let terms = [
            term("r(t(c), c)"),
            term("exists x: s2. t(x) = f(t(x), x)"),
            term("forall x: s2. x = f(t(x), c)"),
            term("forall x: s2. f(t(x), c) != x"),
            term("forall x: s1. r(x, c)"),
            term("forall x: s1. !r(x, f(x, c))"),
            term("forall x: s1. (r(x, c'') | r'(t(c), c))"),
            term("if (exists x: s1. r(x, c)) then r(t(c), c) else !r(t(c), c)"),
        ];
        let flat_terms: Vec<_> = terms.iter().map(|t| flatten_term(&sig, t)).collect();
        let expected_terms = [
            term("exists __flat_0: s2, __flat_1: s1. (__flat_0 = c) & (__flat_1 = t(__flat_0)) & r(__flat_1, __flat_0)"),
            term("exists x: s2. exists __flat_0: s1. (__flat_0 = t(x)) & (__flat_0 = f(__flat_0, x))"),
            term("forall x: s2. exists __flat_0: s1, __flat_1: s2. (__flat_0 = t(x)) & (__flat_1 = c) & (x = f(__flat_0, __flat_1))"),
            term("forall x: s2. exists __flat_0: s1, __flat_1: s2. (__flat_0 = t(x)) & (__flat_1 = c) & (f(__flat_0, __flat_1) != x)"),
            term("forall x: s1. exists __flat_0: s2. (__flat_0 = c) & r(x, __flat_0)"),
            term("forall x: s1. !(exists __flat_0: s2, __flat_1: s2. (__flat_0 = c) & (__flat_1 = f(x, __flat_0)) & r(x, __flat_1))"),
            term("forall x: s1. (
                (exists __flat_0:s2. (__flat_0 = c'') & r(x, __flat_0)) | 
                (exists __flat_0: s2, __flat_1: s1. (__flat_0 = c) & (__flat_1 = t(__flat_0)) & r'(__flat_1, __flat_0))
            )"),
            term("if (exists x: s1. exists __flat_0: s2. (__flat_0 = c) & r(x, __flat_0))
                    then (exists __flat_0: s2, __flat_1: s1. (__flat_0 = c) & (__flat_1 = t(__flat_0)) & r(__flat_1, __flat_0))
                    else !(exists __flat_0: s2, __flat_1: s1. (__flat_0 = c) & (__flat_1 = t(__flat_0)) & r(__flat_1, __flat_0))"),
        ];

        for (flat, expected) in flat_terms.iter().zip(&expected_terms) {
            assert_eq!(flat, expected);
        }
    }
}
