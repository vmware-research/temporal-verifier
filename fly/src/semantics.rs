// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Model the semantics of flyvy functions under finite universes.

use crate::{ouritertools::OurItertools, syntax::*};
use itertools::Itertools;
use serde::Serialize;
use std::borrow::Borrow;

use BinOp::*;
use NOp::*;
use Quantifier::*;
use UOp::*;

/// Element is an integer type for representing members of a universe within an
/// interpretation.
pub type Element = usize;

/// A universe maps each sort (in the order of the Signature) to its number of
/// elements in an interpretation.
pub type Universe = Vec<usize>;

/// An assignment maps the names of Id terms to elements of a model.
pub type Assignment = im::HashMap<String, Element>;

/// An interpretation gives the complete value of a function for a
/// finite-cardinality universe.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Hash)]
pub struct Interpretation {
    /// The type of this function, given as the cardinality first of all the
    /// inputs and finally the cardinality of the output.
    pub shape: Vec<usize>,
    /// The value of the function at every possible input.
    pub data: Vec<Element>,
}

impl Interpretation {
    /// Get the function's value for a slice of argument values.
    // TODO(oded): make this more space efficient by using the right amount of bits (probably with padding)
    pub fn get(&self, args: &[Element]) -> Element {
        assert_eq!(self.shape.len() - 1, args.len());
        let mut index: usize = 0;
        for (a, s) in args.iter().zip(&self.shape) {
            assert!(a < s);
            index = index * s + a;
        }
        assert!(self.data[index] < self.shape[self.shape.len() - 1]);
        self.data[index]
    }

    /// Create a new interpretation of a given shape based on a function, by
    /// calling the function on all possible input tuple
    pub fn new(shape: &[usize], f: impl Fn(&[Element]) -> Element) -> Self {
        let args = &shape[..shape.len() - 1];
        let ret_card = shape[shape.len() - 1];
        // wrap f just to add this assertion
        let f = |args: &[Element]| -> Element {
            let y = f(args);
            assert!(y < ret_card, "interpretation is out-of-bounds at {args:?}");
            y
        };
        let data = args
            .iter()
            .map(|&card| (0..card).collect::<Vec<Element>>())
            .multi_cartesian_product_fixed()
            .map(|args| f(&args))
            .collect();
        Self {
            shape: shape.to_owned(),
            data,
        }
    }
}

/// A Model is a finite structure that includes a Signature, a Universe for the
/// sorts in the signature, and an interpretation of all the functions in the
/// signature.
#[derive(Debug, Clone, Serialize, PartialEq, Eq, Hash)]
pub struct Model {
    // TODO(oded): to optimize, make things Rc<_> (_ = Signature, Universe, and Interpretation)
    /// The signature this model is for
    pub signature: Signature,
    /// universe matches signature.sorts
    pub universe: Universe,
    /// interp matches signature.relations
    pub interp: Vec<Interpretation>,
}

impl Model {
    /// Get the cardinality using the universe from this model
    pub fn cardinality(&self, sort: &Sort) -> usize {
        match sort {
            Sort::Bool => 2,
            _ => self.universe[self.signature.sort_idx(sort)],
        }
    }

    fn wf(&self) {
        assert_eq!(self.universe.len(), self.signature.sorts.len());
        assert_eq!(self.interp.len(), self.signature.relations.len());
        for i in 0..self.interp.len() {
            let relation = &self.signature.relations[i];
            let interp = &self.interp[i];
            assert_eq!(relation.args.len(), interp.shape.len() - 1);
            assert_eq!(
                interp.shape.iter().last().unwrap(),
                &self.cardinality(&relation.sort),
            );
            for j in 0..relation.args.len() {
                assert_eq!(self.cardinality(&relation.args[j]), interp.shape[j]);
            }
        }
    }

    /// Constructor for a Model
    pub fn new(sig: &Signature, universe: &Universe, interp: Vec<Interpretation>) -> Self {
        let model = Self {
            signature: sig.clone(),
            universe: universe.clone(),
            interp,
        };
        model.wf();
        model
    }

    /// Evaluate a term to a model element.
    ///
    /// The term should be closed (that is, have no free logical variables).
    pub fn eval(&self, t: &Term) -> Element {
        self.eval_assign(t, &Assignment::new())
    }

    /// Evaluate a term to a model element, given an assignment of
    /// logical variables to elements.
    ///
    /// The assignment is unsorted, and so is the return value of this
    /// function.
    pub fn eval_assign(&self, t: &Term, assignment: &Assignment) -> Element {
        let go = |t: &Term| self.eval_assign(t, assignment);
        match t {
            Term::Literal(false) => 0,
            Term::Literal(true) => 1,
            Term::Id(name) if assignment.contains_key(name) => assignment[name],
            Term::Id(name) => {
                let i = self.signature.relation_idx(name);
                assert!(
                    self.signature.relations[i].args.is_empty(),
                    "tried to eval non-nullary function {name}"
                );
                self.interp[i].get(&[])
            }
            Term::App(f, p, args) => {
                let args: Vec<Element> = args.iter().map(go).collect();
                if *p != 0 {
                    panic!("tried to eval {t}")
                }
                self.interp[self.signature.relation_idx(f)].get(&args)
            }
            Term::UnaryOp(Not, t) => {
                let v = go(t);
                assert!(v == 0 || v == 1);
                1 - v
            }
            Term::BinOp(Equals | Iff, lhs, rhs) => {
                let lhs = go(lhs);
                let rhs = go(rhs);
                if lhs == rhs {
                    1
                } else {
                    0
                }
            }
            Term::BinOp(NotEquals, lhs, rhs) => {
                go(&Term::negate(Term::BinOp(Equals, lhs.clone(), rhs.clone())))
            }
            Term::BinOp(Implies, lhs, rhs) => {
                let lhs = go(lhs);
                let rhs = go(rhs);
                if lhs <= rhs {
                    1
                } else {
                    0
                }
            }
            Term::NAryOp(And, ts) => {
                let res = ts.iter().all(|t| go(t) == 1);
                if res {
                    1
                } else {
                    0
                }
            }
            Term::NAryOp(Or, ts) => {
                let res = ts.iter().any(|t| go(t) == 1);
                if res {
                    1
                } else {
                    0
                }
            }
            Term::Ite { cond, then, else_ } => {
                if go(cond) == 1 {
                    go(then)
                } else {
                    go(else_)
                }
            }
            Term::Quantified {
                quantifier: _,
                binders,
                body,
            } if binders.is_empty() => go(body),
            Term::Quantified {
                quantifier,
                binders,
                body,
            } => {
                assert!(!binders.is_empty());
                let shape: Vec<usize> = binders.iter().map(|b| self.cardinality(&b.sort)).collect();
                let names: Vec<&String> = binders.iter().map(|b| &b.name).collect();
                // evaluate on all combinations of values for quantified sorts
                let mut iter = shape
                    .iter()
                    .map(|&card| (0..card).collect::<Vec<Element>>())
                    .multi_cartesian_product_fixed()
                    .map(|elements| {
                        // extend assignment with all variables bound to these `elements`
                        let mut assignment = assignment.clone();
                        for (name, element) in names.iter().zip(elements) {
                            assignment.insert(name.to_string(), element);
                        }
                        self.eval_assign(body, &assignment) == 1
                    });
                let result = match quantifier {
                    Forall => iter.all(|x| x),
                    Exists => iter.any(|x| x),
                };
                // TODO(oded): make a bool_to_element function (and also bool_from_element)
                if result {
                    1
                } else {
                    0
                }
            }
            Term::UnaryOp(Always | Eventually | Prime | Next | Previous, _)
            | Term::BinOp(Until | Since, _, _) => {
                panic!("tried to eval temporal {t}")
            }
        }
    }

    /// Negate the necessary terms in order to make all given terms hold
    /// on the model and the given assignment.
    pub fn flip_to_sat(&self, terms: &mut Vec<Term>, assignment: &Assignment) {
        for term in terms {
            if self.eval_assign(term, assignment) == 0 {
                *term = Term::negate(term.clone());
            }
        }
    }

    /// Represent the model as a term.
    pub fn to_term(&self) -> Term {
        self.to_term_internal(true)
    }

    /// Represent the model as a diagram.
    /// This is the same as `to_term` without the cardinality constraints.
    pub fn to_diagram(&self) -> Term {
        self.to_term_internal(false)
    }

    /// This function is called by `to_term` and `to_diagram`.
    fn to_term_internal(&self, include_cardinalities: bool) -> Term {
        let sort_cnt = self.signature.sorts.len();

        let mut exists_vars: Vec<Vec<String>> = vec![];
        let mut univ_vars: Vec<String> = vec![];
        let mut exists_binders: Vec<Binder> = vec![];
        let mut assignment: Assignment = Assignment::new();
        for i in 0..sort_cnt {
            let sort_name = &self.signature.sorts[i];
            // EDEN: We should use some convention so the names here will not be available for use elsewhere.
            exists_vars.push(
                (0..self.universe[i])
                    .map(|j| format!("{}_{}", sort_name.clone(), j))
                    .collect(),
            );
            univ_vars.push(format!("{}_{}", sort_name.clone(), self.universe[i]));
            for (j, name) in exists_vars[i].iter().enumerate() {
                assignment.insert(name.clone(), j);
                exists_binders.push(Binder {
                    name: name.clone(),
                    sort: Sort::uninterpreted(&self.signature.sorts[i]),
                });
            }
        }

        // Get depth=1 terms (without inequalities).
        let mut terms = self.signature.terms_by_sort(&exists_vars, Some(1), false);
        self.flip_to_sat(&mut terms[sort_cnt], &assignment);

        for i in 0..sort_cnt {
            let mut new_terms = vec![];
            // Note that the first self.universe[i] terms of sort i are exist_vars[i].
            // Add inequalities for exists_vars of sort i.
            for v in (0..self.universe[i]).combinations(2) {
                new_terms.push(Term::BinOp(
                    BinOp::NotEquals,
                    Box::new(terms[i][v[0]].clone()),
                    Box::new(terms[i][v[1]].clone()),
                ));
            }
            // Add equalities for the other terms of sort i.
            for j in self.universe[i]..terms[i].len() {
                let elem = self.eval_assign(&terms[i][j], &assignment);
                new_terms.push(Term::BinOp(
                    BinOp::Equals,
                    Box::new(terms[i][j].clone()),
                    Box::new(terms[i][elem].clone()),
                ));
            }
            if include_cardinalities {
                // Add size constraint for sort i.
                new_terms.push(Term::Quantified {
                    quantifier: Quantifier::Forall,
                    binders: vec![Binder {
                        name: univ_vars[i].clone(),
                        sort: Sort::Uninterpreted(self.signature.sorts[i].clone()),
                    }],
                    body: Box::new(Term::NAryOp(
                        NOp::Or,
                        (0..self.universe[i])
                            .map(|j| {
                                Term::BinOp(
                                    BinOp::Equals,
                                    Box::new(Term::Id(univ_vars[i].clone())),
                                    Box::new(Term::Id(exists_vars[i][j].clone())),
                                )
                            })
                            .collect(),
                    )),
                });
            }
            // Add the above to the Bool terms.
            terms[sort_cnt].append(&mut new_terms);
        }

        Term::Quantified {
            quantifier: Quantifier::Exists,
            binders: exists_binders,
            body: Box::new(Term::NAryOp(NOp::And, terms.pop().unwrap())),
        }
    }
}

impl std::fmt::Display for Model {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        fn fmt_rel(decl: &RelationDecl, interp: &Interpretation) -> String {
            fn fmt_element(sort: &Sort, element: Element) -> String {
                match sort {
                    Sort::Bool => match element {
                        0 => "false".to_string(),
                        1 => "true".to_string(),
                        _ => unreachable!(),
                    },
                    Sort::Uninterpreted(s) => format!("@{s}_{element}"),
                }
            }

            let mut lines = vec![];
            let args_list = interp.shape[..interp.shape.len() - 1]
                .iter()
                .map(|&card| (0..card).collect::<Vec<Element>>())
                .multi_cartesian_product_fixed()
                .collect::<Vec<_>>();
            for args in args_list {
                let name = &decl.name;
                let args_s = decl
                    .args
                    .iter()
                    .zip(&args)
                    .map(|(typ, &idx)| fmt_element(typ, idx))
                    .collect::<Vec<_>>();
                let args_s = if args_s.is_empty() {
                    format!("")
                } else {
                    format!("({})", args_s.join(","))
                };
                let ret_s = fmt_element(&decl.sort, interp.get(&args));
                lines.push(format!("{name}{args_s} = {ret_s}"));
            }
            lines.join("\n")
        }

        assert_eq!(self.signature.relations.len(), self.interp.len());
        for (rel, interp) in self.signature.relations.iter().zip(&self.interp) {
            writeln!(f, "{}", fmt_rel(rel, interp))?;
        }
        Ok(())
    }
}

/// Print a list of models in a format suitable for display to the user.
// ODED: I think we should also print the universe here
pub fn models_to_string<I>(models: I) -> String
where
    I: IntoIterator,
    I::Item: Borrow<Model>,
{
    models
        .into_iter()
        .enumerate()
        .map(|(i, model)| format!("state {i}:\n{}", model.borrow()))
        .join("\n")
}

#[cfg(test)]
mod tests {
    use crate::{
        semantics::Element,
        syntax::{
            BinOp::*, Binder, NOp::*, Quantifier::*, RelationDecl, Signature, Sort, Term, Term::*,
            UOp::*,
        },
    };

    use super::{Interpretation, Model, Universe};

    #[test]
    fn test1() {
        println!("Hello!");
        let i1 = Interpretation {
            shape: vec![10, 10],
            data: (0..10).collect(),
        };
        for i in 0..10 {
            dbg!(i, i1.get(&[i]));
        }

        let i2 = Interpretation {
            shape: vec![5, 2, 10],
            data: (0..10).collect(),
        };
        for i in 0..5 {
            for j in 0..2 {
                dbg!(i, j, i2.get(&[i, j]));
            }
        }
        assert_eq!(i2.get(&[3, 1]), 3 * i2.shape[1] + 1);
    }

    #[test]
    fn test_wf() {
        let sort = |n: usize| Sort::Uninterpreted(format!("T{n}"));

        let sig = Signature {
            sorts: vec!["T1".to_string(), "T2".to_string()],
            relations: vec![
                RelationDecl {
                    mutable: true,
                    name: "r1".to_string(),
                    args: vec![sort(2), sort(1)],
                    sort: Sort::Bool,
                },
                RelationDecl {
                    mutable: true,
                    name: "r2".to_string(),
                    args: vec![sort(1)],
                    sort: sort(2),
                },
            ],
        };

        // T1 has cardinality 2, T2 has cardinality 3
        let universe: Universe = vec![2, 3];

        // r1 is of type (T2, T1) -> bool
        let r1_interp = Interpretation {
            shape: vec![3, 2, 2],
            data: vec![0, 1, 1, 0, 1, 0],
        };

        // r2 is of type (T1) -> T2
        let r2_interp = Interpretation {
            shape: vec![2, 3],
            data: vec![2, 0],
        };

        let model = Model {
            signature: sig,
            universe,
            interp: vec![r1_interp, r2_interp],
        };

        model.wf();
    }

    #[test]
    fn test_interp_new() {
        let interp = Interpretation::new(&[3], |_| 2);
        assert_eq!(interp.get(&[]), 2);
        assert_eq!(interp.data, vec![2]);

        let interp = Interpretation::new(&[3, 2, 4], |es| es[0] + es[1]);
        for i in 0..3 {
            for j in 0..2 {
                assert_eq!(interp.get(&[i, j]), i + j, "wrong value at {i}, {j}");
            }
        }

        let interp = Interpretation::new(&[3, 2, 4, 7], |es| es[0] + es[1] * es[2]);
        for i in 0..3 {
            for j in 0..2 {
                for k in 0..4 {
                    assert_eq!(
                        interp.get(&[i, j, k]),
                        i + j * k,
                        "wrong value at {i}, {j}, {k}"
                    );
                }
            }
        }
    }

    #[test]
    #[allow(clippy::redundant_clone)]
    fn test_eval() {
        let sort = |n: usize| Sort::Uninterpreted(format!("T{n}"));

        let sig = Signature {
            sorts: vec!["T1".to_string(), "T2".to_string()],
            relations: vec![
                RelationDecl {
                    mutable: true,
                    name: "r1".to_string(),
                    args: vec![sort(2), sort(1)],
                    sort: Sort::Bool,
                },
                RelationDecl {
                    mutable: true,
                    name: "r2".to_string(),
                    args: vec![sort(1)],
                    sort: sort(2),
                },
                RelationDecl {
                    mutable: true,
                    name: "c1".to_string(),
                    args: vec![],
                    sort: sort(1),
                },
                RelationDecl {
                    mutable: true,
                    name: "c2".to_string(),
                    args: vec![],
                    sort: sort(2),
                },
            ],
        };

        // T1 has cardinality 2, T2 has cardinality 3
        let universe: Universe = vec![2, 3];

        // r1 is of type (T2, T1) -> bool
        let r1_interp = Interpretation {
            shape: vec![3, 2, 2],
            data: vec![0, 1, 1, 0, 1, 0],
        };

        // r2 is of type (T1) -> T2
        let r2_interp = Interpretation {
            shape: vec![2, 3],
            data: vec![1, 2],
        };

        // c1 is of type T1
        let c1_interp = Interpretation {
            shape: vec![2],
            data: vec![1],
        };

        // c2 is of type T2
        let c2_interp = Interpretation {
            shape: vec![3],
            data: vec![2],
        };

        let model = Model {
            signature: sig,
            universe,
            interp: vec![r1_interp, r2_interp, c1_interp, c2_interp],
        };

        model.wf();

        println!("model is:\n{model}\n");

        let f = Literal(false);
        let t = Literal(true);
        let r1 = "r1".to_string();
        let r2 = "r2".to_string();
        let c1 = Id("c1".to_string());
        let c2 = Id("c2".to_string());

        let e = |t| model.eval(t);
        let b = |t: &Term| Box::new(t.clone());
        let ite = |cond, then, else_| Ite {
            cond: b(cond),
            then: b(then),
            else_: b(else_),
        };

        let mut tests: Vec<(Term, Element)> = vec![];

        // Testing using bool
        tests.extend(vec![
            // true and false
            (f.clone(), 0),
            (t.clone(), 1),
            // UnaryOp: Not
            (UnaryOp(Not, b(&f)), 1),
            (UnaryOp(Not, b(&t)), 0),
            // BinOp: Equals
            (BinOp(Equals, b(&f), b(&f)), 1),
            (BinOp(Equals, b(&f), b(&t)), 0),
            (BinOp(Equals, b(&t), b(&f)), 0),
            (BinOp(Equals, b(&t), b(&t)), 1),
            // BinOp: NotEquals
            (BinOp(NotEquals, b(&f), b(&f)), 0),
            (BinOp(NotEquals, b(&f), b(&t)), 1),
            (BinOp(NotEquals, b(&t), b(&f)), 1),
            (BinOp(NotEquals, b(&t), b(&t)), 0),
            // BinOp: Implies
            (BinOp(Implies, b(&f), b(&f)), 1),
            (BinOp(Implies, b(&f), b(&t)), 1),
            (BinOp(Implies, b(&t), b(&f)), 0),
            (BinOp(Implies, b(&t), b(&t)), 1),
            // BinOp: Iff,
            (BinOp(Iff, b(&f), b(&f)), 1),
            (BinOp(Iff, b(&f), b(&t)), 0),
            (BinOp(Iff, b(&t), b(&f)), 0),
            (BinOp(Iff, b(&t), b(&t)), 1),
            // NAryOp: And
            (NAryOp(And, vec![]), 1),
            (NAryOp(And, vec![f.clone()]), 0),
            (NAryOp(And, vec![t.clone()]), 1),
            (NAryOp(And, vec![f.clone(), f.clone()]), 0),
            (NAryOp(And, vec![f.clone(), t.clone()]), 0),
            (NAryOp(And, vec![t.clone(), f.clone()]), 0),
            (NAryOp(And, vec![t.clone(), t.clone()]), 1),
            (NAryOp(And, vec![f.clone(), f.clone(), f.clone()]), 0),
            (NAryOp(And, vec![f.clone(), f.clone(), t.clone()]), 0),
            (NAryOp(And, vec![f.clone(), t.clone(), f.clone()]), 0),
            (NAryOp(And, vec![f.clone(), t.clone(), t.clone()]), 0),
            (NAryOp(And, vec![t.clone(), f.clone(), f.clone()]), 0),
            (NAryOp(And, vec![t.clone(), f.clone(), t.clone()]), 0),
            (NAryOp(And, vec![t.clone(), t.clone(), f.clone()]), 0),
            (NAryOp(And, vec![t.clone(), t.clone(), t.clone()]), 1),
            // NAryOp: Or
            (NAryOp(Or, vec![]), 0),
            (NAryOp(Or, vec![f.clone()]), 0),
            (NAryOp(Or, vec![t.clone()]), 1),
            (NAryOp(Or, vec![f.clone(), f.clone()]), 0),
            (NAryOp(Or, vec![f.clone(), t.clone()]), 1),
            (NAryOp(Or, vec![t.clone(), f.clone()]), 1),
            (NAryOp(Or, vec![t.clone(), t.clone()]), 1),
            (NAryOp(Or, vec![f.clone(), f.clone(), f.clone()]), 0),
            (NAryOp(Or, vec![f.clone(), f.clone(), t.clone()]), 1),
            (NAryOp(Or, vec![f.clone(), t.clone(), f.clone()]), 1),
            (NAryOp(Or, vec![f.clone(), t.clone(), t.clone()]), 1),
            (NAryOp(Or, vec![t.clone(), f.clone(), f.clone()]), 1),
            (NAryOp(Or, vec![t.clone(), f.clone(), t.clone()]), 1),
            (NAryOp(Or, vec![t.clone(), t.clone(), f.clone()]), 1),
            (NAryOp(Or, vec![t.clone(), t.clone(), t.clone()]), 1),
            // Ite
            (ite(&f, &f, &f), 0),
            (ite(&f, &f, &t), 1),
            (ite(&f, &t, &f), 0),
            (ite(&f, &t, &t), 1),
            (ite(&t, &f, &f), 0),
            (ite(&t, &f, &t), 0),
            (ite(&t, &t, &f), 1),
            (ite(&t, &t, &t), 1),
            // Quantified: Forall
            (
                Quantified {
                    quantifier: Forall,
                    binders: vec![Binder {
                        name: "x".to_string(),
                        sort: Sort::Bool,
                    }],
                    body: Box::new(Id("x".to_string())),
                },
                0,
            ),
            // Quantified: Exists
            (
                Quantified {
                    quantifier: Exists,
                    binders: vec![Binder {
                        name: "x".to_string(),
                        sort: Sort::Bool,
                    }],
                    body: Box::new(Id("x".to_string())),
                },
                1,
            ),
        ]);

        // Testing of constants and relations
        tests.extend(vec![
            (c1.clone(), 1),
            (c2.clone(), 2),
            //
            (BinOp(Equals, b(&c1), b(&c1)), 1),
            (BinOp(NotEquals, b(&c1), b(&c1)), 0),
            //
            (App(r1, 0, vec![c2.clone(), c1.clone()]), 0),
            (App(r2, 0, vec![c1.clone()]), 2),
        ]);

        for (t, v) in tests.iter() {
            println!("evaluating {t} (expecting {v})");
            assert_eq!(&e(t), v, "evaluating {t} should give {v}");
        }
    }

    #[test]
    fn test_to_term() {
        let sort = |n: usize| Sort::Uninterpreted(format!("T{n}"));

        let sig = Signature {
            sorts: vec!["T1".to_string(), "T2".to_string()],
            relations: vec![
                RelationDecl {
                    mutable: true,
                    name: "r1".to_string(),
                    args: vec![sort(2), sort(1)],
                    sort: Sort::Bool,
                },
                RelationDecl {
                    mutable: true,
                    name: "r2".to_string(),
                    args: vec![sort(1)],
                    sort: sort(2),
                },
                RelationDecl {
                    mutable: true,
                    name: "c1".to_string(),
                    args: vec![],
                    sort: sort(1),
                },
                RelationDecl {
                    mutable: true,
                    name: "c2".to_string(),
                    args: vec![],
                    sort: sort(2),
                },
            ],
        };

        // FIRST MODEL

        // T1 has cardinality 2, T2 has cardinality 3
        let universe: Universe = vec![2, 3];

        // r1 is of type (T2, T1) -> bool
        let r1_interp = Interpretation {
            shape: vec![3, 2, 2],
            data: vec![0, 1, 1, 0, 1, 0],
        };

        // r2 is of type (T1) -> T2
        let r2_interp = Interpretation {
            shape: vec![2, 3],
            data: vec![1, 2],
        };

        // c1 is of type T1
        let c1_interp = Interpretation {
            shape: vec![2],
            data: vec![1],
        };

        // c2 is of type T2
        let c2_interp = Interpretation {
            shape: vec![3],
            data: vec![2],
        };

        let fst_model = Model {
            signature: sig.clone(),
            universe,
            interp: vec![r1_interp, r2_interp, c1_interp, c2_interp],
        };

        // SECOND MODEL -- SAME SIZE AS FIRST, DIFFERENT INTERPS

        // T1 has cardinality 2, T2 has cardinality 3
        let universe: Universe = vec![2, 3];

        // r1 is of type (T2, T1) -> bool
        let r1_interp = Interpretation {
            shape: vec![3, 2, 2],
            data: vec![0, 0, 1, 1, 1, 0],
        };

        // r2 is of type (T1) -> T2
        let r2_interp = Interpretation {
            shape: vec![2, 3],
            data: vec![2, 1],
        };

        // c1 is of type T1
        let c1_interp = Interpretation {
            shape: vec![2],
            data: vec![1],
        };

        // c2 is of type T2
        let c2_interp = Interpretation {
            shape: vec![3],
            data: vec![2],
        };

        let snd_model = Model {
            signature: sig.clone(),
            universe,
            interp: vec![r1_interp, r2_interp, c1_interp, c2_interp],
        };

        // THIRD MODEL -- DIFFERENT SIZE FROM FIRST, EXTENDED INTERPS

        // T1 has cardinality 2, T2 has cardinality 3
        let universe: Universe = vec![3, 3];

        // r1 is of type (T2, T1) -> bool
        let r1_interp = Interpretation {
            shape: vec![3, 3, 2],
            data: vec![0, 1, 1, 0, 1, 0, 0, 1, 0],
        };

        // r2 is of type (T1) -> T2
        let r2_interp = Interpretation {
            shape: vec![3, 3],
            data: vec![1, 2, 1],
        };

        // c1 is of type T1
        let c1_interp = Interpretation {
            shape: vec![3],
            data: vec![1],
        };

        // c2 is of type T2
        let c2_interp = Interpretation {
            shape: vec![3],
            data: vec![2],
        };

        let thr_model = Model {
            signature: sig.clone(),
            universe,
            interp: vec![r1_interp, r2_interp, c1_interp, c2_interp],
        };

        // FOURTH MODEL -- ISOMORPHIC TO FIRST

        // T1 has cardinality 2, T2 has cardinality 3
        let universe: Universe = vec![2, 3];

        // r1 is of type (T2, T1) -> bool
        let r1_interp = Interpretation {
            shape: vec![3, 2, 2],
            data: vec![1, 0, 0, 1, 0, 1],
        };

        // r2 is of type (T1) -> T2
        let r2_interp = Interpretation {
            shape: vec![2, 3],
            data: vec![2, 1],
        };

        // c1 is of type T1
        let c1_interp = Interpretation {
            shape: vec![2],
            data: vec![0],
        };

        // c2 is of type T2
        let c2_interp = Interpretation {
            shape: vec![3],
            data: vec![2],
        };

        let fth_model = Model {
            signature: sig,
            universe,
            interp: vec![r1_interp, r2_interp, c1_interp, c2_interp],
        };

        fst_model.wf();
        snd_model.wf();
        thr_model.wf();
        fth_model.wf();

        let fst_as_term = fst_model.to_term();
        let snd_as_term = snd_model.to_term();
        let thr_as_term = thr_model.to_term();
        let fth_as_term = fth_model.to_term();

        assert_ne!(fst_as_term, fth_as_term);

        assert_eq!(fst_model.eval(&fst_as_term), 1);
        assert_eq!(fst_model.eval(&snd_as_term), 0);
        assert_eq!(fst_model.eval(&thr_as_term), 0);
        assert_eq!(fst_model.eval(&fth_as_term), 1);

        assert_eq!(snd_model.eval(&fst_as_term), 0);
        assert_eq!(snd_model.eval(&snd_as_term), 1);
        assert_eq!(snd_model.eval(&thr_as_term), 0);
        assert_eq!(snd_model.eval(&fth_as_term), 0);

        assert_eq!(thr_model.eval(&fst_as_term), 0);
        assert_eq!(thr_model.eval(&snd_as_term), 0);
        assert_eq!(thr_model.eval(&thr_as_term), 1);
        assert_eq!(thr_model.eval(&fth_as_term), 0);

        assert_eq!(fth_model.eval(&fst_as_term), 1);
        assert_eq!(fth_model.eval(&snd_as_term), 0);
        assert_eq!(fth_model.eval(&thr_as_term), 0);
        assert_eq!(fth_model.eval(&fth_as_term), 1);
    }
}
