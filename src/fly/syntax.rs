// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

use itertools::Itertools;
use std::fmt;

use serde::Serialize;

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash)]
pub enum UOp {
    Not,
    Prime,
    Always,
    Eventually,
}

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash)]
pub enum BinOp {
    Equals,
    NotEquals,
    Implies,
    Iff,
}

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash)]
pub enum NOp {
    And,
    Or,
}

#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash)]
pub enum Quantifier {
    Forall,
    Exists,
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct Binder {
    pub name: String,
    pub sort: Sort,
}

#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub enum Term {
    Literal(bool),
    Id(String),
    App(String, usize, Vec<Term>),
    UnaryOp(UOp, Box<Term>),
    BinOp(BinOp, Box<Term>, Box<Term>),
    NAryOp(NOp, Vec<Term>),
    #[allow(dead_code)]
    Ite {
        cond: Box<Term>,
        then: Box<Term>,
        else_: Box<Term>,
    },
    Quantified {
        quantifier: Quantifier,
        binders: Vec<Binder>,
        body: Box<Term>,
    },
}

impl Term {
    /// Flatten an n-ary relation one level deep.
    fn flatten_nary(self) -> Self {
        match self {
            Self::NAryOp(op, ts) => {
                let new_ts = ts
                    .into_iter()
                    .flat_map(|t| match t {
                        Self::NAryOp(op2, ts2) if op == op2 => ts2,
                        _ => vec![t],
                    })
                    .collect();
                Self::NAryOp(op, new_ts)
            }
            _ => self,
        }
    }

    pub fn nary(op: NOp, lhs: Term, rhs: Term) -> Self {
        Self::NAryOp(op, vec![lhs, rhs]).flatten_nary()
    }

    pub fn and<I>(ts: I) -> Self
    where
        I: IntoIterator,
        I::IntoIter: Iterator<Item = Term>,
    {
        let mut ts: Vec<Term> = ts.into_iter().collect();
        if ts.is_empty() {
            return Term::Literal(true);
        } else if ts.len() == 1 {
            return ts.pop().unwrap();
        }
        Self::NAryOp(NOp::And, ts)
    }

    pub fn or<I>(ts: I) -> Self
    where
        I: IntoIterator,
        I::IntoIter: Iterator<Item = Term>,
    {
        let mut ts: Vec<Term> = ts.into_iter().collect();
        if ts.is_empty() {
            return Term::Literal(false);
        } else if ts.len() == 1 {
            return ts.pop().unwrap();
        }
        Self::NAryOp(NOp::Or, ts)
    }

    pub fn implies(lhs: Term, rhs: Term) -> Self {
        Self::BinOp(BinOp::Implies, Box::new(lhs), Box::new(rhs))
    }

    pub fn equals(lhs: Term, rhs: Term) -> Self {
        Self::BinOp(BinOp::Equals, Box::new(lhs), Box::new(rhs))
    }

    pub fn negate(t: Term) -> Self {
        Self::UnaryOp(UOp::Not, Box::new(t))
    }

    pub fn exists<I>(binders: I, body: Term) -> Self
    where
        I: IntoIterator,
        I::IntoIter: Iterator<Item = Binder>,
    {
        Self::Quantified {
            quantifier: Quantifier::Exists,
            binders: binders.into_iter().collect(),
            body: Box::new(body),
        }
    }

    pub fn forall<I>(binders: I, body: Term) -> Self
    where
        I: IntoIterator,
        I::IntoIter: Iterator<Item = Binder>,
    {
        Self::Quantified {
            quantifier: Quantifier::Forall,
            binders: binders.into_iter().collect(),
            body: Box::new(body),
        }
    }
}

#[derive(PartialEq, Eq, Clone, Debug, Hash, Serialize)]
pub enum Sort {
    Bool,
    Id(String),
}

impl Sort {
    pub fn new<S: AsRef<str>>(s: S) -> Self {
        Self::Id(s.as_ref().to_string())
    }
}

impl fmt::Display for Sort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Sort::Bool => "bool".to_string(),
            Sort::Id(i) => i.to_string(),
        };
        write!(f, "{s}")
    }
}

// TODO(oded): rename Relation to Function

#[derive(PartialEq, Eq, Clone, Debug, Serialize)]
pub struct RelationDecl {
    pub mutable: bool,
    pub name: String,
    pub args: Vec<Sort>,
    pub sort: Sort,
}

#[derive(PartialEq, Eq, Clone, Debug, Serialize)]
pub struct Signature {
    pub sorts: Vec<String>, // only contains uninterpreted sorts
    pub relations: Vec<RelationDecl>,
}

impl Signature {
    pub fn sort_idx(&self, sort: &Sort) -> usize {
        match sort {
            Sort::Bool => panic!("invalid sort {sort}"),
            Sort::Id(sort) => self
                .sorts
                .iter()
                .position(|x| x == sort)
                .unwrap_or_else(|| panic!("invalid sort {sort}")),
        }
    }

    /// Get the declaration for a given name.
    ///
    /// Removes trailing primes from name and gives the underlying relation.
    pub fn relation_decl(&self, name: &str) -> &RelationDecl {
        let name = name.trim_end_matches('\'');
        self.relations
            .iter()
            .find(|x| x.name == name)
            .unwrap_or_else(|| panic!("could not find relation {name}"))
    }

    pub fn relation_idx(&self, name: &str) -> usize {
        self.relations
            .iter()
            .position(|x| x.name == name)
            .unwrap_or_else(|| panic!("invalid relation {name}"))
    }

    pub fn contains_name(&self, name: &str) -> bool {
        let symbol_no_primes = name.trim_end_matches(|c| c == '\'');
        return self.relations.iter().any(|r| r.name == symbol_no_primes);
    }

    /// Compute all terms up to a certain nesting depth (optional), using the given variable names.
    /// If include_eq is true, include equality terms between any two same-sorted, non-Bool terms.
    ///
    /// Both sorted_vars and the returned vector match self.sorts w.r.t sorted indices, and have an extra final entry for the Bool sort.
    pub fn terms_by_sort(
        &self,
        sorted_vars: &[Vec<String>],
        mut depth: Option<usize>,
        include_eq: bool,
    ) -> Vec<Vec<Term>> {
        let sort_idx = |sort: &Sort| -> usize {
            match sort {
                Sort::Bool => self.sorts.len(),
                _ => self.sort_idx(sort),
            }
        };

        let mut terms = vec![vec![]; self.sorts.len() + 1];
        let mut new_terms = vec![vec![]; self.sorts.len() + 1];

        // Generate sorted variables.
        for (i, names) in sorted_vars.iter().enumerate() {
            for name in names {
                new_terms[i].push(Term::Id(name.clone()));
            }
        }

        // Generate constants.
        for rel_decl in &self.relations {
            if rel_decl.args.is_empty() {
                new_terms[sort_idx(&rel_decl.sort)].push(Term::Id(rel_decl.name.clone()));
            }
        }

        // Generated terms up to the given nesting depth, or until no new terms can be generated.
        while !new_terms.iter().all(|v| v.is_empty()) && depth.unwrap_or(1) > 0 {
            if let Some(n) = depth {
                depth = Some(n - 1);
            }

            let mut new_new_terms = vec![vec![]; self.sorts.len() + 1];
            for rel_decl in &self.relations {
                if rel_decl.args.is_empty() {
                    continue;
                }

                for new_ind in (0..rel_decl.args.len())
                    .map(|_| [false, true])
                    .multi_cartesian_product()
                {
                    // Only generate terms where at least one argument is a newly generated term,
                    // to make sure each term is generated exactly once.
                    if !new_ind.iter().any(|&x| x) {
                        continue;
                    }

                    let mut arg_terms = vec![];
                    for i in 0..rel_decl.args.len() {
                        if new_ind[i] {
                            arg_terms.push(&new_terms[sort_idx(&rel_decl.args[i])]);
                        } else {
                            arg_terms.push(&terms[sort_idx(&rel_decl.args[i])]);
                        }
                    }

                    if !arg_terms.iter().any(|v| v.is_empty()) {
                        for args in arg_terms
                            .iter()
                            .map(|&t| t.iter())
                            .multi_cartesian_product()
                        {
                            let term_vec = args.iter().map(|&x| x.clone()).collect();
                            new_new_terms[sort_idx(&rel_decl.sort)].push(Term::App(
                                rel_decl.name.clone(),
                                0,
                                term_vec,
                            ));
                        }
                    }
                }
            }

            for (i, ts) in new_terms.iter_mut().enumerate() {
                terms[i].append(ts);
            }
            new_terms = new_new_terms
        }

        for (i, vt) in new_terms.iter_mut().enumerate() {
            terms[i].append(vt);
        }

        // Generate equality terms.
        if include_eq {
            let mut eq_terms = vec![];
            for term in terms.iter().take(self.sorts.len()) {
                eq_terms.append(
                    &mut term
                        .iter()
                        .combinations(2)
                        .map(|v| {
                            Term::BinOp(
                                BinOp::Equals,
                                Box::new(v[0].clone()),
                                Box::new(v[1].clone()),
                            )
                        })
                        .collect(),
                );
            }
            terms[self.sorts.len()].append(&mut eq_terms);
        }

        terms
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Definition {
    pub name: String,
    pub binders: Vec<Binder>,
    pub ret_sort: Sort,
    pub body: Term,
}

/// A Span records a span of text in the source code, for error reporting.
#[derive(PartialEq, Eq, Copy, Clone, Debug, Serialize)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

#[derive(PartialEq, Eq, Clone, Debug, Serialize)]
pub struct Spanned<T> {
    pub x: T,
    pub span: Span,
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Proof {
    pub assert: Spanned<Term>,
    pub invariants: Vec<Spanned<Term>>,
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum ThmStmt {
    Assume(Term),
    Assert(Proof),
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Module {
    pub signature: Signature,
    pub defs: Vec<Definition>,
    pub statements: Vec<ThmStmt>,
}

#[cfg(test)]
mod tests {
    use std::vec;

    use super::{RelationDecl, Signature, Sort};
    use crate::fly::parser::parse_term;

    #[test]
    fn test_terms_by_sort() {
        let sort = |n: usize| Sort::Id(format!("T{n}"));

        let mut sig = Signature {
            sorts: vec!["T1".to_string(), "T2".to_string()],
            relations: vec![
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
                RelationDecl {
                    mutable: true,
                    name: "f12".to_string(),
                    args: vec![sort(1)],
                    sort: sort(2),
                },
                RelationDecl {
                    mutable: true,
                    name: "f21".to_string(),
                    args: vec![sort(2)],
                    sort: sort(1),
                },
                RelationDecl {
                    mutable: true,
                    name: "r".to_string(),
                    args: vec![sort(2), sort(1)],
                    sort: Sort::Bool,
                },
            ],
        };

        let sorted_vars = vec![
            vec!["a1".to_string(), "a2".to_string()],
            vec!["b".to_string()],
        ];

        let mut terms = sig.terms_by_sort(&sorted_vars, Some(0), true);
        assert_eq!(
            terms,
            vec![
                vec![
                    parse_term("a1").expect("parser error"),
                    parse_term("a2").expect("parser error"),
                    parse_term("c1").expect("parser error"),
                ],
                vec![
                    parse_term("b").expect("parser error"),
                    parse_term("c2").expect("parser error"),
                ],
                vec![
                    parse_term("a1=a2").expect("parser error"),
                    parse_term("a1=c1").expect("parser error"),
                    parse_term("a2=c1").expect("parser error"),
                    parse_term("b=c2").expect("parser error"),
                ]
            ]
        );

        terms = sig.terms_by_sort(&sorted_vars, Some(2), false);
        assert_eq!(
            terms,
            vec![
                vec![
                    parse_term("a1").expect("parser error"),
                    parse_term("a2").expect("parser error"),
                    parse_term("c1").expect("parser error"),
                    parse_term("f21(b)").expect("parser error"),
                    parse_term("f21(c2)").expect("parser error"),
                    parse_term("f21(f12(a1))").expect("parser error"),
                    parse_term("f21(f12(a2))").expect("parser error"),
                    parse_term("f21(f12(c1))").expect("parser error"),
                ],
                vec![
                    parse_term("b").expect("parser error"),
                    parse_term("c2").expect("parser error"),
                    parse_term("f12(a1)").expect("parser error"),
                    parse_term("f12(a2)").expect("parser error"),
                    parse_term("f12(c1)").expect("parser error"),
                    parse_term("f12(f21(b))").expect("parser error"),
                    parse_term("f12(f21(c2))").expect("parser error"),
                ],
                vec![
                    parse_term("r(b, a1)").expect("parser error"),
                    parse_term("r(b, a2)").expect("parser error"),
                    parse_term("r(b, c1)").expect("parser error"),
                    parse_term("r(c2, a1)").expect("parser error"),
                    parse_term("r(c2, a2)").expect("parser error"),
                    parse_term("r(c2, c1)").expect("parser error"),
                    parse_term("r(b, f21(b))").expect("parser error"),
                    parse_term("r(b, f21(c2))").expect("parser error"),
                    parse_term("r(c2, f21(b))").expect("parser error"),
                    parse_term("r(c2, f21(c2))").expect("parser error"),
                    parse_term("r(f12(a1), a1)").expect("parser error"),
                    parse_term("r(f12(a1), a2)").expect("parser error"),
                    parse_term("r(f12(a1), c1)").expect("parser error"),
                    parse_term("r(f12(a2), a1)").expect("parser error"),
                    parse_term("r(f12(a2), a2)").expect("parser error"),
                    parse_term("r(f12(a2), c1)").expect("parser error"),
                    parse_term("r(f12(c1), a1)").expect("parser error"),
                    parse_term("r(f12(c1), a2)").expect("parser error"),
                    parse_term("r(f12(c1), c1)").expect("parser error"),
                    parse_term("r(f12(a1), f21(b))").expect("parser error"),
                    parse_term("r(f12(a1), f21(c2))").expect("parser error"),
                    parse_term("r(f12(a2), f21(b))").expect("parser error"),
                    parse_term("r(f12(a2), f21(c2))").expect("parser error"),
                    parse_term("r(f12(c1), f21(b))").expect("parser error"),
                    parse_term("r(f12(c1), f21(c2))").expect("parser error"),
                ]
            ]
        );

        sig = Signature {
            sorts: vec!["T1".to_string(), "T2".to_string()],
            relations: vec![
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
                RelationDecl {
                    mutable: true,
                    name: "f12".to_string(),
                    args: vec![sort(1)],
                    sort: sort(2),
                },
                RelationDecl {
                    mutable: true,
                    name: "r".to_string(),
                    args: vec![sort(2), sort(1)],
                    sort: Sort::Bool,
                },
            ],
        };

        terms = sig.terms_by_sort(&sorted_vars, None, false);
        assert_eq!(
            terms,
            vec![
                vec![
                    parse_term("a1").expect("parser error"),
                    parse_term("a2").expect("parser error"),
                    parse_term("c1").expect("parser error"),
                ],
                vec![
                    parse_term("b").expect("parser error"),
                    parse_term("c2").expect("parser error"),
                    parse_term("f12(a1)").expect("parser error"),
                    parse_term("f12(a2)").expect("parser error"),
                    parse_term("f12(c1)").expect("parser error"),
                ],
                vec![
                    parse_term("r(b, a1)").expect("parser error"),
                    parse_term("r(b, a2)").expect("parser error"),
                    parse_term("r(b, c1)").expect("parser error"),
                    parse_term("r(c2, a1)").expect("parser error"),
                    parse_term("r(c2, a2)").expect("parser error"),
                    parse_term("r(c2, c1)").expect("parser error"),
                    parse_term("r(f12(a1), a1)").expect("parser error"),
                    parse_term("r(f12(a1), a2)").expect("parser error"),
                    parse_term("r(f12(a1), c1)").expect("parser error"),
                    parse_term("r(f12(a2), a1)").expect("parser error"),
                    parse_term("r(f12(a2), a2)").expect("parser error"),
                    parse_term("r(f12(a2), c1)").expect("parser error"),
                    parse_term("r(f12(c1), a1)").expect("parser error"),
                    parse_term("r(f12(c1), a2)").expect("parser error"),
                    parse_term("r(f12(c1), c1)").expect("parser error"),
                ]
            ]
        );
    }
}
