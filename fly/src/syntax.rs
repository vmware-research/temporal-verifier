// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! The flyvy AST for terms and modules.

use itertools::Itertools;
use std::fmt;

use serde::Serialize;

use crate::ouritertools::OurItertools;

/// A Sort represents a collection of values, which can be the built-in boolean
/// sort or a named sort (coming from a Signature).
#[derive(PartialEq, Eq, Clone, Debug, Hash, Serialize, PartialOrd, Ord)]
pub enum Sort {
    /// Boolean sort
    Bool,
    /// Uninterpreted sort identified by its name
    Uninterpreted(String),
    /*
    /// Unspecified sort
    ///
    /// This is used in sort inference, and assumed to not occur anywhere after
    /// sort inference.
    Unknown,
    */
}

impl Sort {
    /// Smart constructor for uninterpreted sort that takes &str
    pub fn uninterpreted(name: &str) -> Self {
        Self::Uninterpreted(name.to_string())
    }

    /// Unknown sort (used in sort inference) is represented as Uninterpreted("")
    pub fn unknown() -> Self {
        Self::uninterpreted("")
    }
}

impl From<&str> for Sort {
    /// This is mostly for the Binder smart constructor, making it possible to
    /// pass either Sort, &Sort, &str, or &String
    fn from(value: &str) -> Self {
        Self::uninterpreted(value)
    }
}

impl From<&String> for Sort {
    /// This is mostly for the Binder smart constructor, making it possible to
    /// pass either Sort, &Sort, &str, or &String
    fn from(value: &String) -> Self {
        Self::uninterpreted(value)
    }
}

impl From<&Sort> for Sort {
    /// This is mostly for the Binder smart constructor, making it possible to
    /// pass either Sort, &Sort, or &str
    fn from(value: &Self) -> Self {
        value.clone()
    }
}

impl fmt::Display for Sort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Sort::Bool => "bool".to_string(),
            Sort::Uninterpreted(i) => i.to_string(),
        };
        write!(f, "{s}")
    }
}

/// A binder is a variable name and a sort (used e.g. for a quantifier)
#[derive(PartialEq, Eq, Clone, Debug, Hash, PartialOrd, Ord)]
pub struct Binder {
    /// Bound name
    pub name: String,
    /// Sort for this binder
    pub sort: Sort,
}

impl Binder {
    /// Smart constructor for a Binder that takes arguments by reference.
    pub fn new<T>(name: &str, sort: T) -> Self
    where
        T: Into<Sort>,
    {
        Binder {
            name: name.to_string(),
            sort: sort.into(),
        }
    }
}

/// Unary operators
#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash, PartialOrd, Ord)]
pub enum UOp {
    /// Boolean negation
    Not,
    /// Gives the value of the argument one step in the future
    Prime,
    /// Always temporal modality
    Always,
    /// Eventually temporal modality
    Eventually,
    /// Used for the l2s construction (may end up replaced with just Prime)
    Next,
    /// Past operator, used only for the l2s construction
    Previous,
}

/// Binary operators
#[allow(missing_docs)]
#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash, PartialOrd, Ord)]
pub enum BinOp {
    Equals,
    NotEquals,
    Implies,
    Iff,
    /// Used for the l2s construction
    Until,
    /// Past operator, used only for the l2s construction
    Since,
}

/// N-ary logical operators
#[allow(missing_docs)]
#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash, PartialOrd, Ord)]
pub enum NOp {
    And,
    Or,
}

/// A kind of quantifier (forall or exists)
#[allow(missing_docs)]
#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash, PartialOrd, Ord)]
pub enum Quantifier {
    Forall,
    Exists,
}

/// FO-LTL term or formula
///
/// FO-LTL (first-order linear temporal logic) is an extension of
/// first-order logic where the semantics is given in terms of
/// infinite sequences of models (over a shared universe). A term is
/// interpreted at a particular point (time) in the sequence, and
/// using temporal operators it can also query the past or future. For
/// example: `exists x. p(x) & (previous !p(x)) & always r(x)` means
/// that there exists some element for which `p` now holds, but it
/// didn't hold a moment ago, and from this point onwards `r` keeps
/// holding for it.
///
/// The temporal operators supported are: Prime, Next, Prev, Until,
/// Since, Always, Eventually (see [`UOp`] and [`BinOp`]).
#[derive(PartialEq, Eq, Clone, Debug, Hash, PartialOrd, Ord)]
pub enum Term {
    /// A constant true or false
    Literal(bool),
    /// A reference to a bound variable or function in the signature
    Id(String),
    /// Application. `App(f, n_primes, args)` represents applying the function
    /// `f` with `n_primes` primes to `args`.
    App(String, usize, Vec<Term>),
    /// An applied unary operation
    UnaryOp(UOp, Box<Term>),
    /// An applied binary operation
    BinOp(BinOp, Box<Term>, Box<Term>),
    /// An applied n-ary operation
    NAryOp(NOp, Vec<Term>),
    /// If-then-else
    Ite {
        /// A boolean conditional
        cond: Box<Term>,
        /// Value of the Ite when `cond` is true
        then: Box<Term>,
        /// Value of the Ite when `cond` is false
        else_: Box<Term>,
    },
    /// A quantifier with a sequence of binders and a body where the binders
    /// might be used freely.
    #[allow(missing_docs)]
    Quantified {
        quantifier: Quantifier,
        /// The sequence of bindings bound by this quantifier. Might be empty.
        binders: Vec<Binder>,
        body: Box<Term>,
    },
}

impl From<&Term> for Term {
    /// This is mostly for smart constructor, making it possible to
    /// pass either Sort or &Sort with an automatic clone if needed
    fn from(value: &Self) -> Self {
        value.clone()
    }
}

/// Smart constructors for Term. These generally take arguments by reference and
/// clone them. Should this become a performence concern we can revisit this
/// choice.
impl Term {
    /// Smart constructor for Literal. Mainly here for uniformity.
    pub fn literal(value: bool) -> Self {
        Self::Literal(value)
    }

    /// Smart constructor for Literal(true)
    pub fn true_() -> Self {
        Self::Literal(true)
    }

    /// Smart constructor for Literal(false)
    pub fn false_() -> Self {
        Self::Literal(false)
    }

    /// Smart constructor for Id
    pub fn id(name: &str) -> Self {
        Self::Id(name.to_string())
    }

    /// Smart constructor for function application
    ///
    /// TODO(oded): I think in case args is empty we should return Id, but maybe
    /// we do that after Id has n_primes
    pub fn app<I>(f: &str, n_primes: usize, args: I) -> Self
    where
        I: IntoIterator,
        I::Item: Into<Term>,
    {
        Self::App(
            f.to_string(),
            n_primes,
            args.into_iter().map(|x| x.into()).collect(),
        )
    }

    //////////////////
    // Unary operations: Not, Prime, Always, Eventually, Next, Previously
    //////////////////

    /// Smart constructor for not. Note this does not push negation inwards, but
    /// it does cancel double negation and flips Equals and NotEquals
    pub fn not<T>(t: T) -> Self
    where
        T: Into<Term>,
    {
        let t = t.into();
        match t {
            Self::UnaryOp(UOp::Not, body) => *body,
            Self::BinOp(BinOp::Equals, lhs, rhs) => Self::BinOp(BinOp::NotEquals, lhs, rhs),
            Self::BinOp(BinOp::NotEquals, lhs, rhs) => Self::BinOp(BinOp::Equals, lhs, rhs),
            _ => Self::UnaryOp(UOp::Not, Box::new(t)),
        }
    }

    /// Smart constructor for prime. Note this does not push primes (which would
    /// require a signature and context)
    pub fn prime<T>(t: T) -> Self
    where
        T: Into<Term>,
    {
        Self::UnaryOp(UOp::Prime, Box::new(t.into()))
    }

    /// Smart constructor for always
    pub fn always<T>(t: T) -> Self
    where
        T: Into<Term>,
    {
        Self::UnaryOp(UOp::Always, Box::new(t.into()))
    }

    /// Smart constructor for eventually
    pub fn eventually<T>(t: T) -> Self
    where
        T: Into<Term>,
    {
        Self::UnaryOp(UOp::Eventually, Box::new(t.into()))
    }

    /// Smart constructor for next
    pub fn next<T>(t: T) -> Self
    where
        T: Into<Term>,
    {
        Self::UnaryOp(UOp::Next, Box::new(t.into()))
    }

    /// Smart constructor for previous
    pub fn previous<T>(t: T) -> Self
    where
        T: Into<Term>,
    {
        Self::UnaryOp(UOp::Previous, Box::new(t.into()))
    }

    //////////////////
    // Binary operations: Equals, NotEquals, Implies, Iff, Until, Since
    //////////////////

    /// Smart constructor for `lhs = rhs`
    pub fn equals<T1, T2>(lhs: T1, rhs: T2) -> Self
    where
        T1: Into<Term>,
        T2: Into<Term>,
    {
        Self::BinOp(BinOp::Equals, Box::new(lhs.into()), Box::new(rhs.into()))
    }

    /// Smart constructor for `lhs != rhs`
    pub fn not_equals<T1, T2>(lhs: T1, rhs: T2) -> Self
    where
        T1: Into<Term>,
        T2: Into<Term>,
    {
        Self::BinOp(BinOp::NotEquals, Box::new(lhs.into()), Box::new(rhs.into()))
    }

    /// Smart constructor for `lhs -> rhs`
    pub fn implies<T1, T2>(lhs: T1, rhs: T2) -> Self
    where
        T1: Into<Term>,
        T2: Into<Term>,
    {
        Self::BinOp(BinOp::Implies, Box::new(lhs.into()), Box::new(rhs.into()))
    }

    /// Smart constructor for `lhs <-> rhs`
    pub fn iff<T1, T2>(lhs: T1, rhs: T2) -> Self
    where
        T1: Into<Term>,
        T2: Into<Term>,
    {
        Self::BinOp(BinOp::Iff, Box::new(lhs.into()), Box::new(rhs.into()))
    }

    /// Smart constructor for `lhs until rhs`
    pub fn until<T1, T2>(lhs: T1, rhs: T2) -> Self
    where
        T1: Into<Term>,
        T2: Into<Term>,
    {
        Self::BinOp(BinOp::Until, Box::new(lhs.into()), Box::new(rhs.into()))
    }

    /// Smart constructor for `lhs since rhs`
    pub fn since<T1, T2>(lhs: T1, rhs: T2) -> Self
    where
        T1: Into<Term>,
        T2: Into<Term>,
    {
        Self::BinOp(BinOp::Since, Box::new(lhs.into()), Box::new(rhs.into()))
    }

    //////////////////
    // N-ary operations: And, Or
    //////////////////

    /// Helper function for [`Self::and`] and [`Self::or`]
    fn flatten_terms_of_op(ts: Vec<Term>, op: NOp) -> Vec<Term> {
        ts.into_iter()
            .flat_map(|t| match t {
                Self::NAryOp(op2, ts2) if op == op2 => ts2,
                _ => vec![t],
            })
            .collect()
    }

    /// Smart constructor for And. Zero and one conjuncts are handled specially, and
    /// conjuncts that are And are flattened (but not recursively).
    pub fn and<I>(ts: I) -> Self
    where
        I: IntoIterator,
        I::Item: Into<Term>,
    {
        let mut ts = ts.into_iter().map(|x| x.into()).collect_vec();
        if ts.is_empty() {
            Self::true_()
        } else if ts.len() == 1 {
            return ts.pop().unwrap();
        } else {
            Self::NAryOp(NOp::And, Self::flatten_terms_of_op(ts, NOp::And))
        }
    }

    /// Smart constructor for Or. Zero and one disjuncts are handled specially,
    /// and disjuncts that are Or are flattened (but not recursively).
    pub fn or<I>(ts: I) -> Self
    where
        I: IntoIterator,
        I::Item: Into<Term>,
    {
        let mut ts = ts.into_iter().map(|x| x.into()).collect_vec();
        if ts.is_empty() {
            Self::false_()
        } else if ts.len() == 1 {
            return ts.pop().unwrap();
        } else {
            Self::NAryOp(NOp::Or, Self::flatten_terms_of_op(ts, NOp::Or))
        }
    }

    //////////////////
    // Remaining operations: Ite, Forall, Exists
    //////////////////

    /// Smart constructor for Ite
    pub fn ite<T1, T2, T3>(cond: T1, then: T2, else_: T3) -> Self
    where
        T1: Into<Term>,
        T2: Into<Term>,
        T3: Into<Term>,
    {
        Self::Ite {
            cond: Box::new(cond.into()),
            then: Box::new(then.into()),
            else_: Box::new(else_.into()),
        }
    }

    /// Helper function for forall, exists. Special handling for zero binders
    /// and one level flattening.
    fn quantify(quantifier: Quantifier, binders: Vec<Binder>, body: Self) -> Self {
        // debug_assert that all binders have distinct names
        debug_assert!(binders
            .iter()
            .enumerate()
            .all(|(i, b1)| binders[(i + 1)..].iter().all(|b2| b1.name != b2.name)));
        if binders.is_empty() {
            body
        } else {
            match body {
                Term::Quantified {
                    quantifier: quantifier2,
                    binders: binders2,
                    body: body2,
                } if quantifier == quantifier2 => {
                    // Handle shadowing
                    let mut combined_binders = binders
                        .into_iter()
                        .filter(|b| binders2.iter().all(|b2| b.name != b2.name))
                        .collect_vec();
                    combined_binders.extend(binders2);
                    Self::Quantified {
                        quantifier,
                        binders: combined_binders,
                        body: body2,
                    }
                }
                _ => Self::Quantified {
                    quantifier,
                    binders,
                    body: Box::new(body),
                },
            }
        }
    }

    /// Smart constructor for `forall binders. body`. Zero binders is handled
    /// specially, and nested forall is kept flat (but not recursively).
    pub fn forall<I, T>(binders: I, body: T) -> Self
    where
        I: IntoIterator,
        I::IntoIter: Iterator<Item = Binder>,
        T: Into<Term>,
    {
        let binders = binders.into_iter().collect_vec();
        let body = body.into();
        Self::quantify(Quantifier::Forall, binders, body)
    }

    /// Smart constructor for `exists binders. body`. Zero binders is handled
    /// specially, and nested exists is kept flat (but not recursively).
    pub fn exists<I, T>(binders: I, body: T) -> Self
    where
        I: IntoIterator,
        I::IntoIter: Iterator<Item = Binder>,
        T: Into<Term>,
    {
        let binders = binders.into_iter().collect_vec();
        let body = body.into();
        Self::quantify(Quantifier::Exists, binders, body)
    }
}

/// Leftovers that should be eliminated
impl Term {
    /// Convenience function to create `!t`
    ///
    /// TODO(oded): eliminate this in favor of not, or maybe make it a "method"
    pub fn negate(t: Term) -> Self {
        Self::UnaryOp(UOp::Not, Box::new(t))
    }

    /// Construct a simplified term logically equivalent to `!t`
    ///
    /// TODO(oded): I think this should be eliminated once we have NNF
    ///             conversion (or even before). This is a very strange function
    ///             anyway, used only once in UPDR. Note that it supports
    ///             negating forall but not exists. Maybe for now it should be moved to updr.rs.
    pub fn negate_and_simplify(t: Term) -> Self {
        match t {
            Term::Literal(b) => Term::Literal(!b),
            Term::UnaryOp(UOp::Not, t) => *t,
            Term::UnaryOp(..) => panic!("got UnaryOp other than Not!"),
            Term::BinOp(BinOp::NotEquals, lhs, rhs) => Term::BinOp(BinOp::Equals, lhs, rhs),
            Term::BinOp(BinOp::Equals, lhs, rhs) => Term::BinOp(BinOp::NotEquals, lhs, rhs),
            Term::NAryOp(NOp::Or, terms) => Term::NAryOp(
                NOp::And,
                terms.into_iter().map(Term::negate_and_simplify).collect(),
            ),
            Term::NAryOp(NOp::And, terms) => Term::NAryOp(
                NOp::Or,
                terms.into_iter().map(Term::negate_and_simplify).collect(),
            ),
            Term::Id(_) | Term::App(_, _, _) => Term::negate(t),
            Term::Quantified {
                quantifier: Quantifier::Forall,
                binders,
                body,
            } => Term::Quantified {
                quantifier: Quantifier::Exists,
                binders,
                body: Box::new(Term::negate_and_simplify(*body)),
            },
            _ => panic!("got illegal operator in negate and simplify"),
        }
    }
}

// TODO(oded): rename Relation to Function

/// The declaration of a single function as part of a Signature
#[derive(PartialEq, Eq, Clone, Debug, Serialize)]
pub struct RelationDecl {
    /// If false, the relation is immutable with respect to time
    pub mutable: bool,
    /// The name of the function
    pub name: String,
    /// Sorts for the arguments (which are unnamed)
    pub args: Vec<Sort>,
    /// Sort for the return value
    pub sort: Sort,
}

/// A Signature defines a state space for an LTL Term, consisting of some number
/// of uninterpreted sorts and declarations for functions using those sorts (or
/// the built-in boolean sort).
#[derive(PartialEq, Eq, Clone, Debug, Serialize)]
pub struct Signature {
    /// Names of uninterpreted sorts
    pub sorts: Vec<String>,
    /// Declarations for functions
    pub relations: Vec<RelationDecl>,
}

impl Signature {
    /// Get the index of an uninterpreted sort.
    pub fn sort_idx(&self, sort: &Sort) -> usize {
        match sort {
            Sort::Bool => panic!("invalid sort {sort}"),
            Sort::Uninterpreted(sort) => self
                .sorts
                .iter()
                .position(|x| x == sort)
                .unwrap_or_else(|| panic!("invalid sort {sort}")),
        }
    }

    /// Check if `name` is the name of an uninterpreted sort in the signature
    pub fn contains_sort(&self, name: &str) -> bool {
        self.sorts.iter().any(|s| s == name)
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

    /// Returns true if name is an immutable relation, or a primed version of one.
    pub fn is_immutable(&self, name: &str) -> bool {
        let name = name.trim_end_matches('\'');
        match self.relations.iter().find(|x| x.name == name) {
            Some(decl) => !decl.mutable,
            None => false,
        }
    }

    /// Get the index of a named function in the signature. Panics if invalid.
    pub fn relation_idx(&self, name: &str) -> usize {
        self.relations
            .iter()
            .position(|x| x.name == name)
            .unwrap_or_else(|| panic!("invalid relation {name}"))
    }

    /// Check if `name` is a relation in the signature, or a primed version of
    /// one.
    pub fn contains_relation(&self, name: &str) -> bool {
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
                    .multi_cartesian_product_fixed()
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
                            .multi_cartesian_product_fixed()
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

/// A definition and its body. These are essentially treated as macros over the
/// functions in the signature.
#[allow(missing_docs)]
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
    /// Start of the span as a character offset
    pub start: usize,
    /// End of the span as a character offset
    pub end: usize,
}

/// Wrap a value of type `T` with its `Span`
#[allow(missing_docs)]
#[derive(PartialEq, Eq, Clone, Debug, Serialize)]
pub struct Spanned<T> {
    pub x: T,
    pub span: Option<Span>,
}

/// A Proof is an asserted boolean Term and a list of invariants to prove that
/// assertion inductively.
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Proof {
    /// A boolean term to be proven equivalent to true
    pub assert: Spanned<Term>,
    /// Invariants whose conjunction should be inductive to prove `assert`
    pub invariants: Vec<Spanned<Term>>,
}

/// A theorem statement that can appear in a module. Statements are interpreted
/// imperatively in order, so earlier assumes and asserts may be used in later
/// checks.
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum ThmStmt {
    /// Assume that a term is true without proof for the remaining statements
    Assume(Term),
    /// Assert a term with an inductive proof
    Assert(Proof),
}

/// A Module consists of a Signature and some theorem statements to be proven in that signature.
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Module {
    /// Signature for all terms in the module
    pub signature: Signature,
    /// Helper definitions (essentially macros) that may be used in the module's
    /// statements
    pub defs: Vec<Definition>,
    /// A sequence of theorem statements that the module makes
    pub statements: Vec<ThmStmt>,
}

#[cfg(test)]
mod tests {
    use std::vec;

    use super::{RelationDecl, Signature, Sort};
    use crate::parser::term;

    #[test]
    fn test_terms_by_sort() {
        let sort = |n: usize| Sort::Uninterpreted(format!("T{n}"));

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
                vec![term("a1"), term("a2"), term("c1"),],
                vec![term("b"), term("c2"),],
                vec![term("a1=a2"), term("a1=c1"), term("a2=c1"), term("b=c2"),]
            ]
        );

        terms = sig.terms_by_sort(&sorted_vars, Some(2), false);
        assert_eq!(
            terms,
            vec![
                vec![
                    term("a1"),
                    term("a2"),
                    term("c1"),
                    term("f21(b)"),
                    term("f21(c2)"),
                    term("f21(f12(a1))"),
                    term("f21(f12(a2))"),
                    term("f21(f12(c1))"),
                ],
                vec![
                    term("b"),
                    term("c2"),
                    term("f12(a1)"),
                    term("f12(a2)"),
                    term("f12(c1)"),
                    term("f12(f21(b))"),
                    term("f12(f21(c2))"),
                ],
                vec![
                    term("r(b, a1)"),
                    term("r(b, a2)"),
                    term("r(b, c1)"),
                    term("r(c2, a1)"),
                    term("r(c2, a2)"),
                    term("r(c2, c1)"),
                    term("r(b, f21(b))"),
                    term("r(b, f21(c2))"),
                    term("r(c2, f21(b))"),
                    term("r(c2, f21(c2))"),
                    term("r(f12(a1), a1)"),
                    term("r(f12(a1), a2)"),
                    term("r(f12(a1), c1)"),
                    term("r(f12(a2), a1)"),
                    term("r(f12(a2), a2)"),
                    term("r(f12(a2), c1)"),
                    term("r(f12(c1), a1)"),
                    term("r(f12(c1), a2)"),
                    term("r(f12(c1), c1)"),
                    term("r(f12(a1), f21(b))"),
                    term("r(f12(a1), f21(c2))"),
                    term("r(f12(a2), f21(b))"),
                    term("r(f12(a2), f21(c2))"),
                    term("r(f12(c1), f21(b))"),
                    term("r(f12(c1), f21(c2))"),
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
                vec![term("a1"), term("a2"), term("c1"),],
                vec![
                    term("b"),
                    term("c2"),
                    term("f12(a1)"),
                    term("f12(a2)"),
                    term("f12(c1)"),
                ],
                vec![
                    term("r(b, a1)"),
                    term("r(b, a2)"),
                    term("r(b, c1)"),
                    term("r(c2, a1)"),
                    term("r(c2, a2)"),
                    term("r(c2, c1)"),
                    term("r(f12(a1), a1)"),
                    term("r(f12(a1), a2)"),
                    term("r(f12(a1), c1)"),
                    term("r(f12(a2), a1)"),
                    term("r(f12(a2), a2)"),
                    term("r(f12(a2), c1)"),
                    term("r(f12(c1), a1)"),
                    term("r(f12(c1), a2)"),
                    term("r(f12(c1), c1)"),
                ]
            ]
        );
    }
}
