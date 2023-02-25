// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Normalize primes (next) down to constants.

use crate::fly::syntax::{Term, UOp};

/// Wrap t in `next` primes.
fn with_primes(mut t: Term, next: usize) -> Term {
    for _ in 0..next {
        t = Term::UnaryOp(UOp::Prime, Box::new(t));
    }
    t
}

/// Push occurrences of prime inward in `t`, adding `next` primes at the bottom.
/// Keeps track of a set of bound variables `bound` that should not be primed.
fn with_next(t: &Term, bound: im::HashSet<String>, next: usize) -> Term {
    let go = |t| with_next(t, bound.clone(), next);
    let go_box = |t| Box::new(go(t));
    match t {
        // increase next
        Term::UnaryOp(UOp::Prime, t) => with_next(t, bound.clone(), next + 1),
        // apply accumulated next
        Term::Id(s) => with_primes(
            Term::Id(s.clone()),
            if bound.contains(s) { 0 } else { next },
        ),
        // TODO: we do not add primes to arguments; this is just a heuristic
        Term::App(f, p, xs) => Term::App(f.clone(), p + next, xs.iter().map(go).collect()),

        // boring recursive cases
        Term::Literal(b) => Term::Literal(*b),
        Term::UnaryOp(op, t) => Term::UnaryOp(*op, go_box(t)),
        Term::BinOp(op, lhs, rhs) => Term::BinOp(*op, go_box(lhs), go_box(rhs)),
        Term::NAryOp(op, xs) => Term::NAryOp(*op, xs.iter().map(go).collect()),
        Term::Ite { cond, then, else_ } => Term::Ite {
            cond: go_box(cond),
            then: go_box(then),
            else_: go_box(else_),
        },
        Term::Quantified {
            quantifier,
            binders,
            body,
        } => Term::Quantified {
            quantifier: *quantifier,
            binders: binders.clone(),
            body: {
                let mut bound = bound.clone();
                bound.extend(binders.iter().map(|binder| binder.name.clone()));
                Box::new(with_next(body, bound, next))
            },
        },
    }
}

pub struct Next {}

impl Next {
    /// Normalize any occurrences of (p)' to push the prime as deep as possible,
    /// down to terms.
    pub fn normalize(t: &Term) -> Term {
        let bound = im::hashset! {};
        with_next(t, bound, 0)
    }

    /// Add a prime to t and push it as far as possible.
    pub fn prime(t: &Term) -> Term {
        Self::normalize(&Term::UnaryOp(UOp::Prime, Box::new(t.clone())))
    }
}

#[cfg(test)]
mod tests {
    use crate::fly::parser::parse_term;
    use crate::fly::syntax::Term;

    use super::Next;

    fn term(s: &str) -> Term {
        parse_term(s).unwrap()
    }

    #[test]
    fn test_normalize() {
        assert_eq!(Next::normalize(&term("r'(x) | z")), term("r'(x) | z"));
        assert_eq!(
            Next::normalize(&term("(r(x) | z & forall x:t. p(x)')'")),
            // this x gets primed because it's a free variable
            term("r'(x') | z' & forall x:t. p''(x)")
        );
        assert_eq!(
            Next::prime(&term("r(x) | z & forall x:t. p(x)'")),
            term("r'(x') | z' & forall x:t. p''(x)")
        );
    }
}
