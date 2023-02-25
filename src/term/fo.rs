// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! First-order (non-temporal) terms.
//!
//! See the documentation for [`FirstOrder`] for details.

use std::cmp::max;

use crate::fly::syntax::{Term, UOp};

use UOp::*;

/// First-order terms. The only allowed temporal construct is prime.
pub struct FirstOrder(pub Term);

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum Unrolling {
    Finite(usize),
    Infinite,
}

impl Unrolling {
    fn is_finite(&self) -> bool {
        matches!(self, Unrolling::Finite(_))
    }
}

impl std::ops::Add for Unrolling {
    type Output = Unrolling;

    fn add(self, rhs: Self) -> Self::Output {
        use Unrolling::*;
        match (self, rhs) {
            (Infinite, _) => Infinite,
            (_, Infinite) => Infinite,
            (Finite(n), Finite(m)) => Finite(n + m),
        }
    }
}

impl std::ops::BitAnd for Unrolling {
    type Output = Unrolling;

    fn bitand(self, rhs: Self) -> Self::Output {
        use Unrolling::*;
        match (self, rhs) {
            (Infinite, _) => Infinite,
            (_, Infinite) => Infinite,
            (Finite(n), Finite(m)) => Finite(max(n, m)),
        }
    }
}

fn max_unrolling(t: &[Term]) -> Unrolling {
    t.iter()
        .fold(Unrolling::Finite(0), |acc, t| acc & unrolling(t))
}

fn unrolling(t: &Term) -> Unrolling {
    use Unrolling::Finite;
    match t {
        Term::Literal(_) | Term::Id(_) => Finite(0),
        Term::App(_f, p, x) => Finite(*p) & max_unrolling(x),
        Term::UnaryOp(Always | Eventually, _) => Unrolling::Infinite,
        Term::UnaryOp(Not, t) => unrolling(t),
        Term::UnaryOp(Prime, t) => Finite(1) + unrolling(t),
        Term::BinOp(_, lhs, rhs) => unrolling(lhs) & unrolling(rhs),
        Term::NAryOp(_, ts) => max_unrolling(ts),
        Term::Ite { cond, then, else_ } => unrolling(cond) & unrolling(then) & unrolling(else_),
        Term::Quantified { body, .. } => unrolling(body),
    }
}

impl FirstOrder {
    pub fn new(t: Term) -> Self {
        assert!(unrolling(&t).is_finite(), "term is not first order");
        Self(t)
    }

    /// Returns the number of nested primes in `t`, or None if term is not
    /// first-order.
    // TODO(oded): change this so 1 means no primes, 2 means 1 prime, and 0
    // means no mutable symbols mentioned.
    pub fn unrolling(t: &Term) -> Option<usize> {
        match unrolling(t) {
            Unrolling::Finite(n) => Some(n),
            Unrolling::Infinite => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::fly::parser::parse_term;
    use crate::fly::syntax::Term;

    use super::FirstOrder;

    fn term(s: &str) -> Term {
        parse_term(s).unwrap()
    }

    #[test]
    fn test_fo() {
        assert_eq!(
            FirstOrder::unrolling(&term("p & exists x:t. r(x) & p -> z(x)")),
            Some(0),
        );
        assert_eq!(
            FirstOrder::unrolling(&term("p | q & forall x:t. r'(x)")),
            Some(1),
        );
        assert_eq!(
            FirstOrder::unrolling(&term("p' | q & (forall x:t. r'(x))'")),
            Some(2),
        );
    }

    #[test]
    fn test_temporal() {
        assert_eq!(
            FirstOrder::unrolling(&term("(always p) & (eventually q)")),
            None
        );
        assert_eq!(
            FirstOrder::unrolling(&term("a | b & exists x:t. always p(x)")),
            None
        );
    }
}
