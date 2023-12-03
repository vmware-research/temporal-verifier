// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Prove safety temporal assertions using invariants.

use thiserror::Error;

use fly::{
    syntax::*,
    term::{fo::FirstOrder, prime::Next},
    transitions::Proof,
};

/// A temporal property expressed as an invariant problem.
#[derive(Debug, Clone)]
pub struct InvariantAssertion {
    /// The signature
    pub sig: Signature,
    /// The initial states
    pub init: Term,
    /// The states reachable in one step
    pub next: Term,
    /// The assumptions that were recognized as invariants
    pub assumed_inv: Term,
    /// The invariant given in the module
    pub inv: Spanned<Term>,
    /// The other invariants in the same proof as `inv`
    pub proof_invs: Vec<Spanned<Term>>,
}

/// An error that occured while constructing an invariant assertion
#[derive(Error, Debug)]
pub enum InvariantError {
    /// Assertion is not a safety property
    #[error("assertion is not of the form (always p)")]
    NotSafety,
    /// Proof invariant mentioned more than one timestep
    #[error("proof invariant is not a well-formed single-state fomula")]
    BadProofInvariant,
}

impl InvariantAssertion {
    /// Construct an invariant assertion to represent a temporal assertion.
    pub fn for_assert(
        sig: &Signature,
        inits: &[Term],
        transitions: &[Term],
        axioms: &[Term],
        proof: &Proof,
    ) -> Result<Self, InvariantError> {
        Ok(Self {
            sig: sig.clone(),
            init: Term::and(inits.iter().cloned()),
            next: Next::new(sig).normalize(&Term::and(transitions.iter().cloned())),
            assumed_inv: Term::and(axioms.iter().cloned()),
            inv: proof.safety.clone(),
            proof_invs: proof.invariants.clone(),
        })
    }

    fn invariants(&self) -> impl Iterator<Item = &Spanned<Term>> {
        [&self.inv].into_iter().chain(self.proof_invs.iter())
    }

    fn inductive_invariant(&self) -> Term {
        Term::and(self.invariants().map(|inv| &inv.x))
    }

    /// Convert this invariant to a first order term.
    pub fn initiation(&self) -> FirstOrder {
        let lhs = Term::and(vec![self.init.clone(), self.assumed_inv.clone()]);
        let rhs = self.inductive_invariant();
        FirstOrder::new(Term::implies(lhs, rhs))
    }

    /// Return a list of consecution checks. All checks assumes `self.next`,
    /// `self.assumed_inv`, `prime(self.assumed_inv)`, and that all of the
    /// invariants to be proven hold in the pre state. Each check shows that
    /// given these assumptions, one of the invariants (either the proof
    /// invariants or top-level assertion) holds in the post state.
    pub fn consecutions(&self) -> Vec<(Option<Span>, FirstOrder)> {
        let lhs = Term::and(vec![
            self.assumed_inv.clone(),
            self.next.clone(),
            Next::new(&self.sig).prime(&self.assumed_inv),
            self.inductive_invariant(),
        ]);
        self.invariants()
            .map(|inv| {
                log::info!("checking inductiveness of {}", inv.x);
                let rhs = Next::new(&self.sig).prime(&inv.x);
                let consection = FirstOrder::new(Term::implies(lhs.clone(), rhs));
                (inv.span, consection)
            })
            .collect()
    }
}
