// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! A structure that can map between (relation name, arguments) pairs and indices.

use crate::quant_enum::*;
use biodivine_lib_bdd::*;
use fly::{ouritertools::OurItertools, semantics::*, syntax::*};
use std::{collections::HashMap, sync::Arc};

/// Holds a map from (relation name, arguments) pairs to a number. The number is used
/// for different purposes depending on the checker, but this is common functionality
/// among most of the bounded model checkers. This map also keeps track of the number
/// of primes on mutable relations, and also supports creating unique indices that
/// don't correspond to relations. Other features:
///   - It also remembers the signature and universe that were used to create it,
///   because functions that need this object frequently also need the signature or
///   the universe, and this means that they don't need to accept them separately.
///   - It wraps the BDD library that we're using, because anyone who wants to use
///   BDDs needs to have both a`BddVariableSet` and this mapping, so it makes sense
///   to bundle them together.
pub struct Indices {
    /// The signature used to create this object
    pub signature: Arc<Signature>,
    /// The universe used to create this object
    pub universe: UniverseBounds,
    /// The number of copies of mutable relations that this object holds
    pub num_mutable_copies: usize,
    /// The number of indices in one copy of the mutable relations
    pub num_mutables: usize,
    /// The total number of indices that are used in a state
    pub num_indices: usize,
    /// The total number of indices that are tracked
    pub num_vars: usize,
    /// Data used by the BDD library to build new BDDs
    pub bdd_context: BddVariableSet,
    /// Map from indices to BddVariable objects
    pub bdd_variables: Vec<BddVariable>,
    /// The map that this object is wrapping
    indices: HashMap<String, HashMap<Vec<Element>, (usize, bool)>>,
}

impl Indices {
    /// Create a new `Indices` object from a signature, universe bounds, and the number
    /// of mutable copies to include.
    pub fn new(
        signature: Arc<Signature>,
        universe: &UniverseBounds,
        num_mutable_copies: usize,
    ) -> Indices {
        let (mutable, immutable): (Vec<_>, Vec<_>) = signature
            .relations
            .iter()
            .partition(|relation| relation.mutable);
        let elements = |relation: &&RelationDecl| {
            relation
                .args
                .iter()
                .map(|sort| cardinality(universe, sort))
                .map(|card| (0..card).collect::<Vec<usize>>())
                .multi_cartesian_product_fixed()
                .map(|element| (relation.name.clone(), element))
                .collect::<Vec<_>>()
        };

        let mut indices: HashMap<_, HashMap<_, _>> = HashMap::new();

        let mut num_mutables = 0;
        for (i, (r, e)) in mutable.iter().flat_map(elements).enumerate() {
            num_mutables += 1;
            indices.entry(r).or_default().insert(e, (i, true));
        }
        let mut num_immutables = 0;
        for (i, (r, e)) in immutable.iter().flat_map(elements).enumerate() {
            num_immutables += 1;
            indices
                .entry(r)
                .or_default()
                .insert(e, (num_mutables * num_mutable_copies + i, false));
        }
        let num_vars = num_mutables * num_mutable_copies + num_immutables;

        let bdd_context = BddVariableSet::new_anonymous(num_vars.try_into().unwrap());
        let bdd_variables = bdd_context.variables();

        Indices {
            signature,
            universe: universe.clone(),
            num_mutable_copies,
            num_mutables,
            num_indices: num_vars,
            num_vars,
            bdd_context,
            bdd_variables,
            indices,
        }
    }

    /// Get an index from the information contained in a `Term::App`.
    pub fn get(&self, relation: &str, primes: usize, elements: &[usize]) -> usize {
        assert!(primes < self.num_mutable_copies);
        let (mut i, mutable) = self.indices[relation][elements];
        if mutable {
            i += primes * self.num_mutables;
        }
        i
    }

    /// Create a new unique index that doesn't correspond to a relation.
    pub fn var(&mut self) -> usize {
        self.num_vars += 1;
        self.num_vars - 1
    }

    /// Returns an iterator over one copy of the mutable and immutable indices.
    pub fn iter(&self) -> impl Iterator<Item = (&String, &HashMap<Vec<Element>, (usize, bool)>)> {
        self.indices.iter()
    }

    /// Get the `BddVariable` corresponding to the given `Term::App`.
    pub fn bdd_var(&self, relation: &str, primes: usize, elements: &[usize]) -> Bdd {
        self.bdd_context
            .mk_var(self.bdd_variables[self.get(relation, primes, elements)])
    }

    /// Construct an n-ary conjunction of `Bdd`s.
    pub fn bdd_and(&self, bdds: impl IntoIterator<Item = Bdd>) -> Bdd {
        bdds.into_iter()
            .fold(self.bdd_context.mk_true(), |acc, term| acc.and(&term))
    }

    /// Construct an n-ary disjunction of `Bdd`s.
    pub fn bdd_or(&self, bdds: impl IntoIterator<Item = Bdd>) -> Bdd {
        bdds.into_iter()
            .fold(self.bdd_context.mk_false(), |acc, term| acc.or(&term))
    }

    /// Construct a `Bdd` from an `Enumerated`.
    pub fn bdd_from_enumerated(&self, term: Enumerated) -> Bdd {
        let go = |term| self.bdd_from_enumerated(term);
        match term {
            Enumerated::And(xs) => self.bdd_and(xs.into_iter().map(go)),
            Enumerated::Or(xs) => self.bdd_or(xs.into_iter().map(go)),
            Enumerated::Not(x) => go(*x).not(),
            Enumerated::Eq(x, y) => go(*x).iff(&go(*y)),
            Enumerated::App(name, primes, args) => self.bdd_var(&name, primes, &args),
        }
    }

    /// Construct a [`Model`] given a function over its indices at some time.
    pub fn model(&self, primes: usize, f: impl Fn(usize) -> usize) -> Model {
        Model::new(
            &self.signature,
            &self
                .signature
                .sorts
                .iter()
                .map(|s| self.universe[s])
                .collect(),
            self.signature
                .relations
                .iter()
                .map(|r| {
                    let shape: Vec<_> = r
                        .args
                        .iter()
                        .map(|s| cardinality(&self.universe, s))
                        .chain([cardinality(&self.universe, &r.sort)])
                        .collect();
                    Interpretation::new(&shape, |xs| f(self.get(&r.name, primes, xs)))
                })
                .collect(),
        )
    }
}
