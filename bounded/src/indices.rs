// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! A structure that can map between (relation name, arguments) pairs and indices.

use crate::quantenum::*;
use biodivine_lib_bdd::*;
use fly::{ouritertools::OurItertools, semantics::*, syntax::*};
use std::collections::HashMap;

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
pub struct Indices<'a> {
    /// The signature used to create this object
    pub signature: &'a Signature,
    /// The universe used to create this object
    pub universe: &'a UniverseBounds,
    /// The number of copies of mutable relations that this object holds
    pub num_mutable_copies: usize,
    /// The number of indices in one copy of the mutable relations
    pub num_mutables: usize,
    /// The total number of indices that are tracked
    pub num_vars: usize,
    /// Data used by the BDD library to build new BDDs
    pub bdd_context: BddVariableSet,
    /// Map from indices to BddVariable objects
    pub bdd_variables: Vec<BddVariable>,
    /// The map that this object is wrapping
    indices: HashMap<&'a str, HashMap<Vec<Element>, (usize, bool)>>,
}

impl Indices<'_> {
    /// Create a new `Indices` object from a signature, universe bounds, and the number
    /// of mutable copies to include.
    pub fn new<'a>(
        signature: &'a Signature,
        universe: &'a UniverseBounds,
        num_mutable_copies: usize,
    ) -> Indices<'a> {
        let (mutable, immutable): (Vec<_>, Vec<_>) = signature
            .relations
            .iter()
            .partition(|relation| relation.mutable);
        let elements = |relation: &&'a RelationDecl| {
            relation
                .args
                .iter()
                .map(|sort| cardinality(universe, sort))
                .map(|card| (0..card).collect::<Vec<usize>>())
                .multi_cartesian_product_fixed()
                .map(|element| (relation.name.as_str(), element))
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
            universe,
            num_mutable_copies,
            num_mutables,
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
    pub fn iter(&self) -> impl Iterator<Item = (&&str, &HashMap<Vec<Element>, (usize, bool)>)> {
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
}
