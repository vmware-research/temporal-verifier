// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Manage sets of quantified lemmas used in inference, and provide foundational algorithms
//! for handling them, e.g. checking subsumption, weakening, etc.

use std::collections::BTreeMap;
use std::fmt::Debug;
use std::iter::empty;
use std::ops::AddAssign;
use std::sync::Arc;
use std::time::Instant;

use crate::hashmap::HashMap;

use itertools::Itertools;
use rayon::prelude::*;

use crate::{
    basics::OrderedTerms,
    qalpha::language::{BoundedLanguage, FormulaId, FormulaSet},
};
use fly::{
    semantics::{Assignment, Model},
    syntax::{Quantifier, Term},
};

macro_rules! timed {
    ($blk:block) => {{
        let start = Instant::now();
        $blk
        start.elapsed()
    }};
}

/// Manages lemmas from a [`BoundedLanguage`] and allows weakening them simultaneously.
pub struct WeakenLemmaSet<L: BoundedLanguage> {
    lang: Arc<L>,
    set: L::Set,
    sorted: BTreeMap<LemmaKey, Term>,
    rev_sorted: HashMap<Term, (LemmaKey, FormulaId)>,
    total: FormulaId,
    pub max_size: usize,
}
pub struct WeakenHypotheses<'a, L: BoundedLanguage> {
    set: &'a WeakenLemmaSet<L>,
    permanent: Vec<(LemmaKey, Term)>,
    before: Option<LemmaKey>,
    try_first: Vec<LemmaKey>,
}

impl<'a, L: BoundedLanguage> OrderedTerms for &WeakenHypotheses<'a, L> {
    type Key = LemmaKey;

    fn permanent(&self) -> Vec<(&Self::Key, &Term)> {
        self.permanent.iter().map(|(k, t)| (k, t)).collect()
    }

    fn first_unsat(self, model: &Model) -> Option<(Self::Key, Term)> {
        self.try_first
            .iter()
            .map(|k| (k, &self.set.sorted[k]))
            .find(|(_, t)| model.eval(t) == 0)
            .or_else(|| {
                let is_after = |k| self.before.as_ref().is_some_and(|b| k >= b);
                self.set
                    .sorted
                    .iter()
                    .find(|(key, term)| is_after(*key) || model.eval(term) == 0)
                    .filter(|(key, _)| !is_after(*key))
            })
            .map(|(key, term)| (*key, term.clone()))
    }

    fn all_terms(self) -> BTreeMap<Self::Key, Term> {
        if let Some(before) = self.before {
            self.set
                .sorted
                .range(..before)
                .map(|(key, term)| (*key, term.clone()))
                .collect()
        } else {
            self.set.sorted.clone()
        }
    }
}

impl<L: BoundedLanguage> WeakenLemmaSet<L> {
    pub fn new(lang: Arc<L>) -> Self {
        Self {
            lang,
            set: L::Set::default(),
            sorted: BTreeMap::new(),
            rev_sorted: HashMap::default(),
            total: 0,
            max_size: 0,
        }
    }

    pub fn simplified_len(&self) -> usize {
        self.sorted.len()
    }

    pub fn len(&self) -> usize {
        self.set.len()
    }

    pub fn hypotheses(
        &self,
        permanent: Vec<LemmaKey>,
        before: Option<LemmaKey>,
        try_first: Vec<LemmaKey>,
    ) -> WeakenHypotheses<'_, L> {
        WeakenHypotheses {
            set: self,
            permanent: permanent
                .into_iter()
                .map(|k| (k, self.sorted[&k].clone()))
                .collect(),
            before,
            try_first,
        }
    }

    pub fn init(&mut self) {
        self.insert(self.lang.bottom());
        self.max_size = self.max_size.max(self.len());
    }

    fn insert(&mut self, f: L::Formula) -> Vec<LemmaKey> {
        let simplified = self.lang.simplify(&f);
        self.set.insert(f);

        simplified
            .into_iter()
            .filter_map(|term| {
                if let Some((_, count)) = self.rev_sorted.get_mut(&term) {
                    *count += 1;
                    None
                } else {
                    let key = LemmaKey::key(&term, self.total);
                    self.total += 1;
                    assert!(self.sorted.insert(key, term.clone()).is_none());
                    assert!(self.rev_sorted.insert(term, (key, 1)).is_none());
                    Some(key)
                }
            })
            .collect()
    }

    fn remove(&mut self, f: &L::Formula) -> Vec<LemmaKey> {
        self.lang
            .simplify(f)
            .iter()
            .filter_map(|term| {
                let (_, count) = self.rev_sorted.get_mut(term).unwrap();
                assert!(*count > 0);
                *count -= 1;
                if *count == 0 {
                    let (key, _) = self.rev_sorted.remove(term).unwrap();
                    assert!(self.sorted.remove(&key).is_some());
                    Some(key)
                } else {
                    None
                }
            })
            .collect()
    }

    pub fn unsat(&self, model: &Model) -> bool {
        !self.set.get_unsat(model, &Assignment::new()).is_empty()
    }

    pub fn weaken(&mut self, model: &Model) -> (Vec<LemmaKey>, Vec<LemmaKey>) {
        let start_time = Instant::now();
        let empty_assigment = Assignment::new();

        let unsat;
        let mut removed: Vec<LemmaKey> = vec![];
        let mut added: Vec<LemmaKey> = vec![];
        let mut total_added = 0_usize;

        let unsat_time = timed!({
            unsat = self.set.get_unsat_formulas(model, &empty_assigment);
        });
        for f in &unsat {
            removed.append(&mut self.remove(f));
        }

        let ignore = |f: &L::Formula| !self.set.get_subsuming(f).is_empty();

        let mut weakenings: Vec<_>;
        let weaken_time = timed!({
            weakenings = unsat
                .par_iter()
                .flat_map_iter(|f| self.lang.weaken(f, model, &empty_assigment, ignore))
                .collect::<Vec<_>>();
        });

        let minimization_time = timed!({ weakenings = L::minimize(empty(), weakenings) });

        let insertion_time = timed!({
            for f in weakenings.into_iter().sorted() {
                total_added += 1;
                added.append(&mut self.insert(f));
            }
        });

        self.max_size = self.max_size.max(self.len());

        if !unsat.is_empty() {
            log::info!(
                "[{} ~> {} | {}] Weakened: removed={}({}), added={}({}), total_time={}ms (unsat={}ms, weaken={}ms, min={}ms, insertion={}ms)",
                self.len(),
                self.simplified_len(),
                self.max_size,
                unsat.len(),
                removed.len(),
                total_added,
                added.len(),
                start_time.elapsed().as_millis(),
                unsat_time.as_millis(),
                weaken_time.as_millis(),
                minimization_time.as_millis(),
                insertion_time.as_millis(),
            );
        }

        (removed, added)
    }

    pub fn remove_unsat(&mut self, model: &Model) -> Vec<LemmaKey> {
        let start_time = Instant::now();
        let empty_assigment = Assignment::new();

        let unsat = self.set.get_unsat_formulas(model, &empty_assigment);
        let mut removed: Vec<LemmaKey> = vec![];

        for f in &unsat {
            removed.append(&mut self.remove(f));
        }

        if !removed.is_empty() {
            log::info!(
                "[{}] Removed UNSAT: removed={}, total_time={}ms",
                self.len(),
                unsat.len(),
                start_time.elapsed().as_millis(),
            );
        }

        removed
    }

    pub fn key_to_idx(&self) -> HashMap<LemmaKey, usize> {
        self.sorted
            .keys()
            .cloned()
            .enumerate()
            .map(|(i, k)| (k, i))
            .collect()
    }

    pub fn keys(&self) -> impl Iterator<Item = &LemmaKey> {
        self.sorted.keys()
    }

    pub fn to_terms_keys(&self) -> impl Iterator<Item = (&Term, &LemmaKey)> {
        self.rev_sorted.iter().map(|(t, (k, _))| (t, k))
    }

    pub fn to_terms(&self) -> Vec<Term> {
        self.sorted.values().cloned().collect()
    }

    pub fn key_to_term(&self, key: &LemmaKey) -> Term {
        self.sorted[key].clone()
    }
}

/// Lemma complexity consists of
/// - the number of existentials,
/// - the number of literals,
/// - the number of quantified variables
#[derive(Hash, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug)]
pub struct LemmaComplexity(usize, usize, usize);

#[derive(Hash, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug)]
pub struct LemmaKey(LemmaComplexity, FormulaId);

impl LemmaKey {
    fn key(term: &Term, id: FormulaId) -> Self {
        LemmaKey(LemmaComplexity::complexity(term), id)
    }

    pub fn is_universal(&self) -> bool {
        self.0 .0 == 0
    }
}

impl AddAssign for LemmaComplexity {
    fn add_assign(&mut self, rhs: Self) {
        self.0 += rhs.0;
        self.1 += rhs.1;
        self.2 += rhs.2;
    }
}

impl LemmaComplexity {
    /// Return the complexity of this lemma, assuming it contains only quantifiers and boolean connectives, and is in NNF.
    fn complexity(term: &Term) -> Self {
        let mut comp = LemmaComplexity(0, 0, 0);
        match term {
            Term::Quantified {
                quantifier,
                binders: _,
                body,
            } => {
                comp += LemmaComplexity::complexity(body);
                if matches!(quantifier, Quantifier::Exists) {
                    comp.0 += 1
                }
                comp.2 += 1;
            }
            Term::NAryOp(_, args) => {
                for a in args {
                    comp += LemmaComplexity::complexity(a);
                }
            }
            _ => comp.1 += 1,
        }

        comp
    }
}
