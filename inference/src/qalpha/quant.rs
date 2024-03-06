// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Manage quantifiers used in inference.

use std::{cmp::Ordering, hash::Hash};

use crate::hashmap::HashSet;
use fly::ouritertools::OurItertools;
use itertools::Itertools;
use std::fmt::Debug;
use std::sync::Arc;

use crate::qalpha::frame;
use fly::syntax::{Binder, Quantifier, Signature, Sort, Term};
use fly::term::subst::Substitution;

/// Generate the variable names for this [`QuantifierSequence`]. The names are grouped
/// and ordered based on their position in the sequence.
pub fn vars(signature: &Signature, sorts: &[usize], counts: &[usize]) -> Vec<Vec<String>> {
    let mut vars = vec![vec![]; sorts.len()];
    let mut sorted_counts: Vec<usize> = vec![0; signature.sorts.len()];
    for i in 0..sorts.len() {
        vars[i].extend((0..counts[i]).map(|_| {
            sorted_counts[sorts[i]] += 1;
            format!("{}_{}", signature.sorts[sorts[i]], sorted_counts[sorts[i]])
        }));
    }

    vars
}

fn push_front<T>(mut v: Vec<T>, t: T) -> Vec<T> {
    v.insert(0, t);
    v
}

/// Returns all possible distributions of `amount` into `boxes` of the specified sizes.
fn distribute(amount: usize, boxes: &[usize]) -> Vec<Vec<usize>> {
    if boxes.is_empty() {
        match amount {
            0 => vec![vec![]],
            _ => vec![],
        }
    } else {
        (0..=amount.min(boxes[0]))
            .flat_map(|c| {
                distribute(amount - c, &boxes[1..])
                    .into_iter()
                    .map(|v| push_front(v, c))
                    .collect_vec()
            })
            .collect_vec()
    }
}

/// Return a vector whose position `i` is `boxes[i][..sizes[i]]`.
fn sub_boxes<T: Clone>(sizes: &[usize], boxes: &[Vec<T>]) -> Vec<Vec<T>> {
    assert_eq!(sizes.len(), boxes.len());
    sizes
        .iter()
        .enumerate()
        .map(|(i, size)| boxes[i][..*size].to_vec())
        .collect()
}

/// Find the first location `i` such that the sum of `boxes[i..]` is less than or equal to `max`.
fn select_last(max: usize, boxes: &[usize]) -> usize {
    (1..=boxes.len())
        .rev()
        .find(|i| boxes[(i - 1)..].iter().sum::<usize>() > max)
        .unwrap_or(0)
}

pub fn parse_quantifier(
    sig: &Signature,
    s: &str,
) -> Result<(Option<Quantifier>, Sort, usize), String> {
    let mut parts = s.split_whitespace();

    let quantifier = match parts.next().unwrap() {
        "*" => None,
        "F" => Some(Quantifier::Forall),
        "E" => Some(Quantifier::Exists),
        _ => return Err("invalid quantifier (choose F/E/*)".to_string()),
    };

    let sort_id = parts.next().unwrap().to_string();
    let sort = if sig.sorts.contains(&sort_id) {
        Sort::Uninterpreted(sort_id)
    } else {
        return Err(format!("invalid sort {sort_id}"));
    };

    let count = parts.next().unwrap().parse::<usize>().unwrap();
    Ok((quantifier, sort, count))
}

/// A [`QuantifierSequence`] is a sequence where each position represents a sorted
/// quantifier with a certain number of quantified variables.
/// Note that this is a generic structure with a generic quantifier.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct QuantifierSequence<Q: Clone + Hash + Eq> {
    pub quantifiers: Vec<Q>,
    pub sorts: Arc<Vec<Sort>>,
    pub names: Arc<Vec<Vec<String>>>,
}

/// A [`QuantifierSequence`] where each quantifier is either [`None`], [`Some(Quantifier::Forall)`],
/// or [`Some(Quantifier::Exists)`], where [`None`] represents a wildcard configuration which allows
/// both classical quantifiers.
pub type QuantifierConfig = QuantifierSequence<Option<Quantifier>>;
/// A [`QuantifierSequence`] where each quantifier is either [`Quantifier::Forall`] or [`Quantifier::Exists`],
/// i.e. a classical quantifier prefix.
pub type QuantifierPrefix = QuantifierSequence<Quantifier>;

impl<Q: Clone + Hash + Eq> QuantifierSequence<Q> {
    pub fn new(
        signature: Arc<Signature>,
        quantifiers: Vec<Q>,
        sorts: Vec<Sort>,
        counts: &[usize],
    ) -> Self {
        let sort_indices: Vec<usize> = sorts.iter().map(|sort| signature.sort_idx(sort)).collect();
        let names = vars(&signature, &sort_indices, counts);

        QuantifierSequence {
            quantifiers,
            sorts: Arc::new(sorts),
            names: Arc::new(names),
        }
    }

    /// Get the length of the [`QuantifierSequence`].
    pub fn len(&self) -> usize {
        self.quantifiers.len()
    }

    pub fn counts(&self) -> Vec<usize> {
        self.names.iter().map(|n| n.len()).collect()
    }

    /// Return whether the sequence is empty.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Restrict the sequence to variables in the given ID set.
    pub fn restrict(&self, ids: HashSet<String>) -> Self {
        Self {
            quantifiers: self.quantifiers.clone(),
            sorts: self.sorts.clone(),
            names: Arc::new(
                self.names
                    .iter()
                    .map(|n| n.iter().filter(|id| ids.contains(*id)).cloned().collect())
                    .collect(),
            ),
        }
    }

    /// Return the number of quantified variables.
    pub fn num_vars(&self) -> usize {
        self.names.iter().map(|n| n.len()).sum()
    }

    /// Return the names of all quantified variables in this sequence.
    pub fn all_vars(&self) -> HashSet<String> {
        self.names.iter().flat_map(|n| n.iter().cloned()).collect()
    }

    /// Generate all atoms in a given signature with this [`QuantifierSequence`].
    pub fn atoms(
        &self,
        signature: &Signature,
        nesting: Option<usize>,
        include_eq: bool,
    ) -> Vec<Term> {
        let mut sorted_vars = vec![vec![]; signature.sorts.len()];
        for (i, v) in self.names.iter().enumerate() {
            sorted_vars[signature.sort_idx(&self.sorts[i])].extend(v.iter().cloned());
        }

        signature
            .terms_by_sort(&sorted_vars, nesting, include_eq)
            .pop()
            .unwrap()
    }

    /// Generate all permutations of grouped variables in the [`QuantifierSequence`],
    /// starting at position `start_at`. Include only the variables in `only` in the
    /// resulting permutations.
    pub fn permutations(
        &self,
        start_at: usize,
        only: Option<&HashSet<String>>,
    ) -> Vec<Substitution> {
        if start_at >= self.len() {
            return vec![Substitution::new()];
        }

        let vars = &self.names[start_at..];
        let only_vars = if let Some(only_set) = only {
            vars.iter()
                .map(|vs| {
                    vs.iter()
                        .filter(|&v| only_set.contains(v))
                        .cloned()
                        .collect_vec()
                })
                .collect_vec()
        } else {
            Vec::from(vars)
        };
        vars.iter()
            .enumerate()
            .map(|(i, vs)| vs.iter().permutations(only_vars[i].len()))
            .multi_cartesian_product_fixed()
            .map(|perm| {
                only_vars
                    .iter()
                    .flatten()
                    .cloned()
                    .zip(perm.into_iter().flatten().map(|s| Term::Id(s.clone())))
                    .collect()
            })
            .collect_vec()
    }

    pub fn substitutions_for(&self, other: &Self) -> Vec<Substitution> {
        assert_eq!(self.len(), other.len());

        (0..self.len())
            .map(|i| {
                other.names[i]
                    .iter()
                    .cloned()
                    .permutations(self.names[i].len())
            })
            .multi_cartesian_product_fixed()
            .map(|asgn| {
                self.names
                    .iter()
                    .flatten()
                    .cloned()
                    .zip(asgn.into_iter().flatten().map(Term::Id))
                    .collect()
            })
            .collect()
    }

    pub fn as_universal(&self) -> QuantifierPrefix {
        QuantifierPrefix {
            quantifiers: vec![Quantifier::Forall; self.len()],
            sorts: self.sorts.clone(),
            names: self.names.clone(),
        }
    }

    pub fn subsequences(&self, size: usize) -> Vec<Self> {
        distribute(size, &self.counts())
            .iter()
            .map(|size_dist| Self {
                quantifiers: self.quantifiers.clone(),
                sorts: self.sorts.clone(),
                names: Arc::new(sub_boxes(size_dist, &self.names)),
            })
            .collect()
    }
}

impl QuantifierConfig {
    /// Return all prefixes of the given configuration without any redundancy in terms of containment.
    pub fn prefixes(&self, max_size: usize, last_exist: usize) -> Vec<QuantifierPrefix> {
        let mut res = vec![];

        // Go over all prefix of exact size and existential count, from largest to smallest, and add
        // those that aren't contained by previously added prefixes. Since we go from largest to smallest
        // we will not have any containment between any two prefixes in the result.
        for size in (0..=max_size).rev() {
            for prefix in self.exact_prefixes(size, last_exist) {
                if !res.iter().any(|p: &QuantifierPrefix| p.contains(&prefix)) {
                    res.push(prefix);
                }
            }
        }

        res
    }

    /// Returns all sub-prefixes of exactly length `size` and `exist` existentials
    pub fn exact_prefixes(&self, size: usize, last_exist: usize) -> Vec<QuantifierPrefix> {
        distribute(size, &self.counts())
            .iter()
            .flat_map(|size_dist| {
                let exist_limit = select_last(last_exist, size_dist);
                (0..size_dist.len())
                    .map(|i| {
                        if i >= exist_limit && size_dist[i] > 0 {
                            vec![false, true]
                        } else {
                            vec![false]
                        }
                    })
                    .multi_cartesian_product_fixed()
                    .filter(|exist_select| {
                        exist_select.iter().enumerate().all(|(i, e)| {
                            // Existential selection must conform with configuration in non-zero places.
                            match (self.quantifiers[i], size_dist[i]) {
                                (None, _) | (_, 0) => true,
                                (Some(Quantifier::Forall), _) => !e,
                                (Some(Quantifier::Exists), _) => *e,
                            }
                        })
                    })
                    .map(|exist_select| QuantifierPrefix {
                        quantifiers: exist_select
                            .iter()
                            .map(|e| match e {
                                true => Quantifier::Exists,
                                false => Quantifier::Forall,
                            })
                            .collect(),
                        sorts: self.sorts.clone(),
                        names: Arc::new(sub_boxes(size_dist, &self.names)),
                    })
                    .collect_vec()
            })
            .collect()
    }

    pub fn strictly_universal_vars(&self) -> HashSet<String> {
        self.quantifiers
            .iter()
            .zip(self.names.iter())
            .filter_map(|(q, ns)| match q {
                Some(Quantifier::Forall) => Some(ns.iter().cloned()),
                _ => None,
            })
            .flatten()
            .collect()
    }

    pub fn vars_after_first_exist(&self) -> HashSet<String> {
        match (0..self.len()).find(|i| !matches!(self.quantifiers[*i], Some(Quantifier::Forall))) {
            Some(first_exists) => self.names[first_exists..]
                .iter()
                .flat_map(|ns| ns.iter().cloned())
                .collect(),
            None => HashSet::default(),
        }
    }

    pub fn is_universal(&self) -> bool {
        self.names
            .iter()
            .zip(self.quantifiers.iter())
            .all(|(ns, q)| ns.is_empty() || matches!(q, Some(Quantifier::Forall)))
    }
}

impl Debug for QuantifierConfig {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut parts = vec![];
        for i in 0..self.len() {
            let q_vec = vec![
                match self.quantifiers[i] {
                    None => "***".to_string(),
                    Some(Quantifier::Exists) => "exists".to_string(),
                    Some(Quantifier::Forall) => "forall".to_string(),
                },
                self.names[i].iter().join(", "),
            ];

            parts.push(q_vec.into_iter().join(" "));
        }

        write!(f, "{}", parts.iter().join(" . "))
    }
}

impl QuantifierPrefix {
    /// Quantify the given term according to this [`QuantifierPrefix`].
    pub fn quantify(&self, mut term: Term) -> Term {
        let present_ids = frame::ids(&term);
        for (i, v) in self.names.iter().enumerate().rev() {
            let binders = v
                .iter()
                .filter_map(|name| {
                    if present_ids.contains(name) {
                        Some(Binder {
                            name: name.clone(),
                            sort: self.sorts[i].clone(),
                        })
                    } else {
                        None
                    }
                })
                .collect_vec();

            if !binders.is_empty() {
                term = Term::Quantified {
                    quantifier: self.quantifiers[i],
                    binders,
                    body: Box::new(term),
                }
            }
        }

        term
    }

    /// Check whether one [`QuantifierPrefix`] subsumes another. A prefix Q1 is said to subsume Q2
    /// if Q2 can be gotten from Q1 by only flipping universal quantifiers to existential ones
    /// and dropping quantified variables.
    ///
    /// This subsumption behaves in the following way with the [`Ord`] defined for [`QuantifierPrefix`]:
    /// If Q1 subsumes Q2, then Q1 <= Q2.
    pub fn subsumes(&self, other: &Self) -> bool {
        assert_eq!(self.len(), other.len());

        (0..self.len()).all(|i| {
            self.names.is_empty()
                || other.names.is_empty()
                || self.quantifiers[i] == Quantifier::Forall
                || other.quantifiers[i] == Quantifier::Exists
        })
    }

    /// Check whether one [`QuantifierPrefix`] contains another.
    pub fn contains(&self, other: &Self) -> bool {
        assert_eq!(self.len(), other.len());
        (0..self.len()).all(|i| {
            other.names[i].is_empty()
                || (self.quantifiers[i] == other.quantifiers[i]
                    && self.names[i].len() >= other.names[i].len())
        })
    }

    pub fn existentials(&self) -> usize {
        (0..self.len())
            .map(|i| match self.quantifiers[i] {
                Quantifier::Exists => self.names[i].len(),
                Quantifier::Forall => 0,
            })
            .sum()
    }

    pub fn vars_after_first_exist(&self) -> HashSet<String> {
        match (0..self.len()).find(|i| matches!(self.quantifiers[*i], Quantifier::Exists)) {
            Some(first_exists) => self.names[first_exists..]
                .iter()
                .flat_map(|ns| ns.iter().cloned())
                .collect(),
            None => HashSet::default(),
        }
    }

    pub fn is_universal(&self) -> bool {
        self.names
            .iter()
            .zip(self.quantifiers.iter())
            .all(|(ns, q)| ns.is_empty() || matches!(q, Quantifier::Forall))
    }
}

impl Debug for QuantifierPrefix {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut parts = vec![];
        for i in 0..self.len() {
            let q_vec = vec![
                match self.quantifiers[i] {
                    Quantifier::Exists => "exists".to_string(),
                    Quantifier::Forall => "forall".to_string(),
                },
                self.names[i].iter().join(", "),
            ];

            parts.push(q_vec.into_iter().join(" "));
        }

        write!(f, "{}", parts.iter().join(". "))
    }
}

impl PartialOrd for QuantifierPrefix {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for QuantifierPrefix {
    fn cmp(&self, other: &Self) -> Ordering {
        assert_eq!(self.len(), other.len());
        assert_eq!(self.sorts, other.sorts);

        for i in 0..self.len() {
            match (self.names[i].is_empty(), other.names[i].is_empty()) {
                (true, true) => continue,
                (true, false) => return Ordering::Greater,
                (false, true) => return Ordering::Less,
                (false, false) => (),
            }

            match (self.quantifiers[i], other.quantifiers[i]) {
                (Quantifier::Forall, Quantifier::Exists) => return Ordering::Less,
                (Quantifier::Exists, Quantifier::Forall) => return Ordering::Greater,
                _ => (),
            }

            match self.names[i].len().cmp(&other.names[i].len()) {
                Ordering::Greater => return Ordering::Less,
                Ordering::Less => return Ordering::Greater,
                _ => (),
            }
        }

        Ordering::Equal
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fly::{parser, term::subst::Substitution};
    use std::collections::HashMap;

    #[test]
    fn test_permutations() {
        let signature = parser::parse_signature(
            r#"
sort A
sort B
sort C
"#
            .trim(),
        );

        let sort = Sort::uninterpreted;
        let config = QuantifierConfig::new(
            Arc::new(signature),
            vec![None, None, None],
            vec![sort("A"), sort("B"), sort("C")],
            &[2, 1, 2],
        );
        let a = |i: usize| format!("A_{i}");
        let b = |i: usize| format!("B_{i}");
        let c = |i: usize| format!("C_{i}");
        let ta = |i: usize| Term::Id(a(i));
        let tb = |i: usize| Term::Id(b(i));
        let tc = |i: usize| Term::Id(c(i));

        let same = |perms1: &[Substitution], perms2: &[Substitution]| -> bool {
            perms1.iter().all(|p| perms2.contains(p)) && perms2.iter().all(|p| perms1.contains(p))
        };

        assert!(same(
            &config.permutations(0, None),
            &[
                HashMap::from_iter([
                    (a(1), ta(1)),
                    (a(2), ta(2)),
                    (b(1), tb(1)),
                    (c(1), tc(1)),
                    (c(2), tc(2)),
                ]),
                HashMap::from_iter([
                    (a(1), ta(2)),
                    (a(2), ta(1)),
                    (b(1), tb(1)),
                    (c(1), tc(1)),
                    (c(2), tc(2)),
                ]),
                HashMap::from_iter([
                    (a(1), ta(1)),
                    (a(2), ta(2)),
                    (b(1), tb(1)),
                    (c(1), tc(2)),
                    (c(2), tc(1)),
                ]),
                HashMap::from_iter([
                    (a(1), ta(2)),
                    (a(2), ta(1)),
                    (b(1), tb(1)),
                    (c(1), tc(2)),
                    (c(2), tc(1)),
                ])
            ]
        ));

        assert!(same(
            &config.permutations(1, None),
            &[
                HashMap::from_iter([(b(1), tb(1)), (c(1), tc(1)), (c(2), tc(2)),]),
                HashMap::from_iter([(b(1), tb(1)), (c(1), tc(2)), (c(2), tc(1))]),
            ]
        ));

        assert!(same(
            &config.permutations(0, Some(&HashSet::from_iter([a(1), c(2)]))),
            &[
                HashMap::from_iter([(a(1), ta(1)), (c(2), tc(1)),]),
                HashMap::from_iter([(a(1), ta(2)), (c(2), tc(1)),]),
                HashMap::from_iter([(a(1), ta(1)), (c(2), tc(2)),]),
                HashMap::from_iter([(a(1), ta(2)), (c(2), tc(2)),]),
            ]
        ));
    }
}
