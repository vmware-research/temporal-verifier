// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Handle lemmas used in inference.

use crate::{
    fly::{semantics::*, syntax::*},
    term::subst::*,
};
use itertools::Itertools;

impl Term {
    /// Negate a term by removing the outer UOp::Not, or adding one.
    pub fn flip(&self) -> Term {
        match self {
            Term::UnaryOp(UOp::Not, t) => t.as_ref().clone(),
            _ => Term::UnaryOp(UOp::Not, Box::new(self.clone())),
        }
    }
}

/// LemmaQF defines the functionality of the quantifier-free part of a lemma.
/// An implementation of it should define a subsumption relation between two instances
/// of Self, as well as a method to weaken an instance of Self to satisfy a quantifier-free
/// model, represented by the cube of literals that hold on that model.
///
/// For complete description of the subsumption relation and the weakening process,
/// see the documentation of [`LemmaQF::subsumes`] and [`LemmaQF::weaken`], respectively.
///
/// See [`crate::inference::pdnf::PDNF`] for an example implementation of [`LemmaQF`].
pub trait LemmaQF: Clone {
    /// Check whether one LemmaQF subsumes another.
    /// The subsumption relation is assumed to respect semantic consequence;
    /// that is, if X subsumes Y, then X implies Y.
    /// However, the converse is not ensured.
    fn subsumes(&self, other: &Self) -> bool;

    /// Weaken the LemmaQF so that it would hold on all models satisfying the terms in `cube`.
    /// Return a Vec of possible weakenings.
    ///
    /// The weakening process must have the following property:
    /// If for two instances of Self, `p` and `q`, it holds that `p.subsumes(&q)`,
    /// and `cube` implies `q`, then there's some `r` in `p.weaken(cube)` such that `r.subsumes(&q)`.
    /// Moreover, for all `r` in `p.weaken(cube)`, it holds that `p.subsumes(&r)` and `cube` implies `r`.
    fn weaken(&self, cube: Vec<Term>) -> Vec<Self>;

    /// Perform a substitution.
    fn substitute(&self, substitution: &Substitution) -> Self;

    /// Convert into a Term.
    fn to_term(&self) -> Term;
}

pub struct QuantifierConfig {
    pub quantifiers: Vec<Option<Quantifier>>,
    pub sorts: Vec<Sort>,
    pub names: Vec<Vec<String>>,
    // TODO: Add EPR coercion indication
    // pub epr: bool,
    pub depth: Option<usize>,
    pub include_eq: bool,
}

impl QuantifierConfig {
    /// Wrap the quantifier-free part of a lemma with the "strongest" possible quantification
    /// in the quantifier configuration. When applied to quantifier-free `false`, this yields
    /// the strongest possible Lemma w.r.t subsumption.
    pub fn quantify_false<T: LemmaQF>(&self, lemma_qf: T) -> Lemma<T> {
        Lemma::<T> {
            quantifiers: self
                .quantifiers
                .iter()
                .map(|q| match q {
                    Some(Quantifier::Exists) => Quantifier::Exists,
                    _ => Quantifier::Forall,
                })
                .collect(),
            sorts: self.sorts.clone(),
            names: self.names.clone(),
            lemma_qf,
        }
    }

    /// Generate all atoms of a given signature in with this quantifier configuration.
    pub fn atoms(&self, signature: &Signature) -> Vec<Term> {
        let mut sorted_vars = vec![vec![]; signature.sorts.len()];
        for i in 0..self.quantifiers.len() {
            sorted_vars[signature.sort_idx(&self.sorts[i])].append(&mut self.names[i].clone());
        }

        signature
            .terms_by_sort(&sorted_vars, self.depth, self.include_eq)
            .pop()
            .unwrap()
    }
}

/// Lemma<T: LemmaQF> represents a quantified lemma with a QF matrix of type T.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Lemma<T: LemmaQF> {
    quantifiers: Vec<Quantifier>,
    sorts: Vec<Sort>,
    names: Vec<Vec<String>>,
    lemma_qf: T,
}

/// Insert a lemma into a Vec of lemmas only if it isn't subsumed by another,
/// and remove all lemmas subsumed by it if inserted.
pub fn insert_lemma<T: LemmaQF>(lemma_vec: &mut Vec<Lemma<T>>, lemma: Lemma<T>) {
    if !lemma_vec.iter().any(|l| l.subsumes(&lemma)) {
        lemma_vec.retain(|l| !lemma.subsumes(l));
        lemma_vec.push(lemma);
    }
}

pub fn merge_lemmas<T: LemmaQF>(mut v1: Vec<Lemma<T>>, mut v2: Vec<Lemma<T>>) -> Vec<Lemma<T>> {
    v1.retain(|l1| !v2.iter().any(|l2| l2.subsumes(l1)));
    v2.retain(|l2| !v1.iter().any(|l1| l1.subsumes(l2)));
    v1.append(&mut v2);

    v1
}

impl<T: LemmaQF> Lemma<T> {
    /// Convert into a Term.
    pub fn to_term(&self) -> Term {
        assert_eq!(self.quantifiers.len(), self.sorts.len());
        assert_eq!(self.quantifiers.len(), self.names.len());

        let mut term = self.lemma_qf.to_term();

        for i in (0..self.quantifiers.len()).rev() {
            term = Term::Quantified {
                quantifier: self.quantifiers[i],
                binders: self.names[i]
                    .iter()
                    .map(|n| Binder {
                        name: n.clone(),
                        sort: self.sorts[i].clone(),
                    })
                    .collect(),
                body: Box::new(term),
            }
        }

        term
    }

    /// Check whether one lemma subsumes another.
    /// This lifts the quantifier-free subsumption to quantified lemmas.
    pub fn subsumes(&self, other: &Lemma<T>) -> bool {
        // Check whether lemmas have the same quantifiers, while allowing a universal
        // quantifier in `self` to be existential in `other`.
        if self.quantifiers.len() != other.quantifiers.len()
            || (0..self.quantifiers.len()).any(|i| {
                self.sorts[i] != other.sorts[i]
                    || self.names[i].len() != other.names[i].len()
                    || (self.quantifiers[i] == Quantifier::Exists
                        && other.quantifiers[i] == Quantifier::Forall)
            })
        {
            return false;
        }

        // Generate all possible permuations of quantified variables, and check quantifier-free subsumption in each case.
        let mut substs = vec![Substitution::new()];
        for i in 0..self.quantifiers.len() {
            let mut new_substs = vec![];
            for p in other.names[i].iter().permutations(self.names[i].len()) {
                new_substs.extend(substs.iter().map(|s| {
                    let mut new_s = s.clone();
                    for (j, e) in p.iter().enumerate() {
                        new_s.insert(self.names[i][j].clone(), Term::Id(e.to_string()));
                    }
                    new_s
                }));
            }
            substs = new_substs;
        }

        substs
            .iter()
            .any(|s| self.lemma_qf.substitute(s).subsumes(&other.lemma_qf))
    }

    /// Recursively weaken lemma according to a model and a quantifier configuration.
    fn weaken_rec(
        &self,
        model: &Model,
        cfg: &QuantifierConfig,
        atoms: &[Term],
        assignment: &Assignment,
        index: usize,
    ) -> Vec<Self> {
        let mut weakened: Vec<Self> = vec![];

        // Base case: quantifier-free weakening.
        if index == cfg.quantifiers.len() {
            let mut terms = vec![];
            atoms.clone_into(&mut terms);
            model.flip_to_sat(&mut terms, Some(assignment));

            for qf in self.lemma_qf.weaken(terms).into_iter() {
                insert_lemma(
                    &mut weakened,
                    Lemma {
                        quantifiers: vec![],
                        sorts: vec![],
                        names: vec![],
                        lemma_qf: qf,
                    },
                );
            }

            return weakened;
        }

        let mut base_lemma = self.clone();
        base_lemma.quantifiers.remove(0);
        base_lemma.sorts.remove(0);
        base_lemma.names.remove(0);

        // Recursion: univeral quantification case.
        if self.quantifiers[0] == Quantifier::Forall
            && (cfg.quantifiers[index].is_none()
                || cfg.quantifiers[index] == Some(Quantifier::Forall))
        {
            weakened.push(base_lemma.clone());
            let mut new_assignment = assignment.clone();
            let asgn_iter = (0..cfg.names[index].len())
                .map(|_| 0..model.universe[model.signature.sort_idx(&cfg.sorts[index])])
                .multi_cartesian_product();
            for es in asgn_iter {
                for (i, e) in es.iter().enumerate() {
                    new_assignment.insert(cfg.names[index][i].clone(), *e);
                }

                let mut new_weakened: Vec<Self> = vec![];
                for lemma in weakened.iter() {
                    new_weakened = merge_lemmas(
                        new_weakened,
                        lemma.weaken_rec(model, cfg, atoms, &new_assignment, index + 1),
                    );
                }

                weakened = new_weakened;
            }

            let mut new_weakened = vec![];
            for mut lemma in weakened.into_iter() {
                lemma.quantifiers.insert(0, Quantifier::Forall);
                lemma.sorts.insert(0, cfg.sorts[index].clone());
                lemma.names.insert(0, cfg.names[index].clone());
                insert_lemma(&mut new_weakened, lemma);
            }

            weakened = new_weakened;
        }

        // Recursion: existential quantification case.
        if cfg.quantifiers[index].is_none() || cfg.quantifiers[index] == Some(Quantifier::Exists) {
            let mut new_assignment = assignment.clone();
            let asgn_iter = (0..cfg.names[index].len())
                .map(|_| 0..model.universe[model.signature.sort_idx(&cfg.sorts[index])])
                .multi_cartesian_product();
            for es in asgn_iter {
                for (i, e) in es.iter().enumerate() {
                    new_assignment.insert(cfg.names[index][i].clone(), *e);
                }

                for mut lemma in
                    base_lemma.weaken_rec(model, cfg, atoms, &new_assignment, index + 1)
                {
                    lemma.quantifiers.insert(0, Quantifier::Exists);
                    lemma.sorts.insert(0, cfg.sorts[index].clone());
                    lemma.names.insert(0, cfg.names[index].clone());
                    insert_lemma(&mut weakened, lemma);
                }
            }
        }

        weakened
    }

    /// Weaken lemma according to a model and a quantifier configuration.
    pub fn weaken(
        &self,
        model: &Model,
        cfg: &QuantifierConfig,
        atoms: Option<&[Term]>,
    ) -> Vec<Self> {
        if let Some(atoms_v) = atoms {
            self.weaken_rec(model, cfg, atoms_v, &Assignment::new(), 0)
        } else {
            let atoms_v = cfg.atoms(&model.signature);
            self.weaken_rec(model, cfg, &atoms_v, &Assignment::new(), 0)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{fly::parser, inference::pdnf::*};

    #[test]
    fn test_weaken() {
        let sort = |n: usize| Sort::Id(format!("T{n}"));

        let cfg: QuantifierConfig = QuantifierConfig {
            quantifiers: vec![None, None],
            sorts: vec![sort(1), sort(3)],
            names: vec![
                vec!["x11".to_string()],
                vec!["x31".to_string(), "x32".to_string()],
            ],
            depth: None,
            include_eq: true,
        };

        let sig = parser::parse_signature(
            r#"
sort T1
sort T2
sort T3
mutable r(T1, T2, T3, T3): bool
mutable c(): T2
"#
            .trim(),
        );

        // First model, has elements x:1 y:2 z:3, c = y and r(x,y,z) = true
        let universe1: Universe = vec![1, 1, 1];
        let r_interp1 = Interpretation {
            shape: vec![1, 1, 1, 1, 2],
            data: vec![1],
        };
        let c_interp1 = Interpretation {
            shape: vec![1],
            data: vec![0],
        };
        let model1 = Model {
            signature: sig.clone(),
            universe: universe1,
            interp: vec![r_interp1, c_interp1],
        };

        // Second model, has elements x1:1 x2:1 y:2 z1:3 z2:3, c = y and
        // r(x1, y, *, *) = r(x2, y, z1, z2) = true
        // all else = false
        let universe2: Universe = vec![2, 1, 2];
        let r_interp2 = Interpretation {
            shape: vec![2, 1, 2, 2, 2],
            data: vec![1, 1, 1, 1, 0, 1, 0, 0],
        };
        let c_interp2 = Interpretation {
            shape: vec![1],
            data: vec![0],
        };
        let model2 = Model {
            signature: sig,
            universe: universe2,
            interp: vec![r_interp2, c_interp2],
        };

        // Original lemma: forall x11:T1. forall x31:T3, x32:T3. false
        let lemma0 = cfg.quantify_false(PDNF::get_false(0, None));
        assert_eq!(model1.eval(&lemma0.to_term(), None), 0);
        assert_eq!(model2.eval(&lemma0.to_term(), None), 0);

        let lemma1_vec = lemma0.weaken(&model1, &cfg, None);
        for lemma1 in lemma1_vec.iter() {
            assert!(lemma0.subsumes(&lemma1));
            assert_eq!(model1.eval(&lemma1.to_term(), None), 1);
        }

        let mut lemma2_vec = vec![];
        for lemma1 in lemma1_vec.iter() {
            for lemma2 in lemma1.weaken(&model2, &cfg, None) {
                assert!(lemma1.subsumes(&lemma2));
                assert_eq!(model1.eval(&lemma2.to_term(), None), 1);
                assert_eq!(model2.eval(&lemma2.to_term(), None), 1);
                insert_lemma(&mut lemma2_vec, lemma2);
            }
        }
    }
}
