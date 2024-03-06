// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

use fly::{
    semantics::{Assignment, Model},
    syntax::{BinOp, Binder, Quantifier, Signature, Sort, Term, UOp},
    term::subst::{substitute_qf, Substitution},
};
use solver::basics::BasicSolver;

use crate::{
    basics::{CexResult, FOModule},
    hashmap::{HashMap, HashSet},
    qalpha::{
        frame::ids,
        quant::{QuantifierConfig, QuantifierPrefix},
    },
};

use std::sync::Arc;

use rayon::prelude::*;

/// An [`Atom`] is referred to via a certain index.
pub type Atom = Arc<Term>;
/// A [`Literal`] represents an atom, either positive or negated.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Literal(pub Atom, pub bool);
pub type Literals = HashSet<Literal>;

fn substitute(atom: &Atom, substitution: &Substitution) -> Atom {
    Arc::new(match atom.as_ref() {
        Term::BinOp(BinOp::Equals, t1, t2) => {
            let t1_sub = substitute_qf(t1, substitution);
            let t2_sub = substitute_qf(t2, substitution);
            if t1_sub <= t2_sub {
                Term::equals(t1_sub, t2_sub)
            } else {
                Term::equals(t2_sub, t1_sub)
            }
        }
        _ => substitute_qf(atom, substitution),
    })
}

impl Literal {
    pub fn ids(&self) -> HashSet<String> {
        ids(&self.0)
    }

    pub fn negate(&self) -> Self {
        Self(self.0.clone(), !self.1)
    }

    pub fn substitute(&self, substitution: &Substitution) -> Self {
        Self(substitute(&self.0, substitution), self.1)
    }

    pub fn is_neq(&self) -> bool {
        matches!(self.0.as_ref(), Term::BinOp(BinOp::Equals, _, _)) && !self.1
    }
}

impl From<&Literal> for Term {
    fn from(value: &Literal) -> Self {
        match value.1 {
            true => value.0.as_ref().clone(),
            false => Term::not(value.0.as_ref()),
        }
    }
}

/// Adds the sorted variables that appear in the atom to the map.
fn add_variables(signature: &Signature, term: &Term, vars: &mut HashSet<String>) {
    match term {
        Term::Literal(_) => (),
        Term::Id(name) => {
            if !vars.contains(name) && !signature.contains_relation(name) {
                vars.insert(name.clone());
            }
        }
        Term::App(_, _, args) => {
            for a in args {
                add_variables(signature, a, vars);
            }
        }
        Term::UnaryOp(UOp::Next | UOp::Previous | UOp::Prime, t) => {
            add_variables(signature, t, vars);
        }
        Term::BinOp(BinOp::Equals, t1, t2) => {
            add_variables(signature, t1, vars);
            add_variables(signature, t2, vars);
        }
        _ => panic!("this functions only supports atoms"),
    }
}

fn quantify_forall(
    term: Term,
    vars: &HashSet<String>,
    var_to_sort: &HashMap<String, Sort>,
) -> Term {
    if vars.is_empty() {
        term
    } else {
        Term::Quantified {
            quantifier: Quantifier::Forall,
            binders: vars
                .iter()
                .map(|name| Binder {
                    name: name.clone(),
                    sort: var_to_sort[name].clone(),
                })
                .collect(),
            body: Box::new(term),
        }
    }
}

pub fn generate_literals<C: FromParallelIterator<Literal>, S: BasicSolver>(
    signature: &Signature,
    quant_cfg: &QuantifierConfig,
    nesting: Option<usize>,
    include_eq: bool,
    fo: &FOModule,
    solver: &S,
) -> C {
    let var_to_sort: HashMap<_, _> = quant_cfg
        .names
        .iter()
        .zip(quant_cfg.sorts.iter())
        .flat_map(|(names, sort)| names.iter().map(|n| (n.clone(), sort.clone())))
        .collect();

    quant_cfg
        .atoms(signature, nesting, include_eq)
        .into_par_iter()
        // Make sure all equality atoms "t1 = t2" satisfy t1 <= t2.
        // This is done to allow substitutions without creating equivalent equalities.
        .map(|a| match a {
            Term::BinOp(BinOp::Equals, t1, t2) => {
                if t1 <= t2 {
                    Term::BinOp(BinOp::Equals, t1, t2)
                } else {
                    Term::BinOp(BinOp::Equals, t2, t1)
                }
            }
            _ => a,
        })
        .filter_map(|a| {
            let mut vars = HashSet::default();
            add_variables(signature, &a, &mut vars);
            let univ_a = quantify_forall(a.clone(), &vars, &var_to_sort);
            let univ_not_a = quantify_forall(Term::not(&a), &vars, &var_to_sort);
            if matches!(
                fo.implication_cex(solver, &[], &univ_a, None, false),
                CexResult::UnsatCore(_)
            ) || matches!(
                fo.implication_cex(solver, &[], &univ_not_a, None, false),
                CexResult::UnsatCore(_)
            ) {
                None
            } else {
                let lit_pos = Literal(Arc::new(a), true);
                let lit_neg = lit_pos.negate();
                Some([lit_pos, lit_neg])
            }
        })
        .flatten()
        .collect()
}

pub fn sat_literals(literals: &Literals, model: &Model, assignment: &Assignment) -> Literals {
    literals
        .iter()
        .filter(|lit| (model.eval_assign(&lit.0, assignment) == 1) == lit.1)
        .cloned()
        .collect()
}

pub fn restrict_by_prefix(
    literals: &Literals,
    config: &QuantifierConfig,
    prefix: &QuantifierPrefix,
) -> Literals {
    let config_vars = config.all_vars();
    let prefix_vars = prefix.all_vars();
    let difference: HashSet<String> = config_vars.difference(&prefix_vars).cloned().collect();

    literals
        .iter()
        .filter(|lit| lit.ids().is_disjoint(&difference))
        .cloned()
        .collect()
}
