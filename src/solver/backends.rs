// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

#![allow(clippy::needless_return)]
use std::{
    collections::{HashMap, HashSet},
    iter::zip,
};

use crate::{
    fly::{
        semantics::{Element, Interpretation},
        syntax::{Signature, Sort},
    },
    smtlib::{
        proc::{CvcConf, SolverCmd, Z3Conf},
        sexp::{self, atom_s},
    },
};

use super::{
    models::{self, subst},
    {Backend, FOModel},
};

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum SolverType {
    Z3,
    Cvc4,
    Cvc5,
}

#[derive(Debug, Clone)]
pub struct GenericBackend {
    solver_type: SolverType,
    bin: String,
}

impl GenericBackend {
    pub fn new(solver_type: SolverType, bin: &str) -> Self {
        Self {
            solver_type,
            bin: bin.to_string(),
        }
    }
}

fn sort_cardinality(universes: &HashMap<String, usize>, sort: &Sort) -> usize {
    match sort {
        Sort::Bool => 2,
        Sort::Id(s) => *universes
            .get(s)
            .unwrap_or_else(|| panic!("unknown sort {s}")),
    }
}

impl Backend for &GenericBackend {
    fn get_cmd(&self) -> SolverCmd {
        // TODO: move Z3Conf and CvcConf into this module
        match self.solver_type {
            SolverType::Z3 => {
                let mut conf = Z3Conf::new(&self.bin);
                conf.model_compact();
                conf.done()
            }
            SolverType::Cvc4 => {
                let mut conf = CvcConf::new_cvc4(&self.bin);
                conf.finite_models();
                conf.interleave_enumerative_instantiation();
                conf.done()
            }
            SolverType::Cvc5 => {
                let mut conf = CvcConf::new_cvc5(&self.bin);
                conf.finite_models();
                conf.interleave_enumerative_instantiation();
                conf.done()
            }
        }
    }

    fn parse(
        &self,
        sig: &Signature,
        // TODO(tej): unused, maybe we can remove from Backend trait
        _n_states: usize,
        indicators: &HashSet<String>,
        model: &sexp::Sexp,
    ) -> FOModel {
        let model = match self.solver_type {
            SolverType::Z3 => models::parse_z3(model),
            SolverType::Cvc4 => models::parse_cvc(model, false),
            SolverType::Cvc5 => models::parse_cvc(model, true),
        };

        let universe: HashMap<String, usize> = model
            .universes
            .iter()
            .map(|(sort, elements)| (sort.clone(), elements.len()))
            .collect();

        let mut interps = HashMap::new();
        for (symbol, (binders, body)) in &model.symbols {
            if indicators.contains(symbol) {
                continue;
            }
            let symbol_no_primes = symbol.trim_end_matches(|c| c == '\'');
            // this symbol is not in the signature
            if !sig.relations.iter().any(|r| r.name == symbol_no_primes) {
                continue;
            }
            let rel = sig.relation_decl(symbol);
            let mut shape = rel
                .args
                .iter()
                .map(|sort| sort_cardinality(&universe, sort))
                .collect::<Vec<usize>>();
            shape.push(sort_cardinality(&universe, &rel.sort));
            let interp = Interpretation::new(&shape, |args: &[Element]| -> Element {
                // get the arguments as terms, based on model.universes
                let args = zip(args, &rel.args)
                    .map(|(&e_idx, sort)| match sort {
                        Sort::Bool => {
                            if e_idx == 0 {
                                atom_s("false")
                            } else {
                                atom_s("true")
                            }
                        }
                        Sort::Id(sort) => {
                            let elements = &model.universes[sort];
                            let element = elements[e_idx].clone();
                            atom_s(element)
                        }
                    })
                    .collect::<Vec<_>>();
                let repl = zip(binders.iter().map(|s| s.as_str()), args).collect::<Vec<_>>();
                let body = subst(&repl, body);
                let e = model
                    .smt_eval(&body)
                    .unwrap_or_else(|err| panic!("could not interpret {}: {err}", &rel.name));
                let res = e.s().expect("unhandled evaluation result");
                match &rel.sort {
                    Sort::Bool => {
                        if res == "false" {
                            return 0;
                        } else if res == "true" {
                            return 1;
                        } else {
                            panic!("unexpected bool {res}")
                        }
                    }
                    Sort::Id(sort) => {
                        let elements = &model.universes[sort];
                        let res_idx = elements
                            .iter()
                            .position(|x| x == res)
                            .unwrap_or_else(|| panic!("unknown {sort} element {res}"));
                        return res_idx as Element;
                    }
                }
            });
            interps.insert(symbol.clone(), interp);
        }

        FOModel {
            universe,
            interp: interps,
        }
    }
}

#[cfg(test)]
mod tests {
    use std::{collections::HashSet, fs};

    use crate::{fly::parser, smtlib::sexp};

    use super::{Backend, GenericBackend, SolverType};

    #[test]
    #[ignore] // parsing this model takes too long
    fn test_issue_5_parse_model_with_auxilliary_defs() {
        let sig = parser::parse_signature(
            r#"
        sort node
        sort quorum
        sort value

        # constants:


        # functions:


        # relations:
        mutable member(node, quorum): bool
        mutable vote_request_msg(node, node): bool
        mutable voted(node): bool
        mutable vote_msg(node, node): bool
        mutable votes(node, node): bool
        mutable leader(node): bool
        mutable decided(node, value): bool
        "#
            .trim(),
        );

        let backend = GenericBackend {
            solver_type: SolverType::Z3,
            bin: "z3".to_string(),
        };

        let model_text =
            fs::read_to_string("tests/issue_5_model.sexp").expect("could not find model file");
        let model_sexp = sexp::parse(&model_text).expect("test model does not parse");

        let fo_model = (&backend).parse(&sig, 1, &HashSet::new(), &model_sexp);
        // a (primed) relation from the signature
        assert!(fo_model.interp.contains_key("leader'"));
        // auxilliary definition in Z3's model
        assert!(!fo_model.interp.contains_key("k!1058"));
    }
}
