// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

use std::{
    collections::{HashMap, HashSet},
    iter::zip,
    time::Instant,
};

use crate::{
    fly::{
        semantics::{Element, Interpretation},
        syntax::{Signature, Sort},
    },
    smtlib::{
        proc::{CvcConf, SolverCmd, Z3Conf},
        sexp::{self, Atom},
    },
    solver::models::ModelSymbol,
};

use super::{
    models::{self, PartialInterp},
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

        let mut part_interp = PartialInterp::for_model(&model);
        let mut symbols = model.symbols.iter().collect::<Vec<_>>();
        symbols.sort_unstable_by_key(|(symbol, _)| {
            let in_signature = sig.contains_name(symbol);
            // sort the model-only signatures first
            //
            // NOTE: this is just a heuristic to evaluate auxilliary functions
            // first, for now.
            (in_signature, symbol.to_string())
        });
        for (symbol, model_sym) in symbols.into_iter() {
            if indicators.contains(symbol) {
                continue;
            }
            let start = Instant::now();
            let ModelSymbol {
                binders,
                body,
                ret_sort,
            } = model_sym;
            let arg_sorts = binders
                .iter()
                .map(|(_, sort)| sort.clone())
                .collect::<Vec<_>>();
            let mut shape = arg_sorts
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
                                Atom::S("false".to_string())
                            } else {
                                Atom::S("true".to_string())
                            }
                        }
                        Sort::Id(sort) => {
                            let elements = &model.universes[sort];
                            let element = elements[e_idx].clone();
                            Atom::S(element)
                        }
                    })
                    .collect::<Vec<_>>();
                let repl: HashMap<&str, Atom> =
                    zip(binders.iter().map(|s| s.0.as_str()), args).collect();
                let e = model
                    .smt_eval(&repl, &part_interp, body)
                    .unwrap_or_else(|err| panic!("could not interpret {symbol}: {err}"));
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
            part_interp
                .interps
                .insert(symbol.clone(), (interp, ret_sort.clone()));
            log::debug!(
                "evaluated {symbol} in {:.1}s",
                Instant::now().duration_since(start).as_secs_f64()
            )
        }

        let interp = part_interp
            .interps
            .into_iter()
            .filter(|(symbol, _)| sig.contains_name(symbol))
            .map(|(symbol, (interp, _))| (symbol, interp))
            .collect();
        FOModel { universe, interp }
    }
}

#[cfg(test)]
mod tests {
    use std::{collections::HashSet, fs};

    use crate::{fly::parser, smtlib::sexp};

    use super::{Backend, GenericBackend, SolverType};

    use test_log::test;

    #[test]
    fn test_issue_5_parse_model_with_auxilliary_defs() {
        let _ = pretty_env_logger::try_init();
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

    #[test]
    fn test_parse_test_model() {
        let _ = pretty_env_logger::try_init();
        let sig = parser::parse_signature(
            r#"
        sort node
        mutable votes(node, node): bool
        "#
            .trim(),
        );

        let backend = GenericBackend {
            solver_type: SolverType::Z3,
            bin: "z3".to_string(),
        };

        let model_text =
            fs::read_to_string("tests/test_model.sexp").expect("could not find model file");
        let model_sexp = sexp::parse(&model_text).expect("test model does not parse");

        let fo_model = (&backend).parse(&sig, 0, &HashSet::new(), &model_sexp);
        assert!(fo_model.interp.contains_key("votes"));
    }
}
