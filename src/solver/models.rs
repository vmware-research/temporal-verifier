// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

use lazy_static::lazy_static;
use serde::Serialize;
use std::{collections::HashMap, iter};
use thiserror::Error;

use regex::Regex;

use crate::{
    fly::{
        semantics::{Element, Interpretation},
        syntax::Sort,
    },
    smtlib::sexp::{atom_s, sexp_l, Atom, Sexp},
};

#[derive(Debug, Clone)]
pub struct PartialInterp {
    universes: HashMap<String, Vec<String>>,
    // reverse of universes
    term_to_element: HashMap<String, Element>,
    pub interps: HashMap<String, (Interpretation, Sort)>,
}

#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
pub struct ModelSymbol {
    pub binders: Vec<(String, Sort)>,
    pub body: Sexp,
    pub ret_sort: Sort,
}

#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
pub struct Model {
    pub universes: HashMap<String, Vec<String>>,
    pub symbols: HashMap<String, ModelSymbol>,
}

#[derive(Debug, Error)]
#[error("eval error: {0}")]
pub struct EvalError(String);

fn bool_atom(b: bool) -> Atom {
    let v = if b { "true" } else { "false" };
    Atom::S(v.to_string())
}

fn subst_hashmap(repl: &HashMap<&str, &Sexp>, e: &mut Sexp) {
    match e {
        Sexp::Atom(Atom::I(_)) | Sexp::Comment(_) => {}
        Sexp::Atom(Atom::S(s)) => {
            if let Some(&new) = repl.get(s.as_str()) {
                *e = new.clone();
            }
        }
        Sexp::List(ss) => {
            for s in ss.iter_mut() {
                subst_hashmap(repl, s)
            }
        }
    }
}

/// Parallel substitution into an sexp.
pub fn subst(repl: &[(&str, Sexp)], e: &Sexp) -> Sexp {
    let mut repl_map: HashMap<&str, &Sexp> = HashMap::with_capacity(repl.len());
    for (name, e) in repl {
        let old = repl_map.insert(name, e);
        assert_eq!(old, None, "duplicate replacement for {name} in subst");
    }
    let mut new = e.clone();
    subst_hashmap(&repl_map, &mut new);
    new
}

fn parse_sort(sort: &Sexp) -> Sort {
    let sort_name = sort.atom_s().unwrap();
    if sort_name == "Bool" {
        Sort::Bool
    } else {
        Sort::Id(sort_name.to_string())
    }
}

fn parse_binders(binders: &Sexp) -> Vec<(String, Sort)> {
    let binder_sexps = binders.list().unwrap();
    binder_sexps
        .iter()
        .map(|b| {
            // b should be a list of (name type)
            let ss = b.list().unwrap();
            assert!(ss.len() == 2, "binder is ill-formed");
            let name = ss[0].atom_s().unwrap().to_string();
            let sort = parse_sort(&ss[1]);
            (name, sort)
        })
        .collect()
}

pub(crate) fn parse_z3(model: &Sexp) -> Model {
    let mut universes: HashMap<String, Vec<String>> = HashMap::new();
    let mut symbols: HashMap<String, ModelSymbol> = HashMap::new();
    if let Some(ss) = model.list() {
        // remove a leading "model" for older versions
        let ss = if !ss.is_empty() && ss[0] == atom_s("model") {
            &ss[1..]
        } else {
            ss
        };
        for s in ss {
            if let Some((head, args)) = s.app() {
                if head == "declare-fun" {
                    assert_eq!(args.len(), 3, "declare-fun should have name, binders, sort");
                    let name = args[0].atom_s().unwrap().to_string();
                    let binders = &args[1];
                    let sort = args[2].atom_s().unwrap();
                    // this is a universe element, with no body
                    assert_eq!(
                        binders,
                        &sexp_l([]),
                        "universe elements should take no argments"
                    );
                    universes.entry(sort.to_string()).or_default().push(name);
                } else if head == "define-fun" {
                    assert_eq!(
                        args.len(),
                        4,
                        "define-fun should have name, binders, sort, body"
                    );
                    let name = args[0].atom_s().unwrap().to_string();
                    let binders = parse_binders(&args[1]);
                    let ret_sort = parse_sort(&args[2]);
                    let body = args[3].clone();
                    let sym = ModelSymbol {
                        binders,
                        body,
                        ret_sort,
                    };
                    symbols.insert(name, sym);
                } else if head == "forall" {
                    // ignore, cardinality constraint
                } else {
                    eprintln!("warning: unexpected {head} in z3 model")
                }
            }
        }
    }
    Model { universes, symbols }
}

pub(crate) fn parse_cvc(model: &Sexp, version5: bool) -> Model {
    let version4 = !version5;
    let mut universe_cardinalities: HashMap<String, usize> = HashMap::new();
    let mut symbols: HashMap<String, ModelSymbol> = HashMap::new();
    lazy_static! {
        static ref CARDINALITY_RE: Regex = Regex::new("cardinality of (.*) is ([0-9]+)$").unwrap();
    }
    if let Some(ss) = model.list() {
        // remove a leading "model" for CVC4
        let ss = {
            if version4 {
                assert!(!ss.is_empty());
                assert_eq!(ss[0], atom_s("model"));
                &ss[1..]
            } else {
                ss
            }
        };
        for s in ss {
            if let Sexp::Comment(s) = s {
                if let Some(cs) = CARDINALITY_RE.captures(s) {
                    let sort = cs.get(1).unwrap().as_str().to_string();
                    let card = cs.get(2).unwrap().as_str().parse::<usize>().unwrap();
                    universe_cardinalities.insert(sort, card);
                }
                continue;
            }
            if let Some((head, args)) = s.app() {
                if head == "define-fun" {
                    assert_eq!(
                        args.len(),
                        4,
                        "define-fun should have name, binders, sort, body"
                    );
                    let name = args[0].atom_s().unwrap().to_string();
                    let binders = parse_binders(&args[1]);
                    let ret_sort = parse_sort(&args[2]);
                    let body = args[3].clone();
                    let sym = ModelSymbol {
                        binders,
                        body,
                        ret_sort,
                    };
                    symbols.insert(name, sym);
                } else if version4 && head == "declare-sort" {
                    // cvc4 only
                    continue;
                } else {
                    eprintln!("warning: unexpected {head} in cvc model")
                }
            }
        }
    }
    let mut universes = HashMap::new();
    for (sort, card) in universe_cardinalities.into_iter() {
        let elements: Vec<String> = (0..card)
            .map(|i| {
                if version4 {
                    format!("@uc_{sort}_{i}")
                } else {
                    format!("@{sort}_{i}")
                }
            })
            .collect();
        universes.insert(sort, elements);
    }
    Model { universes, symbols }
}

impl PartialInterp {
    pub fn for_model(model: &Model) -> Self {
        let mut term_to_element = HashMap::new();
        // the sort doesn't matter here (universe element names are already
        // distinct between sorts)
        for elements in model.universes.values() {
            for (e_idx, term) in elements.iter().enumerate() {
                term_to_element.insert(term.to_string(), e_idx);
            }
        }
        Self {
            term_to_element,
            universes: model.universes.clone(),
            interps: HashMap::new(),
        }
    }

    fn has_eval(&self, f: &str) -> bool {
        self.interps.contains_key(f)
    }

    fn eval(&self, f: &str, args: &[Atom]) -> String {
        let (interp, ret_sort) = &self.interps[f];
        let args = args
            .iter()
            .map(|atom| match atom {
                Atom::I(_) => panic!("cannot evaluate on integers"),
                Atom::S(name) => {
                    if name == "true" {
                        1
                    } else if name == "false" {
                        0
                    } else {
                        self.term_to_element[name]
                    }
                }
            })
            .collect::<Vec<usize>>();
        let result_el = interp.get(&args);
        match ret_sort {
            Sort::Bool => {
                if result_el == 1 {
                    "true".to_string()
                } else {
                    "false".to_string()
                }
            }
            Sort::Id(sort) => self.universes[sort][result_el].clone(),
        }
    }
}

impl Model {
    fn eval_bool(
        &self,
        repl: &HashMap<&str, Atom>,
        part_eval: &PartialInterp,
        e: &Sexp,
    ) -> Result<bool, EvalError> {
        let a = self.smt_eval(repl, part_eval, e)?;
        match a {
            Atom::S(s) if s == "true" => Ok(true),
            Atom::S(s) if s == "false" => Ok(false),
            _ => Err(EvalError(format!("unexpected bool: {a}"))),
        }
    }

    /// Evaluate an SMT expression, reducing constants with known semantics. Fails
    /// if this does not result in an Atom.
    pub fn smt_eval(
        &self,
        repl: &HashMap<&str, Atom>,
        part_eval: &PartialInterp,
        e: &Sexp,
    ) -> Result<Atom, EvalError> {
        // println!("evaluating {e}");
        let go_bool = |e: &Sexp| self.eval_bool(repl, part_eval, e);
        let go = |e: &Sexp| self.smt_eval(repl, part_eval, e);
        match e {
            Sexp::Atom(a) => {
                if let Some(id) = a.s() {
                    Ok(repl.get(id).unwrap_or(a).clone())
                } else {
                    Ok(a.clone())
                }
            }
            Sexp::Comment(_) => Err(EvalError("comment".to_string())),
            Sexp::List(ss) => {
                let ss = ss
                    .iter()
                    .filter(|s| !matches!(s, Sexp::Comment(_)))
                    .collect::<Vec<_>>();
                if ss.is_empty() {
                    return Err(EvalError("empty list".to_string()));
                }
                let head = ss[0].atom_s().ok_or(EvalError(format!(
                    "unexpected function {} (non-atom)",
                    ss[0]
                )))?;
                let args = &ss[1..];
                if head == "and" {
                    for arg in args {
                        let v = go_bool(arg)?;
                        if !v {
                            return Ok(bool_atom(false));
                        }
                    }
                    return Ok(bool_atom(true));
                } else if head == "or" {
                    for arg in args {
                        let v = go_bool(arg)?;
                        if v {
                            return Ok(bool_atom(true));
                        }
                    }
                    return Ok(bool_atom(false));
                } else if head == "not" || head == "!" {
                    assert_eq!(args.len(), 1);
                    let x = go_bool(args[0])?;
                    Ok(bool_atom(!x))
                } else if head == "as" {
                    // type cast (basically ignored)
                    go(args[0])
                } else if head == "=" {
                    assert_eq!(args.len(), 2);
                    let lhs = go(args[0])?;
                    let rhs = go(args[1])?;
                    Ok(bool_atom(lhs == rhs))
                } else if head == "ite" {
                    assert_eq!(args.len(), 3);
                    let cond = go_bool(args[0])?;
                    if cond {
                        go(args[1])
                    } else {
                        go(args[2])
                    }
                } else if head == "let" {
                    // (let ((x1 e1) (x2 e2)) e)
                    assert_eq!(args.len(), 2);
                    let binders = args[0]
                        .list()
                        .expect("let argument should be a list of binders");
                    let repl: Vec<(&str, Sexp)> = binders
                        .iter()
                        .map(|binder| {
                            let (name, e) = binder.app().expect("unexpected binder");
                            assert_eq!(e.len(), 1, "unexpected binder val");
                            (name, e[0].clone())
                        })
                        .collect();
                    let e = subst(&repl, args[1]);
                    go(&e)
                } else if self.symbols.contains_key(head) {
                    if part_eval.has_eval(head) {
                        let args = args.iter().flat_map(|e| go(e)).collect::<Vec<_>>();
                        let res = part_eval.eval(head, &args);
                        return Ok(Atom::S(res));
                    }
                    let ModelSymbol { binders, body, .. } = &self.symbols[head];
                    assert_eq!(
                        binders.len(),
                        args.len(),
                        "wrong number of arguments to {head}"
                    );
                    // first evaluate all arguments
                    let args = args
                        .iter()
                        .map(|e| -> Result<Sexp, EvalError> {
                            let a = go(e)?;
                            Ok(Sexp::Atom(a))
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    // then substitute for each binder
                    let repl: Vec<(&str, Sexp)> = iter::zip(binders, args.iter().cloned())
                        .map(|(binder, e)| (binder.0.as_str(), e))
                        .collect();
                    go(&subst(&repl, body))
                } else {
                    Err(EvalError(format!("unexpected function {head}")))
                }
            }
        }
    }
}
