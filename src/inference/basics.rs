// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

use itertools::Itertools;
use std::collections::HashMap;
use std::io::BufRead;
use std::io::Write;
use std::rc::Rc;

use crate::{
    fly::{
        semantics::Model,
        syntax::{Module, NOp, Quantifier, Signature, Sort, Term, ThmStmt, UOp},
    },
    inference::lemma::{Lemma, LemmaQF, QuantifierConfig},
    smtlib::proc::SatResp,
    term::{FirstOrder, Next},
    verify::SolverConf,
};

/// A first-order module is represented using first-order formulas,
/// namely single-vocabulary axioms, initial assertions and safety assertions,
/// and double-vocabulary transition assertions.
/// `disj` denotes whether to split the transitions disjunctively, if possible.
pub struct FOModule {
    signature: Signature,
    pub axioms: Vec<Term>,
    pub inits: Vec<Term>,
    pub transitions: Vec<Term>,
    pub safeties: Vec<Term>,
    disj: bool,
}

impl FOModule {
    pub fn new(m: &Module, disj: bool) -> Self {
        let mut fo = FOModule {
            signature: m.signature.clone(),
            axioms: vec![],
            inits: vec![],
            transitions: vec![],
            safeties: vec![],
            disj,
        };

        for statement in &m.statements {
            match statement {
                ThmStmt::Assume(t) => {
                    if FirstOrder::unrolling(t) == Some(0) {
                        fo.inits.push(t.clone());
                    } else if let Term::UnaryOp(UOp::Always, t) = t {
                        match FirstOrder::unrolling(t) {
                            Some(0) => fo.axioms.push(t.as_ref().clone()),
                            Some(1) => fo.transitions.push(Next::normalize(t.as_ref())),
                            _ => (),
                        }
                    }
                }
                ThmStmt::Assert(pf) => {
                    if let Term::UnaryOp(UOp::Always, t) = &pf.assert.x {
                        if FirstOrder::unrolling(t) == Some(0) {
                            fo.safeties.push(t.as_ref().clone());
                        }
                    }
                }
            }
        }

        fo
    }

    pub fn init_cex(&self, conf: &SolverConf, t: &Term) -> Option<Model> {
        let mut solver = conf.solver(&self.signature, 1);
        for a in self.axioms.iter().chain(self.inits.iter()) {
            solver.assert(a);
        }
        solver.assert(&Term::negate(t.clone()));

        let resp = solver.check_sat(HashMap::new()).expect("error in solver");
        match resp {
            SatResp::Sat => {
                let mut states = solver.get_minimal_model();
                assert_eq!(states.len(), 1);

                Some(states.remove(0))
            }
            SatResp::Unsat => None,
            SatResp::Unknown(_) => panic!(),
        }
    }

    pub fn trans_cex(&self, conf: &SolverConf, hyp: &[Term], t: &Term) -> Option<(Model, Model)> {
        let disj_trans = if self.disj {
            self.transitions
                .iter()
                .map(|t| match t {
                    Term::NAryOp(NOp::Or, args) => args.iter().collect_vec(),
                    _ => vec![t],
                })
                .multi_cartesian_product()
                .collect_vec()
        } else {
            vec![self.transitions.iter().collect_vec()]
        };

        for trans in disj_trans {
            let mut solver = conf.solver(&self.signature, 2);
            for a in self
                .axioms
                .iter()
                .chain(self.safeties.iter())
                .chain(hyp.iter())
                .chain(trans.into_iter())
            {
                solver.assert(a);
            }
            for a in self.axioms.iter() {
                solver.assert(&Next::prime(a));
            }
            solver.assert(&Term::negate(Next::prime(t)));

            let resp = solver.check_sat(HashMap::new()).expect("error in solver");
            match resp {
                SatResp::Sat => {
                    let states = solver.get_minimal_model();
                    assert_eq!(states.len(), 2);

                    return Some(states.into_iter().collect_tuple().unwrap());
                }
                SatResp::Unsat => (),
                SatResp::Unknown(reason) => panic!("sat solver returned unknown: {reason}"),
            }
        }

        None
    }

    pub fn trans_safe_cex(&self, conf: &SolverConf, hyp: &[Term]) -> Option<Model> {
        for s in self.safeties.iter() {
            if let Some(models) = self.trans_cex(conf, hyp, s) {
                return Some(models.0);
            }
        }

        None
    }
}

#[derive(Clone)]
struct FrameEntry<T: LemmaQF> {
    lemma: Lemma<T>,
    weakened: Vec<Lemma<T>>,
    progress: bool,
}

/// A frame handles lemmas and their weakenings.
#[derive(Clone)]
pub struct Frame<T: LemmaQF> {
    entries: Vec<FrameEntry<T>>,
    fo: Rc<FOModule>,
    cfg: Rc<QuantifierConfig>,
    conf: Rc<SolverConf>,
}

impl<T: LemmaQF> Frame<T> {
    pub fn new(
        lemmas: Vec<Lemma<T>>,
        fo: Rc<FOModule>,
        cfg: Rc<QuantifierConfig>,
        conf: Rc<SolverConf>,
    ) -> Self {
        Frame {
            entries: lemmas
                .into_iter()
                .map(|lemma| FrameEntry {
                    lemma: lemma.clone(),
                    weakened: vec![lemma],
                    progress: false,
                })
                .collect_vec(),
            fo,
            cfg,
            conf,
        }
    }

    /// Convert frame to a Vec of terms.
    pub fn to_terms(&self) -> Vec<Term> {
        self.entries.iter().map(|e| e.lemma.to_term()).collect_vec()
    }

    /// Get a counter-example to induction which extends a specific model.
    pub fn get_cex_extend(
        &mut self,
        model: &Model,
        start_at: Option<&mut (usize, usize)>,
    ) -> Option<Model> {
        let hyp = vec![model.to_term()];
        let mut default_start = (0, 0);
        let i = start_at.unwrap_or(&mut default_start);
        while i.0 < self.entries.len() {
            while i.1 < self.entries[i.0].weakened.len() {
                if let Some(models) =
                    self.fo
                        .trans_cex(&self.conf, &hyp, &self.entries[i.0].weakened[i.1].to_term())
                {
                    return Some(models.1);
                }

                i.1 += 1;
            }

            i.0 += 1;
            i.1 = 0;
        }

        None
    }

    /// Get a counter-example to induction which is an initial state.
    pub fn get_cex_init(&mut self, start_at: Option<&mut (usize, usize)>) -> Option<Model> {
        let mut default_start = (0, 0);
        let i = start_at.unwrap_or(&mut default_start);
        while i.0 < self.entries.len() {
            while i.1 < self.entries[i.0].weakened.len() {
                if let Some(model) = self
                    .fo
                    .init_cex(&self.conf, &self.entries[i.0].weakened[i.1].to_term())
                {
                    return Some(model);
                }

                i.1 += 1;
            }

            i.0 += 1;
            i.1 = 0;
        }

        None
    }

    /// Get a counter-example to induction which is a transition from the current frame.
    pub fn get_cex_trans(
        &mut self,
        frame: &[Term],
        start_at: Option<&mut (usize, usize)>,
    ) -> Option<(Model, Model)> {
        let mut default_start = (0, 0);
        let i = start_at.unwrap_or(&mut default_start);
        while i.0 < self.entries.len() {
            while i.1 < self.entries[i.0].weakened.len() {
                if let Some(models) = self.fo.trans_cex(
                    &self.conf,
                    frame,
                    &self.entries[i.0].weakened[i.1].to_term(),
                ) {
                    return Some(models);
                }

                i.1 += 1;
            }

            i.0 += 1;
            i.1 = 0;
        }

        None
    }

    /// Weaken the frame to satisfy a model.
    pub fn weaken<F>(
        &mut self,
        model: &Model,
        filter: F,
        atoms: &[Term],
        start_at: Option<(usize, usize)>,
    ) where
        F: Fn(&Lemma<T>) -> bool,
    {
        let mut i = start_at.unwrap_or((0, 0));
        while i.0 < self.entries.len() {
            while i.1 < self.entries[i.0].weakened.len() {
                if model.eval(&self.entries[i.0].weakened[i.1].to_term(), None) == 0 {
                    self.entries[i.0].progress = true;
                    let lemma = self.entries[i.0].weakened.remove(i.1);
                    let mut new_lemmas = lemma.weaken(model, &self.cfg, Some(atoms));
                    // Remove weakened lemmas that are subsumed by others.
                    // Note that weakened lemmas cannot subsume others themselves,
                    // since the lemmas are maintained so that there will never be
                    // a lemma which subsumes another.
                    new_lemmas.retain(&filter);
                    new_lemmas.retain(|new_lemma| {
                        !self
                            .entries
                            .iter()
                            .flat_map(|e| &e.weakened)
                            .any(|l| l.subsumes(new_lemma))
                    });
                    self.entries[i.0].weakened.append(&mut new_lemmas);
                } else {
                    i.1 += 1;
                }
            }

            i.0 += 1;
            i.1 = 0;
        }
    }

    /// Update the frame with previously weakened lemmas.
    /// Return whether the frame could be weakened.
    pub fn update(&mut self, increasing: bool) -> bool {
        let mut updated = false;

        let mut i = 0;
        let mut prog_index: Option<usize> = None;
        while i < self.entries.len() {
            if self.entries[i].progress {
                match self.entries[i].weakened.len() {
                    0 => {
                        updated = true;
                    }
                    1 => {
                        self.entries[i].lemma = self.entries[i].weakened[0].clone();
                        self.entries[i].progress = false;
                        updated = true;
                    }
                    _ => {
                        if increasing && prog_index.is_none() {
                            prog_index = Some(i);
                        }
                    }
                }
            }

            i += 1;
        }

        if updated {
            self.entries.retain(|e| !e.weakened.is_empty());
        } else if let Some(index) = prog_index {
            let entry = self.entries.remove(index);
            println!("    Replacing {} with", &entry.lemma.to_term());
            for w in entry.weakened {
                println!("        {}", &w.to_term());
                self.entries.push(FrameEntry {
                    lemma: w.clone(),
                    weakened: vec![w],
                    progress: false,
                });
            }
            updated = true;
        }

        updated
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn len_weakened(&self) -> usize {
        self.entries.iter().map(|e| e.weakened.len()).sum()
    }
}

/// Create a quantifier configuration using user input.
// TODO: replace with config file or command-line arguments
pub fn input_cfg(sig: &Signature) -> (QuantifierConfig, usize, Option<usize>) {
    let mut quantifiers = vec![];
    let mut sorts = vec![];
    let mut names = vec![];

    let stdin = std::io::stdin();
    let mut stdout = std::io::stdout();

    print!("Prefix length: ");
    stdout.flush().unwrap();
    let length = stdin
        .lock()
        .lines()
        .next()
        .unwrap()
        .unwrap()
        .parse::<usize>()
        .unwrap();

    println!();

    println!("Please enter each quantifier on a separate line, in the form");
    println!("<quantifier: F/E/*> <sort> <first var name> <second var name> ...");
    for _ in 0..length {
        let line = stdin.lock().lines().next().unwrap().unwrap();
        let mut parts = line.split_whitespace();

        quantifiers.push(match parts.next().unwrap() {
            "*" => None,
            "F" => Some(Quantifier::Forall),
            "E" => Some(Quantifier::Exists),
            _ => panic!("Invalid quantifier entered."),
        });

        let sort_id = parts.next().unwrap().to_string();
        if sig.sorts.contains(&sort_id) {
            sorts.push(Sort::Id(sort_id));
        } else {
            panic!("Invalid sort entered.");
        }

        names.push(parts.map(|s| s.to_string()).collect_vec());
    }

    println!();

    print!("k-pDNF # of cubes: ");
    stdout.flush().unwrap();
    let kpdnf = stdin
        .lock()
        .lines()
        .next()
        .unwrap()
        .unwrap()
        .parse::<usize>()
        .unwrap();

    println!();

    print!("k-pDNF # of literals: ");
    stdout.flush().unwrap();
    let kpdnf_lit = stdin
        .lock()
        .lines()
        .next()
        .unwrap()
        .unwrap()
        .parse::<usize>()
        .unwrap();

    (
        QuantifierConfig {
            quantifiers,
            sorts,
            names,
            depth: None,
            include_eq: true,
        },
        kpdnf,
        Some(kpdnf_lit),
    )
}
