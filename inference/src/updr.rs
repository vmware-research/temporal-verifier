// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Implementation of UPDR. See <https://www.tau.ac.il/~sharonshoham/papers/jacm17.pdf>.

use im::{hashset, HashSet};
use itertools::Itertools;
use solver::basics::SingleSolver;
use std::sync::Arc;

use crate::basics::{CexOrCore, CexResult, FOModule, SmtTactic, TermOrModel};
use fly::syntax::Term::{NAryOp, Quantified, UnaryOp};
use fly::syntax::*;
use fly::term::cnf::term_to_cnf_clauses;

#[derive(Debug, Clone)]
struct Frame {
    terms: Vec<Term>,
}

impl Frame {
    fn strengthen(&mut self, term: Term) {
        self.terms.push(term);
    }
}

struct BackwardsReachableState {
    id: usize,
    term_or_model: TermOrModel,
    num_steps_to_bad: usize,
    known_absent_until_frame: usize,
}

/// State for a UPDR invariant search
pub struct Updr {
    solver: Arc<SingleSolver>,
    frames: Vec<Frame>,
    backwards_reachable_states: Vec<BackwardsReachableState>,
    currently_blocking_id: Option<usize>,
}

impl Updr {
    /// Initialize a UPDR search
    pub fn new(solver_conf: Arc<SingleSolver>) -> Updr {
        Updr {
            solver: solver_conf,
            frames: vec![],
            backwards_reachable_states: vec![],
            currently_blocking_id: None,
        }
    }

    fn find_state_to_block(&mut self, module: &FOModule) -> Option<usize> {
        // println!("start");
        loop {
            // println!("loop");
            // Search for a known state.
            let bstate_min = self.backwards_reachable_states.iter_mut().min_by(|b1, b2| {
                (b1.known_absent_until_frame, b1.num_steps_to_bad)
                    .cmp(&(b2.known_absent_until_frame, b2.num_steps_to_bad))
            });
            if bstate_min.is_none()
                || bstate_min.as_ref().unwrap().known_absent_until_frame == self.frames.len() - 1
            {
                // println!("break for no bstates");
                break;
            }
            let found_state = bstate_min.unwrap();
            match &found_state.term_or_model {
                TermOrModel::Term(t) => {
                    // println!("m: {}", t);
                    if module
                        .implies_cex(
                            self.solver.as_conf(),
                            &self.frames[found_state.known_absent_until_frame + 1].terms,
                            &Term::negate(t.clone()),
                        )
                        .is_some()
                    {
                        // println!("returning for term implies");
                        return Some(found_state.id);
                    }
                }
                TermOrModel::Model(m) => {
                    // println!("m: {}", m.to_diagram());
                    if m.eval(&NAryOp(
                        NOp::And,
                        self.frames[found_state.known_absent_until_frame + 1]
                            .terms
                            .clone(),
                    )) != 0
                    {
                        // println!("returning for model eval");
                        return Some(found_state.id);
                    }
                }
            }
            // The state does not appear in this frame.
            found_state.known_absent_until_frame += 1;
        }
        // println!("broke");

        // Search for a new state.
        let last_frame = self.frames.last().unwrap();
        // println!("last_frame.terms {}", &last_frame.terms[0]);
        let counter_example = module.safe_cex(self.solver.as_conf(), &last_frame.terms);
        if module.module.proofs.is_empty() || counter_example.is_none() {
            // println!("None");
            // Nothing to block.
            return None;
        }
        // println!(
        //     "counter_example: {}",
        //     &counter_example.as_ref().unwrap().to_diagram()
        // );
        let new_state = BackwardsReachableState {
            id: self.backwards_reachable_states.len(),
            term_or_model: TermOrModel::Model(counter_example.unwrap()),
            num_steps_to_bad: 0,
            // Was not found in the last frame, only in this one.
            known_absent_until_frame: self.frames.len() - 2,
        };
        self.backwards_reachable_states.push(new_state);
        Some(self.backwards_reachable_states.len() - 1)
    }

    fn establish_safety(&mut self, module: &FOModule) {
        while let Some(state_index) = self.find_state_to_block(module) {
            // println!("got ID: {}", &state_index);
            self.currently_blocking_id = Some(state_index);
            {
                let bstate = &self.backwards_reachable_states[state_index];
                let mut trace: Vec<(Term, TermOrModel)> = vec![];
                self.block(
                    &bstate.term_or_model.clone(),
                    &bstate.known_absent_until_frame + 1,
                    &mut trace,
                    module,
                );
            }
            self.backwards_reachable_states[state_index].known_absent_until_frame += 1;
        }
    }

    fn block(
        &mut self,
        term_or_model: &TermOrModel,
        frame_index: usize,
        trace: &mut Vec<(Term, TermOrModel)>,
        module: &FOModule,
    ) {
        let as_term: Term = match term_or_model {
            TermOrModel::Term(t) => t.clone(),
            TermOrModel::Model(m) => m.to_diagram(),
        };
        // println!("blocking as term: {} at index {}", as_term, frame_index);
        if frame_index == 0
            || (frame_index == 1
                && module
                    .implies_cex(
                        self.solver.as_conf(),
                        &self.frames[0].terms,
                        &Term::negate(as_term.clone()),
                    )
                    .is_some())
        {
            panic!("abstract cex");
        }
        let core = loop {
            match self.get_predecessor(term_or_model, frame_index - 1, module) {
                CexOrCore::Cex((trans, pred)) => {
                    let src = &self.backwards_reachable_states[self.currently_blocking_id.unwrap()];
                    let steps_from_cex =
                        src.known_absent_until_frame + 2 - frame_index + src.num_steps_to_bad;
                    let bstate = BackwardsReachableState {
                        id: self.backwards_reachable_states.len(),
                        term_or_model: TermOrModel::Model(pred.clone()),
                        known_absent_until_frame: 0,
                        num_steps_to_bad: steps_from_cex,
                    };
                    if let TermOrModel::Model(m) = bstate.term_or_model.clone() {
                        println!("managed to reach {m}");
                    }
                    if let TermOrModel::Term(t) = bstate.term_or_model.clone() {
                        println!("managed to reach {t}");
                    }
                    self.backwards_reachable_states.push(bstate);
                    trace.push((trans.clone(), TermOrModel::Model(pred.clone())));
                    self.block(&TermOrModel::Model(pred), frame_index - 1, trace, module);
                    trace.pop();
                }
                CexOrCore::Core(core_map) => break core_map,
            }
        };
        // println!("CORE");
        let mut terms: Vec<Term> = vec![];
        for key in core.keys().sorted() {
            // println!("{}", key);
            if let UnaryOp(UOp::Next, t) = key.clone() {
                terms.push(*t);
            } else {
                terms.push(key.clone());
            }
        }
        // println!("END CORE");
        if let Quantified {
            quantifier: Quantifier::Exists,
            mut body,
            binders,
        } = as_term
        {
            if !&terms.is_empty() {
                body = Box::new(NAryOp(NOp::And, terms));
            }
            let negated = Term::negate(Quantified {
                quantifier: Quantifier::Exists,
                body,
                binders,
            });
            // println!("blocking in {} term: {}", frame_index, &negated);
            for i in 0..(frame_index + 1) {
                if self.frames[i].terms.contains(&negated) {
                    continue;
                }
                self.frames[i].strengthen(negated.clone());
            }
            'push_frames: for i in frame_index..(self.frames.len() - 1) {
                let prev_terms = self.frames[i].terms.clone();
                if self.frames[i + 1].terms.contains(&negated) {
                    continue;
                }
                if let CexResult::UnsatCore(_) = module.trans_cex(
                    self.solver.as_ref(),
                    &prev_terms,
                    &negated,
                    true,
                    None,
                    true,
                ) {
                    self.frames[i + 1].strengthen(negated.clone());
                } else {
                    break 'push_frames;
                }
            }
            // println!("frames in block:");
            // self.print_frames();
        } else {
            panic!()
        }
    }

    #[allow(clippy::let_and_return)]
    fn get_predecessor(
        &mut self,
        term_or_model: &TermOrModel,
        frame_index: usize,
        module: &FOModule,
    ) -> CexOrCore {
        // run UPDR
        let prev_frame = &self.frames[frame_index];
        let out = module.get_pred(self.solver.as_conf(), &prev_frame.terms, term_or_model);

        // if let TermOrModel::Model(model) = term_or_model {
        //     if let CexOrCore::Core(out) = &out {
        //         // run MARCO on cores without affecting UPDR
        //         if let Term::Quantified {
        //             quantifier,
        //             binders,
        //             body,
        //         } = &model.to_diagram()
        //         {
        //             if *quantifier == Quantifier::Exists {
        //                 if let Term::NAryOp(NOp::And, conj) = &**body {
        //                     let func = |array: &[bool]| {
        //                         assert!(array.len() == conj.len());
        //                         // only enable terms in conj that match array
        //                         let chosen: Vec<Term> = (0..conj.len())
        //                             .filter(|i| array[*i])
        //                             .map(|i| conj[i].clone())
        //                             .collect();
        //                         let term = Term::Quantified {
        //                             quantifier: Quantifier::Exists,
        //                             binders: binders.clone(),
        //                             body: Box::new(Term::NAryOp(NOp::And, chosen)),
        //                         };
        //                         let term = TermOrModel::Term(term);
        //                         let out =
        //                             module.get_pred(&self.solver_conf, &prev_frame.terms, &term);
        //                         matches!(out, CexOrCore::Core(_))
        //                     };

        //                     use crate::inference::marco::*;
        //                     // we use !func because func is monotone in the wrong direction
        //                     let results: Vec<_> = marco(|array| !func(array), conj.len())
        //                         // therefore we also want MUS instead of MSS
        //                         .filter_map(|mss_or_mus| match mss_or_mus {
        //                             MssOrMus::Mus(array) => Some(array),
        //                             MssOrMus::Mss(_) => None,
        //                         })
        //                         .collect();

        //                     println!("\nunsat core:");
        //                     for (term, b) in out.iter().sorted() {
        //                         if *b {
        //                             println!("{}", term);
        //                         }
        //                     }

        //                     println!("\nMARCO: {} cores", results.len());
        //                     for (i, array) in results.iter().enumerate() {
        //                         println!("core {}:", i);
        //                         for (i, b) in array.iter().enumerate() {
        //                             if *b {
        //                                 println!("{}", conj[i]);
        //                             }
        //                         }
        //                     }
        //                     println!("\n");
        //                 } else {
        //                     panic!("MARCO: bad diagram");
        //                 }
        //             } else {
        //                 panic!("MARCO: bad diagram");
        //             }
        //         } else {
        //             panic!("MARCO: bad diagram");
        //         }
        //     }
        // }

        // return the actual UPDR output
        out
    }

    fn find_frame(&mut self, m: &Module) -> Option<Frame> {
        let module = FOModule::new(m, false, SmtTactic::Full);
        self.backwards_reachable_states = Vec::new();
        for proof in &module.module.proofs {
            for clause in term_to_cnf_clauses(&proof.safety.x) {
                self.backwards_reachable_states
                    .push(BackwardsReachableState {
                        id: self.backwards_reachable_states.len(),
                        term_or_model: TermOrModel::Term(Term::negate_and_simplify(clause)),
                        num_steps_to_bad: 0,
                        known_absent_until_frame: 0,
                    })
            }
        }
        self.frames = vec![Frame {
            terms: module
                .module
                .inits
                .clone()
                .into_iter()
                .flat_map(|t| -> Vec<Term> {
                    match t {
                        NAryOp(NOp::And, terms) => terms,
                        _ => panic!("got malformed inits"),
                    }
                })
                .collect(),
        }];
        // println!("{}", &module.safeties[0]);
        // println!("{}", backwards_reachable_states[0].term);
        // println!("{}", frames[0].terms[0]);
        // Some(frames[0].clone())
        loop {
            // println!("establish_safety");
            self.establish_safety(&module);
            self.print_frames();
            // println!("simplify");
            self.simplify(&module);
            let inductive_frame: Option<Frame> = self.get_inductive_frame(&module);
            if inductive_frame.is_some() {
                println!("inductive_frame");
                for t in &inductive_frame.as_ref().unwrap().terms {
                    println!("{t}");
                }
                return inductive_frame;
            }
            // println!("add_frame_and_push");
            self.add_frame_and_push(&module);
            self.print_frames();
        }
    }

    /// Search for an inductive invariant.
    pub fn search(&mut self, m: &Module) -> Option<Term> {
        // TODO: is the and of the terms correct?
        self.find_frame(m).map(|t| Term::and(t.terms))
    }

    fn simplify(&mut self, module: &FOModule) {
        for frame in self.frames.iter_mut() {
            let mut terms: Vec<Term> = vec![];
            let mut removed: HashSet<Term> = hashset![];
            for term in frame.terms.iter().rev() {
                let f_minus_t: Vec<Term> = frame
                    .terms
                    .clone()
                    .into_iter()
                    .filter(|t| t != term && !removed.contains(t))
                    .collect();
                if module
                    .implies_cex(self.solver.as_conf(), &f_minus_t, term)
                    .is_some()
                    && !module
                        .module
                        .proofs
                        .iter()
                        .any(|proof| &proof.safety.x == term)
                {
                    terms.push(term.clone())
                } else {
                    // println!("imp cex t: {}, {}, {}", &term, f_minus_t.len(), frame.terms.len());
                    // for h in &f_minus_t {
                    //     print!(" {} ", h)
                    // }
                    // println!("");
                    // println!("removing in {} simplify: {}", i, &term);
                    removed.insert(term.clone());
                }
            }
            frame.terms = terms.into_iter().rev().collect();
        }
    }

    fn add_frame_and_push(&mut self, module: &FOModule) {
        self.frames.push(Frame { terms: vec![] });
        for i in 0..(self.frames.len() - 1) {
            let prev_terms = self.frames[i].terms.clone();
            for term in prev_terms.iter() {
                if self.frames[i + 1].terms.contains(term) {
                    continue;
                }
                if let CexResult::UnsatCore(_) =
                    module.trans_cex(self.solver.as_ref(), &prev_terms, term, true, None, true)
                {
                    self.frames[i + 1].strengthen(term.clone());
                }
            }
        }
    }

    fn print_frames(&self) {
        println!("all frames:");
        for frame in self.frames.iter() {
            print!("[");
            for term in frame.terms.iter() {
                print!("{term}, ");
            }
            println!("]");
        }
        println!("all BRS:");
        for state in self.backwards_reachable_states.iter() {
            print!(
                "term: {} ",
                match state.term_or_model.clone() {
                    TermOrModel::Term(t) => t,
                    TermOrModel::Model(m) => m.to_diagram(),
                }
            );
            println!(
                "known_absent_until_frame: {}, num_steps_to_bad : {}",
                state.known_absent_until_frame, state.num_steps_to_bad
            );
        }
    }

    fn get_inductive_frame(&self, module: &FOModule) -> Option<Frame> {
        for i in 0..(self.frames.len() - 1) {
            let mut is_inductive = true;
            // println!("checking inductiveness of frame {}", i);
            for term in &self.frames[i].terms {
                if module
                    .implies_cex(self.solver.as_conf(), &self.frames[i + 1].terms, term)
                    .is_some()
                {
                    is_inductive = false;
                }
            }
            if is_inductive {
                return Some(self.frames[i].clone());
            }
        }
        return None;
    }
}
