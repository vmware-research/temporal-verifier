// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! High-level interface to an SMT solver using `fly::syntax::Term`s.

use std::{
    collections::{HashMap, HashSet},
    path::{Path, PathBuf},
    time::Instant,
};

use itertools::Itertools;

use crate::sexp;
use fly::timing::TimeType;
use fly::{
    semantics::{Interpretation, Model, Universe},
    syntax::{Binder, Signature, Sort, Term},
};
use smtlib::{
    conf::SolverCmd,
    proc::{SatResp, SmtPid, SmtProc, SolverError},
    sexp::{app, atom_i, atom_s, sexp_l, Atom, Sexp},
};

/// A [`Solver`] requires a Backend, which specifies how to start a particular
/// solver process and how to parse its models (this is not part of SMT-LIB and
/// thus there are meaningful differences in the format of how solvers respond
/// to `(get-model)`).
pub trait Backend {
    /// Get a [`SolverCmd`] with all the info to launch instances of this solver.
    fn get_cmd(&self) -> SolverCmd;

    /// Parse a model returned by `(get-model)` into something structured and
    /// uniform.
    fn parse(
        &self,
        sig: &Signature,
        n_states: usize,
        indicators: &HashSet<String>,
        model: &Sexp,
    ) -> FOModel;

    /// Indicates whether this solver returns minimal models when `(get-model)` is called.
    fn returns_minimal(&self) -> bool;
}

/// An FOModel ("first-order model") gives a cardinality to each universe and an
/// interpretation to each symbol (including primed versions). This is intended
/// to be an easy-to-construct representation of a trace involving multiple
/// states, parseable from an SMT solver's counter example to a single query.
pub struct FOModel {
    /// For each sort in the signature, its cardinality.
    pub universe: HashMap<String, usize>,
    /// For each symbol (including primed versions, with the primes in the
    /// name), its Interpretation in this model (which gives the full table of
    /// values on the finite universes of its input sorts).
    pub interp: HashMap<String, Interpretation>,
}

/// A Solver provides an interface to a running SMT solver, allowing interaction
/// with it using [`fly::syntax::Term`]'s.
///
/// The Backend makes it possible to parse and return models in the compact
/// representation of `semantics::Model`.
pub struct Solver<B> {
    proc: SmtProc,
    signature: Signature,
    n_states: usize,
    asserts: Vec<Term>,
    indicators: HashSet<String>,
    backend: B,
    /// The assumptions used in the last call to `check_sat` (if that was the last call).
    last_assumptions: Option<HashMap<Term, bool>>,
}

impl<B: Backend> Solver<B> {
    /// Start a Solver for a particular signature and backend.
    ///
    /// The `tee` argument causes the SMT2 output sent to the solver to also be
    /// sent to a file, for debugging purposes.
    pub fn new(
        signature: &Signature,
        n_states: usize,
        backend: B,
        tee: Option<&Path>,
    ) -> Result<Self, SolverError> {
        let signature = signature.clone();
        let mut proc = SmtProc::new(backend.get_cmd(), tee)?;
        Self::send_signature(&mut proc, &signature, n_states);
        Ok(Self {
            proc,
            signature,
            n_states,
            asserts: vec![],
            indicators: HashSet::new(),
            backend,
            last_assumptions: None,
        })
    }

    /// Return a handle to cancel the solver
    pub fn pid(&self) -> SmtPid {
        self.proc.pid()
    }

    /// Save the solver state so far to a tee file.
    pub fn save_tee(&self) -> Option<PathBuf> {
        self.proc.save_tee()
    }

    /// Emit encoding of signature, using `n_states` to determine how many times
    /// to emit each mutable symbol.
    fn send_signature(proc: &mut SmtProc, sig: &Signature, n_states: usize) {
        for sort in &sig.sorts {
            proc.send(&app("declare-sort", [atom_s(sort.clone()), atom_i(0)]));
        }
        for r in &sig.relations {
            // immutable symbols are always declared once
            if !r.mutable {
                proc.send(&app(
                    "declare-fun",
                    [
                        atom_s(&r.name),
                        sexp_l(r.args.iter().map(sexp::sort)),
                        sexp::sort(&r.sort),
                    ],
                ));
            }
            // mutable symbols are declared according to n_states (or not at all
            // if n_states=0)
            if r.mutable {
                for n_primes in 0..n_states {
                    let name = &r.name;
                    proc.send(&app(
                        "declare-fun",
                        [
                            atom_s(format!("{name}{}", "'".repeat(n_primes))),
                            sexp_l(r.args.iter().map(sexp::sort)),
                            sexp::sort(&r.sort),
                        ],
                    ));
                }
            }
        }
    }

    /// Send `(assert ...)` to the solver.
    pub fn assert(&mut self, t: &Term) {
        self.proc.send(&app("assert", [sexp::term(t)]));
        self.last_assumptions = None;
        self.asserts.push(t.clone())
    }

    /// Create a comment in the tee'd SMT file, if there is one.
    ///
    /// The comment is passed as a closure so that it isn't computed if we're
    /// not generating an SMT file (in this case it is not sent to the solver;
    /// note that this will affect line numbers in error messages).
    pub fn comment_with<F>(&mut self, comment: F)
    where
        F: FnOnce() -> String,
    {
        self.proc.comment_with(comment)
    }

    /// Get an indicator variable uniquely determined by `name`.
    pub fn get_indicator(&mut self, name: &str) -> Term {
        let ind = format!("__ind@{name}");
        // if this is a new indicator variable, declare it in the solver
        if self.indicators.insert(ind.clone()) {
            self.proc.send(&app(
                "declare-const",
                vec![atom_s(ind.clone()), atom_s("Bool")],
            ));
        }
        self.last_assumptions = None;
        Term::Id(ind)
    }

    /// The `assumptions` map should map indicator variables to whether they
    /// should be assumed true or false.
    pub fn check_sat(&mut self, assumptions: HashMap<Term, bool>) -> Result<SatResp, SolverError> {
        if cfg!(debug_assertions) {
            for assumption in assumptions.keys() {
                assert!(
                    if let Term::Id(s) = assumption {
                        self.indicators.contains(s)
                    } else {
                        false
                    },
                    "assumption {assumption} is not an indicator variable"
                );
            }
        }
        let start = fly::timing::start();
        let r = if assumptions.is_empty() {
            let sat = self.proc.check_sat()?;
            self.comment_with(|| format!("check sat result: {sat:?}"));
            Ok(sat)
        } else {
            self.last_assumptions = Some(assumptions.clone());
            let assumptions = assumptions
                .into_iter()
                .map(|(ind, set_true)| {
                    if set_true {
                        sexp::term(&ind)
                    } else {
                        sexp::negated_term(&ind)
                    }
                })
                .sorted()
                .collect::<Vec<_>>();
            let sat = self.proc.check_sat_assuming(&assumptions)?;
            self.comment_with(|| format!("check sat result: {sat:?}"));
            Ok(sat)
        };
        fly::timing::elapsed(
            TimeType::CheckSatCall {
                sat: matches!(r, Ok(SatResp::Sat)),
            },
            start,
        );
        r
    }

    fn get_fo_model(&mut self, typ: TimeType, start: Instant) -> Result<FOModel, SolverError> {
        let model = self.proc.get_model()?;
        fly::timing::elapsed(typ, start);
        Ok(self
            .backend
            .parse(&self.signature, self.n_states, &self.indicators, &model))
    }

    /// After a sat response to check_sat or check_sat_assuming, produce a trace
    /// of models, one per state. Each model interprets all of the symbols in
    /// the signature.
    pub fn get_model(&mut self) -> Result<Vec<Model>, SolverError> {
        self.last_assumptions = None;
        let start = fly::timing::start();
        let fo_model = self.get_fo_model(TimeType::GetModel, start)?;
        Ok(fo_model.into_trace(&self.signature, self.n_states))
    }

    /// Construct an assertion that enforces `univ` has max cardinality `card`.
    /// The assertion is guarded by an indicator and this indicator is the
    /// returned `Term`.
    fn set_universe_card(&mut self, univ: &str, card: usize) -> Term {
        assert!(card > 0);
        self.proc
            .comment_with(|| format!("setting {univ} to cardinality {card}"));
        let ind = self.get_indicator(&format!("{univ}_card_{card}"));

        let univ: Sort = Sort::uninterpreted(univ);

        // (exists ((x0 univ) ... (xn univ)) (forall ((x univ)) (or (= x x1) ... (= x xn))))
        let univ_card =
            Term::exists(
                (0..card).map(|n| Binder {
                    name: format!("x{n}"),
                    sort: univ.clone(),
                }),
                Term::forall(
                    [Binder {
                        name: "x".to_string(),
                        sort: univ.clone(),
                    }],
                    Term::or((0..card).map(|n| {
                        Term::equals(Term::Id("x".to_string()), Term::Id(format!("x{n}")))
                    })),
                ),
            );
        self.assert(&Term::implies(ind.clone(), univ_card));
        ind
    }

    /// Find the minimum cardinality for a specific universe. As a side effect,
    /// adds an indicator to `assumptions` that enforces this cardinality.
    fn minimize_card(
        &mut self,
        max_card: usize,
        assumptions: &mut Vec<Term>,
        univ: &str,
    ) -> Result<usize, SolverError> {
        // The loop attempts to go from max_card-1 down. Thus it will go from
        // sat to unsat at some point, and we want the cardinality and indicator
        // for the last sat. If it starts out unsat, then no further
        // minimization is possible and we don't need to change `assumptions`.
        let mut prev_ind = None;
        for new_card in (1..max_card).rev() {
            let ind = self.set_universe_card(univ, new_card);
            let r = self
                .proc
                .check_sat_assuming(&assumptions.iter().map(sexp::term).collect::<Vec<_>>())?;
            match r {
                SatResp::Sat => (),
                SatResp::Unsat => {
                    // The previous cardinality was the minimum one.
                    if let Some(ind) = prev_ind {
                        self.proc.comment_with(|| format!("assuming {ind} for now"));
                        assumptions.push(ind);
                    }
                    return Ok(new_card + 1);
                }
                SatResp::Unknown(msg) => {
                    return Err(SolverError::CouldNotMinimize(msg));
                }
            }
            prev_ind = Some(ind);
        }
        // if we never got unsat, then 1 is a valid cardinality (and we don't
        // check if 0 would work)
        return Ok(1);
    }

    /// Try to set all universes to have cardinality (at most) card.
    ///
    /// Returns true on success and adds indicators to `indicators` to enforce
    /// the cardinality `card`.
    fn is_valid_max_card(
        &mut self,
        card: usize,
        indicators: &mut Vec<Term>,
    ) -> Result<bool, SolverError> {
        let mut new_indicators = vec![];
        let sorts = self.signature.sorts.clone();
        for sort in &sorts {
            let ind = self.set_universe_card(sort, card);
            new_indicators.push(ind);
        }
        let assumptions = indicators
            .iter()
            .chain(new_indicators.iter())
            .map(sexp::term)
            .collect::<Vec<_>>();
        let r = self.proc.check_sat_assuming(&assumptions)?;
        match r {
            SatResp::Sat => {
                indicators.extend(new_indicators);
                Ok(true)
            }
            SatResp::Unsat => Ok(false),
            SatResp::Unknown(msg) => Err(SolverError::CouldNotMinimize(msg)),
        }
    }

    /// Search for the minimum cardinality `card` such that there is a model
    /// where all universes are at `card` in size.
    ///
    /// Returns the cardinality `card` and adds indicators to enforce this cardinality to `indicators`.
    fn get_min_max_card(&mut self, indicators: &mut Vec<Term>) -> Result<usize, SolverError> {
        if self.signature.sorts.is_empty() {
            return Ok(0);
        }
        for card in 1..100 {
            if self.is_valid_max_card(card, indicators)? {
                return Ok(card);
            }
        }
        panic!("max cardinality got too high");
    }

    /// Get a minimized model after a call to `check_sat` returns `Sat`.
    ///
    /// Will fail in some unexpected way if the solver has not just replied
    /// `sat`.
    ///
    /// The minimization process makes several more sat queries, which add
    /// constraints on universe cardinalities. The algorithm first finds the
    /// smallest maximum cardinality across all universes that is still sat.
    /// starting at 1, then enforces that for the remainder of the process.
    /// Then, it greedily minimizes each sort in the signature in turn; at each
    /// step it enforces that all the previous sorts have their minimized
    /// cardinalities. Finally, it returns the model with these cardinality
    /// constraints in place.
    pub fn get_minimal_model(&mut self) -> Result<Vec<Model>, SolverError> {
        if self.backend.returns_minimal() {
            return self.get_model();
        }

        let start = std::time::Instant::now();
        let assumptions = self.last_assumptions.take();
        // initially, assume anything used by the last check_sat call
        let mut indicators = assumptions
            .unwrap_or_default()
            .into_iter()
            .map(|(ind, val)| if val { ind } else { Term::negate(ind) })
            .sorted()
            .collect::<Vec<_>>();
        let max_card = self.get_min_max_card(&mut indicators)?;
        // Minimize each sort in turn, greedily in the order of the signature.
        //
        // (This does not produce a global optimum but the search process is
        // simple to implement.)
        {
            let sorts = self.signature.sorts.clone();
            for sort in sorts {
                self.minimize_card(max_card, &mut indicators, &sort)?;
            }
        }
        let model = self.get_fo_model(TimeType::GetMinimalModel, start)?;
        Ok(model.into_trace(&self.signature, self.n_states))
    }

    /// Returns an unsat core as a set of indicator variables (a subset of the
    /// assumptions passed to `check_sat`).
    pub fn get_unsat_core(&mut self) -> Result<HashMap<Term, bool>, SolverError> {
        let indicators = self.proc.get_unsat_assumptions()?;
        let mut assumptions = HashMap::new();
        for t in indicators {
            // TODO: this is very ugly, replace with Sexp destructor methods
            // (even at the expense of precise error reporting)
            match t {
                Sexp::Atom(Atom::S(s)) => {
                    assumptions.insert(Term::Id(s), true);
                }
                Sexp::List(ss) => {
                    // should be (not i)
                    assert!(
                        ss.len() == 2 && (ss[0] == atom_s("not") || ss[0] == atom_s("!")),
                        "malformed unsat assumption {} in solver response",
                        &Sexp::List(ss),
                    );
                    if let Sexp::Atom(Atom::S(s)) = ss[1].clone() {
                        assumptions.insert(Term::Id(s), false);
                    } else {
                        panic!("non-string unsat assumption {} in solver response", &ss[1]);
                    }
                }
                Sexp::Comment(_) => continue,
                _ => panic!("non-string unsat assumption {} in solver response", &t),
            }
        }
        self.last_assumptions = None;
        Ok(assumptions)
    }

    /// After a call to check-sat returns unsat, get a minimized unsat core: a
    /// minimal set of indicator variables which still result in unsat.
    ///
    /// Not yet implemented so there is no algorithm here.
    pub fn get_minimal_unsat_core(&mut self) -> Result<HashMap<Term, bool>, SolverError> {
        eprintln!("unsat code minimization is not yet implemented");
        self.get_unsat_core()
    }

    /// Call the SMT push command to create a new assertion stack frame.
    pub fn push(&mut self) {
        self.last_assumptions = None;
        self.proc.send(&app("push", []));
    }

    /// Call the SMT pop command to rewind the solver to the last pop.
    pub fn pop(&mut self) {
        self.last_assumptions = None;
        self.proc.send(&app("pop", []));
    }
}

impl FOModel {
    fn into_trace(self, signature: &Signature, n_states: usize) -> Vec<Model> {
        let universe: Universe = signature
            .sorts
            .iter()
            .map(|s| {
                *self
                    .universe
                    .get(s)
                    .unwrap_or_else(|| panic!("unknown sort {s} in model"))
            })
            .collect();
        let mut states: Vec<Model> = vec![];
        for n in 0..n_states {
            let interp = signature
                .relations
                .iter()
                .map(|r| {
                    let n = if r.mutable { n } else { 0 };
                    let relation = format!("{r}{primes}", r = &r.name, primes = "'".repeat(n));
                    self.interp[&relation].clone()
                })
                .collect::<Vec<_>>();
            let model = Model::new(signature, &universe, interp);
            states.push(model);
        }
        states
    }
}
