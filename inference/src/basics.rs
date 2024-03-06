// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

use itertools;
use itertools::Itertools;
use std::{
    collections::{BTreeMap, HashMap, HashSet},
    hash::Hash,
    sync::{Arc, Mutex},
    thread,
};

use crate::qalpha::{fixpoint::Strategy, quant::QuantifierConfig};
use fly::syntax::BinOp;
use fly::syntax::Term::*;
use fly::syntax::*;
use fly::term::{prime::clear_next, prime::Next};
use fly::{ouritertools::OurItertools, semantics::Model, transitions::*};
use smtlib::proc::{SatResp, SolverError};
use solver::{
    basics::{BasicCanceler, BasicSolver, BasicSolverResp, MultiCanceler, QueryConf},
    conf::SolverConf,
};

pub enum CexResult<K: Eq + Hash> {
    Cex(Vec<Model>),
    UnsatCore(HashSet<K>),
    Canceled,
    Unknown(String),
}

impl<K: Eq + Hash> CexResult<K> {
    /// Convert into an [`Option`], which either contains a counterexample or [`None`].
    pub fn into_option(self) -> Option<Vec<Model>> {
        match self {
            CexResult::Cex(models) => Some(models),
            CexResult::UnsatCore(_) => None,
            _ => panic!("cex result is neither sat or unsat"),
        }
    }

    /// Return `true` if the [`CexResult`] contains a counterexample, or `false` if it contains an UNSAT-core.
    /// If the query is either `Canceled` or `Unknown`, this panics.
    pub fn is_cex(&self) -> bool {
        match self {
            CexResult::Cex(_) => true,
            CexResult::UnsatCore(_) => false,
            _ => panic!("cex result is neither sat or unsat"),
        }
    }
}

/// Manages a subset of formulas based on the counter-models they do not satisfy.
///
/// This is used to find a small UNSAT-core of some SMT query by iteratively adding negative
/// counterexamples to be blocked and growing the core in a minimal way to block all of them.
/// If `minimal` is set, the core is guaranteed to be minimal in the local sense that
/// no formula can be dropped from it while still blocking all the previous counterexamples.
struct Core<H: OrderedTerms> {
    formulas: H,
    participants: BTreeMap<H::Key, Term>,
    counter_models: Vec<Model>,
    to_participants: HashMap<usize, HashSet<H::Key>>,
    to_counter_models: HashMap<H::Key, HashSet<usize>>,
    minimal: bool,
}

impl<H: OrderedTerms> Core<H> {
    /// Create a new core from the given formulas. `participants` specifies which formulas
    /// to intialize the core with, and `minimal` determines whether to minimize the core
    /// when adding future participants.
    fn new(formulas: H, participants: BTreeMap<H::Key, Term>, minimal: bool) -> Self {
        Core {
            formulas,
            participants,
            counter_models: vec![],
            to_participants: HashMap::new(),
            to_counter_models: HashMap::new(),
            minimal,
        }
    }

    /// Update the core so that it blocks the given model and all previously blocked models.
    /// This involves adding a blocking formula to the core and potentially minimizing it.
    /// We assume that the new model satisfies the current core (i.e. is not blocked by it).
    ///
    /// Returns `true` if the model has been successfully blocked or `false` if it couldn't be
    /// blocked because it satisfied all candidate formulas.
    fn add_counter_model(&mut self, counter_model: Model) -> bool {
        match self.formulas.first_unsat(&counter_model) {
            Some((key, term)) => {
                let model_idx = self.counter_models.len();
                self.to_participants.insert(model_idx, HashSet::new());
                let mut counter_models: HashSet<usize> = (0..self.counter_models.len())
                    .filter(|i| self.counter_models[*i].eval(&term) == 0)
                    .collect();
                counter_models.insert(model_idx);
                self.counter_models.push(counter_model);
                for m_idx in &counter_models {
                    self.to_participants.get_mut(m_idx).unwrap().insert(key);
                }
                self.to_counter_models.insert(key, counter_models);
                self.participants.insert(key, term);

                if self.minimal {
                    while self.reduce() {}

                    assert!(self.participants.keys().all(|key| {
                        self.to_counter_models[key]
                            .iter()
                            .any(|m_idx| self.to_participants[m_idx] == HashSet::from([*key]))
                    }));
                }

                true
            }
            None => false,
        }
    }

    /// Reduces the size of the core by one if possible, by trying to find a formula such that any model it blocks
    /// is also blocked by a different formula in the core. Formulas with a higher index are prioritized for removal.
    ///
    /// Returns `true` if the core has been reduced, or `false` otherwise.
    fn reduce(&mut self) -> bool {
        if let Some(key) = self.participants.keys().cloned().rev().find(|p_idx| {
            self.to_counter_models[p_idx]
                .iter()
                .all(|m_idx| self.to_participants[m_idx].len() > 1)
        }) {
            assert!(self.participants.remove(&key).is_some());
            for m_idx in self.to_counter_models.remove(&key).unwrap() {
                assert!(self.to_participants.get_mut(&m_idx).unwrap().remove(&key));
            }

            true
        } else {
            false
        }
    }

    /// Convert the current core to a set of assumption for use by the solver.
    /// This yields a map which maps each participant index to its [`Term`] and Boolean assumption,
    /// in this case always `true`.
    fn to_assumptions(&self) -> HashMap<usize, (Term, bool)> {
        self.present()
            .enumerate()
            .map(|(i, (_, t))| (i, (t.clone(), true)))
            .collect()
    }

    /// Convert a core returned by the solver to one of `H::Key` elements.
    fn convert_core<O>(&self, core: &HashSet<usize>) -> O
    where
        O: FromIterator<H::Key>,
    {
        self.present()
            .enumerate()
            .filter_map(|(i, (k, _))| if core.contains(&i) { Some(*k) } else { None })
            .collect()
    }

    /// Get the keys and terms currently present in the core.
    fn present(&self) -> impl Iterator<Item = (&H::Key, &Term)> {
        let permanent = self.formulas.permanent();
        let seen: HashSet<H::Key> = permanent.iter().map(|(k, _)| **k).collect();
        permanent
            .into_iter()
            .chain(
                self.participants
                    .iter()
                    .filter(move |(k, _)| !seen.contains(k)),
            )
            .unique()
    }
}

#[derive(Debug, Clone)]
pub enum TermOrModel {
    Model(Model),
    Term(Term),
}

pub enum CexOrCore {
    Cex((Term, Model)),
    Core(HashMap<Term, bool>),
}

pub trait OrderedTerms: Copy + Send + Sync {
    type Key: Ord + Hash + Eq + Clone + Copy + Send + Sync;

    fn permanent(&self) -> Vec<(&Self::Key, &Term)>;

    fn first_unsat(self, model: &Model) -> Option<(Self::Key, Term)>;

    fn all_terms(self) -> BTreeMap<Self::Key, Term>;
}

impl<V: AsRef<[Term]> + Copy + Send + Sync> OrderedTerms for V {
    type Key = usize;

    fn permanent(&self) -> Vec<(&Self::Key, &Term)> {
        vec![]
    }

    fn first_unsat(self, model: &Model) -> Option<(Self::Key, Term)> {
        self.as_ref().iter().enumerate().find_map(|(i, t)| {
            if model.eval(t) == 0 {
                Some((i, t.clone()))
            } else {
                None
            }
        })
    }

    fn all_terms(self) -> BTreeMap<Self::Key, Term> {
        self.as_ref().iter().cloned().enumerate().collect()
    }
}

/// A first-order module is represented using first-order formulas,
/// namely single-vocabulary axioms, initial assertions and safety assertions,
/// and double-vocabulary transition assertions.
/// `disj` denotes whether to split the transitions disjunctively, if possible.
pub struct FOModule {
    signature: Arc<Signature>,
    pub module: DestructuredModule,
    disj: bool,
    smt_tactic: SmtTactic,
}

impl FOModule {
    pub fn new(m: &Module, disj: bool, smt_tactic: SmtTactic) -> Self {
        FOModule {
            signature: m.signature.clone(),
            module: extract(m).unwrap(),
            disj,
            smt_tactic,
        }
    }

    fn disj_trans(&self) -> Vec<Vec<&Term>> {
        if self.disj {
            self.module
                .transitions
                .iter()
                .map(|t| match t {
                    Term::NAryOp(NOp::Or, args) => args.iter().collect_vec(),
                    _ => vec![t],
                })
                .multi_cartesian_product_fixed()
                .collect_vec()
        } else {
            vec![self.module.transitions.iter().collect_vec()]
        }
    }

    pub fn init_cex<B: BasicSolver>(&self, solver: &B, t: &Term) -> Option<Model> {
        self.implication_cex(solver, &self.module.inits, t, None, false)
            .into_option()
            .map(|mut models| {
                assert_eq!(models.len(), 1);
                models.pop().unwrap()
            })
    }

    pub fn trans_cex<H, B, C>(
        &self,
        solver: &B,
        hyp: H,
        t: &Term,
        with_safety: bool,
        cancelers: Option<MultiCanceler<MultiCanceler<C>>>,
        save_tee: bool,
    ) -> CexResult<H::Key>
    where
        H: OrderedTerms,
        C: BasicCanceler,
        B: BasicSolver<Canceler = C>,
    {
        let transitions = self.disj_trans();
        let local_cancelers: MultiCanceler<C> = MultiCanceler::new();

        if cancelers
            .as_ref()
            .is_some_and(|c| !c.add_canceler(local_cancelers.clone()))
        {
            return CexResult::Canceled;
        }

        let query_conf = QueryConf {
            sig: &self.signature,
            n_states: 2,
            cancelers: Some(local_cancelers.clone()),
            minimal_model: true,
            save_tee,
        };
        let next = Next::new(&self.signature);
        let mut assertions = self.module.axioms.clone();
        assertions.extend(self.module.axioms.iter().map(|a| next.prime(a)));
        if with_safety {
            assertions.extend(self.module.proofs.iter().map(|p| p.safety.x.clone()))
        }
        assertions.push(Term::not(next.prime(t)));

        let cex_results: Vec<CexResult<H::Key>> = thread::scope(|s| {
            transitions
                .into_iter()
                .map(|transition| {
                    s.spawn(|| {
                        let mut core = match self.smt_tactic {
                            SmtTactic::Full => Core::new(hyp, hyp.all_terms(), false),
                            SmtTactic::Gradual => Core::new(hyp, BTreeMap::new(), false),
                            SmtTactic::Minimal => Core::new(hyp, BTreeMap::new(), true),
                        };

                        let mut local_assertions = assertions.clone();
                        local_assertions.extend(transition.into_iter().cloned());
                        loop {
                            let assumptions = core.to_assumptions();
                            match solver.check_sat(&query_conf, &local_assertions, &assumptions) {
                                Ok(BasicSolverResp::Sat(models)) => {
                                    if !core.add_counter_model(models[0].clone()) {
                                        // A counter-example to the transition was found, no need to search further.
                                        local_cancelers.cancel();
                                        return CexResult::Cex(models);
                                    }
                                }
                                Ok(BasicSolverResp::Unsat(c)) => {
                                    return CexResult::UnsatCore(core.convert_core(&c))
                                }
                                Ok(BasicSolverResp::Unknown(reason)) => {
                                    return CexResult::Unknown(reason)
                                }
                                Err(SolverError::Killed) => return CexResult::Canceled,
                                Err(e) => panic!("error in solver: {e}"),
                            }
                        }
                    })
                })
                .collect_vec()
                .into_iter()
                .map(|h| h.join().unwrap())
                .collect_vec()
        });

        // Check whether any counterexample has been found
        if cex_results
            .iter()
            .any(|res| matches!(res, CexResult::Cex(_)))
        {
            return cex_results
                .into_iter()
                .find(|res| matches!(res, CexResult::Cex(_)))
                .unwrap();
        }

        // Check whether any query has been canceled
        if cex_results
            .iter()
            .any(|res| matches!(res, CexResult::Canceled))
        {
            return CexResult::Canceled;
        }

        // Check whether any query has returned 'unknown'
        if cex_results
            .iter()
            .any(|res| matches!(res, CexResult::Unknown(_)))
        {
            return CexResult::Unknown(
                cex_results
                    .into_iter()
                    .filter_map(|res| match res {
                        CexResult::Unknown(reason) => Some(reason),
                        _ => None,
                    })
                    .join("\n"),
            );
        }

        // Otherwise, all results must be UNSAT-cores
        let unsat_core = cex_results
            .into_iter()
            .flat_map(|res| match res {
                CexResult::UnsatCore(core) => core,
                _ => unreachable!(),
            })
            .collect();

        CexResult::UnsatCore(unsat_core)
    }

    pub fn implication_cex<H, B, C>(
        &self,
        solver: &B,
        hyp: H,
        t: &Term,
        cancelers: Option<MultiCanceler<MultiCanceler<C>>>,
        save_tee: bool,
    ) -> CexResult<H::Key>
    where
        H: OrderedTerms,
        C: BasicCanceler,
        B: BasicSolver<Canceler = C>,
    {
        let local_cancelers: MultiCanceler<C> = MultiCanceler::new();
        if cancelers
            .as_ref()
            .is_some_and(|c| !c.add_canceler(local_cancelers.clone()))
        {
            return CexResult::Canceled;
        }

        let mut core = match self.smt_tactic {
            SmtTactic::Full => Core::new(hyp, hyp.all_terms(), false),
            SmtTactic::Gradual => Core::new(hyp, BTreeMap::new(), false),
            SmtTactic::Minimal => Core::new(hyp, BTreeMap::new(), true),
        };

        let query_conf = QueryConf {
            sig: &self.signature,
            n_states: 1,
            cancelers: Some(local_cancelers),
            minimal_model: true,
            save_tee,
        };
        let mut assertions = self.module.axioms.clone();
        assertions.push(Term::not(t));
        loop {
            match solver.check_sat(&query_conf, &assertions, &core.to_assumptions()) {
                Ok(BasicSolverResp::Sat(models)) => {
                    if !core.add_counter_model(models[0].clone()) {
                        return CexResult::Cex(models);
                    }
                }
                Ok(BasicSolverResp::Unsat(c)) => {
                    return CexResult::UnsatCore(core.convert_core(&c))
                }
                Ok(BasicSolverResp::Unknown(reason)) => return CexResult::Unknown(reason),
                Err(SolverError::Killed) => return CexResult::Canceled,
                Err(e) => panic!("error in solver: {e}"),
            }
        }
    }

    pub fn simulate_from<B, C>(&self, solver: &B, state: &Model, width: usize) -> Vec<Model>
    where
        C: BasicCanceler,
        B: BasicSolver<Canceler = C>,
    {
        let transitions = self.disj_trans();
        let cancelers = MultiCanceler::new();
        let empty_assumptions = HashMap::new();
        let next = Next::new(&self.signature);
        let query_conf = QueryConf {
            sig: &self.signature,
            n_states: 2,
            cancelers: Some(cancelers.clone()),
            minimal_model: false,
            save_tee: false,
        };

        let state_term = state.to_term();
        let samples = Mutex::new(vec![]);
        thread::scope(|s| {
            for transition in &transitions {
                s.spawn(|| {
                    let mut assertions = vec![state_term.clone()];
                    assertions.extend(self.module.axioms.iter().map(|a| next.prime(a)));
                    assertions.extend(transition.iter().copied().cloned());

                    'this_loop: loop {
                        let resp = solver.check_sat(&query_conf, &assertions, &empty_assumptions);
                        match resp {
                            Ok(BasicSolverResp::Sat(mut models)) => {
                                assert_eq!(models.len(), 2);
                                let new_sample = models.pop().unwrap();
                                assertions.push(Term::negate(next.prime(&new_sample.to_term())));
                                {
                                    let mut samples_lock = samples.lock().unwrap();
                                    if samples_lock.len() < width {
                                        samples_lock.push(new_sample);
                                    }
                                    if samples_lock.len() >= width {
                                        cancelers.cancel();
                                        break 'this_loop;
                                    }
                                }
                            }
                            _ => break 'this_loop,
                        }
                    }
                });
            }
        });

        samples.into_inner().unwrap()
    }

    pub fn get_pred(&self, conf: &SolverConf, hyp: &[Term], t: &TermOrModel) -> CexOrCore {
        let as_term: Term = match t {
            TermOrModel::Term(t) => t.clone(),
            TermOrModel::Model(m) => m.to_diagram(),
        };
        assert_eq!(self.module.transitions.len(), 1);
        if let NAryOp(NOp::Or, _) = self.module.transitions[0].clone() {
        } else {
            panic!("malformed transitions!")
        }
        let separate_trans = self
            .module
            .transitions
            .iter()
            .flat_map(|t| match t {
                NAryOp(NOp::Or, args) => args.iter().collect_vec(),
                _ => vec![t],
            })
            .collect_vec();

        let mut core = HashMap::new();
        for trans in separate_trans {
            let mut solver = conf.solver(&self.signature, 2);
            for a in self
                .module
                .axioms
                .iter()
                .chain(hyp.iter())
                .chain(vec![trans])
            {
                solver.assert(a);
            }
            for a in self.module.axioms.iter() {
                solver.assert(&Next::new(&self.signature).prime(a));
            }
            let mut indicators = HashMap::new();
            let mut ind_to_term = HashMap::new();
            let mut new_terms = vec![];
            if let TermOrModel::Term(term) = t {
                // println!("got term, asserting with no core");
                solver.assert(&Next::new(&self.signature).prime(term));
            } else if let Quantified {
                quantifier: Quantifier::Exists,
                body,
                binders,
            } = Next::new(&self.signature).prime(&as_term)
            {
                if let NAryOp(NOp::And, terms) = *body {
                    for (i, clause) in terms.into_iter().enumerate() {
                        let ind = solver.get_indicator(&i.to_string());
                        new_terms.push(Term::BinOp(
                            BinOp::Equals,
                            Box::new(ind.clone()),
                            Box::new(clause.clone()),
                        ));
                        // println!("adding clause {}", &clause);
                        indicators.insert(ind.clone(), true);
                        ind_to_term.insert(ind, clause);
                    }
                    let new_term = Quantified {
                        quantifier: Quantifier::Exists,
                        body: Box::new(NAryOp(NOp::And, new_terms)),
                        binders,
                    };
                    solver.assert(&new_term);
                } else {
                    panic!("bad term for pred!");
                }
            } else {
                panic!("bad term for pred!");
            }

            let resp = solver.check_sat(indicators).expect("error in solver");
            match resp {
                SatResp::Sat => {
                    let states = solver.get_minimal_model().expect("error in solver");
                    assert_eq!(states.len(), 2);
                    // println!("trans: {}", &trans);
                    return CexOrCore::Cex((trans.clone(), states[0].clone()));
                }
                SatResp::Unsat => {
                    // println!("adding group");
                    for (ind, b) in solver
                        .get_unsat_core()
                        .expect("could not get unsat assumptions")
                    {
                        assert!(b, "got false in core");
                        // println!("adding to core: {}", clear_next(ind_to_term[&ind].clone()));
                        core.insert(clear_next(ind_to_term[&ind].clone()), b);
                    }
                }
                SatResp::Unknown(error) => panic!("{}", error),
            }
            solver.save_tee();
        }
        return CexOrCore::Core(core);
    }

    pub fn implies_cex(&self, conf: &SolverConf, hyp: &[Term], t: &Term) -> Option<Model> {
        let mut solver = conf.solver(&self.signature, 1);
        for a in hyp {
            solver.assert(a);
        }
        solver.assert(&Term::negate(t.clone()));

        let resp = solver.check_sat(HashMap::new()).expect("error in solver");
        solver.save_tee();
        match resp {
            SatResp::Sat => {
                let states = solver.get_minimal_model().expect("error in solver");
                assert_eq!(states.len(), 1);
                return Some(states[0].clone());
            }
            SatResp::Unsat => None,
            SatResp::Unknown(_) => panic!(),
        }
    }

    pub fn safe_implication_cex<H, B, C>(
        &self,
        solver: &B,
        hyp: H,
        cancelers: Option<MultiCanceler<MultiCanceler<C>>>,
    ) -> CexResult<H::Key>
    where
        H: OrderedTerms,
        C: BasicCanceler,
        B: BasicSolver<Canceler = C>,
    {
        let mut core = HashSet::new();
        for s in self.module.proofs.iter() {
            match self.implication_cex(solver, hyp, &s.safety.x, cancelers.clone(), false) {
                CexResult::UnsatCore(new_core) => core.extend(new_core),
                res => return res,
            }
        }

        CexResult::UnsatCore(core)
    }

    pub fn trans_safe_cex<H, C, B>(
        &self,
        solver: &B,
        hyp: H,
        cancelers: Option<MultiCanceler<MultiCanceler<C>>>,
    ) -> CexResult<H::Key>
    where
        H: OrderedTerms,
        C: BasicCanceler,
        B: BasicSolver<Canceler = C>,
    {
        let mut core = HashSet::new();
        for s in self.module.proofs.iter() {
            match self.trans_cex(solver, hyp, &s.safety.x, true, cancelers.clone(), false) {
                CexResult::UnsatCore(new_core) => core.extend(new_core),
                res => return res,
            }
        }

        CexResult::UnsatCore(core)
    }

    pub fn safe_cex(&self, conf: &SolverConf, hyp: &[Term]) -> Option<Model> {
        for s in self.module.proofs.iter() {
            if let Some(model) = self.implies_cex(conf, hyp, &s.safety.x) {
                return Some(model);
            }
        }

        None
    }
}

pub enum SmtTactic {
    Full,
    Gradual,
    Minimal,
}

impl Default for SmtTactic {
    fn default() -> Self {
        Self::Gradual
    }
}

impl From<&String> for SmtTactic {
    fn from(value: &String) -> Self {
        match value.as_str() {
            "gradual" => Self::Gradual,
            "minimal" => Self::Minimal,
            "full" => Self::Full,
            _ => panic!("invalid choice of SMT technique!"),
        }
    }
}

pub enum QfBody {
    Cnf,
    PDnf,
    Dnf,
}

impl Default for QfBody {
    fn default() -> Self {
        Self::PDnf
    }
}

impl From<&String> for QfBody {
    fn from(value: &String) -> Self {
        match value.as_str() {
            "cnf" => QfBody::Cnf,
            "dnf" => QfBody::Dnf,
            "pdnf" => QfBody::PDnf,
            _ => panic!("invalid choice of quantifier-free body!"),
        }
    }
}

pub struct QuantifierFreeConfig {
    pub qf_body: QfBody,
    pub clause_size: Option<usize>,
    pub cubes: Option<usize>,
    pub nesting: Option<usize>,
}

#[derive(Clone)]
pub struct SimulationConfig {
    pub universe: Vec<usize>,
    pub sum: Option<usize>,
    pub depth: Option<usize>,
    pub guided: bool,
    pub dfs: bool,
}

pub struct QalphaConfig {
    pub fname: String,
    pub fo: FOModule,

    pub quant_cfg: Arc<QuantifierConfig>,

    pub qf_cfg: QuantifierFreeConfig,

    pub sim: SimulationConfig,

    pub strategy: Strategy,

    pub until_safe: bool,

    pub seeds: usize,

    pub baseline: bool,
}
