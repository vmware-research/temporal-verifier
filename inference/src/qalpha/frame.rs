// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Implement simple components, lemma domains and data structures for use in inference.

use fly::ouritertools::OurItertools;
use itertools::Itertools;
use solver::basics::{BasicCanceler, BasicSolver, MultiCanceler};
use std::fmt::{Debug, Display};
use std::hash::Hash;
use std::sync::{Arc, Mutex, RwLock};
use std::time::{Duration, Instant};

use fly::semantics::Model;
use fly::syntax::{Module, Signature, Term};

use bounded::simulator::{MultiSimulator, SatSimulator};

use crate::{
    basics::{CexResult, FOModule, SimulationConfig},
    hashmap::{HashMap, HashSet},
    parallel::{parallelism, ParallelWorker, Tasks},
    qalpha::{
        fixpoint::{sample_priority, SamplePriority},
        language::BoundedLanguage,
        lemmas::{LemmaKey, WeakenLemmaSet},
    },
};

macro_rules! timed {
    ($blk:block) => {{
        let start = Instant::now();
        $blk
        start.elapsed()
    }};
}

/// Compute the names of [`Term::Id`]'s present in the given term.
///
/// Supports only quantifier-free terms.
pub fn ids(term: &Term) -> HashSet<String> {
    match term {
        Term::Id(name) => HashSet::from_iter([name.clone()]),
        Term::App(_, _, vt) => vt.iter().flat_map(ids).collect(),
        Term::UnaryOp(_, t) => ids(t),
        Term::BinOp(_, t1, t2) => [t1, t2].iter().flat_map(|t| ids(t)).collect(),
        Term::NAryOp(_, vt) => vt.iter().flat_map(ids).collect(),
        Term::Ite { cond, then, else_ } => {
            [cond, then, else_].iter().flat_map(|t| ids(t)).collect()
        }
        _ => HashSet::default(),
    }
}

#[derive(PartialEq, Eq, Debug)]
enum Blocked<I: Eq + Hash + Clone> {
    Initial,
    Consequence(HashSet<I>),
    Transition(HashSet<I>),
}

impl<I: Eq + Hash + Clone> Blocked<I> {
    fn constituents(&self) -> HashSet<I> {
        match self {
            Blocked::Initial => HashSet::default(),
            Blocked::Consequence(core) | Blocked::Transition(core) => core.clone(),
        }
    }

    fn contains(&self, id: &I) -> bool {
        match self {
            Blocked::Initial => false,
            Blocked::Consequence(core) | Blocked::Transition(core) => core.contains(id),
        }
    }
}

struct LemmaManager<I: Hash + Eq + Copy> {
    /// The set of lemmas inductively implied by the frame, mapped to the unsat-cores implying them.
    blocked_to_core: HashMap<I, Blocked<I>>,
    /// Mapping from each lemma to the lemmas whose inductiveness proof they paricipate in.
    core_to_blocked: HashMap<I, HashSet<I>>,
    /// A subset of the frame's lemmas which inductively implies the safety assertions.
    safety_core: Option<Blocked<I>>,
}

impl<I: Hash + Eq + Copy> LemmaManager<I> {
    fn new() -> Self {
        Self {
            blocked_to_core: HashMap::default(),
            core_to_blocked: HashMap::default(),
            safety_core: None,
        }
    }

    fn inductively_proven(&self, id: &I) -> bool {
        self.blocked_to_core
            .get(id)
            .is_some_and(|core| matches!(core, Blocked::Transition(_)))
    }

    fn add_blocked(&mut self, id: I, core: Blocked<I>) {
        for core_id in core.constituents() {
            if let Some(hs) = self.core_to_blocked.get_mut(&core_id) {
                hs.insert(id);
            } else {
                self.core_to_blocked
                    .insert(core_id, HashSet::from_iter([id]));
            }
        }
        self.blocked_to_core.insert(id, core);
    }

    fn remove_from_blocked(&mut self, id: &I) {
        let core = self.blocked_to_core.remove(id).unwrap();
        for core_id in &core.constituents() {
            if let Some(b) = self.core_to_blocked.get_mut(core_id) {
                b.remove(id);
                if b.is_empty() {
                    self.core_to_blocked.remove(core_id);
                }
            }
        }
    }

    fn remove_from_cores(&mut self, id: &I) {
        if let Some(blocked) = self.core_to_blocked.remove(id) {
            for blocked_id in &blocked {
                self.remove_from_blocked(blocked_id);
            }
        }
    }

    fn remove(&mut self, id: &I) {
        if self
            .safety_core
            .as_ref()
            .is_some_and(|core| core.contains(id))
        {
            self.safety_core = None;
        }
        if self.blocked_to_core.contains_key(id) {
            self.remove_from_blocked(id);
        }
        if self.core_to_blocked.contains_key(id) {
            self.remove_from_cores(id);
        }
    }

    fn blocked_closure(&self, core: HashSet<I>) -> Option<HashSet<I>> {
        let mut extended_core: HashSet<I> = HashSet::default();
        let mut new_ids: HashSet<I> = core;

        while !new_ids.is_empty() {
            let mut new_new_ids = HashSet::default();
            for id in &new_ids {
                new_new_ids.extend(self.blocked_to_core.get(id)?.constituents());
            }

            extended_core.extend(new_ids);
            new_ids = new_new_ids
                .into_iter()
                .filter(|id| !extended_core.contains(id))
                .collect();
        }

        extended_core.retain(|id| self.inductively_proven(id));

        Some(extended_core)
    }
}

/// A [`InductionFrame`] maintains quantified formulas during invariant inference.
pub struct InductionFrame<'a, L: BoundedLanguage> {
    /// The signature of the module associated with this induction frame.
    signature: Arc<Signature>,
    /// Manages lemmas inductively proven by the frame.
    lemmas: RwLock<LemmaManager<LemmaKey>>,
    /// The mapping from a key to the lemma's position in the ordering.
    key_to_idx: HashMap<LemmaKey, usize>,
    /// The lemmas in the frame, maintained in a way that supports weakening them.
    pub weaken_lemmas: WeakenLemmaSet<L>,
    /// Whether to extend CTI traces, and how much.
    sim_config: SimulationConfig,
    /// The time of creation of the frame (for logging purposes)
    start_time: Instant,
    /// The simulator to run simulations from reachable states or previous samples
    simulator: MultiSimulator<'a, SatSimulator>,
    /// Whether the search for the invariant is property-directed
    property_directed: bool,
    /// The amount of parallelism to use when launching solvers in parallel
    solver_parallelism: usize,
    /// Statistics about weakening operations
    weaken_stats: OperationStats,
    /// Statistics about retrieving unsafistied formulas in simulations
    get_unsat_stats: Mutex<OperationStats>,
}

#[derive(Clone, serde::Serialize)]
pub struct OperationStats {
    total_duration: Duration,
    total_calls: usize,
    effective_calls: usize,
}

impl Default for OperationStats {
    fn default() -> Self {
        Self {
            total_duration: Duration::ZERO,
            total_calls: 0,
            effective_calls: 0,
        }
    }
}

impl<'a, L: BoundedLanguage> InductionFrame<'a, L> {
    /// Create a new frame using the given configuration.
    pub fn new(
        module: &'a Module,
        signature: Arc<Signature>,
        lang: Arc<L>,
        sim_config: SimulationConfig,
        property_directed: bool,
        parallelism_count: usize,
    ) -> Self {
        assert!(parallelism_count > 0);
        let mut weaken_lemmas = WeakenLemmaSet::new(lang);
        weaken_lemmas.init();
        let key_to_idx = weaken_lemmas.key_to_idx();

        InductionFrame {
            signature,
            lemmas: RwLock::new(LemmaManager::new()),
            key_to_idx,
            weaken_lemmas,
            sim_config,
            start_time: Instant::now(),
            simulator: MultiSimulator::new(module),
            property_directed,
            solver_parallelism: parallelism_count,
            weaken_stats: OperationStats::default(),
            get_unsat_stats: Mutex::new(OperationStats::default()),
        }
    }

    /// Get the term representation of the lemmas in the frame.
    pub fn proof(&self) -> Vec<Term> {
        self.weaken_lemmas.to_terms()
    }

    /// Get a reduced (but equivalent) fixpoint representations.
    pub fn reduced_proof(&self) -> Option<Vec<Term>> {
        let manager = self.lemmas.read().unwrap();
        let mut reduced_proof = vec![];
        let mut indices = vec![];
        for (i, (t, id)) in self.weaken_lemmas.to_terms_keys().enumerate() {
            // Not inductive
            if !manager.blocked_to_core.contains_key(id) {
                return None;
            }
            // Necessary
            if manager.inductively_proven(id) {
                reduced_proof.push(t.clone());
                indices.push(i);
            }
        }

        self.log_info(format!("Reduced lemmas at indices {indices:?}"));

        Some(reduced_proof)
    }

    /// Get a minimized inductive set of lemmas in the frame which inductively implies safety,
    /// provided that `is_safe` has been called and returned `true`.
    pub fn safety_proof(&self) -> Option<Vec<Term>> {
        let manager = self.lemmas.read().unwrap();
        let extended_core: HashSet<LemmaKey> =
            manager.blocked_closure(manager.safety_core.as_ref()?.constituents())?;

        let indices = extended_core
            .iter()
            .map(|key| self.key_to_idx[key])
            .collect_vec();
        let core = extended_core
            .iter()
            .map(|key| self.weaken_lemmas.key_to_term(key))
            .collect_vec();

        self.log_info(format!("Safety lemmas at indices {indices:?}"));

        Some(core)
    }

    /// Add details about the frame to the given [`Display`].
    pub fn add_details<D: Display>(&self, d: D) -> String {
        format!(
            "[{:.2}s] [{} ~> {} | {}] {}",
            self.start_time.elapsed().as_secs_f64(),
            self.weaken_lemmas.len(),
            self.weaken_lemmas.simplified_len(),
            self.weaken_lemmas.max_size,
            d,
        )
    }

    /// Log at `info` level along with details about the frame.
    pub fn log_info<D: Display>(&self, d: D) {
        log::info!("{}", self.add_details(d));
    }

    /// Get an initial state which violates one of the frame's lemmas.
    pub fn init_cex<S: BasicSolver>(&self, fo: &FOModule, solver: &S) -> Vec<Model> {
        self.log_info("Finding initial CTI...");
        let results = ParallelWorker::new(
            &mut self.weaken_lemmas.keys().map(|key| (*key, *key)).collect(),
            |_, key| {
                {
                    let manager = self.lemmas.read().unwrap();
                    if manager.blocked_to_core.contains_key(key) {
                        return (None, vec![], false);
                    }
                }

                let term = self.weaken_lemmas.key_to_term(key);
                let res = fo.init_cex(solver, &term);
                let found = res.is_some();
                return (res, vec![], found);
            },
        )
        .run(self.solver_parallelism);

        let mut ctis = vec![];
        let mut manager = self.lemmas.write().unwrap();
        for (key, out) in results {
            match out {
                Some(model) => ctis.push(model),
                None => {
                    manager.blocked_to_core.insert(key, Blocked::Initial);
                }
            }
        }

        self.log_info(format!("{} initial CTI(s) found.", ctis.len()));

        ctis
    }

    /// Weaken the lemmas in the frame.
    pub fn weaken(&mut self, models: &[Model]) -> bool {
        let mut changed = false;
        let weaken_time = timed!({
            for model in models {
                let (r, a) = self.weaken_lemmas.weaken(model);

                if !r.is_empty() {
                    self.remove_by_keys(&r);
                }
                self.weaken_stats.total_calls += 1;
                if !r.is_empty() || !a.is_empty() {
                    changed |= true;
                    self.weaken_stats.effective_calls += 1;
                }
            }
            if changed {
                self.log_info("Cores updated.");
                self.key_to_idx = self.weaken_lemmas.key_to_idx();
                self.log_info("Indices updated.");
            }
        });
        self.weaken_stats.total_duration += weaken_time;
        self.log_info(format!(
            "Weaken aggregated statistics: total_duration={}s, total_calls={}, effective_calls={}",
            self.weaken_stats.total_duration.as_secs_f64(),
            self.weaken_stats.total_calls,
            self.weaken_stats.effective_calls,
        ));
        changed
    }

    pub fn remove_unsat(&mut self, models: &[Model]) {
        let removed = models
            .iter()
            .flat_map(|model| {
                let rem = self.weaken_lemmas.remove_unsat(model);
                if !rem.is_empty() {
                    self.log_info("Removed unsatisfied.");
                }
                rem
            })
            .collect_vec();
        if !removed.is_empty() {
            self.remove_by_keys(&removed);
            self.log_info("Cores updated.");
            self.key_to_idx = self.weaken_lemmas.key_to_idx();
            self.log_info("Indices updated.");
        }
    }

    fn remove_by_keys(&self, removed: &[LemmaKey]) {
        {
            let mut manager = self.lemmas.write().unwrap();
            for key in removed {
                manager.remove(key);
            }
        }
    }

    /// Extend simulations of traces in order to find a CTI for the current frame.
    pub fn extend<C: BasicCanceler>(
        &self,
        samples: &mut Tasks<SamplePriority, Model>,
        canceler: C,
    ) -> Vec<Model> {
        self.log_info("Simulating traces...");
        // Maps models to whether they violate the current frame, and extends them using the simulator.
        let results = ParallelWorker::new(samples, |(_, t_depth), model| {
            let unsat;
            let unsat_time = timed!({
                unsat = self.weaken_lemmas.unsat(model);
            });

            let depth = if unsat && self.sim_config.guided {
                0
            } else {
                t_depth.depth()
            };

            let cancel = if unsat {
                canceler.cancel();
                true
            } else {
                canceler.is_canceled()
            };

            let new_samples =
                if let Some(p) = sample_priority(&self.sim_config, &model.universe, depth + 1) {
                    let sim = self
                        .simulator
                        .simulate_new(model)
                        .into_iter()
                        .map(|sample| (p.clone(), sample))
                        .collect_vec();
                    log::debug!("Found {} simulated samples from CTI.", sim.len());
                    sim
                } else {
                    vec![]
                };

            ((unsat, unsat_time), new_samples, cancel)
        })
        .run(parallelism());

        let unsat_dur = results.iter().map(|(_, (_, dur))| dur).sum();
        let unsat_calls = results.len();
        let unsat_count = results.iter().filter(|(_, (unsat, _))| *unsat).count();
        {
            let mut unsat_stats = self.get_unsat_stats.lock().unwrap();
            unsat_stats.total_duration += unsat_dur;
            unsat_stats.total_calls += unsat_calls;
            unsat_stats.effective_calls += unsat_count;
        }

        let unsat = results
            .into_iter()
            .filter(|(_, (unsat, _))| *unsat)
            .map(|(m, _)| m)
            .collect_vec();

        self.log_info(format!(
            "{} simulated CTI(s) found (unsat_calls={unsat_calls}, unsat_duration={}ms).",
            unsat_count,
            unsat_dur.as_millis()
        ));

        if !unsat.is_empty() {
            canceler.cancel();
        }

        unsat
    }

    /// Make sure that all lemmas overapproximate initial states and remove the corresponding proofs.
    pub fn finish_initial(&self) {
        let mut manager = self.lemmas.write().unwrap();
        for key in self.weaken_lemmas.keys() {
            assert!(matches!(
                manager.blocked_to_core.get(key),
                Some(Blocked::Initial) | Some(Blocked::Consequence(_))
            ));
        }
        manager.blocked_to_core = HashMap::default();
        manager.core_to_blocked = HashMap::default();
    }

    /// Get an post-state of the frame which violates one of the frame's lemmas.
    pub fn trans_cex<S: BasicSolver>(
        &self,
        fo: &FOModule,
        solver: &S,
        cancelers: MultiCanceler<MultiCanceler<S::Canceler>>,
    ) -> Vec<Model> {
        self.log_info("Finding transition CTI...");
        let mut tasks = if self.property_directed {
            let manager = self.lemmas.read().unwrap();
            manager
                .safety_core
                .as_ref()
                .unwrap()
                .constituents()
                .into_iter()
                .map(|key| ((0_u8, key), key))
                .collect()
        } else {
            self.weaken_lemmas
                .keys()
                .map(|key| ((1_u8, *key), *key))
                .collect()
        };

        let first_sat = Mutex::new(None);
        let start_time = Instant::now();
        // The tasks here are lemmas ID's, and each result is an Option<CexResult>.
        let results = ParallelWorker::new(
            &mut tasks,
            |(check_implied, _), key| {
                let previous: Vec<LemmaKey>;
                {
                    let blocked = self.lemmas.read().unwrap();
                    if let Some(core) = blocked.blocked_to_core.get(key) {
                        return (
                            None,
                            core.constituents()
                                .into_iter()
                                .map(|k| ((1, k), k))
                                .collect(),
                            false,
                        );
                    }
                    previous = blocked.core_to_blocked.keys().cloned().sorted().collect();
                }

                let (mut permanent, try_first): (Vec<_>, Vec<_>) = previous.into_iter().partition(|k| k.is_universal());
                let permanent_imply = permanent.iter().filter(|k| *k < key).cloned().collect();
                let try_first_imply = try_first.iter().filter(|k| *k < key).cloned().collect();

                let idx = self.key_to_idx[key];
                let term = self.weaken_lemmas.key_to_term(key);
                self.log_info(format!("            ({idx}) Checking formula (permanent={}): {term}", permanent.len()));
                // Check if the lemma is implied by the lemmas preceding it.
                if *check_implied == 1 {
                    let query_start = Instant::now();
                    // If that fails, use a semantic implication check.
                    let res = fo.implication_cex(
                        solver,
                        &self.weaken_lemmas.hypotheses(permanent_imply, Some(*key), try_first_imply),
                        &term,
                        Some(cancelers.clone()),
                        false,
                    );
                    if let CexResult::UnsatCore(core) = &res {
                        self.log_info(format!(
                            "{:>8}ms. ({idx}) Semantic implication found UNSAT with {} formulas in core",
                            query_start.elapsed().as_millis(),
                            core.len(),
                        ));
                        let blocking_core = Blocked::Consequence(core.iter().cloned().collect());
                        {
                            let mut manager = self.lemmas.write().unwrap();
                            manager.add_blocked(*key, blocking_core);
                        }
                        let core_tasks = core.iter().cloned().map(|k| ((0, k), k)).collect();
                        return (Some(res), core_tasks, false);
                    }
                }

                // Check if the lemma is inductively implied by the entire frame.
                if !permanent.contains(key) {
                    permanent.push(*key);
                }
                let query_start = Instant::now();
                let res = fo.trans_cex(
                    solver,
                    &self.weaken_lemmas.hypotheses(permanent, None, try_first),
                    &term,
                    false,
                    Some(cancelers.clone()),
                    false,
                );
                match &res {
                    CexResult::Cex(models) => {
                        cancelers.cancel();
                        {
                            let mut first_sat_lock = first_sat.lock().unwrap();
                            if first_sat_lock.is_none() {
                                *first_sat_lock = Some(Instant::now());
                            }
                        }
                        self.log_info(format!(
                            "{:>8}ms. ({idx}) Transition found SAT with universe size {:?}",
                            query_start.elapsed().as_millis(),
                            models[0].universe
                        ));
                        (Some(res), vec![], true)
                    }
                    CexResult::UnsatCore(core) => {
                        self.log_info(format!(
                            "{:>8}ms. ({idx}) Transition found UNSAT with {} formulas in core",
                            query_start.elapsed().as_millis(),
                            core.len()
                        ));
                        let core = Blocked::Transition(core.iter().cloned().collect());
                        let core_tasks = core
                            .constituents()
                            .into_iter()
                            .map(|k| ((0, k), k))
                            .collect();
                        {
                            let mut manager = self.lemmas.write().unwrap();
                            manager.add_blocked(*key, core);
                        }
                        (Some(res), core_tasks, false)
                    }
                    CexResult::Canceled => (Some(res), vec![], true),
                    CexResult::Unknown(reason) => {
                        self.log_info(format!(
                            "{:>8}ms. ({idx}) Transition found unknown: {reason}",
                            query_start.elapsed().as_millis()
                        ));
                        (Some(res), vec![], false)
                    }
                }
            },
        )
        .run(self.solver_parallelism);

        cancelers.cancel();

        let mut ctis = vec![];
        let mut total_sat = 0_usize;
        let mut total_unsat = 0_usize;
        let mut unknown = false;
        for (_, out) in results {
            match out {
                Some(CexResult::Cex(mut models)) => {
                    total_sat += 1;
                    ctis.push(models.pop().unwrap());
                }
                Some(CexResult::UnsatCore(_)) => {
                    total_unsat += 1;
                }
                Some(CexResult::Unknown(_)) => {
                    unknown = true;
                }
                _ => (),
            }
        }

        if ctis.is_empty() && unknown {
            panic!("SMT queries got 'unknown' and no SAT results.")
        }

        self.log_info(format!(
            "    SMT STATS: total_time={:.5}s, until_sat={:.5}s, sat_found={}, unsat_found={}",
            (Instant::now() - start_time).as_secs_f64(),
            (first_sat.into_inner().unwrap().unwrap_or(start_time) - start_time).as_secs_f64(),
            total_sat,
            total_unsat,
        ));
        self.log_info(format!("{} transition CTI(s) found.", ctis.len()));

        ctis
    }

    /// Return whether the current frame inductively implies the safety assertions
    /// of the given module.
    pub fn is_safe<S: BasicSolver>(
        &self,
        fo: &FOModule,
        solver: &S,
        cancelers: Option<MultiCanceler<MultiCanceler<S::Canceler>>>,
    ) -> Option<bool> {
        let mut manager = self.lemmas.write().unwrap();
        if manager.safety_core.is_some() {
            return Some(true);
        }
        let permanent = manager.blocked_to_core.keys().cloned().sorted().collect();

        let start_time = Instant::now();
        let hyp = self.weaken_lemmas.hypotheses(permanent, None, vec![]);
        match fo.safe_implication_cex(solver, &hyp, cancelers.clone()) {
            CexResult::UnsatCore(core) => {
                self.log_info(format!(
                    "{:>8}ms. Safety implied with {} formulas in core",
                    start_time.elapsed().as_millis(),
                    core.len()
                ));
                manager.safety_core = Some(Blocked::Consequence(HashSet::from_iter(core)));
                return Some(true);
            }
            CexResult::Canceled => {
                self.log_info(format!(
                    "{:>8}ms. Safety implication check canceled",
                    start_time.elapsed().as_millis()
                ));
                return None;
            }
            _ => (),
        }

        match fo.trans_safe_cex(solver, &hyp, cancelers) {
            CexResult::Cex(_) => {
                self.log_info(format!(
                    "{:>8}ms. Safety violated",
                    start_time.elapsed().as_millis()
                ));
                Some(false)
            }
            CexResult::UnsatCore(core) => {
                self.log_info(format!(
                    "{:>8}ms. Safety proven using transition with {} formulas in core",
                    start_time.elapsed().as_millis(),
                    core.len()
                ));
                manager.safety_core = Some(Blocked::Transition(HashSet::from_iter(core)));
                Some(true)
            }
            CexResult::Canceled => {
                self.log_info(format!(
                    "{:>8}ms. Safety transition check canceled",
                    start_time.elapsed().as_millis()
                ));
                None
            }
            _ => panic!("safety check failed"),
        }
    }

    pub fn initial_samples(&mut self) -> Tasks<SamplePriority, Model> {
        let universes = if let Some(p) = self.sim_config.sum {
            (0..self.signature.sorts.len())
                .map(|_| (1..=p))
                .multi_cartesian_product_fixed()
                .filter(|v| v.iter().sum::<usize>() <= p)
                .collect()
        } else {
            self.sim_config
                .universe
                .iter()
                .map(|c| 1..=*c)
                .multi_cartesian_product_fixed()
                .collect_vec()
        };
        let models = universes
            .into_iter()
            .flat_map(|u| {
                self.log_info(format!("Gathering initial states with universe {:?}", &u));
                self.simulator.initials_new(&u)
            })
            .sorted_by_key(|model| sample_priority(&self.sim_config, &model.universe, 0).unwrap())
            .collect_vec();
        self.log_info(format!("Gathered {} initial states.", models.len()));
        self.weaken(&models);
        let mut samples = Tasks::new();
        for model in models {
            samples.insert(
                sample_priority(&self.sim_config, &model.universe, 0).unwrap(),
                model,
            )
        }

        samples
    }

    pub fn see(&self, model: &Model) -> Option<bool> {
        self.simulator.see(model)
    }

    pub fn weaken_stats(&self) -> OperationStats {
        self.weaken_stats.clone()
    }

    pub fn get_unsat_stats(&self) -> OperationStats {
        self.get_unsat_stats.lock().unwrap().clone()
    }
}
