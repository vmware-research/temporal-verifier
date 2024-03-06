// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! A simulator for flyvy programs based on the bounded model-checker implemented in `set.rs`.
//! It implements a [`Simulator`] for a fixed universe size, as well as a [`MultiSimulator`] that
//! dynamically manages several universe sizes as needed.

use std::{
    collections::HashMap,
    sync::{Mutex, RwLock},
};

use cadical::Solver;

use fly::{
    ouritertools::OurItertools,
    semantics::Model,
    syntax::{Module, Signature},
    transitions::{extract, DestructuredModule},
};

use crate::{
    checker::CheckerError,
    indices::Indices,
    quant_enum::{enumerate_quantifiers, Enumerated, UniverseBounds},
    sat::{tseytin, Cnf},
    set::{translate, BoundedProgram, BoundedState, IsoStateSet, Transitions, STATE_LEN},
};

/// Get the [`UniverseBounds`] for the given universe sizes in the given signature.
fn universe_bounds(signature: &Signature, universe: &[usize]) -> UniverseBounds {
    assert_eq!(signature.sorts.len(), universe.len());
    signature
        .sorts
        .iter()
        .cloned()
        .zip(universe.iter().cloned())
        .collect()
}

fn get_state(indices: &Indices, solver: &Solver) -> BoundedState {
    assert_eq!(solver.status(), Some(true));
    let mut state = BoundedState::ZERO;
    for i in 0..indices.num_indices {
        if solver.value(i as i32 + 1) == Some(true) {
            state.set(i, true);
        }
    }
    state
}

fn block_model(indices: &Indices, solver: &mut Solver, model: &Model, primes: usize) {
    let mut clause = vec![];
    for (relation, interp) in model.signature.relations.iter().zip(&model.interp) {
        for elements in interp.shape[..(interp.shape.len() - 1)]
            .iter()
            .map(|n| 0..*n)
            .multi_cartesian_product_fixed()
        {
            let var = indices.get(&relation.name, primes, &elements) as i32 + 1;
            clause.push(if interp.get(&elements) == 1 {
                -var
            } else {
                var
            });
        }
    }
    solver.add_clause(clause);
}

/// Convert the [`BoundedState`] to a flyvy [`Model`].
fn state_to_model(indices: &Indices, state: &BoundedState, primes: usize) -> Model {
    state.to_model(indices, primes)
}

/// Convert the flyvy [`Model`] to a [`BoundedState`].
fn model_to_state(indices: &Indices, model: &Model) -> BoundedState {
    BoundedState::from_model(indices, model)
}

/// A simulator for a fixed-size universe.
/// Keeps track of the states it has already seen and ignores them in new simulations.
pub trait Simulator: Sized {
    /// Create a new simulator for the given module and universe size.
    fn new(
        module: &Module,
        dest_module: &DestructuredModule,
        universe: &UniverseBounds,
    ) -> Result<Self, CheckerError>;

    /// Simulate all transitions from the given model and return those that weren't seen before.
    fn simulate_new(&self, model: &Model) -> Vec<Model>;

    /// Return all initial models that weren't seen before.
    fn initials_new(&self) -> Vec<Model>;

    /// Register the given model as already seen by the simulator.
    ///
    /// Returns `true` if this model is seen for the first time, or `false` if seen before.
    fn see(&self, model: &Model) -> bool;
}

/// A simulator using explicit-state search.
pub struct SetSimulator {
    indices: Indices,
    program: BoundedProgram,
    seen: Mutex<IsoStateSet>,
}

/// A simulator using a SAT-based search.
pub struct SatSimulator {
    single_indices: Indices,
    double_indices: Indices,
    init: Cnf,
    transition: Cnf,
    seen: Mutex<IsoStateSet>,
}

/// A simulator for arbitrary universe sizes.
/// Keeps track of the states it has already seen and ignores them in new simulations.
pub struct MultiSimulator<'a, S: Simulator> {
    module: &'a Module,
    bool_module: Module,
    dest_bool_module: DestructuredModule,
    sims: RwLock<HashMap<Vec<usize>, S>>,
}

impl Simulator for SetSimulator {
    fn new(
        module: &Module,
        _: &DestructuredModule,
        universe: &UniverseBounds,
    ) -> Result<Self, CheckerError> {
        let (program, indices) = translate(module, universe, false)?;
        let seen = Mutex::new(IsoStateSet::new(&indices));

        Ok(Self {
            indices,
            program,
            seen,
        })
    }

    fn simulate_new(&self, model: &Model) -> Vec<Model> {
        let state = model_to_state(&self.indices, model);
        let mut transitions = Transitions::new();
        for tr in &self.program.trs {
            transitions.insert(tr);
        }

        let mut states: Vec<_> = transitions
            .get_subsets(&state)
            .iter()
            .map(|tr| tr.update(&state))
            .collect();

        {
            let mut seen = self.seen.lock().unwrap();
            states.retain(|st| seen.insert(st));
        }

        states
            .into_iter()
            .map(|st| state_to_model(&self.indices, &st, 0))
            .collect()
    }

    fn initials_new(&self) -> Vec<Model> {
        let mut seen = self.seen.lock().unwrap();
        self.program
            .inits
            .iter()
            .filter(|st| seen.insert(st))
            .map(|st| state_to_model(&self.indices, st, 0))
            .collect()
    }

    fn see(&self, model: &Model) -> bool {
        self.seen
            .lock()
            .unwrap()
            .insert(&model_to_state(&self.indices, model))
    }
}

impl Simulator for SatSimulator {
    fn new(
        module: &Module,
        dest_module: &DestructuredModule,
        universe: &UniverseBounds,
    ) -> Result<Self, CheckerError> {
        let translate = |term| {
            enumerate_quantifiers(term, &module.signature, universe)
                .map_err(CheckerError::EnumerationError)
        };

        let mut single_indices = Indices::new(module.signature.clone(), universe, 1);
        let mut double_indices = Indices::new(module.signature.clone(), universe, 2);

        if double_indices.num_indices >= STATE_LEN {
            return Err(CheckerError::StateLenTooSmall);
        }

        let init_enum = dest_module
            .inits
            .iter()
            .chain(&dest_module.axioms)
            .map(translate)
            .collect::<Result<Vec<_>, _>>()?;
        let init = tseytin(&Enumerated::and(init_enum), &mut single_indices);

        let primed_mut_axioms = dest_module
            .mutable_axioms(&module.signature.relations)
            .map(translate)
            .map(|res| res.map(|t| t.prime(1)))
            .collect::<Result<Vec<_>, _>>()?;

        let transition_enum = dest_module
            .transitions
            .iter()
            .map(translate)
            .collect::<Result<Vec<_>, _>>()?;
        let transition = tseytin(
            &Enumerated::and(transition_enum.into_iter().chain(primed_mut_axioms)),
            &mut double_indices,
        );

        let seen = Mutex::new(IsoStateSet::new(&single_indices));

        Ok(Self {
            single_indices,
            double_indices,
            init,
            transition,
            seen,
        })
    }

    fn simulate_new(&self, model: &Model) -> Vec<Model> {
        let mut prestate_literals = vec![];
        for (relation, interp) in model.signature.relations.iter().zip(&model.interp) {
            for elements in interp.shape[..(interp.shape.len() - 1)]
                .iter()
                .map(|n| 0..*n)
                .multi_cartesian_product_fixed()
            {
                let var = self.double_indices.get(&relation.name, 0, &elements) as i32 + 1;
                prestate_literals.push(if interp.get(&elements) == 1 {
                    var
                } else {
                    -var
                });
            }
        }

        let mut states = vec![];

        let mut solver: Solver = Default::default();
        for lit in &prestate_literals {
            solver.add_clause([*lit]);
        }
        for clause in &self.transition {
            solver.add_clause(clause.iter().map(|lit| lit.as_int()));
        }

        while solver.solve().expect("simulations solver failed") {
            let double_state = get_state(&self.double_indices, &solver);
            let model = state_to_model(&self.double_indices, &double_state, 1);
            let single_state = model_to_state(&self.single_indices, &model);
            block_model(&self.double_indices, &mut solver, &model, 1);
            states.push((single_state, model));
        }

        let mut seen = self.seen.lock().unwrap();
        states
            .into_iter()
            .filter(|(state, _)| seen.insert(state))
            .map(|(_, model)| model)
            .collect()
    }

    fn initials_new(&self) -> Vec<Model> {
        let mut solver: Solver = Default::default();
        for clause in &self.init {
            solver.add_clause(clause.iter().map(|lit| lit.as_int()));
        }

        let mut states = vec![];
        while solver.solve().expect("simulations solver failed") {
            let state = get_state(&self.single_indices, &solver);
            let model = state_to_model(&self.single_indices, &state, 0);
            block_model(&self.single_indices, &mut solver, &model, 0);
            states.push((state, model));
        }

        let mut seen = self.seen.lock().unwrap();
        states
            .into_iter()
            .filter(|(state, _)| seen.insert(state))
            .map(|(_, model)| model)
            .collect()
    }

    fn see(&self, model: &Model) -> bool {
        self.seen
            .lock()
            .unwrap()
            .insert(&model_to_state(&self.single_indices, model))
    }
}

impl<'a, S: Simulator> MultiSimulator<'a, S> {
    /// Create a new simulator for the given module which supports arbitrary universe sizes.
    pub fn new(module: &'a Module) -> Self {
        let mut bool_module = module.clone();
        let _ = bool_module.convert_non_bool_relations().unwrap();
        let dest_bool_module = extract(&bool_module).unwrap();
        Self {
            module,
            bool_module,
            dest_bool_module,
            sims: RwLock::new(HashMap::new()),
        }
    }

    /// Create a new internal, fixed-size simulator for the given universe size if one doesn't exist.
    fn create_sim(&self, universe: &Vec<usize>) -> Result<(), CheckerError> {
        assert_eq!(universe.len(), self.module.signature.sorts.len());
        {
            let sims = self.sims.read().unwrap();
            if sims.contains_key(universe) {
                return Ok(());
            }
        }
        {
            let mut sims = self.sims.write().unwrap();
            if sims.contains_key(universe) {
                return Ok(());
            }
            let res = S::new(
                &self.bool_module,
                &self.dest_bool_module,
                &universe_bounds(&self.module.signature, universe),
            );
            match res {
                Ok(sim) => {
                    sims.insert(universe.clone(), sim);
                    Ok(())
                }
                Err(err) => {
                    log::info!("Simulator creation error (universe={universe:?}): {err:?}");
                    Err(err)
                }
            }
        }
    }

    /// Simulate all transitions from the given model and return those that weren't see before.
    pub fn simulate_new(&self, model: &Model) -> Vec<Model> {
        if self.create_sim(&model.universe).is_ok() {
            let sims = self.sims.read().unwrap();
            let sim = &sims[&model.universe];
            let bool_model = self.bool_module.to_bool_model(model);
            sim.simulate_new(&bool_model)
                .iter()
                .map(|bool_m| self.module.to_non_bool_model(bool_m))
                .collect()
        } else {
            vec![]
        }
    }

    /// Register the given model as already seen by the simulator.
    ///
    /// Returns whether this model is seen for the first time, or None if a simulator couldn't be created for this model.
    pub fn see(&self, model: &Model) -> Option<bool> {
        if self.create_sim(&model.universe).is_ok() {
            let sims = self.sims.read().unwrap();
            let sim = &sims[&model.universe];
            let bool_model = self.bool_module.to_bool_model(model);
            Some(sim.see(&bool_model))
        } else {
            None
        }
    }

    /// Return all initial states of the given universe size that weren't see before.
    pub fn initials_new(&self, universe: &Vec<usize>) -> Vec<Model> {
        if self.create_sim(universe).is_ok() {
            let sims = self.sims.read().unwrap();
            let sim = &sims[universe];
            sim.initials_new()
                .iter()
                .map(|bool_m| self.module.to_non_bool_model(bool_m))
                .collect()
        } else {
            vec![]
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn set_sat_simulator() {
        let source = include_str!("../../temporal-verifier/examples/fol/consensus_epr.fly");

        let module = fly::parser::parse(source).unwrap();
        let universe = vec![2; 3];
        let depth = 5;

        let set_sim: MultiSimulator<SetSimulator> = MultiSimulator::new(&module);
        let sat_sim: MultiSimulator<SatSimulator> = MultiSimulator::new(&module);

        let mut set_models = set_sim.initials_new(&universe);
        let mut sat_models = sat_sim.initials_new(&universe);
        assert_eq!(set_models.len(), sat_models.len());

        for _ in 0..depth {
            set_models = set_models
                .iter()
                .flat_map(|m| set_sim.simulate_new(m))
                .collect();
            sat_models = sat_models
                .iter()
                .flat_map(|m| sat_sim.simulate_new(m))
                .collect();
            assert_eq!(set_models.len(), sat_models.len());
        }
    }
}
