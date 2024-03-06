// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! A bounded model checker for flyvy programs. Use `translate` to turn a flyvy `Module`
//! into a `BoundedProgram`, then use `interpret` to evaluate it.

use crate::{checker::*, indices::*, quant_enum::*};
use bitvec::prelude::*;
use fly::{ouritertools::OurItertools, semantics::*, syntax::*, transitions::*};
use itertools::Itertools;
use std::collections::VecDeque;
use std::fmt::{Debug, Formatter};

// We use FxHashMap and FxHashSet because the hash function performance is about 25% faster
// and the bounded model checker is essentially a hashing microbenchmark :)
use fxhash::{FxHashMap as HashMap, FxHashSet as HashSet};

/// Combined entry point to both translate and search the module.
pub fn check(
    module: &Module,
    universe: &UniverseBounds,
    depth: Option<usize>,
    compress_traces: TraceCompression,
    print_timing: bool,
) -> Result<CheckerAnswer<()>, CheckerError> {
    let (program, indices) = translate(module, universe, print_timing)?;
    match interpret(&program, depth, compress_traces, print_timing, &indices) {
        InterpreterResult::Unknown => Ok(CheckerAnswer::Unknown),
        InterpreterResult::Convergence => Ok(CheckerAnswer::Convergence(())),
        InterpreterResult::Counterexample(trace) => {
            let models: Vec<Model> = match compress_traces {
                TraceCompression::Yes => {
                    let (state, depth) = match trace {
                        Trace::Trace(..) => unreachable!(),
                        Trace::CompressedTrace(state, depth) => (state, depth),
                    };
                    println!("counterexample is at depth {depth}, not 0");
                    vec![indices.model(0, |i| state.get(i) as Element)]
                }
                TraceCompression::No => match trace {
                    Trace::Trace(states) => states
                        .iter()
                        .map(|state| indices.model(0, |i| state.get(i) as Element))
                        .collect(),
                    Trace::CompressedTrace(..) => unreachable!(),
                },
            };
            Ok(CheckerAnswer::Counterexample(models))
        }
    }
}

/// Compile-time upper bound on the bounded universe size.
pub const STATE_LEN: usize = 256;

/// A state in the bounded system. Conceptually, this is an interpretation of the signature on the
/// bounded universe. We represent states concretely as a bitvector, where each bit represents the
/// presence of a tuple in a relation. The order of the bits is determined by [Indices].
#[derive(Clone, Copy, Eq, PartialOrd)]
pub struct BoundedState(BitArr!(for STATE_LEN));

// Go word by word instead of bit by bit.
impl std::hash::Hash for BoundedState {
    fn hash<H>(&self, h: &mut H)
    where
        H: std::hash::Hasher,
    {
        self.0.as_raw_slice().hash(h)
    }
}
impl PartialEq for BoundedState {
    fn eq(&self, other: &BoundedState) -> bool {
        self.0.as_raw_slice().eq(other.0.as_raw_slice())
    }
}

impl BoundedState {
    /// A bounded state with all zeros.
    pub const ZERO: BoundedState = BoundedState(BitArray::ZERO);

    fn get(&self, index: usize) -> bool {
        assert!(index < STATE_LEN, "STATE_LEN is too small");
        self.0[index]
    }

    /// Set the bit at the given index of the bounded state to the given value.
    pub fn set(&mut self, index: usize, value: bool) {
        assert!(index < STATE_LEN, "STATE_LEN is too small");
        self.0.set(index, value);
    }

    /// Convert this [`BoundedState`] into a flyvy [`Model`].
    pub fn to_model(&self, indices: &Indices, primes: usize) -> Model {
        indices.model(primes, |i| self.get(i) as Element)
    }

    /// Convert this flyvy [`Model`] into a [`BoundedState`].
    pub fn from_model(indices: &Indices, model: &Model) -> Self {
        let mut state = Self::ZERO;

        for (i, relation) in indices.signature.relations.iter().enumerate() {
            let ranges = relation.args.iter().map(|s| (0..model.cardinality(s)));
            for values in ranges.multi_cartesian_product_fixed() {
                state.set(
                    indices.get(&relation.name, 0, &values),
                    model.interp[i].get(&values) == 1,
                )
            }
        }

        state
    }
}

impl Debug for BoundedState {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        write!(f, "[")?;
        let mut max = STATE_LEN - 1;
        while !self.get(max) {
            if max == 0 {
                return write!(f, "]");
            }
            max -= 1;
        }
        for i in 0..=max {
            write!(f, "{}", self.get(i) as usize)?;
        }
        write!(f, "]")
    }
}

/// A BoundedProgram is a set of initial states, a set of transitions, and a safety property
#[derive(Clone, Debug, PartialEq)]
pub struct BoundedProgram {
    /// List of initial states
    pub inits: Vec<BoundedState>,
    /// List of transitions to potentially take at each step. The transition relation is the
    /// disjunction of all these transitions.
    pub trs: Vec<Transition>,
    /// Safety property to check in each reachable state.
    safe: Formula,
}

/// A Transition is a deterministic partial function on states expressed as a guarded update.
///
/// The guard is represented as the conjunction of a cube (the `guards` field, where every
/// Guard is an assertion on one literal) and a formula (the `slow_guard` field). This is done
/// because we can match on the cube effeciently using the [`Transitions`] data structure, but not every
/// guard can be represented as a cube, so we also must add the `slow_guard` to do filtering
/// in these cases.
///
/// If the guard is true, then the transition is enabled and can step to the updated state.
/// If the guard is false, then the transition is not enabled.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Transition {
    guards: Vec<Guard>,
    updates: Vec<Update>,
    slow_guard: Formula,
}

/// A Guard is a logical literal, i.e., a possibly negated relation applied to an argument tuple
/// such as `r(x, y)` or `!r(x, y)`. The relation and argument tuple are represented by an index
/// into an ambient `Indices` map.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct Guard {
    /// The index representing the relation and argument tuple. Indexes into an ambient `Indices`
    /// map.
    index: usize,
    /// True for positive literal, false for negative literal
    value: bool,
}

/// An Update is either an insertion or a removal of a tuple from a relation. The relation and
/// argument tuple are represented by an index into an ambient `Indices` map.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct Update {
    /// The index representing the relation and argument tuple. Indexes into an ambient `Indices`
    /// map.
    index: usize,
    /// True for insertion, false for removal
    formula: Formula,
}

impl Transition {
    // This function constructs a Transition that comes from taking all of the
    // input transitions at the same time. If any of the input transitions would
    // not be run for a given state, the new transition will not be run for that state.
    fn from_conjunction(
        trs: impl IntoIterator<Item = Transition>,
    ) -> Result<Transition, CheckerError> {
        let mut guards: Vec<_> = vec![];
        let mut updates: Vec<_> = vec![];
        let mut slow_guard = Formula::always_true();
        for tr in trs {
            guards.extend(tr.guards);
            updates.extend(tr.updates);
            slow_guard = Formula::and([slow_guard, tr.slow_guard]);
        }

        guards.sort();
        guards.dedup();
        for g in &guards {
            for h in &guards {
                if g != h && g.index == h.index {
                    return Err(CheckerError::ParallelGuards(
                        format!("{g:?}"),
                        format!("{h:?}"),
                    ));
                }
            }
        }
        updates.sort();
        updates.dedup();
        for u in &updates {
            for v in &updates {
                if u != v && u.index == v.index {
                    panic!("found two parallel updates that conflict\n{u:?}\n{v:?}")
                }
            }
        }

        Ok(Transition {
            guards,
            updates,
            slow_guard,
        })
    }

    /// Perform this transition's updates on the given [`BoundedState`].
    pub fn update(&self, state: &BoundedState) -> BoundedState {
        let mut next = *state;
        self.updates
            .iter()
            .for_each(|update| next.set(update.index, update.formula.evaluate(state)));
        next
    }
}

/// Translate a flyvy module into a `BoundedProgram`, given the bounds on the sort sizes.
/// The universe should contain the sizes of all the sorts in module.signature.sorts.
/// This function returns both the desired `BoundedProgram` and an `Indices` object. The
/// `Indices` can be used to translate the indices from the program back into a relation
/// name and the argument values.
/// The module is assumed to have already been typechecked.
/// The translator ignores proof blocks.
pub fn translate(
    module: &Module,
    universe: &UniverseBounds,
    print_timing: bool,
) -> Result<(BoundedProgram, Indices), CheckerError> {
    for relation in &module.signature.relations {
        if relation.sort != Sort::Bool {
            panic!("non-bool relations in checker (use Module::convert_non_bool_relations)")
        }
    }

    let indices = Indices::new(module.signature.clone(), universe, 1);
    if indices
        .iter()
        .any(|(_, rest)| rest.values().any(|(i, _)| i >= &STATE_LEN))
    {
        return Err(CheckerError::StateLenTooSmall);
    }

    for sort in &module.signature.sorts {
        if !universe.contains_key(sort) {
            return Err(CheckerError::UnknownSort(sort.clone(), universe.clone()));
        }
    }

    if !module.defs.is_empty() {
        panic!("definitions in checker (use Module::inline_defs)")
    }

    log::debug!("starting translation...");
    let timer = std::time::Instant::now();

    let d = extract(module).map_err(CheckerError::ExtractionError)?;

    let formula = |term| {
        let term = enumerate_quantifiers(&term, &module.signature, universe)
            .map_err(CheckerError::EnumerationError)?;
        enumerated_to_formula(term, &indices)
    };

    // compute initial states
    let inits = Term::and(d.inits.iter().chain(&d.axioms));
    let inits = indices.bdd_from_enumerated(
        enumerate_quantifiers(&inits, &module.signature, universe)
            .map_err(CheckerError::EnumerationError)?,
    );
    log::debug!("enumerating {} initial states", inits.exact_cardinality());
    let inits: Vec<BoundedState> = inits
        .sat_valuations()
        .map(|valuation| {
            let mut init = BoundedState::ZERO;
            for (r, rest) in indices.iter() {
                for (xs, (i, _)) in rest {
                    init.set(
                        *i,
                        valuation.value(indices.bdd_variables[indices.get(r, 0, xs)]),
                    );
                }
            }
            init
        })
        .collect();

    // compute imperative transitions
    let trs = match d.transitions.as_slice() {
        [] => vec![],
        [tr] => enumerate_quantifiers(tr, &module.signature, universe)
            .map_err(CheckerError::EnumerationError)?
            .get_or()
            .into_iter()
            .map(|term| enumerated_to_transition(term, &indices))
            .collect::<Result<Vec<_>, _>>()?,
        _ => return Err(CheckerError::MultipleTrs),
    };
    let trs: Vec<(Transition, _)> = trs
        .into_iter()
        .filter(|tr| tr.slow_guard != Formula::always_false())
        .map(|tr| {
            // get cube
            let mut constrained: HashSet<usize> = HashSet::default();
            for &Update { index, .. } in &tr.updates {
                constrained.insert(index);
            }
            let mut unconstrained = vec![];
            for (_, rest) in indices.iter() {
                for (index, mutable) in rest.values() {
                    if !constrained.contains(index) && *mutable {
                        unconstrained.push(index);
                    }
                }
            }
            (tr, unconstrained)
        })
        .collect();
    log::debug!(
        "enumerating {} transitions",
        trs.iter()
            .map(|(_, unconstrained)| 2_usize.pow(unconstrained.len() as u32))
            .sum::<usize>()
    );
    let mut trs: Vec<_> = trs
        .into_iter()
        .flat_map(|(tr, unconstrained)| {
            // enumerate cube
            let mut trs = vec![tr];
            for index in unconstrained {
                let len = trs.len();
                for i in 0..len {
                    let mut with_unconstrained = trs[i].clone();
                    with_unconstrained.updates.push(Update {
                        index: *index,
                        formula: Formula::always_true(),
                    });
                    trs.push(with_unconstrained);

                    trs[i].updates.push(Update {
                        index: *index,
                        formula: Formula::always_false(),
                    });
                }
            }
            // filter out no-ops
            for tr in &mut trs {
                tr.updates.retain(|update| {
                    update.formula
                        != Formula::Guard(Guard {
                            index: update.index,
                            value: true,
                        })
                        && !(update.formula == Formula::always_true()
                            && tr.guards.contains(&Guard {
                                index: update.index,
                                value: true,
                            }))
                        && !(update.formula == Formula::always_false()
                            && tr.guards.contains(&Guard {
                                index: update.index,
                                value: false,
                            }))
                });
            }
            trs
        })
        .collect();

    // filter transitions using the mutable axioms
    let mutable_axioms = formula(Term::and(d.mutable_axioms(&module.signature.relations)))?;
    let guard_indices = mutable_axioms.guard_indices();
    let mut should_keep = vec![true; trs.len()];
    for (i, should_keep) in should_keep.iter_mut().enumerate() {
        // if the axiom was true in the pre-state, it will still be true in the post-state
        if guard_indices
            .iter()
            .all(|index| !trs[i].updates.iter().any(|u| *index == u.index))
        {
            continue;
        }
        // else, try to statically determine the post-state and evaluate it
        let guards_with_no_updates: Vec<_> = trs[i]
            .guards
            .iter()
            .filter(|&guard| {
                !trs[i]
                    .updates
                    .iter()
                    .any(|update| update.index == guard.index)
            })
            .cloned()
            .collect();
        let true_or_false_updates: Vec<_> = trs[i]
            .updates
            .iter()
            .filter_map(|update| match &update.formula {
                f if *f == Formula::always_true() => Some(Guard {
                    index: update.index,
                    value: true,
                }),
                f if *f == Formula::always_false() => Some(Guard {
                    index: update.index,
                    value: false,
                }),
                _ => None,
            })
            .collect();
        match mutable_axioms.evaluate_partial(
            guards_with_no_updates
                .into_iter()
                .chain(true_or_false_updates),
        ) {
            Some(b) => *should_keep = b,
            None => return Err(CheckerError::UnprovenMutableAxiom),
        }
    }
    let mut i = 0;
    trs.retain(|_| {
        i += 1;
        should_keep[i - 1]
    });

    // compute safety property
    let safes = d.proofs.iter().map(|proof| proof.safety.x.clone());
    let safe = formula(Term::and(safes))?;

    if print_timing {
        println!(
            "translation finished in {:0.1}s",
            timer.elapsed().as_secs_f64()
        );
    }

    // do sanity checks on the transitions
    for tr in &trs {
        let mut indices_to_sets: Vec<&str> = vec![""; indices.num_vars];
        for (r, rest) in indices.iter() {
            for (i, _) in rest.values() {
                indices_to_sets[*i] = r;
            }
        }

        // check that none of the transitions violate immutability
        for update in &tr.updates {
            if !module
                .signature
                .relations
                .iter()
                .find(|r| r.name == indices_to_sets[update.index])
                .unwrap()
                .mutable
            {
                panic!("one of the generated updates violated immutability");
            }
        }
        // check that all guards and updates target different indices
        for a in &tr.guards {
            if tr.guards.iter().any(|b| a != b && a.index == b.index) {
                panic!("found two guards with the same index\n{tr:?}");
            }
        }
        for a in &tr.updates {
            if tr.updates.iter().any(|b| a != b && a.index == b.index) {
                panic!("found two updates with the same index\n{tr:?}");
            }
        }
        // check no updates are redundant
        for &Guard { index, value } in &tr.guards {
            if tr.updates.contains(&Update {
                index,
                formula: match value {
                    true => Formula::always_true(),
                    false => Formula::always_false(),
                },
            }) {
                panic!("found an update that was redundant with a guard")
            }
        }
        for Update { index, formula } in &tr.updates {
            if let Formula::Guard(guard) = formula {
                if *index == guard.index && guard.value {
                    panic!("found an update that doesn't do anything")
                }
            }
        }
        assert!(
            tr.slow_guard != Formula::always_false(),
            "found an update that had an always-false slow guard"
        );
    }

    Ok((BoundedProgram { inits, trs, safe }, indices))
}

/// A propositional formula over `Guard`s.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Formula {
    And(Vec<Formula>),
    Or(Vec<Formula>),
    Guard(Guard),
}

impl Formula {
    fn always_true() -> Formula {
        Formula::And(vec![])
    }

    fn always_false() -> Formula {
        Formula::Or(vec![])
    }

    fn and(terms: impl IntoIterator<Item = Formula>) -> Formula {
        let mut terms: Vec<_> = terms
            .into_iter()
            .flat_map(Formula::get_and)
            .sorted()
            .collect();
        terms.dedup();

        if terms.iter().any(|term| *term == Formula::always_false()) {
            Formula::always_false()
        } else if terms.len() == 1 {
            terms.pop().unwrap()
        } else {
            Formula::And(terms)
        }
    }

    fn get_and(self) -> Vec<Formula> {
        match self {
            Formula::And(terms) => terms,
            term => vec![term],
        }
    }

    fn or(terms: impl IntoIterator<Item = Formula>) -> Formula {
        let mut terms: Vec<_> = terms
            .into_iter()
            .flat_map(Formula::get_or)
            .sorted()
            .collect();
        terms.dedup();

        if terms.iter().any(|term| *term == Formula::always_true()) {
            Formula::always_true()
        } else if terms.len() == 1 {
            terms.pop().unwrap()
        } else {
            Formula::Or(terms)
        }
    }

    fn get_or(self) -> Vec<Formula> {
        match self {
            Formula::Or(terms) => terms,
            term => vec![term],
        }
    }

    fn not(self) -> Formula {
        match self {
            Formula::And(terms) => Formula::or(terms.into_iter().map(Formula::not)),
            Formula::Or(terms) => Formula::and(terms.into_iter().map(Formula::not)),
            Formula::Guard(Guard { index, value }) => Formula::Guard(Guard {
                index,
                value: !value,
            }),
        }
    }

    fn iff(self, other: Formula) -> Formula {
        Formula::or([
            Formula::and([self.clone(), other.clone()]),
            Formula::and([self.not(), other.not()]),
        ])
    }

    fn evaluate(&self, state: &BoundedState) -> bool {
        match self {
            Formula::And(terms) => terms.iter().all(|term| term.evaluate(state)),
            Formula::Or(terms) => terms.iter().any(|term| term.evaluate(state)),
            Formula::Guard(Guard { index, value }) => state.get(*index) == *value,
        }
    }

    // returns Some(true) for true, Some(false) for false, and None for unknown
    fn evaluate_partial(&self, state: impl IntoIterator<Item = Guard>) -> Option<bool> {
        fn evaluate_partial(formula: &Formula, state: &HashMap<usize, bool>) -> Option<bool> {
            match formula {
                Formula::And(terms) => terms.iter().try_fold(true, |b, term| {
                    match (b, evaluate_partial(term, state)) {
                        (false, _) | (_, Some(false)) => Some(false),
                        (true, Some(true)) => Some(true),
                        _ => None,
                    }
                }),
                Formula::Or(terms) => terms.iter().try_fold(false, |b, term| {
                    match (b, evaluate_partial(term, state)) {
                        (true, _) | (_, Some(true)) => Some(true),
                        (false, Some(false)) => Some(false),
                        _ => None,
                    }
                }),
                Formula::Guard(Guard { index, value }) => state.get(index).map(|v| v == value),
            }
        }
        let mut map = HashMap::default();
        for guard in state {
            map.insert(guard.index, guard.value);
        }
        evaluate_partial(self, &map)
    }

    // returns a vector of the indices in the guards in this formula
    fn guard_indices(&self) -> Vec<usize> {
        match self {
            Formula::And(terms) | Formula::Or(terms) => {
                terms.iter().flat_map(Formula::guard_indices).collect()
            }
            Formula::Guard(Guard { index, .. }) => vec![*index],
        }
    }
}

// Converts a Term to exactly one Transition (we aren't doing DNF, so this function cannot
// return multiple transitions). It will fail if given a disjunction where one of the
// branches contains a primed variable. (It can handle single-vocabulary disjunctions by
// translating them into `slow_guard`s.)
fn enumerated_to_transition(
    term: Enumerated,
    indices: &Indices,
) -> Result<Transition, CheckerError> {
    let go = |term| enumerated_to_transition(term, indices);
    let formula = |term| enumerated_to_formula(term, indices);

    let transition = match term {
        Enumerated::And(xs) => {
            Transition::from_conjunction(xs.into_iter().map(go).collect::<Result<Vec<_>, _>>()?)?
        }
        Enumerated::Not(ref x) => {
            let mut tr = go(*x.clone())?;
            match (tr.guards.as_mut_slice(), tr.updates.as_mut_slice()) {
                ([guard], []) if tr.slow_guard == Formula::always_true() => {
                    guard.value = !guard.value
                }
                ([], [update]) if tr.slow_guard == Formula::always_true() => {
                    update.formula = update.formula.clone().not()
                }
                ([], []) => tr.slow_guard = tr.slow_guard.not(),
                _ => {
                    tr = Transition {
                        guards: vec![],
                        updates: vec![],
                        slow_guard: formula(term)?,
                    }
                }
            }
            tr
        }
        Enumerated::Eq(x, y) if matches!(*x, Enumerated::App(_, 1, _)) => {
            if let Enumerated::App(name, 1, args) = *x {
                let index = indices.get(&name, 0, &args);
                let formula = formula(*y)?;
                Transition {
                    guards: vec![],
                    updates: vec![Update { index, formula }],
                    slow_guard: Formula::always_true(),
                }
            } else {
                unreachable!()
            }
        }
        Enumerated::App(name, 1, args) => Transition {
            guards: vec![],
            updates: vec![Update {
                index: indices.get(&name, 0, &args),
                formula: Formula::always_true(),
            }],
            slow_guard: Formula::always_true(),
        },
        term => {
            let terms = formula(term)?.get_and();
            if terms.iter().all(|term| matches!(term, Formula::Guard(_))) {
                Transition {
                    guards: terms
                        .into_iter()
                        .map(|term| match term {
                            Formula::Guard(guard) => guard,
                            _ => unreachable!(),
                        })
                        .collect(),
                    updates: vec![],
                    slow_guard: Formula::always_true(),
                }
            } else {
                Transition {
                    guards: vec![],
                    updates: vec![],
                    slow_guard: Formula::and(terms),
                }
            }
        }
    };
    Ok(transition)
}

fn enumerated_to_formula(term: Enumerated, indices: &Indices) -> Result<Formula, CheckerError> {
    let go = |term| enumerated_to_formula(term, indices);

    let formula = match term {
        Enumerated::And(xs) => Formula::and(xs.into_iter().map(go).collect::<Result<Vec<_>, _>>()?),
        Enumerated::Or(xs) => Formula::or(xs.into_iter().map(go).collect::<Result<Vec<_>, _>>()?),
        Enumerated::Not(x) => go(*x)?.not(),
        Enumerated::Eq(x, y) => go(*x)?.iff(go(*y)?),
        Enumerated::App(name, 0, args) => Formula::Guard(Guard {
            index: indices.get(&name, 0, &args),
            value: true,
        }),
        Enumerated::App(..) => return Err(CheckerError::PrimeInFormula),
    };
    Ok(formula)
}

/// Whether to compress traces by keeping only the last state
#[derive(Clone, Copy)]
pub enum TraceCompression {
    /// Compress traces
    Yes,
    /// Don't compress traces
    No,
}

impl From<bool> for TraceCompression {
    fn from(b: bool) -> TraceCompression {
        if b {
            TraceCompression::Yes
        } else {
            TraceCompression::No
        }
    }
}

/// A sequence of states that may or may not be compressed. Here, a "compressed" trace is just its
/// last state together with its depth. (The depth of a trace is the number of transitions it
/// contains, or one less than the number of states it contains.)
#[derive(Clone, Debug, PartialEq)]
enum Trace {
    /// Uncompressed trace, which keeps all states
    Trace(Vec<BoundedState>),
    /// Compressed trace, keeping only the last state and its depth
    CompressedTrace(BoundedState, usize),
}

impl Trace {
    /// Construct a singleton trace. Note that the decision of whether to compress or not is made at
    /// construction time. If the trace is constructed as compressed (`TraceCompression::Yes`), then
    /// future calls to `push` on this trace will only increment the depth and replace the (one)
    /// state.
    fn new(state: BoundedState, compression: TraceCompression) -> Trace {
        match compression {
            TraceCompression::Yes => Trace::CompressedTrace(state, 0),
            TraceCompression::No => Trace::Trace(vec![state]),
        }
    }

    /// The depth of this trace, which is the number of transitions it represents.
    fn depth(&self) -> usize {
        match self {
            Trace::CompressedTrace(_, n) => *n,
            Trace::Trace(v) => v.len() - 1,
        }
    }

    /// The last state of a trace. Since all traces are constructed to be nonempty, this never fails.
    fn last(&self) -> &BoundedState {
        match self {
            Trace::CompressedTrace(s, _) => s,

            // unwrap is safe here since there's no way to construct an empty trace
            Trace::Trace(v) => v.last().unwrap(),
        }
    }

    /// Extend the trace with one new state on the end. Note that if `self` is a compressed trace,
    /// then only the last state is tracked, so `push` will lose the information about the previous
    /// state.
    fn push(&mut self, state: BoundedState) {
        match self {
            Trace::CompressedTrace(s, n) => {
                *s = state;
                *n += 1;
            }
            Trace::Trace(v) => {
                v.push(state);
            }
        }
    }
}

/// The bounded model checker will either find a counterexample or say "no bugs found"
#[derive(Debug, PartialEq)]
enum InterpreterResult {
    /// The checker found a counterexample, here it is
    Counterexample(Trace),
    /// The checker could not find any counterexamples
    Unknown,
    /// The checker found that the set of states stopped changing
    Convergence,
}

/// Explore reachable states of a BoundedProgram up to (and including) the given max_depth using
/// breadth-first search.
///
/// Note that max_depth refers to the number of transitions, not the number of states,
/// so if max_depth is Some(3), it means there will be 3 transitions (so 4 states).
/// If max_depth is None, it means "no upper bound". The program will run until its
/// state space is exhausted or the process is killed.
fn interpret(
    program: &BoundedProgram,
    max_depth: Option<usize>,
    compress_traces: TraceCompression,
    print_timing: bool,
    indices: &Indices,
) -> InterpreterResult {
    // States we have seen so far.
    let mut seen = IsoStateSet::new(indices);
    // The BFS queue, i.e., states on the frontier that need to be explored.
    // The queue is always a subset of seen.
    let mut queue: VecDeque<Trace> = VecDeque::new();

    for init in &program.inits {
        if seen.insert(init) {
            queue.push_back(Trace::new(*init, compress_traces));
        }
    }

    let mut transitions = Transitions::new();
    for tr in &program.trs {
        transitions.insert(tr);
    }

    let mut current_depth = 0;
    let start_time = std::time::Instant::now();
    println!(
        "starting search from depth 0. there are {} initial states in the queue.",
        queue.len()
    );

    while let Some(trace) = queue.pop_front() {
        let depth = trace.depth();
        if depth > current_depth {
            current_depth += 1;
            if print_timing {
                print!("({:0.1}s since start) ", start_time.elapsed().as_secs_f64());
            }
            println!(
                "considering new depth: {current_depth}. \
                 queue length is {}. seen {} unique states.",
                queue.len() + 1, // include current state
                seen.set.len()
            );
        }

        let state = trace.last();
        if !program.safe.evaluate(state) {
            return InterpreterResult::Counterexample(trace);
        }

        if max_depth.map(|md| depth < md).unwrap_or(true) {
            let trs = transitions.get_subsets(state);

            for tr in trs {
                let mut next = *state;
                tr.updates
                    .iter()
                    .for_each(|update| next.set(update.index, update.formula.evaluate(state)));
                if seen.insert(&next) {
                    let mut trace = trace.clone();
                    trace.push(next);
                    queue.push_back(trace);
                }
            }
        }
    }

    if max_depth.map(|md| current_depth < md).unwrap_or(true) {
        InterpreterResult::Convergence
    } else {
        InterpreterResult::Unknown
    }
}

/// A set of transitions indexed by their guards, i.e., a map from guards to transitions. We use a
/// set trie data structure that allows efficiently answering the question "give me all the
/// transitions whose guard sets are *subsets* of the given set". During model checking, this allows
/// efficiently retrieving the set of enabled transitions in a given state without searching through
/// all transitions.
#[derive(Clone, Debug)]
pub struct Transitions<'a> {
    data: Vec<&'a Transition>,
    children: HashMap<&'a Guard, Transitions<'a>>,
}

impl<'a> Transitions<'a> {
    /// Construct an empty set of transitions
    pub fn new() -> Transitions<'a> {
        Transitions {
            data: Vec::new(),
            children: HashMap::default(),
        }
    }

    /// Insert the given transition into the set
    pub fn insert(&mut self, value: &'a Transition) {
        self.insert_from_iter(value.guards.iter(), value)
    }

    // Recursive helper function to insert an iterator of guards into the trie
    fn insert_from_iter(
        &mut self,
        mut set: impl Iterator<Item = &'a Guard>,
        value: &'a Transition,
    ) {
        match set.next() {
            None => {
                self.data.push(value);
            }
            Some(key) => self
                .children
                .entry(key)
                .or_insert_with(Transitions::new)
                .insert_from_iter(set, value),
        }
    }

    /// Get all the transitions whose guards are a subset of the given set.
    pub fn get_subsets(&self, set: &BoundedState) -> Vec<&'a Transition> {
        let mut out = vec![];
        self.get_subsets_into_vec(set, &mut out);
        out
    }

    // Destination passing style helper to recursively collect all the transitions whose guards are
    // a subset of the given set.
    fn get_subsets_into_vec(&self, set: &BoundedState, out: &mut Vec<&'a Transition>) {
        out.extend(self.data.iter().filter(|tr| tr.slow_guard.evaluate(set)));
        for (key, child) in &self.children {
            if set.get(key.index) == key.value {
                child.get_subsets_into_vec(set, out);
            }
        }
    }
}

/// Can answer the question "have I seen a state that is isomorphic to this one before"?
pub struct IsoStateSet {
    set: HashSet<BoundedState>,
    orderings: Vec<Vec<(usize, usize)>>,
}

impl IsoStateSet {
    /// Create a new empty state set.
    pub fn new(indices: &Indices) -> IsoStateSet {
        let sorts: Vec<_> = indices.universe.keys().sorted().collect();
        let orderings = sorts
            .iter()
            .map(|sort| indices.universe[sort.as_str()])
            // the permutations are maps from old to new element values
            .map(|size| (0..size).permutations(size))
            // get all combinations of different ways to permute values
            .multi_cartesian_product_fixed()
            // reattach sort names onto each ordering
            .map(|ordering| {
                assert_eq!(sorts.len(), ordering.len());
                sorts.iter().map(|s| s.as_str()).zip(ordering).collect()
            })
            // convert permutations to copy instructions
            .map(|permutation: HashMap<&str, Vec<usize>>| {
                indices
                    .iter()
                    .flat_map(|(name, rest)| {
                        rest.iter().map(|(elements, (i, _))| {
                            let relation = indices.signature.relation_decl(name);
                            assert_eq!(relation.args.len(), elements.len());
                            // map each old element to a new element
                            let mut new_elements = elements.clone();
                            for i in 0..new_elements.len() {
                                let x = elements[i];
                                new_elements[i] = match &relation.args[i] {
                                    Sort::Uninterpreted(s) => permutation[s.as_str()][x],
                                    Sort::Bool => x,
                                };
                            }
                            // look up the index to precompute the dst
                            (*i, indices.get(&relation.name, 0, &new_elements))
                        })
                    })
                    .filter(|(src, dst)| src != dst)
                    .collect()
            })
            .collect();

        IsoStateSet {
            set: HashSet::default(),
            orderings,
        }
    }

    /// Insert a state into this set.
    pub fn insert(&mut self, x: &BoundedState) -> bool {
        if self.set.contains(x) {
            false
        } else {
            for ordering in &self.orderings {
                let mut y = *x;
                for (src, dst) in ordering {
                    y.set(*dst, x.get(*src));
                }
                self.set.insert(y);
            }
            true
        }
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;
    use fly::sorts::sort_check_module;

    fn includes(set: &str, elements: Vec<Element>, indices: &Indices) -> Guard {
        Guard {
            index: indices.get(set, 0, &elements),
            value: true,
        }
    }
    fn excludes(set: &str, elements: Vec<Element>, indices: &Indices) -> Guard {
        Guard {
            index: indices.get(set, 0, &elements),
            value: false,
        }
    }
    fn insert(set: &str, elements: Vec<Element>, indices: &Indices) -> Update {
        Update {
            index: indices.get(set, 0, &elements),
            formula: Formula::always_true(),
        }
    }
    fn remove(set: &str, elements: Vec<Element>, indices: &Indices) -> Update {
        Update {
            index: indices.get(set, 0, &elements),
            formula: Formula::always_false(),
        }
    }
    fn transition(guards: Vec<Guard>, updates: Vec<Update>) -> Transition {
        Transition {
            guards: guards.into_iter().sorted().collect(),
            updates: updates.into_iter().sorted().collect(),
            slow_guard: Formula::always_true(),
        }
    }
    fn state(iter: impl IntoIterator<Item = u8>) -> BoundedState {
        let mut out = BoundedState::ZERO;
        for (i, x) in iter.into_iter().enumerate() {
            out.set(i, x == 1);
        }
        out
    }

    #[test]
    fn checker_set_states() {
        let mut s = state([0, 1, 0, 1]);

        assert!(!s.get(0));
        assert!(s.get(1));
        assert!(!s.get(2));
        assert!(s.get(3));

        s.set(0, true);
        s.set(2, true);

        assert!(s.get(0));
        assert!(s.get(1));
        assert!(s.get(2));
        assert!(s.get(3));

        s.set(2, false);
        s.set(3, false);

        assert!(s.get(0));
        assert!(s.get(1));
        assert!(!s.get(2));
        assert!(!s.get(3));

        assert!(state([0]) < state([1]));
        assert!(state([0, 1, 0, 1]) < state([1, 0, 1, 0]));
        assert!(state([0, 1, 0, 0]) < state([0, 1, 0, 1]));
        assert!(state([0, 0, 1, 1]) < state([0, 1, 0, 0]));
        assert!(state([0, 0, 1, 0]) < state([0, 0, 1, 1]));
    }

    #[test]
    fn checker_set_basic() {
        let signature = Arc::new(Signature {
            sorts: vec![],
            relations: vec![RelationDecl {
                args: vec![],
                sort: Sort::Bool,
                name: "r".to_string(),
                mutable: true,
            }],
        });
        let universe = std::collections::HashMap::new();
        let indices = Indices::new(signature, &universe, 1);

        let program = BoundedProgram {
            inits: vec![state([0])],
            trs: vec![
                transition(vec![], vec![]),
                transition(
                    vec![],
                    vec![Update {
                        index: 0,
                        formula: Formula::always_true(),
                    }],
                ),
            ],
            safe: Formula::Guard(Guard {
                index: 0,
                value: false,
            }),
        };
        let result0 = interpret(&program, Some(0), TraceCompression::No, false, &indices);
        let result1 = interpret(&program, Some(1), TraceCompression::No, false, &indices);
        assert_eq!(result0, InterpreterResult::Unknown);
        let mut expected1 = Trace::new(state([0]), TraceCompression::No);
        expected1.push(state([1]));
        assert_eq!(result1, InterpreterResult::Counterexample(expected1));
    }

    #[test]
    fn checker_set_cycle() {
        let signature = Arc::new(Signature {
            sorts: vec![],
            relations: vec![
                RelationDecl {
                    args: vec![],
                    sort: Sort::Bool,
                    name: "0".to_string(),
                    mutable: true,
                },
                RelationDecl {
                    args: vec![],
                    sort: Sort::Bool,
                    name: "1".to_string(),
                    mutable: true,
                },
                RelationDecl {
                    args: vec![],
                    sort: Sort::Bool,
                    name: "2".to_string(),
                    mutable: true,
                },
                RelationDecl {
                    args: vec![],
                    sort: Sort::Bool,
                    name: "3".to_string(),
                    mutable: true,
                },
            ],
        });
        let universe = std::collections::HashMap::new();
        let indices = Indices::new(signature, &universe, 1);

        let program = BoundedProgram {
            inits: vec![state([1, 0, 0, 0])],
            trs: vec![
                transition(
                    vec![Guard {
                        index: 0,
                        value: true,
                    }],
                    vec![
                        Update {
                            index: 0,
                            formula: Formula::always_false(),
                        },
                        Update {
                            index: 1,
                            formula: Formula::always_true(),
                        },
                    ],
                ),
                transition(
                    vec![Guard {
                        index: 1,
                        value: true,
                    }],
                    vec![
                        Update {
                            index: 1,
                            formula: Formula::always_false(),
                        },
                        Update {
                            index: 2,
                            formula: Formula::always_true(),
                        },
                    ],
                ),
                transition(
                    vec![Guard {
                        index: 2,
                        value: true,
                    }],
                    vec![
                        Update {
                            index: 2,
                            formula: Formula::always_false(),
                        },
                        Update {
                            index: 3,
                            formula: Formula::always_true(),
                        },
                    ],
                ),
                transition(
                    vec![Guard {
                        index: 3,
                        value: true,
                    }],
                    vec![
                        Update {
                            index: 3,
                            formula: Formula::always_false(),
                        },
                        Update {
                            index: 0,
                            formula: Formula::always_true(),
                        },
                    ],
                ),
            ],
            safe: Formula::Guard(Guard {
                index: 3,
                value: false,
            }),
        };
        let result1 = interpret(&program, Some(0), TraceCompression::No, false, &indices);
        let result2 = interpret(&program, Some(1), TraceCompression::No, false, &indices);
        let result3 = interpret(&program, Some(2), TraceCompression::No, false, &indices);
        let result4 = interpret(&program, Some(3), TraceCompression::No, false, &indices);
        let result5 = interpret(&program, Some(4), TraceCompression::No, false, &indices);
        assert_eq!(result1, InterpreterResult::Unknown);
        assert_eq!(result2, InterpreterResult::Unknown);
        assert_eq!(result3, InterpreterResult::Unknown);
        let mut expected4 = Trace::new(state([1, 0, 0, 0]), TraceCompression::No);
        for state in [
            state([0, 1, 0, 0]),
            state([0, 0, 1, 0]),
            state([0, 0, 0, 1]),
        ] {
            expected4.push(state);
        }
        assert_eq!(result4, InterpreterResult::Counterexample(expected4));
        assert_eq!(result5, result4);
    }

    #[test]
    fn checker_set_lockserver_translation() -> Result<(), CheckerError> {
        let source = include_str!("../../temporal-verifier/examples/lockserver.fly");

        let mut m = fly::parser::parse(source).unwrap();
        sort_check_module(&mut m).unwrap();
        let universe = std::collections::HashMap::from([("node".to_string(), 2)]);
        let indices = Indices::new(m.signature.clone(), &universe, 1);

        let trs = vec![
            transition(
                vec![includes("grant_msg", vec![0], &indices)],
                vec![
                    insert("holds_lock", vec![0], &indices),
                    remove("grant_msg", vec![0], &indices),
                ],
            ),
            transition(
                vec![includes("grant_msg", vec![1], &indices)],
                vec![
                    insert("holds_lock", vec![1], &indices),
                    remove("grant_msg", vec![1], &indices),
                ],
            ),
            transition(
                vec![includes("holds_lock", vec![0], &indices)],
                vec![
                    insert("unlock_msg", vec![0], &indices),
                    remove("holds_lock", vec![0], &indices),
                ],
            ),
            transition(
                vec![includes("holds_lock", vec![1], &indices)],
                vec![
                    insert("unlock_msg", vec![1], &indices),
                    remove("holds_lock", vec![1], &indices),
                ],
            ),
            transition(
                vec![
                    includes("lock_msg", vec![0], &indices),
                    includes("server_holds_lock", vec![], &indices),
                ],
                vec![
                    insert("grant_msg", vec![0], &indices),
                    remove("lock_msg", vec![0], &indices),
                    remove("server_holds_lock", vec![], &indices),
                ],
            ),
            transition(
                vec![
                    includes("lock_msg", vec![1], &indices),
                    includes("server_holds_lock", vec![], &indices),
                ],
                vec![
                    insert("grant_msg", vec![1], &indices),
                    remove("lock_msg", vec![1], &indices),
                    remove("server_holds_lock", vec![], &indices),
                ],
            ),
            transition(
                vec![includes("unlock_msg", vec![0], &indices)],
                vec![
                    insert("server_holds_lock", vec![], &indices),
                    remove("unlock_msg", vec![0], &indices),
                ],
            ),
            transition(
                vec![includes("unlock_msg", vec![1], &indices)],
                vec![
                    insert("server_holds_lock", vec![], &indices),
                    remove("unlock_msg", vec![1], &indices),
                ],
            ),
            transition(vec![], vec![insert("lock_msg", vec![0], &indices)]),
            transition(vec![], vec![insert("lock_msg", vec![1], &indices)]),
        ];

        let expected = BoundedProgram {
            inits: vec![state([0, 0, 0, 0, 0, 0, 0, 0, 1])],
            trs,
            safe: Formula::Or(vec![
                Formula::Guard(excludes("holds_lock", vec![0], &indices)),
                Formula::Guard(excludes("holds_lock", vec![1], &indices)),
            ]),
        };

        let (target, _) = translate(&m, &universe, false)?;
        assert_eq!(target.inits, expected.inits);
        assert_eq!(target.safe, expected.safe);
        assert_eq!(
            expected.trs.iter().sorted().collect::<Vec<_>>(),
            target.trs.iter().sorted().collect::<Vec<_>>(),
        );

        let output = interpret(&target, None, TraceCompression::No, false, &indices);
        assert_eq!(output, InterpreterResult::Convergence);

        Ok(())
    }

    #[test]
    fn checker_set_lockserver_buggy() -> Result<(), CheckerError> {
        let source = include_str!("../../temporal-verifier/tests/examples/lockserver_buggy.fly");

        let mut m = fly::parser::parse(source).unwrap();
        sort_check_module(&mut m).unwrap();
        let universe = std::collections::HashMap::from([("node".to_string(), 2)]);
        let (target, indices) = translate(&m, &universe, false)?;

        let bug = interpret(&target, Some(12), TraceCompression::No, false, &indices);
        if let InterpreterResult::Counterexample(trace) = &bug {
            assert_eq!(trace.depth(), 12);
        } else {
            assert!(matches!(bug, InterpreterResult::Counterexample(_)));
        }

        let too_short = interpret(&target, Some(11), TraceCompression::No, false, &indices);
        assert_eq!(too_short, InterpreterResult::Unknown);

        Ok(())
    }

    #[test]
    fn checker_set_consensus() -> Result<(), CheckerError> {
        let source = include_str!("../../temporal-verifier/examples/consensus.fly");

        let mut m = fly::parser::parse(source).unwrap();
        sort_check_module(&mut m).unwrap();
        let universe = std::collections::HashMap::from([
            ("node".to_string(), 2),
            ("quorum".to_string(), 2),
            ("value".to_string(), 2),
        ]);
        let output = check(&m, &universe, Some(10), TraceCompression::No, false)?;
        assert_eq!(output, CheckerAnswer::Unknown);

        Ok(())
    }

    #[test]
    fn checker_set_consensus_forall() -> Result<(), CheckerError> {
        let source = include_str!("../../temporal-verifier/examples/consensus_forall.fly");

        let mut m = fly::parser::parse(source).unwrap();
        sort_check_module(&mut m).unwrap();
        let _ = m.convert_non_bool_relations().unwrap();
        let universe = std::collections::HashMap::from([
            ("node".to_string(), 2),
            ("quorum".to_string(), 2),
            ("value".to_string(), 2),
        ]);
        let output = check(&m, &universe, Some(10), TraceCompression::No, false)?;
        assert_eq!(output, CheckerAnswer::Unknown);

        Ok(())
    }

    #[test]
    fn checker_set_immutability() {
        let source =
            include_str!("../../temporal-verifier/tests/examples/success/immutability.fly");
        let mut module = fly::parser::parse(source).unwrap();
        sort_check_module(&mut module).unwrap();
        let universe = std::collections::HashMap::new();
        assert_eq!(
            Ok(CheckerAnswer::Convergence(())),
            check(&module, &universe, Some(10), true.into(), false)
        );
    }

    #[test]
    fn checker_set_copy_relation_size() -> Result<(), CheckerError> {
        let source = "
sort x
mutable f(x): bool
mutable g(x): bool

assume forall a:x. !f(a) & !g(a)
assume always forall a:x. ((g'(a) <-> f(a)) & (f'(a) <-> f(a)))
        ";
        let mut m = fly::parser::parse(source).unwrap();
        sort_check_module(&mut m).unwrap();
        let universe = std::collections::HashMap::from([("x".to_string(), 5)]);
        let (target, _) = translate(&m, &universe, false)?;
        assert_eq!(1, target.trs.len());
        Ok(())
    }

    #[test]
    fn checker_set_isostateset_correctness() {
        let source = "
sort s
immutable f(s): bool
        ";
        let m = fly::parser::parse(source).unwrap();
        let universe = std::collections::HashMap::from([("s".to_string(), 2)]);
        let indices = Indices::new(m.signature, &universe, 1);
        let mut set = IsoStateSet::new(&indices);

        assert!(set.insert(&state([0, 0])));
        assert!(!set.insert(&state([0, 0])));
        assert!(set.insert(&state([0, 1])));
        assert!(!set.insert(&state([1, 0])));
        assert!(set.insert(&state([1, 1])));

        let source = "
sort a
sort b
immutable f(a, b): bool
        ";
        let m = fly::parser::parse(source).unwrap();
        let universe =
            std::collections::HashMap::from([("a".to_string(), 3), ("b".to_string(), 3)]);
        let indices = Indices::new(m.signature, &universe, 1);
        let mut set = IsoStateSet::new(&indices);

        // b: 0 -> 2, 2 -> 1, 1 -> 0
        assert!(set.insert(&state([1, 1, 1, 0, 0, 1, 0, 1, 1])));
        assert!(!set.insert(&state([1, 1, 1, 0, 1, 0, 1, 1, 0])));

        let source = "
sort s
sort t
immutable f(s, t, s): bool
        ";
        let m = fly::parser::parse(source).unwrap();
        let universe =
            std::collections::HashMap::from([("s".to_string(), 3), ("t".to_string(), 2)]);
        let indices = Indices::new(m.signature, &universe, 1);
        let mut set = IsoStateSet::new(&indices);
        let state = |vec: Vec<(usize, usize, usize)>| -> BoundedState {
            let mut out = BoundedState::ZERO;
            for (x, y, z) in vec {
                out.set(indices.get("f", 0, &[x, y, z]), true);
            }
            out
        };

        assert!(set.insert(&state(vec![(0, 0, 0)])));
        assert!(!set.insert(&state(vec![(1, 0, 1)])));
        assert!(!set.insert(&state(vec![(2, 0, 2)])));
        assert!(!set.insert(&state(vec![(0, 1, 0)])));
        assert!(!set.insert(&state(vec![(1, 1, 1)])));
        assert!(!set.insert(&state(vec![(2, 1, 2)])));

        assert!(set.insert(&state(vec![(1, 0, 0)])));
        assert!(!set.insert(&state(vec![(1, 0, 0)])));
        assert!(!set.insert(&state(vec![(2, 0, 0)])));
        assert!(!set.insert(&state(vec![(1, 1, 0)])));
        assert!(!set.insert(&state(vec![(0, 1, 1)])));

        assert!(set.insert(&state(vec![(0, 0, 0), (0, 1, 0)])));
        assert!(!set.insert(&state(vec![(1, 0, 1), (1, 1, 1)])));
        assert!(set.insert(&state(vec![(0, 0, 1), (0, 1, 0)])));
        assert!(!set.insert(&state(vec![(1, 0, 0), (1, 1, 1)])));
        assert!(!set.insert(&state(vec![(0, 1, 1), (0, 0, 0)])));

        let source = "
sort s
immutable f(s, bool, s): bool
        ";
        let m = fly::parser::parse(source).unwrap();
        let universe = std::collections::HashMap::from([("s".to_string(), 3)]);
        let indices = Indices::new(m.signature, &universe, 1);
        let mut set = IsoStateSet::new(&indices);
        let state = |vec: Vec<(usize, usize, usize)>| -> BoundedState {
            let mut out = BoundedState::ZERO;
            for (x, y, z) in vec {
                out.set(indices.get("f", 0, &[x, y, z]), true);
            }
            out
        };

        assert!(set.insert(&state(vec![(0, 0, 0)])));
        assert!(!set.insert(&state(vec![(1, 0, 1)])));
        assert!(!set.insert(&state(vec![(2, 0, 2)])));
        assert!(set.insert(&state(vec![(0, 1, 0)])));
        assert!(!set.insert(&state(vec![(1, 1, 1)])));
        assert!(!set.insert(&state(vec![(2, 1, 2)])));

        assert!(set.insert(&state(vec![(1, 0, 0)])));
        assert!(!set.insert(&state(vec![(1, 0, 0)])));
        assert!(!set.insert(&state(vec![(2, 0, 0)])));

        assert!(set.insert(&state(vec![(1, 1, 0)])));
        assert!(!set.insert(&state(vec![(0, 1, 1)])));
    }
}
