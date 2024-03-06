// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! The interface that all bounded model checkers use.

use crate::quant_enum::*;
use fly::{semantics::*, transitions::*};
use thiserror::Error;

/// The result of a successful run of a bounded model checker
#[derive(Debug, PartialEq)]
pub enum CheckerAnswer<C> {
    /// The checker found a counterexample
    Counterexample(Vec<Model>),
    /// The checker did not find a counterexample
    Unknown,
    /// The checker found that the set of states stopped changing
    Convergence(C),
}

/// The result of an unsuccessful attempt to run a bounded model checker.
#[derive(Debug, PartialEq, Error)]
pub enum CheckerError {
    /// A sort existed in a term but not in the universe
    #[error("sort {0} not found in universe {1:#?}")]
    UnknownSort(String, UniverseBounds),
    /// See [`ExtractionError`]
    #[error("{0}")]
    ExtractionError(ExtractionError),
    /// See [`EnumerationError`]
    #[error("{0}")]
    EnumerationError(EnumerationError),

    // sat.rs specific
    /// The SAT solver failed
    #[error("solver failed, likely a timeout")]
    SatSolverFailed,

    // set.rs specific
    /// The translated formula was not a conjunction
    #[error("the set checker currently only handles initial conditions that are a conjunction")]
    InitNotConj,
    /// The transition system extraction found more than one transition relation
    #[error("the set checker currently only handles a single transition relation")]
    MultipleTrs,
    /// `Formula`s are single-vocabulary
    #[error("a transition contained a disjunction that contained a prime")]
    PrimeInFormula,
    /// We can't support unproven mutable axioms without post-guards
    #[error("an axiom that mentioned mutable relations couldn't be proven")]
    UnprovenMutableAxiom,
    /// Conflicting parallel guards
    #[error("found two parallel guards that conflict\n{0}\n{1}")]
    ParallelGuards(String, String),
    /// `STATE_LEN` is too small
    #[error("STATE_LEN is too small")]
    StateLenTooSmall,

    // smt.rs
    /// See solver::SolveError
    #[error("{0}")]
    SolverError(String),
}
