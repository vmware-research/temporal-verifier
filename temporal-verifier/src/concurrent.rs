// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Example of using solvers concurrently using rayon.
//!
//! The solver code itself is largely unaware of concurrency. The `conf` from
//! which a solver can be created is shared among threads via a reference, and
//! then each thread creates an owned `Solver` instance to operate on (which is
//! not thread-safe).
//!
//! The example uses rayon's `par_map` to simplify spawning and joining all the
//! tasks, but adds a bit of complexity by implementing a form of task
//! cancellation if one of the parallel operations gets a Sat response from the
//! solver.

#[cfg(test)]
mod tests {
    use std::{collections::HashMap, fs, sync::Mutex};

    use rayon::prelude::*;

    use fly::syntax::{Proof, Term, ThmStmt};
    use fly::term::prime::Next;
    use solver::{
        backends::{GenericBackend, SolverType},
        conf::SolverConf,
        solver_path, SatResp,
    };
    use verify::safety::InvariantAssertion;

    struct Task {
        cancelled_m: Mutex<bool>,
    }

    impl Task {
        /// Create a new tracker for a task.
        pub fn new() -> Self {
            return Self {
                cancelled_m: Mutex::new(false),
            };
        }

        /// Mark this task cancelled.
        pub fn cancel(&self) {
            *self.cancelled_m.lock().unwrap() = true;
        }

        /// Check if the task
        pub fn is_cancelled(&self) -> bool {
            *self.cancelled_m.lock().unwrap()
        }
    }

    #[test]
    fn test_concurrent_verify() {
        let file =
            fs::read_to_string("../examples/consensus_epr.fly").expect("could not find test file");
        let m = fly::parser::parse(&file).expect("could not parse test file");

        let assumes: Vec<&Term> = m
            .statements
            .iter()
            .filter_map(|s| match s {
                ThmStmt::Assume(t) => Some(t),
                _ => None,
            })
            .collect();
        let pf: &Proof = m
            .statements
            .iter()
            .filter_map(|s| match s {
                ThmStmt::Assert(pf) => Some(pf),
                _ => None,
            })
            .next()
            .expect("should have one assertion");
        let inv_assert = InvariantAssertion::for_assert(&m.signature, &assumes, pf)
            .expect("should be an invariant assertion");

        let backend = GenericBackend::new(SolverType::Z3, &solver_path("z3"));
        let conf = SolverConf { backend, tee: None };

        // we'll assume proof_inv (all the invariants) in the pre state and try
        // to prove Next::prime(inv) in the post state for each proof invariant
        // separately
        let proof_inv = Term::and(pf.invariants.iter().map(|pf| pf.x.clone()));
        let task = Task::new();
        // rayon provides .par_iter(), which performs the invariant checks in
        // parallel; then we gather up a Vec of all the results due to the
        // `.collect()`.
        //
        // The `task` tracking above allows one of the parallel checks, if it
        // finds that some invariant is not inductive, to cancel other checks.
        // Note that this cannot terminate `solver.check_sat` calls that have
        // already started (we don't track any handle to the solver for
        // cancellation), but it can prevent checks that haven't started yet.
        //
        // Note that this particular form of cancellation is really only useful
        // for automated usage, not for verifying user-provided invariants; it's
        // useful to provide the user with feedback on all the invariants that
        // are incorrect (or at least to wait a while for these results).
        let results = pf
            .invariants
            .par_iter()
            .map(|inv| {
                let inv = &inv.x;
                if task.is_cancelled() {
                    return None;
                }
                // not bothering to check initiation
                let mut solver = conf.solver(&m.signature, 2);
                solver.assert(&inv_assert.next).expect("error in solver");
                solver
                    .assert(&inv_assert.assumed_inv)
                    .expect("error in solver");
                solver
                    .assert(&Next::new(&m.signature).prime(&inv_assert.assumed_inv))
                    .expect("error in solver");
                solver.assert(&proof_inv).expect("error in solver");
                solver
                    .assert(&Term::negate(Next::new(&m.signature).prime(inv)))
                    .expect("error in solver");
                let resp = solver.check_sat(HashMap::new());
                // if this check fails, don't start new checks
                if matches!(resp, Ok(SatResp::Unsat) | Err(_)) {
                    task.cancel();
                }
                return Some(resp);
            })
            // eliminate the `None` results from cancelled tasks
            .flatten()
            .collect::<Vec<Result<_, _>>>();
        for r in results {
            match r {
                Ok(resp) => assert!(resp == SatResp::Unsat, "invariant is not inductive"),
                Err(err) => panic!("something went wrong in solver: {err}"),
            }
        }
    }
}
