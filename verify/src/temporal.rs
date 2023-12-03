// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Processing of temporal formulas, useful for liveness to safety reduction
//! (may become a separate crate later)

use fly::{
    printer,
    syntax::{Span, Spanned},
};
use thiserror::Error;

use fly::syntax::{BinOp, Binder, RelationDecl, Signature, Sort, Term, UOp};

use crate::safety::InvariantAssertion;

/// A formula or term with free variables, fixing an order and sorts for the
/// free variables. This is used in the tableaux construction and also for
/// prophecy formulas.
#[derive(Debug, Clone)]
pub struct TermWithFreeVariables {
    /// Variables that appear in the formula
    pub binders: Vec<Binder>,
    /// The formula
    pub body: Term,
}

/// The declaration possibly multiple witnesses (each may be a constant or a
/// function).
///
/// Arguments must be a growing sequence. For example c, f(X:s1), g(X:s1, Y:s2)
/// is fine but f(X:s1),g(Y:s2) is not.
///
/// The semantics of c, f(X:s1), g(X:s1, Y:s2) witnessing r(c,f(X),g(X,Y),X,Y) is:
/// (exists C. forall X. exists F. forall Y. exists G. r(C,F,G,X,Y)) -> forall X,Y. r(c,f(X),g(X,Y),X,Y)
#[derive(Debug, Clone)]
pub struct WitnessDecl {
    /// each witness is (name, args, sort)
    pub witnesses: Vec<(String, Vec<Binder>, Sort)>,
    /// all witnesses share a body
    pub body: Term,
}

/// A declaration of function saving another formula (can be of any sort)
#[allow(missing_docs)]
#[derive(Debug, Clone)]
pub struct SavesDecl {
    pub name: String,
    pub binders: Vec<Binder>,
    pub sort: Sort,
    pub body: Term,
}

/// A declaration of relation waiting for a formula
#[allow(missing_docs)]
#[derive(Debug, Clone)]
pub struct WaitsDecl {
    pub name: String,
    pub binders: Vec<Binder>,
    pub body: Term,
}

/// A temporal property assertion to be proven by liveness to safety
#[derive(Debug, Clone)]
pub struct TemporalAssertion {
    /// A signature with sorts, mutable, and immutable symbols
    sig: Signature,

    /// Axioms over the immutable symbols (first-order zero-state formulas)
    pub axioms: Vec<Term>,

    /// Assumed invariants are similar to axioms but over mutable symbols too
    /// (first-order one-state formulas)
    pub assumed_invariants: Vec<Term>,

    /// Formula specifying the initial states (first-order one-state formulas)
    pub init: Term,

    /// Formula specifying the transition relation (first-order two-state formula)
    ///
    /// TODO(oded): this should be separate transitions, probably with a
    /// Transition datatype.
    pub transition_relation: Term,

    /// Temporal properties assumed (temporal formulas)
    pub temporal_assumptions: Vec<Term>,

    /// The proof goal (temporal formula)
    pub temporal_property: Term,

    /// Bound on number of abstract fair cycles for the liveness to safety
    /// construction
    pub max_cycles: usize,

    /// Prophecy formulas for the liveness to safety construction
    pub prophecy: Vec<TermWithFreeVariables>,

    /// Witnesses for the liveness to safety construction (see [`SavesDecl`])
    pub witnesses: Vec<WitnessDecl>,

    /// Formulas to save in the liveness to safety construction (see [`SavesDecl`])
    pub saves: Vec<SavesDecl>,

    /// Formulas to wait for in the liveness to safety construction (see [`WaitsDecl`])
    pub waits: Vec<WaitsDecl>,

    /// Invariants used to prove safety of the result of the liveness to safety construction
    pub invariants: Vec<Term>,
}

/// An error that occured in the liveness to safety transformation
#[derive(Error, Debug)]
pub enum TemporalError {
    /// Assertion is not a safety property
    #[error("assertion is not of the form (always p)")]
    NotSafety,
    /// Proof invariant mentioned more than one timestep
    #[error("proof invariant is not a well-formed single-state fomula")]
    BadProofInvariant,
}

impl TemporalAssertion {
    /// Perform the liveness to safety transformation to get an InvariantAssertion.
    ///
    /// TODO(oded): should this return InvariantAssertion or something else?
    /// TODO(oded): what to do about the spans?
    pub fn livenss_to_safety(&self) -> Result<InvariantAssertion, TemporalError> {
        // TODO(oded): start with some type checking assertions?

        let mut sig = self.sig.clone();

        let a_sort = |sort_name: &str| format!("%a_{sort_name}");
        let b_sort = |sort_name: &str| format!("%b_{sort_name}");
        let d_sort = |sort_name: &str| format!("%d_{sort_name}");

        // Add a_sort, b_sort, d_sort unary relations for each sort
        for sort in &self.sig.sorts {
            for name in [a_sort(sort), b_sort(sort), d_sort(sort)] {
                sig.relations.push(RelationDecl {
                    mutable: true,
                    name,
                    args: vec![Sort::uninterpreted(sort)],
                    sort: Sort::Bool,
                });
            }
        }

        // Use terms_by_sort to initialize and also update d_sort
        // TODO(oded): maybe we want to allow depths > 0 here
        let ground_terms_by_sort = self.sig.terms_by_sort(&[], Some(0), false);

        // Initialize d according to the ground terms:
        //
        // forall X:sort. d_sort(X) <-> (X = g_1 | ... | X = g_n)
        // where g_1,...,g_n are ground terms for sort
        let mut d_init: Vec<Term> = vec![];
        for (sort, ground_terms) in self.sig.sorts.iter().zip(&ground_terms_by_sort) {
            let binder = Binder::new("%X", sort);
            let x = Term::id(&binder.name);
            let lhs = Term::app(&d_sort(sort), 0, [&x]);
            let rhs = Term::or(ground_terms.iter().map(|g| Term::equals(&x, g)));
            d_init.push(Term::forall([binder], Term::iff(&lhs, &rhs)));
        }

        // Compute update for d:
        //
        // forall X:sort. d_sort'(X) <-> (d_sort(X) | X = g_1' | ... | X = g_n')
        // where g_1,...,g_n are ground terms for sort
        //
        // TODO(oded): we also need to add transition inputs to $d
        //
        // TODO(oded): we could use a less deterministic update, which basically
        // would make d_init an assumed invariant, and then d_update will just
        // say d monotonically grows and that it contains transition inputs.
        let mut d_update: Vec<Term> = vec![];
        for (sort, ground_terms) in self.sig.sorts.iter().zip(&ground_terms_by_sort) {
            let binder = Binder::new("%X", sort);
            let x = Term::id(&binder.name);
            let lhs = Term::app(&d_sort(sort), 1, [&x]);
            let rhs = Term::or(
                [Term::app(&d_sort(sort), 0, [&x])].into_iter().chain(
                    ground_terms
                        .iter()
                        .map(|g| Term::equals(&x, Term::prime(g))),
                ),
            );
            d_update.push(Term::forall([binder], Term::iff(&lhs, &rhs)));
        }

        // Initialize a_sort and b_sort to be empty
        let mut ab_init: Vec<Term> = vec![];
        for sort in self.sig.sorts.iter() {
            for name in [a_sort(sort), b_sort(sort)] {
                let binder = Binder::new("%X", sort);
                let x = Term::id(&binder.name);
                ab_init.push(Term::forall([binder], Term::not(Term::app(&name, 0, [&x]))));
            }
        }

        // Collect temporal subformulas from temporal_assumptions,
        // temporal_property, prophecy, saves, and waits
        let mut temporal_subformulas: Vec<TermWithFreeVariables> = vec![];
        let mut worklist: Vec<TermWithFreeVariables> = vec![];

        // TODO(oded): assert that self.temporal_assumptions and
        // self.temporal_property are closed
        //
        // TODO(oded): we should normalize away everything except until and
        // since, for now we should not support prime and next here. for now,
        // the following code asserts that the temporal formulas only contain
        // until and since, and no other temporal operators or primes
        //
        // TODO(oded): maybe normalize to NNF or some other normalization
        //
        // TODO(oded): right now we don't check formulas for any kind of
        // equivalence beyond syntactic equality, but we should do something
        // better, and maybe eventually  use a solver as a quick check
        //
        // TODO(oded): Right now, both in subformulas and in worklist, there
        // might be some variables that are actually unused. This can happen
        // e.g. if we start with X,Y. r(X) until q(Y). We should fix this and
        // maintain the invariant that at least in subformulas, all the
        // variables are used.

        // Add temporal assumptions and temporal property to worklist
        worklist.extend(
            self.temporal_assumptions
                .iter()
                .chain([&self.temporal_property])
                .map(|f| TermWithFreeVariables {
                    binders: vec![],
                    body: f.clone(),
                }),
        );

        // Add prophecy formulas to worklist
        worklist.extend(self.prophecy.clone());
        assert!(self.witnesses.is_empty()); // TODO(oded): add support for witnesses. note we'll need to consider both the formulas with exists and the formulas with the witnesses

        // Add saved terms and formulas to worklist
        worklist.extend(self.saves.iter().map(|s| TermWithFreeVariables {
            binders: s.binders.clone(),
            body: s.body.clone(),
        }));

        // Add (true until phi) to worklist for every phi that is waited for
        worklist.extend(self.waits.iter().map(|w| TermWithFreeVariables {
            binders: w.binders.clone(),
            body: Term::until(&Term::literal(true), &w.body),
        }));

        // Collect all temporal subformulas from worklist into temporal_subformulas
        while let Some(TermWithFreeVariables { binders, body }) = worklist.pop() {
            match body {
                Term::Literal(_) => {}
                Term::Id(_) => {}
                Term::App(_, n_primes, args) => {
                    // Recurse on terms to assert there are no primes. this can
                    // be eliminated once we check this somewhere else (e.g.,
                    // above)
                    assert_eq!(n_primes, 0);
                    worklist.extend(args.into_iter().map(|t| TermWithFreeVariables {
                        binders: binders.clone(),
                        body: t,
                    }));
                }
                Term::UnaryOp(UOp::Not, t) => worklist.push(TermWithFreeVariables {
                    binders: binders.clone(),
                    body: *t,
                }),
                Term::UnaryOp(UOp::Always, _)
                | Term::UnaryOp(UOp::Eventually, _)
                | Term::UnaryOp(UOp::Next, _)
                | Term::UnaryOp(UOp::Previous, _)
                | Term::UnaryOp(UOp::Prime, _) => {
                    panic!("Unexpected temporal operator: {body}")
                }
                Term::BinOp(BinOp::Equals, t1, t2)
                | Term::BinOp(BinOp::Iff, t1, t2)
                | Term::BinOp(BinOp::Implies, t1, t2)
                | Term::BinOp(BinOp::NotEquals, t1, t2) => {
                    worklist.extend([
                        TermWithFreeVariables {
                            binders: binders.clone(),
                            body: *t1,
                        },
                        TermWithFreeVariables {
                            binders: binders.clone(),
                            body: *t2,
                        },
                    ]);
                }
                Term::BinOp(op @ (BinOp::Since | BinOp::Until), t1, t2) => {
                    temporal_subformulas.push(TermWithFreeVariables {
                        binders: binders.clone(),
                        body: Term::BinOp(op, t1.clone(), t2.clone()),
                    });
                    worklist.extend([
                        TermWithFreeVariables {
                            binders: binders.clone(),
                            body: *t1,
                        },
                        TermWithFreeVariables {
                            binders: binders.clone(),
                            body: *t2,
                        },
                    ]);
                }
                Term::NAryOp(_, ts) => {
                    worklist.extend(ts.into_iter().map(|t| TermWithFreeVariables {
                        binders: binders.clone(),
                        body: t,
                    }));
                }
                Term::Ite { cond, then, else_ } => {
                    worklist.extend([
                        TermWithFreeVariables {
                            binders: binders.clone(),
                            body: *cond,
                        },
                        TermWithFreeVariables {
                            binders: binders.clone(),
                            body: *then,
                        },
                        TermWithFreeVariables {
                            binders: binders.clone(),
                            body: *else_,
                        },
                    ]);
                }
                Term::Quantified {
                    quantifier: _,
                    binders,
                    body,
                } => {
                    // carefully support shadowing, e.g.: X:t1. r(X) until forall X:t2. q(X)
                    let vs: Vec<Binder> = binders
                        .iter()
                        .filter(|v| binders.iter().all(|b| v.name != b.name))
                        .chain(binders.iter())
                        .cloned()
                        .collect();
                    worklist.push(TermWithFreeVariables {
                        binders: vs,
                        body: *body,
                    })
                }
            }
        }

        // Add tableaux construction for temporal formulas

        // TODO(oded): right now this only supports Until and Since. We should
        // also support Previos and Next

        let mut tableaux_invariants: Vec<Term> = vec![];
        let mut tableaux_transition: Vec<Term> = vec![];
        for TermWithFreeVariables { binders, body } in &temporal_subformulas {
            // Add temporal relation to sig
            let print_variables = if binders.is_empty() {
                "".to_string()
            } else {
                binders
                    .iter()
                    .map(printer::binder)
                    .collect::<Vec<_>>()
                    .join(", ")
                    + ". "
            };
            let print_body = printer::term(body);
            let relation_name = format!("%{{{print_variables}{print_body}}}"); // TODO(oded): do we put r" and " inside the name or not?
            sig.relations.push(RelationDecl {
                mutable: true,
                name: relation_name.clone(),
                args: binders.iter().map(|b| b.sort.clone()).collect(),
                sort: Sort::Bool,
            });

            // Add appropriate formulas to tableaux_invariants and tableaux_tr
            let close = |t: Term| Term::forall(binders.clone(), t);
            match body {
                Term::BinOp(BinOp::Until, p, q) => {
                    let p = p.as_ref(); // TODO(oded): not sure if this is the nicest, but otherwise p doesn't have Into<Term>, unless we implement that for &Box<Term>
                    let q = q.as_ref();
                    let args: Vec<Term> = binders.iter().map(|b| Term::id(&b.name)).collect();
                    let (p_until_q, p_until_q_prime) = if args.is_empty() {
                        // TODO(oded): eliminate once Term:app is better (see TODO there)
                        (
                            Term::id(&relation_name),
                            Term::prime(Term::id(&relation_name)),
                        )
                    } else {
                        (
                            Term::app(&relation_name, 0, &args),
                            Term::app(&relation_name, 1, &args),
                        )
                    };

                    // Add `q -> (p until q)` to tableaux_invariants
                    tableaux_invariants.push(close(Term::implies(q, &p_until_q)));
                    // Add `(p until q) -> (p | q)` to tableaux_invariants
                    tableaux_invariants.push(close(Term::implies(&p_until_q, Term::or([p, q]))));

                    // Add `(p until q) <-> (q | (p & (p until q)'))` to
                    // tableaux_transition
                    //
                    // TODO(oded): this can be weakened due to the invaraints,
                    // but not sure what's better. The weakened version would
                    // be:
                    // * !q & (p until q) -> (p until q)'
                    // * p & (p until q)' -> (p until q)
                    tableaux_transition.push(close(Term::iff(
                        &p_until_q,
                        &Term::or([q, &Term::and([p, &p_until_q_prime])]),
                    )));
                }
                Term::BinOp(BinOp::Since, p, q) => {
                    let p = p.as_ref(); // TODO(oded): not sure if this is the nicest, but otherwise p doesn't have Into<Term>, unless we implement that for &Box<Term>
                    let q = q.as_ref();
                    let args: Vec<Term> = binders.iter().map(|b| Term::id(&b.name)).collect();
                    let (p_since_q, p_since_q_prime) = if args.is_empty() {
                        // TODO(oded): eliminate once Term:app is better (see TODO there)
                        (
                            Term::id(&relation_name),
                            Term::prime(Term::id(&relation_name)),
                        )
                    } else {
                        (
                            Term::app(&relation_name, 0, &args),
                            Term::app(&relation_name, 1, &args),
                        )
                    };

                    // Add `q -> (p since q)` to tableaux_invariants
                    tableaux_invariants.push(close(Term::implies(q, &p_since_q)));
                    // Add `(p since q) -> (p | q)` to tableaux_invariants
                    tableaux_invariants.push(close(Term::implies(&p_since_q, Term::or([p, q]))));

                    // Add `(p since q)' <-> (q' | (p' & (p since q)))` to
                    // tableaux_transition
                    //
                    // TODO(oded): this can be weakened due to the invaraints,
                    // but not sure what's better. The weakened version would
                    // be:
                    // * !q' & (p since q)' -> (p since q)
                    // * p' & (p since q) -> (p since q)'
                    tableaux_transition.push(close(Term::iff(
                        &p_since_q_prime,
                        &Term::or([Term::prime(q), Term::and([&Term::prime(p), &p_since_q])]),
                    )));
                }
                _ => {
                    panic!("Unexpected term: {body}");
                }
            }
        }

        // add $cycle_0,...,cycle_{max_cycles} to signature
        let cycle = |i: usize| {
            debug_assert!(i <= self.max_cycles);
            Term::id(&format!("$cycle_{i}"))
        };
        sig.relations
            .extend((0..(self.max_cycles + 1)).map(|i| RelationDecl {
                mutable: true,
                name: format!("$cycle_{i}"),
                args: vec![],
                sort: Sort::Bool,
            }));

        let cycle_safety = Term::or((0..(self.max_cycles + 1)).map(cycle));

        let mut cycle_init = vec![cycle(0)];
        for i in 1..(self.max_cycles + 1) {
            cycle_init.push(Term::not(cycle(i)));
        }
        let mut cycle_transition: Vec<Term> = vec![Term::true_()];

        // Increase "$cycle"
        cycle_transition.push(Term::not(Term::prime(cycle(0))));
        for i in 1..(self.max_cycles + 1) {
            cycle_transition.push(Term::iff(Term::prime(cycle(i)), cycle(i - 1)));
        }

        // Check that the current state is identical to the saved state in the
        // current abstraction
        // TODO

        // Wait for all the waiting formulas
        for w in &self.waits {
            cycle_transition.push(Term::forall(
                w.binders.clone(), // TODO(oded): remove clone when possible
                // TODO(oded): this doesn't handle binders.is_empty(), should
                // make Term:app better instead of making this code ugly
                Term::not(Term::app(
                    &w.name,
                    0,
                    w.binders.iter().map(|b| Term::id(&b.name)),
                )),
            ));
        }

        // Update waiting formulas
        for w in &self.waits {
            let args_in_d = w.binders.iter().filter_map(|b| match &b.sort {
                Sort::Bool => None,
                Sort::Uninterpreted(sort_name) => {
                    Some(Term::app(&d_sort(sort_name), 0, [Term::id(&b.name)]))
                }
            });
            cycle_transition.push(Term::forall(
                w.binders.clone(), // TODO(oded): remove clone when possible
                // TODO(oded): this doesn't handle binders.is_empty(), should
                // make Term:app better instead of making this code ugly
                Term::iff(
                    Term::app(&w.name, 1, w.binders.iter().map(|b| Term::id(&b.name))),
                    Term::and(args_in_d.chain([Term::until(Term::true_(), w.body.clone())])), // TODO(oded): this should be a tableaux relation, not a temporal formula
                ),
            ));
        }

        // Update $a and $sa and leave $d unchaged
        for sort_name in sig.sorts.iter() {
            let sort = Sort::uninterpreted(sort_name);
            let binder = Binder::new("%X", &sort);
            let x = Term::id("%X");
            // TODO(oded): move these magic strings for d,a,sd to once place
            let d_sort = format!("$d_{sort}");
            let a_sort = format!("$a_{sort}");
            let sd_sort = format!("$sd_{sort}");
            // update a from sd
            cycle_transition.push(Term::forall(
                [binder.clone()], // TODO(oded): I think we should make Binder (and Sort) impl From<&Binder> (and From<&Sort>) similar to what we do for Term, and then we should remove clone here
                Term::iff(Term::app(&a_sort, 1, [&x]), Term::app(&sd_sort, 0, [&x])),
            ));

            // update sd from d
            cycle_transition.push(Term::forall(
                [binder.clone()], // TODO(oded): remove clone
                Term::iff(Term::app(&sd_sort, 1, [&x]), Term::app(&d_sort, 0, [&x])),
            ));

            // keep d the same
            cycle_transition.push(Term::forall(
                [binder.clone()], // TODO(oded): remove clone
                Term::iff(Term::app(&d_sort, 1, [&x]), Term::app(&d_sort, 0, [&x])),
            ));
        }

        // Update saved state
        // TODO

        // TODO: Convert invariants from temporal formulas to tableaux relations

        Ok(InvariantAssertion {
            sig,
            init: Term::and(cycle_init.into_iter().chain(d_init).chain(ab_init)),
            next: Term::or([
                Term::and(
                    [self.transition_relation.clone()]
                        .into_iter()
                        .chain(d_update)
                        .chain(tableaux_transition),
                ),
                Term::and(cycle_transition),
            ]),
            assumed_inv: Term::and(tableaux_invariants),
            inv: Spanned {
                x: cycle_safety,
                span: Span { start: 0, end: 0 },
            },
            proof_invs: vec![],
        })
    }
}

#[cfg(test)]
mod tests {
    use fly::parser::{parse_signature, term};

    use crate::temporal::TemporalAssertion;

    #[test]
    fn test_livenss_to_safety() {
        let a = TemporalAssertion {
            sig: parse_signature(
                r#"
                sort t

                mutable c: t

                mutable p: bool
                "#,
            ),
            axioms: vec![],
            assumed_invariants: vec![],
            init: term("p"),
            transition_relation: term("p' <-> p"),
            temporal_assumptions: vec![],
            // temporal_property: term("always p"),
            temporal_property: term("!(true until !p)"),
            max_cycles: 0,
            prophecy: vec![],
            witnesses: vec![],
            saves: vec![],
            waits: vec![],
            invariants: vec![term("p")],
        };

        println!("{a:?}");
        let s = a.livenss_to_safety().unwrap();
        println!("\n\n\n{s:?}\n\n\n");
        println!("\ninit:\n{}\n", s.init);
        println!("\nnext:\n{}\n", s.next);
        println!("\nassumed_inv:\n{}\n", s.assumed_inv);
        println!("\ninv:\n{}\n", s.inv.x);
    }
}
