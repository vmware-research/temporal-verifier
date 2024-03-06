// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! A bounded model checker for flyvy programs using the [CaDiCaL][cadical] SAT solver.
//!
//! [cadical]: https://fmv.jku.at/cadical/

use crate::{checker::*, indices::*, quant_enum::*};
use cadical::Solver;
use fly::{semantics::*, syntax::*, transitions::*};

/// Check a given Module out to some depth.
/// This function assumes that the module has been typechecked.
/// The checker ignores proof blocks.
pub fn check(
    module: &Module,
    universe: &UniverseBounds,
    depth: usize,
    print_timing: bool,
) -> Result<CheckerAnswer<()>, CheckerError> {
    for sort in &module.signature.sorts {
        if !universe.contains_key(sort) {
            return Err(CheckerError::UnknownSort(sort.clone(), universe.clone()));
        }
    }

    for relation in &module.signature.relations {
        if relation.sort != Sort::Bool {
            panic!("non-bool relations in checker (use Module::convert_non_bool_relations)")
        }
    }

    if !module.defs.is_empty() {
        panic!("definitions in checker (use Module::inline_defs)")
    }

    let d = extract(module).map_err(CheckerError::ExtractionError)?;
    let inits = d.inits.iter().chain(&d.axioms).cloned();
    let transitions = d
        .transitions
        .iter()
        .chain(d.mutable_axioms(&module.signature.relations))
        .cloned();
    let safeties = d.proofs.iter().map(|proof| proof.safety.x.clone());

    let mut indices = Indices::new(module.signature.clone(), universe, depth + 1);

    let translate = |term| {
        enumerate_quantifiers(&term, &module.signature, universe)
            .map_err(CheckerError::EnumerationError)
    };

    println!("starting translation...");
    let translation = std::time::Instant::now();

    let init = translate(Term::and(inits))?;
    let tr = translate(Term::and(transitions))?;
    let not_safe = Enumerated::Not(Box::new(translate(Term::and(safeties))?));

    let mut program = vec![init];
    for i in 0..depth {
        program.push(tr.clone().prime(i));
    }
    program.push(not_safe.prime(depth));

    let cnf = tseytin(&Enumerated::And(program), &mut indices);

    if print_timing {
        println!(
            "translation finished in {:0.1}s",
            translation.elapsed().as_secs_f64()
        );
    }

    println!("starting search...");
    let search = std::time::Instant::now();

    let mut solver: Solver = Default::default();
    for clause in &cnf {
        let cadical_clause = clause
            .iter()
            .map(|l| (l.var as i32 + 1) * if l.pos { 1 } else { -1 });
        solver.add_clause(cadical_clause);
    }

    let answer = match solver.solve() {
        None => Err(CheckerError::SatSolverFailed),
        Some(false) => Ok(CheckerAnswer::Unknown),
        Some(true) => Ok(CheckerAnswer::Counterexample(
            (0..indices.num_mutable_copies)
                .map(|primes| {
                    indices.model(primes, |i| {
                        solver.value(i as i32 + 1).unwrap_or(false) as Element
                    })
                })
                .collect(),
        )),
    };

    if print_timing {
        println!("search finished in {:0.1}s", search.elapsed().as_secs_f64());
    }

    answer
}

/// A propositional literal, composed of an index and whether it is positive.
#[derive(Clone, Debug, PartialEq)]
pub struct Literal {
    var: usize,
    pos: bool,
}
type Clause = Vec<Literal>;
/// A propositional CNF.
pub type Cnf = Vec<Clause>;

impl Literal {
    fn t(var: usize) -> Literal {
        Literal { var, pos: true }
    }
    fn f(var: usize) -> Literal {
        Literal { var, pos: false }
    }
    /// Convert this literal to a CaDiCaL literal respreseted as a signed integer.
    pub fn as_int(&self) -> i32 {
        (self.var as i32 + 1) * if self.pos { 1 } else { -1 }
    }
}

/// Perform the Tseytin transformation on the given term.
pub fn tseytin(term: &Enumerated, indices: &mut Indices) -> Cnf {
    fn inner(term: &Enumerated, indices: &mut Indices, out: &mut Cnf) -> usize {
        let mut go = |term| inner(term, indices, out);
        match term {
            Enumerated::And(terms) => {
                let olds: Vec<_> = terms.iter().map(go).collect();
                let new = indices.var();
                for old in &olds {
                    out.push(vec![Literal::t(*old), Literal::f(new)]);
                }
                let mut clause: Vec<_> = olds.into_iter().map(Literal::f).collect();
                clause.push(Literal::t(new));
                out.push(clause);
                new
            }
            Enumerated::Or(terms) => {
                let olds: Vec<_> = terms.iter().map(go).collect();
                let new = indices.var();
                for old in &olds {
                    out.push(vec![Literal::f(*old), Literal::t(new)]);
                }
                let mut clause: Vec<_> = olds.into_iter().map(Literal::t).collect();
                clause.push(Literal::f(new));
                out.push(clause);
                new
            }
            Enumerated::Not(term) => {
                let old = go(term);
                let new = indices.var();
                out.push(vec![Literal::t(old), Literal::t(new)]);
                out.push(vec![Literal::f(old), Literal::f(new)]);
                new
            }
            Enumerated::Eq(left, right) => {
                let a = go(left);
                let b = go(right);
                let c = indices.var();
                out.push(vec![Literal::f(a), Literal::f(b), Literal::t(c)]);
                out.push(vec![Literal::f(a), Literal::t(b), Literal::f(c)]);
                out.push(vec![Literal::t(a), Literal::f(b), Literal::f(c)]);
                out.push(vec![Literal::t(a), Literal::t(b), Literal::t(c)]);
                c
            }
            Enumerated::App(relation, primes, elements) => indices.get(relation, *primes, elements),
        }
    }

    let mut out = vec![];
    let var = inner(term, indices, &mut out);
    out.push(vec![Literal::t(var)]);
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use fly::sorts::sort_check_module;
    use std::collections::HashMap;

    #[test]
    fn checker_sat_basic() -> Result<(), CheckerError> {
        let source = include_str!("../../temporal-verifier/tests/examples/basic2.fly");

        let mut module = fly::parser::parse(source).unwrap();
        sort_check_module(&mut module).unwrap();
        let universe = HashMap::from([]);

        assert_eq!(CheckerAnswer::Unknown, check(&module, &universe, 0, false)?);
        assert!(matches!(
            check(&module, &universe, 1, false)?,
            CheckerAnswer::Counterexample(..),
        ));

        Ok(())
    }

    #[test]
    fn checker_sat_lockserver() -> Result<(), CheckerError> {
        let source = include_str!("../../temporal-verifier/examples/lockserver.fly");

        let mut module = fly::parser::parse(source).unwrap();
        sort_check_module(&mut module).unwrap();
        let universe = HashMap::from([("node".to_string(), 2)]);

        assert_eq!(
            CheckerAnswer::Unknown,
            check(&module, &universe, 10, false)?
        );

        Ok(())
    }

    #[test]
    fn checker_sat_lockserver_buggy() -> Result<(), CheckerError> {
        let source = include_str!("../../temporal-verifier/tests/examples/lockserver_buggy.fly");

        let mut module = fly::parser::parse(source).unwrap();
        sort_check_module(&mut module).unwrap();
        let universe = HashMap::from([("node".to_string(), 2)]);

        let bug = check(&module, &universe, 12, false)?;
        assert!(matches!(bug, CheckerAnswer::Counterexample(..)));

        let too_short = check(&module, &universe, 11, false)?;
        assert_eq!(CheckerAnswer::Unknown, too_short);

        Ok(())
    }

    #[test]
    fn checker_sat_consensus() -> Result<(), CheckerError> {
        let source = include_str!("../../temporal-verifier/examples/consensus.fly");

        let mut module = fly::parser::parse(source).unwrap();
        sort_check_module(&mut module).unwrap();
        let universe = std::collections::HashMap::from([
            ("node".to_string(), 2),
            ("quorum".to_string(), 2),
            ("value".to_string(), 2),
        ]);

        assert_eq!(
            CheckerAnswer::Unknown,
            check(&module, &universe, 10, false)?
        );

        Ok(())
    }

    #[test]
    fn checker_sat_immutability() -> Result<(), CheckerError> {
        let source =
            include_str!("../../temporal-verifier/tests/examples/success/immutability.fly");
        let mut module = fly::parser::parse(source).unwrap();
        sort_check_module(&mut module).unwrap();
        let universe = std::collections::HashMap::new();
        assert_eq!(
            CheckerAnswer::Unknown,
            check(&module, &universe, 10, false)?
        );
        Ok(())
    }
}
