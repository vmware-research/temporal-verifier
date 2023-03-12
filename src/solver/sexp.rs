// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

use crate::fly::syntax::{BinOp, Binder, NOp, Quantifier, Sort, Term, UOp};
use crate::smtlib::sexp::{app, atom_s, sexp_l, Sexp};

pub fn sort(s: &Sort) -> Sexp {
    match s {
        Sort::Bool => atom_s("Bool"),
        Sort::Id(s) => atom_s(s),
    }
}

fn binder(b: &Binder) -> Sexp {
    app(&b.name, vec![sort(&b.sort)])
}

fn term_primes(t: &Term, num_primes: usize) -> Sexp {
    if !matches!(t, Term::UnaryOp(UOp::Prime, _) | Term::Id(_)) {
        assert_eq!(
            num_primes, 0,
            "by the time we convert to smtlib, the only primes allowed are over identifiers (t={t})"
        );
        // TODO(oded): simplify the conversion based on this assumption
    }
    let term = |t: &Term| term_primes(t, num_primes);
    match t {
        Term::Literal(false) => atom_s("false"),
        Term::Literal(true) => atom_s("true"),
        Term::Id(s) => atom_s(format!("{s}{}", "'".repeat(num_primes))),
        Term::App(f, p, args) => {
            let head = vec![term_primes(&Term::Id(f.clone()), p + num_primes)].into_iter();
            let args = args.iter().map(term);
            sexp_l(head.chain(args))
        }
        Term::UnaryOp(op, arg) => {
            match op {
                UOp::Not => app("not", vec![term(arg)]),
                UOp::Prime => {
                    assert!(
                        matches!(**arg, Term::UnaryOp(UOp::Prime, _) | Term::Id(_)),
                       "by the time we convert to smtlib, the only primes allowed are over identifiers (t={t})",
                    );
                    // TODO(oded): simplify the conversion based on this assumption
                    term_primes(arg, num_primes + 1)
                }
                // TODO: temporal stuff should be eliminated before here
                UOp::Always | UOp::Eventually | UOp::Next | UOp::Previously => {
                    panic!("attempt to encode a temporal formula for smt")
                }
            }
        }
        Term::BinOp(op, arg1, arg2) => {
            let args = vec![term(arg1), term(arg2)];
            match op {
                BinOp::Equals => app("=", args),
                BinOp::NotEquals => app("distinct", args),
                BinOp::Implies => app("=>", args),
                BinOp::Iff => app("=", args),
                BinOp::Until | BinOp::Since => {
                    panic!("attempt to encode a temporal formula for smt")
                }
            }
        }
        Term::NAryOp(op, args) => {
            let args = args.iter().map(term).collect::<Vec<_>>();
            match op {
                NOp::And => app("and", args),
                NOp::Or => app("or", args),
            }
        }
        Term::Ite { cond, then, else_ } => app("ite", vec![term(cond), term(then), term(else_)]),
        Term::Quantified {
            quantifier,
            binders,
            body,
        } => {
            let quantifier = match quantifier {
                Quantifier::Forall => "forall",
                Quantifier::Exists => "exists",
            };
            let binders = Sexp::List(binders.iter().map(binder).collect());
            let body = term(body);
            app(quantifier, vec![binders, body])
        }
    }
}

pub fn term(t: &Term) -> Sexp {
    term_primes(t, 0)
}

pub fn negated_term(t: &Term) -> Sexp {
    app("not", [term(t)])
}
