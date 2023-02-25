// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Perform substitutions of Id terms by other terms.

use std::collections::HashMap;

use crate::fly::syntax::Term;

pub type Substitution = HashMap<String, Term>;

/// Perform a substitution over a quantifier-free term.
pub fn substitute_qf(term: &Term, substitution: &Substitution) -> Term {
    match term {
        Term::Id(s) => {
            if substitution.contains_key(s) {
                substitution[s].clone()
            } else {
                Term::Id(s.clone())
            }
        }

        Term::App(f, p, args) => Term::App(
            f.clone(),
            *p,
            args.iter()
                .map(|a| substitute_qf(a, substitution))
                .collect(),
        ),

        Term::UnaryOp(op, arg) => Term::UnaryOp(*op, Box::new(substitute_qf(arg, substitution))),

        Term::BinOp(op, arg1, arg2) => Term::BinOp(
            *op,
            Box::new(substitute_qf(arg1, substitution)),
            Box::new(substitute_qf(arg2, substitution)),
        ),

        Term::NAryOp(op, args) => Term::NAryOp(
            *op,
            args.iter()
                .map(|a| substitute_qf(a, substitution))
                .collect(),
        ),

        Term::Ite { cond, then, else_ } => Term::Ite {
            cond: Box::new(substitute_qf(cond, substitution)),
            then: Box::new(substitute_qf(then, substitution)),
            else_: Box::new(substitute_qf(else_, substitution)),
        },

        _ => panic!("Quantifier-free substitution was given quantifier term"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fly::parser::parse_term;

    #[test]
    fn test_subst_qf() {
        let x = Term::Id("x".to_string());
        let y = Term::Id("y".to_string());

        let t1 = parse_term(&"(x | z) -> !y").expect("parser error.");
        let t1_subx = parse_term(&"(y | z) -> !y").expect("parser error.");
        let t1_suby = parse_term(&"(x | z) -> !x").expect("parser error.");
        let t1_subt = parse_term(&"(((x | z) -> !y) | y) -> !x").expect("parser error.");

        let mut subx = Substitution::new();
        subx.insert("x".to_string(), y.clone());
        let mut suby = Substitution::new();
        suby.insert("y".to_string(), x.clone());
        let mut subt = Substitution::new();
        subt.insert("x".to_string(), t1.clone());
        subt.insert("y".to_string(), x.clone());
        subt.insert("z".to_string(), y.clone());

        assert_eq!(substitute_qf(&t1, &subx), t1_subx);
        assert_eq!(substitute_qf(&t1, &suby), t1_suby);
        assert_eq!(substitute_qf(&t1, &subt), t1_subt);
    }
}
