use std::{collections::HashMap, iter::zip};

use super::syntax::{Binder, Definition, Module, Proof, Term, ThmStmt};

fn subst(t: &mut Term, repl: &HashMap<String, &Term>) {
    let go = |t: &mut Term| subst(t, repl);
    match t {
        Term::Literal(_) => {}
        Term::Id(ref s) => {
            if let Some(&y) = repl.get(s) {
                *t = y.clone();
            }
        }
        Term::App(_f, _p, xs) => {
            for t in xs {
                go(t);
            }
        }
        Term::UnaryOp(_, x) => go(x),
        Term::BinOp(_, lhs, rhs) => {
            go(lhs);
            go(rhs);
        }
        Term::NAryOp(_, args) => {
            for a in args {
                go(a);
            }
        }
        Term::Ite { cond, then, else_ } => {
            go(cond);
            go(then);
            go(else_);
        }
        // TODO: didn't worry about shadowing here
        Term::Quantified { body, .. } => go(body),
    }
}

fn subst_binders(t: &mut Term, xs: &[Binder], ts: &[Term]) {
    let repl = zip(xs, ts).map(|(x, y)| (x.name.clone(), y)).collect();
    subst(t, &repl);
}

fn inline_def_term(def: &Definition, t: &mut Term) {
    let body = &def.body;
    let go = |t: &mut Term| inline_def_term(def, t);
    match t {
        Term::Literal(_) => {}
        Term::Id(s) => {
            if s == &def.name {
                assert_eq!(def.binders.len(), 0, "substitution does not match arity");
                *t = body.clone();
            }
        }
        Term::App(f, _p, ts) => {
            if f == &def.name {
                // substitute ts for def.binders in body before doing the replacement
                let mut body = body.clone();
                subst_binders(&mut body, &def.binders, ts);
                *t = body;
            }
        }
        Term::UnaryOp(_, x) => go(x),
        Term::BinOp(_, lhs, rhs) => {
            go(lhs);
            go(rhs);
        }
        Term::NAryOp(_, args) => {
            for a in args {
                go(a);
            }
        }
        Term::Ite { cond, then, else_ } => {
            go(cond);
            go(then);
            go(else_);
        }
        Term::Quantified { body, binders, .. } => {
            if binders.iter().any(|b| b.name == def.name) {
                // definition is shadowed
                return;
            }
            go(body)
        }
    }
}

impl Module {
    fn inline_def(&mut self, def: &Definition) {
        for other_def in &mut self.defs {
            inline_def_term(def, &mut other_def.body);
        }
        for step in &mut self.statements {
            match step {
                ThmStmt::Assume(e) => inline_def_term(def, e),
                ThmStmt::Assert(Proof { assert, invariants }) => {
                    inline_def_term(def, &mut assert.x);
                    for inv in invariants {
                        inline_def_term(def, &mut inv.x);
                    }
                }
            }
        }
    }

    pub fn inline_defs(&mut self) {
        while !self.defs.is_empty() {
            let def = self.defs.remove(0);
            self.inline_def(&def);
        }
    }
}
