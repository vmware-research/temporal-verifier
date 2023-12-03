// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Pretty-printer for the flyvy language.

use std::fmt;

use crate::syntax::*;

fn precedence(t: &Term) -> usize {
    use crate::syntax::{BinOp::*, NOp::*, Quantifier::*, Term::*, UOp::*};

    match t {
        Quantified {
            quantifier: Forall | Exists,
            ..
        } => 0,
        BinOp(Implies | Iff, _, _) => 10,
        UnaryOp(Always | Eventually, _) => 20,
        Ite { .. } => 30,
        NAryOp(Or, _) => 40,
        NAryOp(And, _) => 50,
        BinOp(Until | Since, _, _) => 52,
        UnaryOp(Next | Previous, _) => 54,
        BinOp(Equals | NotEquals, _, _) => 60,
        UnaryOp(Not, _) => 70,
        UnaryOp(Prime, _) => 80,
        Literal(_) | Id(_) | App(_, _, _) => 1000,
    }
}

fn parens(add_parens: bool, s: String) -> String {
    if add_parens {
        format!("({s})")
    } else {
        s
    }
}

fn right_associative(op: &BinOp) -> bool {
    matches!(op, BinOp::Implies | BinOp::Since | BinOp::Until)
}

fn left_associative(_op: &BinOp) -> bool {
    false
}

/// Pretty-print a binder
pub fn binder(b: &Binder) -> String {
    format!("{}:{}", b.name, sort(&b.sort))
}

/// Pretty-print a term
pub fn term(t: &Term) -> String {
    // handling of precedence is based on
    // https://stackoverflow.com/questions/6277747/pretty-print-expression-with-as-few-parentheses-as-possible
    match t {
        Term::Literal(false) => "false".to_string(),
        Term::Literal(true) => "true".to_string(),
        Term::Id(i) => i.to_string(),
        Term::App(f, p, args) => format!(
            "{}{}({})",
            f,
            "\'".repeat(*p),
            args.iter().map(term).collect::<Vec<_>>().join(", ")
        ),
        Term::UnaryOp(op, arg) => {
            let arg = parens(precedence(t) > precedence(arg), term(arg));
            match op {
                UOp::Not => format!("!{arg}"),
                UOp::Prime => format!("{arg}'"),
                UOp::Always => format!("always {arg}"),
                UOp::Eventually => format!("eventually {arg}"),
                UOp::Next => format!("X {arg}"),
                UOp::Previous => format!("X^-1 {arg}"),
            }
        }
        Term::BinOp(op, arg1, arg2) => {
            let use_left_paren = precedence(t) > precedence(arg1)
                || (precedence(t) == precedence(arg1) && right_associative(op));
            let use_right_paren = precedence(t) > precedence(arg2)
                || (precedence(t) == precedence(arg2) && left_associative(op));
            let left = parens(use_left_paren, term(arg1));
            let right = parens(use_right_paren, term(arg2));
            let op = match op {
                BinOp::Equals => "=",
                BinOp::NotEquals => "!=",
                BinOp::Implies => "->",
                BinOp::Iff => "<->",
                BinOp::Until => "until",
                BinOp::Since => "since",
            };
            format!("{left} {op} {right}")
        }
        Term::NAryOp(op, args) => {
            let args = args
                .iter()
                .map(|arg| parens(precedence(t) > precedence(arg), term(arg)))
                .collect::<Vec<_>>();
            let op = match op {
                NOp::And => "&",
                NOp::Or => "|",
            };
            args.join(&format!(" {op} "))
        }
        Term::Ite { cond, then, else_ } => {
            let cond = term(cond);
            // TODO: not sure this gets the right rules, especially for
            // associating nested if-then-else
            let then = parens(precedence(t) >= precedence(then), term(then));
            let else_ = parens(precedence(t) > precedence(else_), term(else_));
            format!("if {cond} then {then} else {else_}")
        }
        Term::Quantified {
            quantifier,
            binders,
            body,
        } => {
            let quantifier = match quantifier {
                Quantifier::Forall => "forall",
                Quantifier::Exists => "exists",
            };
            let binders = binders.iter().map(binder).collect::<Vec<_>>().join(", ");
            format!("{quantifier} {binders}. {}", term(body))
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", term(self))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser;

    fn parse(s: &str) -> Term {
        parser::term(s)
    }

    fn reprint(s: &str) -> String {
        term(&parse(s))
    }

    #[test]
    fn test_printer_basic() {
        let e = parse("a & b | c");
        insta::assert_display_snapshot!(term(&e), @"a & b | c");
        assert_eq!(parse(&term(&e)), e);
    }

    #[test]
    fn test_printer_nary() {
        for s in [
            "a & b & c | d & e",
            "a & b & (c | d) & e",
            "a | b | c & d | e",
        ] {
            assert_eq!(reprint(s), s, "{s} did not roundtrip through printer");
        }
    }

    #[test]
    fn test_roundtrip() {
        let e = parse("a & b & c | d & e");
        assert_eq!(parse(&term(&e)), e);

        let e = parse("a | b | c & d | e");
        assert_eq!(parse(&term(&e)), e);

        insta::assert_display_snapshot!(reprint("forall x:t1, y:t2. f(x, y)"), @"forall x:t1, y:t2. f(x, y)");

        insta::assert_display_snapshot!(reprint("eventually X p until X q"), @"eventually X p until X q");
        insta::assert_display_snapshot!(reprint("eventually (X p) until (X q)"), @"eventually X p until X q");

        insta::assert_display_snapshot!(reprint("p until q since always r"), @"p until q since (always r)");
        insta::assert_display_snapshot!(reprint("p until (q since (always r))"), @"p until q since (always r)");
    }

    #[test]
    fn test_printer_advanced() {
        insta::assert_display_snapshot!(
          reprint("(always a) -> (eventually b)"),
          @"always a -> eventually b");
        insta::assert_display_snapshot!(
          reprint("always (a -> eventually b)"),
          @"always (a -> eventually b)");
        insta::assert_display_snapshot!(
          reprint("always a' & eventually c=d'"),
          @"always a' & (eventually c = d')");
        insta::assert_display_snapshot!(
          reprint("(always a)' & eventually (c=d)'"),
           @"(always a)' & (eventually (c = d)')");

        let s = "(p until q) since (always r)";
        assert_eq!(parse(s), parse(&reprint(s)));
    }
}

fn sort(s: &Sort) -> String {
    match s {
        Sort::Bool => "bool".to_string(),
        Sort::Uninterpreted(i) => i.to_string(),
    }
}

fn relation_decl(decl: &RelationDecl) -> String {
    let name = decl.name.to_string();
    let args = if decl.args.is_empty() {
        "".to_string()
    } else {
        format!(
            "({})",
            decl.args.iter().map(sort).collect::<Vec<_>>().join(", ")
        )
    };
    let sort = sort(&decl.sort);
    format!(
        "{} {name}{args}: {sort}",
        if decl.mutable { "mutable" } else { "immutable" },
    )
}

fn signature(sig: &Signature) -> String {
    let sorts = sig
        .sorts
        .iter()
        // end with trailing newline if there are any sorts
        .map(|s| format!("sort {s}\n"))
        .collect::<Vec<_>>()
        .join("");
    let relations = sig
        .relations
        .iter()
        .map(|decl| format!("{}\n", relation_decl(decl)))
        .collect::<Vec<_>>()
        .join("");
    format!("{sorts}{relations}")
}

fn def_binder(binder: &Binder) -> String {
    format!("{}: {}", &binder.name, sort(&binder.sort))
}

fn def(def: &Definition) -> String {
    let binders = def
        .binders
        .iter()
        .map(def_binder)
        .collect::<Vec<_>>()
        .join(", ");
    let ret_sort = sort(&def.ret_sort);
    let body = term(&def.body);
    format!(
        "def {name}({binders}) -> {ret_sort} {{\n  {body}\n}}",
        name = &def.name
    )
}

fn proof(p: &Proof) -> String {
    let assert = format!("assert {}", term(&p.assert.x));
    let invariants = p
        .invariants
        .iter()
        .map(|inv| format!("  invariant {}", term(&inv.x)))
        .collect::<Vec<_>>()
        .join("\n");
    format!("{assert}\nproof {{\n{invariants}\n}}")
}

fn thm_stmt(s: &ThmStmt) -> String {
    match s {
        ThmStmt::Assume(t) => format!("assume {}", term(t)),
        ThmStmt::Assert(p) => proof(p),
    }
}

fn module(m: &Module) -> String {
    let sig = signature(&m.signature);
    let defs = m
        .defs
        .iter()
        .map(|d| format!("{}\n\n", def(d)))
        .collect::<Vec<_>>()
        .join("");
    let stmts = m
        .statements
        .iter()
        .map(thm_stmt)
        .collect::<Vec<_>>()
        .join("\n");
    format!("{sig}\n{defs}{stmts}")
}

/// Pretty-print a module.
pub fn fmt(m: &Module) -> String {
    module(m)
}

#[cfg(test)]
mod module_tests {
    use super::*;
    use crate::parser::parse;
    use std::fs;

    #[test]
    fn test_module_print() {
        let s = fs::read_to_string("../temporal-verifier/tests/examples/basic1.fly")
            .expect("could not read basic1.fly");
        let m = parse(&s).expect("basic1.fly should parse");
        insta::assert_display_snapshot!(module(&m));
    }
}
