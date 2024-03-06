// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Parser for the flyvy language.

use crate::syntax::*;
use codespan_reporting::diagnostic::{Diagnostic, Label};
use peg::{error::ParseError, str::LineCol};
use std::sync::Arc;

// TODO(oded): Use smart constructors in this module. In principle, no Term
// should be constructed directly by a (non-smart) constructor. I expect this
// will simplify the code, and if there are exceptions then we can revisit the
// design of the smart consturctors.

peg::parser! {

grammar parser() for str {
    use BinOp::*;
    use UOp::*;
    use Quantifier::*;

    rule ident_start() = ['a'..='z' | 'A'..='Z' | '_']
    rule ident_char() = ident_start() / ['0'..='9']
    pub(super) rule ident() -> String
    = s:$(quiet!{ident_start() ident_char()*} / expected!("identifier"))
    { s.to_string() }

    rule nl() = quiet!{ ['\n' | '\r'] } / expected!("newline")
    rule comment() = "#" [^'\n' | '\r']* nl()
    rule ws_no_nl() = quiet!{ [' ' | '\t' ] / comment() }
    rule whitespace() = quiet! { ws_no_nl() / nl() }
    rule word_boundary() = !ident_char()
    rule _ = whitespace()*
    rule __ = word_boundary() _

    rule binder() -> Binder
    =  "(" name:ident() _ ":" _ sort:sort() ")" { Binder {name, sort } } /
        name:ident() sort:(_ ":" _ s:sort() { s })? { Binder {
            name,
            sort: sort.unwrap_or(Sort::unknown())
        } }

    pub(super) rule term() -> Term = precedence!{
        q:("forall" { Forall } / "exists" { Exists }) __
            binders:(binder() ** (_ "," _)) _ "." _ body:@
        { Term::Quantified {
            quantifier: q,
            binders,
            body: Box::new(body),
          } }

        --

        x:@ _ "->" _ y:(@) { Term::BinOp(Implies, Box::new(x), Box::new(y)) }
        x:(@) _ "<->" _ y:@ { Term::BinOp(Iff, Box::new(x), Box::new(y)) }
        --

        op:("always" { Always } / "eventually" { Eventually }) __ x:@
        { Term::UnaryOp(op, Box::new(x)) }

        --
        "if" __ cond:term() __ "then" __ then:term() __ "else" __  else_:(@) {
            Term::Ite { cond: Box::new(cond), then: Box::new(then), else_: Box::new(else_) }
        }
        --
        x:(@) _ "|" _ y:@ { Term::or([x, y]) }
        --
        x:(@) _ "&" _ y:@ { Term::and([x, y]) }
        --
        // NOTE(tej): precedence of these operators was an arbitrary choice
        x:@ _ "until" _ y:(@) { Term::BinOp(BinOp::Until, Box::new(x), Box::new(y)) }
        x:@ _ "since" _ y:(@) { Term::BinOp(BinOp::Since, Box::new(x), Box::new(y)) }
        --
        // NOTE(tej): precedence of these operators was an arbitrary choice
        "X" __ x:@ { Term::UnaryOp(UOp::Next, Box::new(x)) }
        "X^-1" __ x:@ { Term::UnaryOp(UOp::Previous, Box::new(x)) }
        --
        x:(@) _ "=" _ y:@ { Term::BinOp(Equals, Box::new(x), Box::new(y)) }
        x:(@) _ "!=" _ y:@ { Term::BinOp(NotEquals, Box::new(x), Box::new(y)) }
        --
        "!" x:@ { Term::UnaryOp(Not, Box::new(x)) }
        --
        t:(@) "'" { Term::UnaryOp(Prime, Box::new(t)) }
        --
        // note that no space is allowed between relation name and args, so p (q)
        // doesn't parse as a relation call
        f:ident() ps:("\'"*) "(" args:(term() ** (_ "," _)) ")" { Term::App(f, ps.len(), args) }
        s:ident() { match s.as_str() {
            "false" => Term::Literal(false),
            "true" => Term::Literal(true),
            _ => Term::Id(s),
        } }
        "(" _ t:term() _ ")" { t }
    }

    rule sort() -> Sort
    = ("bool" word_boundary() { Sort::Bool }) /
      s:ident() { Sort::Uninterpreted(s) }

    rule sort_decl() -> String
    = "sort" __ s:ident() { s }

    // matches whitespace with at least one newline
    rule newline_separator()
    = quiet!{ ws_no_nl()* (comment() / nl()) _ } / expected!("newline separator")

    rule newline_separated<T>(e: rule<T>) -> Vec<T>
    = e() ** newline_separator()

    rule mutability() -> bool
    = "mutable" word_boundary() { true } /
      "immutable" word_boundary() { false }

    rule relation_args() -> Vec<Sort>
    = "(" _ ss:(sort() ** (_ "," _)) _ ")" { ss } /
       "" { vec![] }

    rule relation_decl() -> RelationDecl
    = m:mutability() _ r:ident() args:relation_args() _ ":" _ s:sort()
    { RelationDecl{
      mutable: m,
      name: r,
      args,
      sort: s,
    } }

    pub(super) rule signature() -> Signature
    = sorts:newline_separated(<sort_decl()>) _
      relations:newline_separated(<relation_decl()>)
     { Signature {
        sorts,
        relations,
     } }

     rule def_binder() -> Binder
     = name:ident() _ ":" _ sort:sort() { Binder { name, sort } }

     rule def_binders() -> Vec<Binder>
     = "(" _ args:(def_binder() ** (_ "," _)) _ ")" { args }

     rule def() -> Definition
     = "def" __ name:ident() _ binders:def_binders() _ "->" _ ret_sort:sort() _
       "{" _ body:term() _ "}"
     { Definition { name, binders, ret_sort, body } }

     rule defs() -> Vec<Definition>
     = newline_separated(<def()>)

     rule assume_stmt() -> ThmStmt
     = "assume" __ t:term() { ThmStmt::Assume(t) }

     rule invariants() -> Vec<Spanned<Term>>
     = newline_separated(<spanned(<"invariant" __ t:term() { t }>)>)

     rule assert_stmt() -> ThmStmt
     = t:spanned(<"assert" __ t:term() {t}>)
       invariants:(newline_separator()
        "proof" __ "{" _ invs:invariants() _ "}" {invs})?
       { ThmStmt::Assert(Proof{
          assert: t, invariants: invariants.unwrap_or_default(),
         }) }

      pub(super) rule stmt() -> ThmStmt
      = assume_stmt() / assert_stmt()

     rule stmts() -> Vec<ThmStmt>
     = newline_separated(<stmt()>)

     rule module0() -> Module
     = _ sig:signature() _ defs:defs() _ thm:stmts() _
       { Module{
          signature: Arc::new(sig), defs, statements: thm,
         } }

      pub rule module() -> Module = traced(<module0()>)

      rule spanned<T>(e: rule<T>) -> Spanned<T>
      = start:position!() x:e() end:position!()
        { Spanned {x, span: Some(Span{start,end}) } }

     // wrap a rule with tracing support, gated under the trace feature
     rule traced<T>(e: rule<T>) -> T =
         &(input:$([_]*) {
             #[cfg(feature = "trace")]
             println!("[PEG_INPUT_START]\n{}\n[PEG_TRACE_START]", input);
         })
         e:e()? {?
             #[cfg(feature = "trace")]
             println!("[PEG_TRACE_STOP]");
             e.ok_or("")
         }
  }
}

/// Parse a single term.
pub fn term(s: &str) -> Term {
    parser::term(s).expect("test term should parse")
}

/// Parse a signature.
pub fn parse_signature(s: &str) -> Signature {
    parser::signature(s.trim()).expect("invalid signature in test")
}

/// Parse a fly module, reporting a human-readable error on failure.
pub fn parse(s: &str) -> Result<Module, ParseError<LineCol>> {
    parser::module(s)
}

/// Convert an opaque FileId and error to a readable `Diagnostic`
pub fn parse_error_diagnostic<FileId>(
    file_id: FileId,
    e: &ParseError<LineCol>,
) -> Diagnostic<FileId> {
    Diagnostic::error()
        .with_message("could not parse file")
        .with_labels(vec![Label::primary(
            file_id,
            e.location.offset..e.location.offset + 1,
        )
        .with_message(format!("expected {}", e.expected))])
}

#[cfg(test)]
mod tests {
    use super::parser;
    use crate::syntax::*;

    fn ident(s: &str) -> String {
        parser::ident(s).expect("test ident should parse")
    }

    fn term(s: &str) -> Term {
        parser::term(s).expect("term in test should parse")
    }

    #[test]
    fn test_ident() {
        assert_eq!(&ident("hello"), "hello");
        assert_eq!(&ident("a"), "a");
        assert_eq!(&ident("hello_world"), "hello_world");
        assert_eq!(&ident("_allowed"), "_allowed");
        assert!(parser::ident("1up").is_err());
    }

    #[test]
    fn test_term() {
        term("!p & !q");

        term("p''");
        term("(p')'");

        term("p(x, y)");
        term("p(x,y)");

        // & and | at the same level are grouped into a single NAry
        assert_eq!(term("(p & q) & r"), term("p & q & r"));
        assert_eq!(term("p & (q & r)"), term("p & q & r"));
        assert_eq!(term("p | (q | r)"), term("(p | q) | r"));

        // precedence of & and |
        assert_eq!(term("a | b & c"), term("a | (b & c)"));

        // precedence of &, ->, and until
        // matches examples in https://www.cl.cam.ac.uk/teaching/1617/HLog+ModC/slides/lecture-8.pdf
        assert_eq!(term("a | b -> c until d"), term("(a | b) -> (c until d)"));
        assert_eq!(term("a -> b | always c"), term("a -> (b | (always c))"),);
        assert_eq!(
            term("always p -> eventually X^-1 b"),
            term("(always p) -> (eventually (X^-1 b))"),
        );

        // always is treated as an atomic keyword
        assert_ne!(term("alwaysx"), term("always x"));

        assert!(parser::term("= x").is_err());
    }

    #[test]
    fn test_term_precedence() {
        assert_eq!(term("!p & !q & !r"), term("(!p) & (!q) & (!r)"));

        assert_eq!(
            term("always p'=(p|q) & q'=q"),
            term("always (p'=(p|q) & ((q')=q))")
        );

        assert_eq!(term("always ((X p) until q)"), term("always X p until q"),);

        assert_eq!(term("p until q since r"), term("p until (q since r)"),);
    }

    #[test]
    fn test_term_associativity() {
        assert_ne!(term("(p until q) since r"), term("p until q since r"),);
    }

    #[test]
    fn test_signature() {
        let s = parser::signature(
            r"mutable p: bool
mutable q: bool",
        )
        .expect("test signature should parse");
        assert_eq!(s.relations.len(), 2);
    }

    #[test]
    fn test_module() {
        let m = parser::module(
            r"mutable p: bool
mutable q: bool

assume !p & !q & (always p'=(p|q) & q'=q)
assert always !p
proof {
    invariant !p
    invariant !q
    # invariant $l2s_w. p
}

# we don't allow this: forall x:t1. exists x:t2. p(x:t1, x:t2)
",
        )
        .expect("test module should parse");
        assert_eq!(m.signature.relations.len(), 2);
        assert_eq!(m.statements.len(), 2);
        match &m.statements[1] {
            ThmStmt::Assert(pf) => {
                assert_eq!(pf.invariants.len(), 2, "wrong number of invariants parsed")
            }
            _ => panic!("incorrect 2nd statement"),
        }
    }

    #[test]
    fn test_quantifiers() {
        term("forall x:t. x = y");
        term("forall x:t, y:t. x = y");
        term("forall x:t,y:t. x = y");
        term("forall x:t , y:t. x = y");
        term("forall x:t, y:t. x = y | y != x");
        term("forall (x : t). x");
        term("forall (x : t),(y:t). x = y");

        term("forall. true"); // empty quantifiers are allowed!

        assert_eq!(
            term("forall x:t. x = y & exists z:t. x = z"),
            term("forall x:t. (x = y & exists z:t. x = z)"),
        );

        assert_eq!(
            term("forall (x : t), (y : t2). f(x) & f(y)"),
            term("forall x:t, y:t2 . f(x) & f(y)"),
        );
    }

    #[test]
    fn test_if_then_else() {
        term("if x then true else false");
        term("if forall x. x = y then q else r");
        assert_eq!(
            term("if x = y then a & b else c | d"),
            term("if x = y then (a & b) else (c | d)"),
        );
        assert_eq!(
            term("a & if x = y then a & b else c & d"),
            term("a & (if x = y then a & b else (c & d))"),
        );
    }
}
