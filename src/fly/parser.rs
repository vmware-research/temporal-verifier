// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

use crate::fly::syntax::*;
use codespan_reporting::diagnostic::{Diagnostic, Label};
use peg::{error::ParseError, str::LineCol};

peg::parser! {

grammar parser() for str {
    use BinOp::*;
    use NOp::*;
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
            sort: sort.unwrap_or(Sort::Id("".to_owned()))
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
        x:(@) _ "|" _ y:@ { Term::nary(Or, x, y) }
        --
        x:(@) _ "&" _ y:@ { Term::nary(And, x, y) }
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
      s:ident() { Sort::Id(s) }

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
          signature: sig, defs, statements: thm,
         } }

      pub rule module() -> Module = traced(<module0()>)

      rule spanned<T>(e: rule<T>) -> Spanned<T>
      = start:position!() x:e() end:position!()
        { Spanned {x, span: Span{start,end} } }

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

#[cfg(test)]
mod tests {
    use super::parser::*;
    use crate::fly::syntax::*;

    #[test]
    fn test_ident() {
        assert_eq!(ident("hello"), Ok("hello".to_string()));
        assert_eq!(ident("a"), Ok("a".to_string()));
        assert_eq!(ident("hello_world"), Ok("hello_world".to_string()));
        assert_eq!(ident("_allowed"), Ok("_allowed".to_string()));
        assert!(ident("1up").is_err());
    }

    #[test]
    fn test_term() {
        term("!p & !q").unwrap();

        term("p''").unwrap();
        term("(p')'").unwrap();

        term("p(x, y)").unwrap();
        term("p(x,y)").unwrap();

        // & and | at the same level are grouped into a single NAry
        assert_eq!(term("(p & q) & r").unwrap(), term("p & q & r").unwrap());
        assert_eq!(term("p & (q & r)").unwrap(), term("p & q & r").unwrap());
        assert_eq!(term("p | (q | r)").unwrap(), term("(p | q) | r").unwrap());

        // precedence of & and |
        assert_eq!(term("a | b & c").unwrap(), term("a | (b & c)").unwrap());

        // always is treated as an atomic keyword
        assert_ne!(term("alwaysx").unwrap(), term("always x").unwrap());

        assert!(term("= x").is_err());
    }

    #[test]
    fn test_term_precedence() {
        assert_eq!(
            term("!p & !q & !r").unwrap(),
            term("(!p) & (!q) & (!r)").unwrap()
        );

        assert_eq!(
            term("always p'=(p|q) & q'=q").unwrap(),
            term("always (p'=(p|q) & ((q')=q))").unwrap()
        );
    }

    #[test]
    fn test_signature() {
        let s = signature(
            r"mutable p: bool
mutable q: bool",
        )
        .unwrap();
        assert_eq!(s.relations.len(), 2);
    }

    #[test]
    fn test_module() {
        let m = module(
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
        .unwrap();
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
        term("forall x:t. x = y").unwrap();
        term("forall x:t, y:t. x = y").unwrap();
        term("forall x:t,y:t. x = y").unwrap();
        term("forall x:t , y:t. x = y").unwrap();
        term("forall x:t, y:t. x = y | y != x").unwrap();
        term("forall (x : t). x").unwrap();
        term("forall (x : t),(y:t). x = y").unwrap();

        assert_eq!(
            term("forall x:t. x = y & exists z:t. x = z").unwrap(),
            term("forall x:t. (x = y & exists z:t. x = z)").unwrap(),
        );

        assert_eq!(
            term("forall (x : t), (y : t2). f(x) & f(y)").unwrap(),
            term("forall x:t, y:t2 . f(x) & f(y)").unwrap(),
        );
    }
}

#[cfg(test)]
/// Parse a single term. Only used for testing.
pub fn parse_term(s: &str) -> Result<Term, String> {
    parser::term(s).map_err(|err| err.to_string())
}

#[cfg(test)]
/// Parse a signature. Only used for testing.
pub fn parse_signature(s: &str) -> Signature {
    parser::signature(s).expect("invalid signature in test")
}

/// Parse a fly module, reporting a human-readable error on failure.
pub fn parse(s: &str) -> Result<Module, ParseError<LineCol>> {
    parser::module(s)
}

pub fn parse_error_diagonistic<FileId>(
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
