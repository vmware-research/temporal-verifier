// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

use crate::fly::syntax::*;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum SortError {
	#[error("module signature should not contain bool")]
	UninterpretedBool,
	#[error("this sort was not declared")]
	UnknownSort(String),
	#[error("this binder was unknown")]
	UnknownName(String),
    #[error("expected one type but found another")]
    NotEqual(Sort, Sort),
}

fn sort_is_bool(sort: &Sort) -> Result<(), SortError> {
	match sort {
		Sort::Bool => Ok(()),
		Sort::Id(_) => Err(SortError::NotEqual(sort.clone(), Sort::Bool))
	}
}

pub fn check(module: &Module) -> Result<(), SortError> {
	let mut context = Context {
		sorts: vec![],
		names: im::HashMap::new(),
	};

	for sort in &module.signature.sorts {
		match sort {
			Sort::Bool => Err(SortError::UninterpretedBool)?,
			Sort::Id(s) => context.sorts.push(s.to_owned()),
		}
	}

	for relation in &module.signature.relations {
		check_relation(&context, relation)?;
	}

	for definition in &module.defs {
		check_definition(&context, definition)?;
	}

	for statement in &module.statements {
		check_statement(&context, statement)?;
	}

	Ok(())
}

struct Context {
	sorts: Vec<String>,
	names: im::HashMap<String, Sort>,
}

fn check_statement(context: &Context, statement: &ThmStmt) -> Result<(), SortError> {
	match statement {
		ThmStmt::Assume(term) => sort_is_bool(&check_term(context, term)?),
		ThmStmt::Assert(proof) => check_proof(context, proof),
	}
}

fn check_proof(context: &Context, proof: &Proof) -> Result<(), SortError> {
	for invariant in &proof.invariants {
		sort_is_bool(&check_term(context, &invariant.x)?)?;
	}
	sort_is_bool(&check_term(context, &proof.assert.x)?)
}

fn check_definition(_context: &Context, _definition: &Definition) -> Result<(), SortError> {
	todo!("we don't check definitions yet")
}

fn check_relation(_context: &Context, _relation: &RelationDecl) -> Result<(), SortError> {
	todo!()
}

fn check_sort(context: &Context, sort: &Sort) -> Result<(), SortError> {
	match sort {
		Sort::Bool => Ok(()),
		Sort::Id(a) => match context.sorts.iter().find(|b| a == *b) {
			Some(_) => Ok(()),
			None => Err(SortError::UnknownSort(a.clone()))
		}
	}
}

fn check_binder(context: &Context, binder: &Binder) -> Result<(), SortError> {
	check_sort(context, &binder.sort)?;
	match context.names.get(&binder.name) {
		Some(sort) => match *sort == binder.sort {
			true => Ok(()),
			false => Err(SortError::NotEqual(sort.clone(), binder.sort.clone())),
		},
		None => Err(SortError::UnknownName(binder.name.clone())),
	}
}

fn check_term(_context: &Context, _term: &Term) -> Result<Sort, SortError> {
	todo!()
}
