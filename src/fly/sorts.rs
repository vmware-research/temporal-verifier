// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

use crate::fly::syntax::*;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum SortError {
	#[error("module signature should not contain bool")]
	UninterpretedBool,
    #[error("expected one type but found another")]
    NotEqual(Sort, Sort),
}


pub fn check(module: &Module) -> Result<(), SortError> {
	for sort in &module.signature.sorts {
		if let Sort::Bool = sort {
			return Err(SortError::UninterpretedBool)
		}
	}

	let context = Context {
		sorts: module.signature.sorts.clone(),
		names: im::HashMap::new(),
	};

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
	sorts: Vec<Sort>,
	names: im::HashMap<String, Sort>,
}

fn check_statement(context: &Context, statement: &ThmStmt) -> Result<(), SortError> {
	match statement {
		ThmStmt::Assume(term) => {
			let sort = check_term(context, term)?;
			if sort != Sort::Bool {
				return Err(SortError::NotEqual(sort, Sort::Bool))
			}
			Ok(())
		},
		ThmStmt::Assert(proof) => check_proof(context, proof),
	}
}

fn check_proof(_context: &Context, _proof: &Proof) -> Result<(), SortError> {
	todo!()
}

fn check_definition(_context: &Context, _definition: &Definition) -> Result<(), SortError> {
	todo!()
}

fn check_relation(_context: &Context, _relation: &RelationDecl) -> Result<(), SortError> {
	todo!()
}

fn check_sort(_context: &Context, _sort: &Sort) -> Result<(), SortError> {
	todo!()
}

fn check_term(_context: &Context, _term: &Term) -> Result<Sort, SortError> {
	todo!()
}
