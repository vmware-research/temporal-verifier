// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! A collection of bounded model checkers.

// configure clippy
#![allow(clippy::needless_return)]
#![allow(clippy::large_enum_variant)]
#![allow(clippy::upper_case_acronyms)]
#![allow(clippy::type_complexity)]
#![deny(clippy::uninlined_format_args)]
#![allow(clippy::new_without_default)]
// documentation-related lints (only checked when running rustdoc)
#![warn(missing_docs)]
#![allow(rustdoc::private_intra_doc_links)]
#![deny(rustdoc::broken_intra_doc_links)]

pub mod checker;
pub mod indices;
pub mod quant_enum;

pub mod bdd;
pub mod sat;
pub mod set;
pub mod simulator;
pub mod smt;
