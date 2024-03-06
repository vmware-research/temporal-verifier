// Copyright 2022-2023 VMware, Inc.
// SPDX-License-Identifier: BSD-2-Clause

//! Invariant inference
//!
//! Mostly consists of an implementation of the "q-alpha" algorithm, but also
//! provides an implementation of Houdini.

#![allow(missing_docs)] // TODO: remove
// configure clippy
#![allow(clippy::needless_return)]
#![allow(clippy::large_enum_variant)]
#![allow(clippy::upper_case_acronyms)]
#![allow(clippy::type_complexity)]
#![allow(clippy::new_without_default)]
#![deny(clippy::uninlined_format_args)]
#![allow(clippy::len_without_is_empty)]
// documentation-related lints (only checked when running rustdoc)
#![allow(rustdoc::private_intra_doc_links)]
#![deny(rustdoc::broken_intra_doc_links)]

pub mod basics;
pub mod hashmap;
pub mod houdini;
pub mod marco;
mod parallel;
pub mod qalpha;
pub mod updr;
